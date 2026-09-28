import Http1.Framing

/-!
# Reading the body, and where it ends

`no_desync` (Framing.lean) proves the framing *decision* is unambiguous. This file proves the layer below:
once the decision is made, the point where the body ends — and the next message begins — is a determined
function of the bytes. That is the byte-level anti-smuggling property: a message occupies a determined
prefix of the connection, so a front-end and back-end split the stream at the same place.

Two body forms:
* `Framing.length n` — the body is exactly the next `n` bytes; the remainder starts right after.
* `Framing.chunked` — the body runs to the `0 CRLF CRLF` terminator; the remainder starts after it.

For each we give the reader and prove it inverts the writer: reading a written body followed by *any*
continuation returns exactly that body and exactly that continuation.
-/

namespace Http1

def CRLF : List UInt8 := [13, 10]

/-! ## Length-delimited bodies -/

/-- Take exactly `n` bytes as the body; the rest is the remainder. Fails if fewer than `n` bytes remain. -/
def takeExact (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ bs.length then some (bs.take n, bs.drop n) else none

/-- **The length boundary is exact.** A body of length `n` followed by any continuation `rest` is read back
as exactly that body, leaving exactly `rest`. So where an `n`-byte message ends is determined by `n` and the
bytes, with nothing left to interpretation. -/
theorem takeExact_append (body rest : List UInt8) :
    takeExact body.length (body ++ rest) = some (body, rest) := by
  unfold takeExact
  rw [if_pos (by simp)]
  simp [List.take_append, List.drop_append]

/-! ## Chunked bodies

A chunk is `<hex-size> CRLF <size bytes> CRLF`; the body ends at a zero-size chunk `0 CRLF CRLF`. We model a
chunked body as the list of its chunk payloads and prove the reader inverts the writer. Chunk extensions and
trailers are out of scope (a stricter reader rejects them), which keeps the boundary canonical. -/

/-- Lowercase hex digit for a nibble `< 16`. -/
def hexDigit (n : Nat) : UInt8 :=
  if n < 10 then UInt8.ofNat (48 + n) else UInt8.ofNat (87 + n)

/-- The hex digits of `m`, most significant first, no leading zeros; `[]` for zero. `fuel` bounds the
recursion. -/
def toHexGo : Nat → Nat → List UInt8
  | 0, _ => []
  | _, 0 => []
  | fuel + 1, m => toHexGo fuel (m / 16) ++ [hexDigit (m % 16)]

/-- Canonical lowercase hex of a natural number (`"0"` for zero). -/
def toHex (n : Nat) : List UInt8 := if n = 0 then [hexDigit 0] else toHexGo (n + 1) n

/-- Value of a hex digit byte, or `none`. -/
def hexVal (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b && b ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b && b ≤ 70 then some (b.toNat - 55)
  else none

/-- Read a run of hex digits up to a CRLF, returning the value and the bytes after the CRLF. Rejects an
empty size, a non-hex byte, or a missing CRLF (so a malformed chunk size is a reject, not a guess).
`fuel` bounds the digits; `bs.length` is always enough. -/
def readChunkSizeF : Nat → Nat → Bool → List UInt8 → Option (Nat × List UInt8)
  | 0, _, _, _ => none
  | fuel + 1, acc, seen, input =>
    match input with
    | [] => none
    | b :: rest =>
      if b == 13 then
        match rest with
        | 10 :: rest2 => if seen then some (acc, rest2) else none
        | _ => none
      else
        match hexVal b with
        | some v => readChunkSizeF fuel (acc * 16 + v) true rest
        | none => none

def readChunkSize (bs : List UInt8) : Option (Nat × List UInt8) :=
  readChunkSizeF (bs.length + 1) 0 false bs

/-- Read a chunked body: successive chunks until a zero-size chunk, then a final CRLF. Returns the decoded
payload bytes and the remainder (the next message). `fuel` bounds the number of chunks. -/
def readChunkedF : Nat → List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, _, _ => none
  | fuel + 1, acc, input =>
    match readChunkSize input with
    | none => none
    | some (0, afterSize) =>
      match afterSize with
      | 13 :: 10 :: rest => some (acc, rest)
      | _ => none
    | some (n, afterSize) =>
      if n ≤ afterSize.length then
        match afterSize.drop n with
        | 13 :: 10 :: rest => readChunkedF fuel (acc ++ afterSize.take n) rest
        | _ => none
      else none

def readChunked (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  readChunkedF (bs.length + 1) [] bs

/-- Write one chunk: hex size, CRLF, data, CRLF. -/
def writeChunk (data : List UInt8) : List UInt8 :=
  toHex data.length ++ CRLF ++ data ++ CRLF

/-- Write a chunked body from its payloads: each chunk, then the `0 CRLF CRLF` terminator. -/
def writeChunked (chunks : List (List UInt8)) : List UInt8 :=
  (chunks.flatMap writeChunk) ++ toHex 0 ++ CRLF ++ CRLF

/-! ## Body reading, keyed by the framing decision -/

/-- Given a framing verdict, read the body and return `(body, remainder)`. `reject` never has a body. -/
def readBody : Framing → List UInt8 → Option (List UInt8 × List UInt8)
  | Framing.length n, bs => takeExact n bs
  | Framing.chunked, bs => readChunked bs
  | Framing.untilClose, bs => some (bs, [])
  | Framing.reject, _ => none

end Http1
