/-!
# HTTP/1.1 message framing (RFC 9112 §6), and why it is unambiguous

Request smuggling happens when two parties on a connection — a proxy in front and the server behind
it — disagree about where one HTTP message ends and the next begins. If the front-end reads the body one
way and the back-end reads it another, an attacker can hide a second request inside the first.

RFC 9112 §6.1 gives the rules for deciding a message body's length. This file writes those rules down, and
proves the property that rules smuggling out: **on every message the conformant checker accepts, the two
readings that a desync plays off against each other — "trust Content-Length" and "trust Transfer-Encoding"
— compute the same message boundary.** So a conformant front-end and a conformant back-end cannot disagree.

The dangerous combinations (both headers at once, conflicting `Content-Length` values, a `Transfer-Encoding`
that does not end in `chunked`) are exactly the ones the checker rejects, and the theorem holds because it
rejects them.

No Mathlib. Bytes are `UInt8`; header names and values are byte lists.
-/

namespace Http1

/-- A header field: a name and a value, as raw bytes. -/
structure Field where
  name : List UInt8
  value : List UInt8
  deriving DecidableEq, Repr

abbrev Headers := List Field

/-! ## ASCII helpers -/

/-- Fold an ASCII byte to lower case; leave everything else alone (RFC 9110 field names are ASCII). -/
def toLowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32 else b

def toLower (s : List UInt8) : List UInt8 := s.map toLowerByte

/-- Case-insensitive name match, as HTTP compares field names. -/
def Field.named (f : Field) (n : List UInt8) : Bool := toLower f.name == toLower n

/-- The bytes of an ASCII string literal, for naming headers. -/
def bytes (s : String) : List UInt8 := s.toUTF8.toList

def cOWS (b : UInt8) : Bool := b == 32 || b == 9  -- space or htab

/-- Strip leading and trailing spaces and htabs (OWS), as header value parsing does. -/
def trimOWS (s : List UInt8) : List UInt8 :=
  (s.dropWhile cOWS).reverse.dropWhile cOWS |>.reverse

/-! ## Parsing the two framing headers

`Content-Length` is a non-empty run of ASCII digits with no sign, no space, no plus (RFC 9110 §8.6). A value
that is anything else is not a length at all, and a reader must reject the message rather than guess. -/

def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- Read one `Content-Length` value: `some n` for a valid decimal, `none` for anything else. -/
def parseCL (v : List UInt8) : Option Nat :=
  let v := trimOWS v
  if v ≠ [] && v.all isDigit then
    some (v.foldl (fun acc b => acc * 10 + (b.toNat - 48)) 0)
  else none

/-- Every `Content-Length` field's parsed value, in order. -/
def contentLengths (h : Headers) : List (Option Nat) :=
  (h.filter (·.named (bytes "content-length"))).map (parseCL ·.value)

/-- Every `Transfer-Encoding` field's value, in order. -/
def transferEncodings (h : Headers) : List (List UInt8) :=
  (h.filter (·.named (bytes "transfer-encoding"))).map (·.value)

/-- Does a `Transfer-Encoding` value end in `chunked` as its final coding? RFC 9112 §6.1 keys the whole
framing on whether `chunked` is the *last* transfer coding. We take the last comma-separated token, trimmed,
folded to lower case. -/
def lastCodingIsChunked (v : List UInt8) : Bool :=
  let toks := (v.splitOn 44).map trimOWS  -- 44 = ','
  match toks.reverse.head? with
  | some t => toLower t == bytes "chunked"
  | none => false

/-- Does `chunked` appear anywhere in a `Transfer-Encoding` value (used to catch it appearing twice, or not
last, both of which RFC 9112 §6.1 and §6.3 make an error)? -/
def mentionsChunked (v : List UInt8) : Bool :=
  ((v.splitOn 44).map (fun t => toLower (trimOWS t))).any (· == bytes "chunked")

/-! ## The framing decision -/

/-- How a message body is delimited. `reject` means the message is malformed or ambiguous and MUST NOT be
processed (RFC 9112 §6.1: respond 400 and close, or close the connection). -/
inductive Framing where
  | reject
  | chunked
  | length (n : Nat)
  | untilClose
  deriving DecidableEq, Repr

/-- Whether this message even takes a body by the length rules (requests and most responses do; the
exceptions — HEAD, 1xx/204/304, CONNECT — are handled by the caller and passed as `bodyAllowed`). -/
structure Msg where
  /-- HTTP/1.0 does not define chunked; a 1.0 message carrying it is malformed. -/
  http11 : Bool
  /-- False for HEAD responses, 1xx/204/304, and 2xx to CONNECT: these have no body regardless of headers. -/
  bodyAllowed : Bool
  headers : Headers

/-- The transfer-encoding chain is *clean chunked*: exactly one `Transfer-Encoding` field, on HTTP/1.1,
whose final coding is `chunked`, with `chunked` appearing exactly once (RFC 9112 §6.1, §6.3). -/
def teValid (m : Msg) : Bool :=
  (transferEncodings m.headers).length == 1 && m.http11
    && lastCodingIsChunked (transferEncodings m.headers).head!
    && ((transferEncodings m.headers).head!.splitOn 44).countP
        (fun t => toLower (trimOWS t) == bytes "chunked") == 1

/-- Is any `Transfer-Encoding` field present at all? -/
def teAny (m : Msg) : Bool := !(transferEncodings m.headers == [])

/-- The `Content-Length` verdict: `none` = no field; `some (some n)` = one or more fields that all agree on
the valid value `n`; `some none` = present but invalid or conflicting (a reader must reject). -/
def clAgreed (m : Msg) : Option (Option Nat) :=
  let cls := contentLengths m.headers
  if cls == [] then none
  else if cls.all (· == cls.head!) then some cls.head!
  else some none

/-- RFC 9112 §6.1, made to reject rather than guess wherever two readers could differ.

* No body allowed (HEAD, 204, 304, 1xx, CONNECT 2xx) → the next message starts immediately.
* `Transfer-Encoding` present: accept only clean chunked with no `Content-Length` (RFC 9112 §6.1 forbids
  sending both; a recipient that forwards both is the classic CL.TE / TE.CL desync). Otherwise **reject**.
* Else `Content-Length`: one valid value, or agreeing duplicates → `length n`; invalid or conflicting →
  **reject**.
* Else a request has no body. -/
def frame (m : Msg) : Framing :=
  if !m.bodyAllowed then Framing.length 0
  else if teAny m then
    if teValid m && (contentLengths m.headers == []) then Framing.chunked else Framing.reject
  else match clAgreed m with
    | none => Framing.length 0
    | some (some n) => Framing.length n
    | some none => Framing.reject

/-! ## The anti-smuggling theorem

A desync is a disagreement between a reader that trusts `Content-Length` and one that trusts
`Transfer-Encoding`. Both are modelled as functions to `Framing`; the theorem is that they agree wherever
`frame` does not reject. -/

/-- The reader that resolves a CL/TE conflict in favour of `Content-Length` (the CL side of a desync). -/
def readerCL (m : Msg) : Framing :=
  if !m.bodyAllowed then Framing.length 0
  else match clAgreed m with
    | some (some n) => Framing.length n
    | _ => if teValid m then Framing.chunked else Framing.length 0

/-- The reader that resolves a CL/TE conflict in favour of `Transfer-Encoding` (the TE side of a desync). -/
def readerTE (m : Msg) : Framing :=
  if !m.bodyAllowed then Framing.length 0
  else if teValid m then Framing.chunked
  else match clAgreed m with
    | some (some n) => Framing.length n
    | _ => Framing.length 0

/-- A clean chunked chain has a `Transfer-Encoding` field, so `teAny` holds. -/
theorem teValid_imp_teAny {m : Msg} (h : teValid m = true) : teAny m = true := by
  simp only [teValid] at h
  unfold teAny
  cases hE : transferEncodings m.headers with
  | nil => rw [hE] at h; simp at h
  | cons a t => simp

/-- A valid, agreed `Content-Length` means at least one field is present. -/
theorem clAgreed_some_imp {m : Msg} {n : Nat} (h : clAgreed m = some (some n)) :
    contentLengths m.headers ≠ [] := by
  intro he
  simp [clAgreed, he] at h

/-- **No desync.** On every message `frame` accepts, the Content-Length-preferring reader and the
Transfer-Encoding-preferring reader compute the same framing. A conformant front-end and back-end that
differ only in which header they trust cannot be played against each other. -/
theorem no_desync (m : Msg) (h : frame m ≠ Framing.reject) : readerCL m = readerTE m := by
  by_cases hb : m.bodyAllowed
  · rcases hca : clAgreed m with _ | x
    · by_cases htv : teValid m <;> simp [readerCL, readerTE, hb, hca, htv]
    · rcases x with _ | n
      · by_cases htv : teValid m <;> simp [readerCL, readerTE, hb, hca, htv]
      · by_cases htv : teValid m
        · exfalso
          unfold frame at h
          rw [if_neg (by simp [hb]), if_pos (teValid_imp_teAny htv), htv] at h
          cases hL : contentLengths m.headers with
          | nil => exact clAgreed_some_imp hca hL
          | cons a t => rw [hL] at h; simp at h
        · simp [readerCL, readerTE, hb, hca, htv]
  · have hb' : m.bodyAllowed = false := by
      cases hbb : m.bodyAllowed with
      | true => exact absurd hbb hb
      | false => rfl
    simp [readerCL, readerTE, hb']

end Http1
