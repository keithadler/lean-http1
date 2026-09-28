import Http1.Framing

/-!
# A raw-bytes front end for the framing oracle

Splits a raw HTTP/1.1 request (bytes up to the blank line that ends the header block) into a `Msg`, so the
proved `frame` can be run on real wire bytes. This is deliberately strict: it is the reference reading, the
one every conformant implementation must agree with.
-/

namespace Http1.Parse

open Http1

def CR : UInt8 := 13
def LF : UInt8 := 10
def COLON : UInt8 := 58
def SP : UInt8 := 32

/-- Split a byte list on the first occurrence of CRLF; `none` if there is no CRLF. -/
partial def splitCRLF (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let rec go (acc : List UInt8) : List UInt8 → Option (List UInt8 × List UInt8)
    | [] => none
    | a :: b :: rest => if a == CR && b == LF then some (acc.reverse, rest) else go (a :: acc) (b :: rest)
    | [_] => none
  go [] bs

/-- Split all header lines from the request bytes: returns the list of raw header lines (each without its
CRLF) and stops at the blank line. `none` if the header block is not terminated by CRLFCRLF. -/
partial def headerLines (bs : List UInt8) : Option (List (List UInt8)) :=
  match splitCRLF bs with
  | none => none
  | some (line, rest) =>
    if line == [] then some []  -- blank line ends the block
    else (headerLines rest).map (line :: ·)

/-- Parse one header line into a field: name up to the first colon, value after it (OWS-trimmed). A line
with no colon, or with whitespace before the colon (which RFC 9112 §5.1 forbids and which some parsers
mishandle), yields `none`. -/
def parseField (line : List UInt8) : Option Field :=
  match line.splitOn COLON with
  | [] => none
  | [_] => none
  | name :: rest =>
    let value := (List.intercalate [COLON] rest)
    -- reject whitespace between field name and colon (a smuggling-relevant ambiguity)
    if name == [] || name.getLast? == some SP || name.getLast? == some 9 then none
    else some ⟨name, trimOWS value⟩

/-- Does the request line end in `HTTP/1.0`? -/
def isHttp10 (reqLine : List UInt8) : Bool :=
  (reqLine.reverse.take 8).reverse == bytes "HTTP/1.0"

/-- Parse raw request bytes into a `Msg`. Every request is allowed a body; the framing is by headers. A
malformed header line makes the whole parse fail (`none`), which the oracle reports as a reject. -/
def parseRequest (bs : List UInt8) : Option Msg := do
  let lines ← headerLines bs
  match lines with
  | [] => none  -- no request line
  | reqLine :: fieldLines =>
    let fields ← fieldLines.mapM parseField
    some ⟨!isHttp10 reqLine, true, fields⟩

/-- The framing verdict for raw request bytes: a malformed message is `reject`. -/
def frameBytes (bs : List UInt8) : Framing :=
  match parseRequest bs with
  | some m => frame m
  | none => Framing.reject

/-- The verdict as a short tag, for the differential harness. -/
def verdict (bs : List UInt8) : String :=
  match frameBytes bs with
  | Framing.reject => "reject"
  | Framing.chunked => "chunked"
  | Framing.length n => s!"length:{n}"
  | Framing.untilClose => "until_close"

end Http1.Parse
