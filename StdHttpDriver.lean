import Std.Http
import Http1.Parse

/-!
`stdhttp`: a differential driver for Lean's own standard-library HTTP framing.

Reads one raw request on stdin and prints the framing verdict that `Std.Http`'s own body-length decision
(`Message.Head.getSize`, RFC 9112 §6.1) computes, in the same tags the other drivers use. This tests the
standard library's framing decision and its `Content-Length` / `Transfer-Encoding` parsers.
-/

open Std.Http Std.Http.Protocol.H1

/-- Extract `(isHttp10, fields)` from raw request bytes; `none` if the header block is malformed. -/
def extract (bs : List UInt8) : Option (Bool × List (String × String)) := do
  let lines ← Http1.Parse.headerLines bs
  match lines with
  | [] => none
  | reqLine :: fieldLines =>
    let mkField (line : List UInt8) : Option (String × String) :=
      match line.splitOn Http1.Parse.COLON with
      | [] => none
      | [_] => none
      | name :: rest =>
        let value := List.intercalate [Http1.Parse.COLON] rest
        let nameS := (String.fromUTF8? (ByteArray.mk name.toArray)).getD ""
        let valS := (String.fromUTF8? (ByteArray.mk (Http1.trimOWS value).toArray)).getD ""
        some (nameS, valS)
    let fields ← fieldLines.mapM mkField
    some (Http1.Parse.isHttp10 reqLine, fields)

/-- Build the standard library's `Request.Head` and read its framing verdict. -/
def stdVerdict (bs : List UInt8) : String :=
  match extract bs with
  | none => "reject"
  | some (isHttp10, fields) =>
    let headers := fields.foldl (fun h (n, v) => h.insert! n v) Headers.empty
    let head : Request.Head :=
      { method := .get, version := if isHttp10 then .v10 else .v11, headers }
    let hasCL := fields.any (fun (n, _) => n.toLower == "content-length")
    let hasTE := fields.any (fun (n, _) => n.toLower == "transfer-encoding")
    match Message.Head.getSize (dir := .receiving) head false with
    | some .chunked => "chunked"
    | some (.fixed n) => s!"length:{n}"
    | none => if !hasCL && !hasTE then "length:0" else "reject"

def main : IO Unit := do
  let raw ← (← IO.getStdin).readBinToEnd
  IO.println (stdVerdict raw.toList)
