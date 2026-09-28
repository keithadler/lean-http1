import Http1.Header
import Http1.BodyProof

/-!
# The whole message occupies a determined prefix

This ties the two boundary results together. `readBlock` finds the end of the header block (`Header.lean`);
`readBody` then reads the body by the framing verdict (`Body.lean`). Composed, they say: a canonical message
— a header block, then a body framed as length-delimited or chunked — followed by any continuation, is read
back as exactly that message, leaving exactly the continuation.

That is the complete byte-level anti-smuggling statement: given a well-formed message followed by the next
request's bytes, a reader consumes exactly the message and hands back exactly the next request. There is no
second place the boundary could fall.
-/

namespace Http1

/-- Read a header block, then the body by the given framing verdict. Returns the header lines, the body, and
the remainder (the next message). -/
def readHeadAndBody (fr : Framing) (bs : List UInt8) :
    Option (List (List UInt8) × List UInt8 × List UInt8) :=
  match readBlock bs with
  | none => none
  | some (lines, after) => (readBody fr after).map (fun (body, rest) => (lines, body, rest))

/-- **A length-delimited message occupies a determined prefix.** A header block followed by an `n`-byte body
and any continuation reads back as exactly the lines, the body, and the continuation. -/
theorem message_boundary_length (lines : List (List UInt8))
    (hne : ∀ l ∈ lines, l ≠ []) (h13 : ∀ l ∈ lines, (13:UInt8) ∉ l)
    (body rest : List UInt8) :
    readHeadAndBody (Framing.length body.length) (serBlock lines ++ (body ++ rest))
      = some (lines, body, rest) := by
  unfold readHeadAndBody
  rw [readBlock_serBlock lines hne h13 (body ++ rest)]
  simp only [readBody, takeExact_append, Option.map_some]

/-- **A chunked message occupies a determined prefix.** A header block followed by a chunked body (non-empty
payloads) and any continuation reads back as exactly the lines, the decoded payloads, and the continuation. -/
theorem message_boundary_chunked (lines : List (List UInt8))
    (hne : ∀ l ∈ lines, l ≠ []) (h13 : ∀ l ∈ lines, (13:UInt8) ∉ l)
    (chunks : List (List UInt8)) (hcne : ∀ c ∈ chunks, c ≠ []) (rest : List UInt8) :
    readHeadAndBody Framing.chunked (serBlock lines ++ (writeChunked chunks ++ rest))
      = some (lines, chunks.flatMap id, rest) := by
  unfold readHeadAndBody
  rw [readBlock_serBlock lines hne h13 (writeChunked chunks ++ rest)]
  simp only [readBody, readChunked_writeChunked chunks hcne rest, Option.map_some]

end Http1
