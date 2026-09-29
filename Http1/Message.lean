import Http1.Header
import Http1.BodyProof
import Http1.Field

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

/-- Parse a full request: header block into a request line and fields, then the body by the framing verdict.
Returns the request line, the parsed fields, the body, and the remainder (the next message). -/
def parseFullMessage (fr : Framing) (bs : List UInt8) :
    Option (List UInt8 × List Field × List UInt8 × List UInt8) :=
  match readHeadAndBody fr bs with
  | none => none
  | some ([], _, _) => none
  | some (reqLine :: fieldLines, body, rest) =>
    (fieldLines.mapM parseField).map (fun fields => (reqLine, fields, body, rest))

/-- 13 is not in a serialized field when it is not in its name or value (the colon and space are not CR). -/
theorem serField_no_cr {f : Field} (hn : (13:UInt8) ∉ f.name) (hv : (13:UInt8) ∉ f.value) :
    (13:UInt8) ∉ serField f := by
  unfold serField
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro ((h | h | h) | h)
  · exact hn h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact hv h

/-- **The whole request occupies a determined prefix.** A request line and canonical fields, serialized as a
header block, followed by an `n`-byte body and any continuation, parse back to exactly the request line, the
fields, the body, and the continuation. The recovered fields are exactly the input to `frame`, so the
framing verdict (and `no_desync`) apply to precisely what was written. -/
theorem full_message_boundary_length (reqLine : List UInt8) (fields : List Field)
    (body rest : List UInt8) (hreq : reqLine ≠ []) (hreq13 : (13:UInt8) ∉ reqLine)
    (hc : ∀ f ∈ fields, Canonical f)
    (hcr : ∀ f ∈ fields, (13:UInt8) ∉ f.name ∧ (13:UInt8) ∉ f.value) :
    parseFullMessage (Framing.length body.length)
      (serBlock (reqLine :: fields.map serField) ++ (body ++ rest))
      = some (reqLine, fields, body, rest) := by
  have hne : ∀ l ∈ (reqLine :: fields.map serField), l ≠ [] := by
    intro l hl
    simp only [List.mem_cons, List.mem_map] at hl
    rcases hl with h | ⟨g, hg, rfl⟩
    · subst h; exact hreq
    · unfold serField; simp [(hc g hg).name_ne]
  have h13 : ∀ l ∈ (reqLine :: fields.map serField), (13:UInt8) ∉ l := by
    intro l hl
    simp only [List.mem_cons, List.mem_map] at hl
    rcases hl with h | ⟨g, hg, rfl⟩
    · subst h; exact hreq13
    · exact serField_no_cr (hcr g hg).1 (hcr g hg).2
  unfold parseFullMessage
  rw [message_boundary_length (reqLine :: fields.map serField) hne h13 body rest]
  show (List.mapM parseField (fields.map serField)).map (fun fs => (reqLine, fs, body, rest))
       = some (reqLine, fields, body, rest)
  rw [mapM_parseField_serField fields hc]
  rfl

end Http1
