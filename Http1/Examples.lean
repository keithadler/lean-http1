import Http1.Framing
import Http1.Body
import Http1.Message

/-!
# Worked framing examples, checked by the kernel

The classic desync vectors, and what `frame` does with each. Every `example` is proved by `decide`, so
Lean's kernel evaluates the framing rules on the actual bytes.
-/

namespace Http1.Examples

open Http1

/-- Build a header from two string literals. -/
def hdr (n v : String) : Field := ⟨bytes n, bytes v⟩

/-- A plain request-shaped message on HTTP/1.1 that is allowed a body. -/
def msg (fields : List Field) : Msg := ⟨true, true, fields⟩

/-! ## Desync vectors: `frame` rejects every one -/

/-- Both `Content-Length` and `Transfer-Encoding: chunked`. This is the CL.TE / TE.CL family: a front-end
that trusts one header and a back-end that trusts the other disagree. RFC 9112 §6.1 forbids sending both. -/
example : frame (msg [hdr "Content-Length" "6", hdr "Transfer-Encoding" "chunked"]) = Framing.reject := by
  decide +kernel

/-- The same, headers in the other order. -/
example : frame (msg [hdr "Transfer-Encoding" "chunked", hdr "Content-Length" "6"]) = Framing.reject := by
  decide +kernel

/-- Two conflicting `Content-Length` values. -/
example : frame (msg [hdr "Content-Length" "6", hdr "Content-Length" "7"]) = Framing.reject := by decide +kernel

/-- One `Content-Length` field with two conflicting list values. -/
example : frame (msg [hdr "Content-Length" "6, 7"]) = Framing.reject := by decide +kernel

/-- `Transfer-Encoding` where `chunked` is not the final coding: many parsers then fall back to
`Content-Length` or to reading until close, a known desync. -/
example : frame (msg [hdr "Transfer-Encoding" "chunked, gzip"]) = Framing.reject := by decide +kernel

/-- `Transfer-Encoding: chunked` twice, which RFC 9112 §6.1 makes an error. -/
example : frame (msg [hdr "Transfer-Encoding" "chunked", hdr "Transfer-Encoding" "chunked"]) = Framing.reject := by
  decide +kernel

/-- Chunked on HTTP/1.0, where the coding is undefined. -/
example : frame ⟨false, true, [hdr "Transfer-Encoding" "chunked"]⟩ = Framing.reject := by decide +kernel

/-- A non-numeric `Content-Length`. -/
example : frame (msg [hdr "Content-Length" "6a"]) = Framing.reject := by decide +kernel

/-- A `Content-Length` with a leading plus, which RFC 9110 §8.6 does not allow. -/
example : frame (msg [hdr "Content-Length" "+6"]) = Framing.reject := by decide +kernel

/-! ## Well-formed messages: `frame` accepts, and the two readers agree -/

/-- A single valid `Content-Length`. -/
example : frame (msg [hdr "Content-Length" "42"]) = Framing.length 42 := by decide +kernel

/-- Duplicate `Content-Length` fields that agree collapse to one. -/
example : frame (msg [hdr "Content-Length" "42", hdr "Content-Length" "42"]) = Framing.length 42 := by decide +kernel

/-- A clean chunked message. -/
example : frame (msg [hdr "Transfer-Encoding" "chunked"]) = Framing.chunked := by decide +kernel

/-- Case-insensitive matching: `TRANSFER-ENCODING: Chunked` is still chunked. -/
example : frame (msg [hdr "TRANSFER-ENCODING" "Chunked"]) = Framing.chunked := by decide +kernel

/-- A request with neither header has no body. -/
example : frame (msg []) = Framing.length 0 := by decide +kernel

/-- On the accepted chunked message, both readers agree (a concrete instance of `no_desync`). -/
example : readerCL (msg [hdr "Transfer-Encoding" "chunked"]) =
    readerTE (msg [hdr "Transfer-Encoding" "chunked"]) := by decide +kernel

/-- On the accepted length message, both readers agree. -/
example : readerCL (msg [hdr "Content-Length" "42"]) = readerTE (msg [hdr "Content-Length" "42"]) := by
  decide +kernel

/-- And on a rejected desync vector, the two readers *disagree* — which is exactly why `frame` rejects it.
The CL reader sees a body of 6 bytes; the TE reader reads it as chunked. -/
example : readerCL (msg [hdr "Content-Length" "6", hdr "Transfer-Encoding" "chunked"]) ≠
    readerTE (msg [hdr "Content-Length" "6", hdr "Transfer-Encoding" "chunked"]) := by decide +kernel

/-! ## The byte boundary is exact (Body.lean, BodyProof.lean) -/

/-- A 5-byte Content-Length body ("hello") followed by the next request's bytes ("GET") hands back exactly
"GET": the boundary is after byte 5, determined. -/
example : takeExact 5 (bytes "hello" ++ bytes "GET") = some (bytes "hello", bytes "GET") := by decide +kernel

/-- A chunked body of one chunk "hi", then a continuation, reads back "hi" and hands back the continuation:
where the chunked message ends is determined by the `0 CRLF CRLF` terminator. -/
example : readChunked (writeChunked [bytes "hi"] ++ bytes "GET /") = some (bytes "hi", bytes "GET /") := by
  decide +kernel

/-- Two chunks concatenate; nothing of the continuation leaks into the body. -/
example : readChunked (writeChunked [bytes "ab", bytes "cd"] ++ [0]) = some (bytes "abcd", [0]) := by
  decide +kernel

/-! ## The whole message occupies a determined prefix (Message.lean) -/

/-- A request line, one header, a 2-byte body "hi", then the next request's bytes: the reader returns the
lines, "hi", and hands back the next request untouched. The header/body/next-request split is determined. -/
example :
    readHeadAndBody (Framing.length 2)
      (serBlock [bytes "POST / HTTP/1.1", bytes "Host: a"] ++ (bytes "hi" ++ bytes "GET /x")) =
      some ([bytes "POST / HTTP/1.1", bytes "Host: a"], bytes "hi", bytes "GET /x") := by
  have h := message_boundary_length [bytes "POST / HTTP/1.1", bytes "Host: a"]
    (by intro l hl; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with h | h <;> subst h <;> decide +kernel)
    (by intro l hl; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with h | h <;> subst h <;> decide +kernel)
    (bytes "hi") (bytes "GET /x")
  have hlen : (bytes "hi").length = 2 := by decide +kernel
  rw [hlen] at h; exact h

end Http1.Examples
