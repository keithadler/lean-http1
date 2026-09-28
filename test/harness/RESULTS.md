# HTTP/1.1 framing: differential results

Each row is a raw request byte stream (`test/corpus/vectors.py`). Each column is a parser's framing verdict: `reject`, `length:N`, or `chunked`. **Lean (proved)** is the reference the `no_desync` theorem is about; a cell that differs from it is **bold**. Two real parsers that differ on one row are a potential request-smuggling desync.

| Vector | probes | Lean (proved) | h11 | Node/llhttp | Std.Http |
|---|---|---|---|---|---|
| `valid-cl` | a single valid Content-Length | length:5 | length:5 | length:5 | length:5 |
| `valid-chunked` | a clean chunked body | chunked | chunked | chunked | chunked |
| `valid-nobody` | a request with no body headers | length:0 | length:0 | length:0 | length:0 |
| `valid-cl-dup-agree` | duplicate Content-Length that agree | length:5 | length:5 | **reject** | **reject** |
| `cl-te` | both Content-Length and Transfer-Encoding (the classic desync) | reject | **chunked** | reject | reject |
| `te-cl` | both headers, Transfer-Encoding first | reject | **chunked** | reject | reject |
| `te-space-cl` | space before the colon on Transfer-Encoding | reject | reject | reject | reject |
| `te-tab` | tab instead of space after the colon | reject | **chunked** | reject | reject |
| `te-not-last` | chunked is not the final coding | reject | reject | reject | reject |
| `te-dup` | two Transfer-Encoding fields | reject | reject | reject | reject |
| `te-xchunked` | an unrecognized coding that ends in 'chunked' | reject | reject | reject | reject |
| `te-chunked-cap` | capitalized Chunked (must still be chunked) | chunked | chunked | chunked | chunked |
| `cl-dup-conflict` | two conflicting Content-Length values | reject | reject | reject | reject |
| `cl-list-conflict` | one Content-Length field with two values | reject | reject | reject | reject |
| `cl-plus` | a leading plus in Content-Length | reject | reject | reject | reject |
| `cl-hex` | a hex-looking Content-Length | reject | reject | reject | reject |
| `cl-space` | trailing space in Content-Length (allowed OWS) | length:5 | length:5 | length:5 | length:5 |
| `cl-leading-space-val` | extra leading OWS in the value (allowed) | length:5 | length:5 | length:5 | length:5 |
| `cl-newline-inject` | baseline for length 5 | length:5 | length:5 | length:5 | length:5 |
| `bare-lf-cl-te` | Content-Length terminated by a bare LF, then Transfer-Encoding | reject | **chunked** | reject | reject |
| `bare-lf-headers` | all header lines terminated by bare LF | reject | **length:5** | reject | reject |

Parsers: 4. Vectors: 21. Rows where parsers disagree: 6.

- **Lean (proved)**: the spec `no_desync` is about
- **h11**: h11 0.16 (Python; hypercorn, uvicorn)
- **Node/llhttp**: Node http.Server (llhttp)
- **Std.Http**: Lean's own standard library HTTP/1.1 parser

## Where parsers disagree

- `valid-cl-dup-agree` (duplicate Content-Length that agree): Lean (proved) = length:5, h11 = length:5, Node/llhttp = reject, Std.Http = reject
- `cl-te` (both Content-Length and Transfer-Encoding (the classic desync)): Lean (proved) = reject, h11 = chunked, Node/llhttp = reject, Std.Http = reject
- `te-cl` (both headers, Transfer-Encoding first): Lean (proved) = reject, h11 = chunked, Node/llhttp = reject, Std.Http = reject
- `te-tab` (tab instead of space after the colon): Lean (proved) = reject, h11 = chunked, Node/llhttp = reject, Std.Http = reject
- `bare-lf-cl-te` (Content-Length terminated by a bare LF, then Transfer-Encoding): Lean (proved) = reject, h11 = chunked, Node/llhttp = reject, Std.Http = reject
- `bare-lf-headers` (all header lines terminated by bare LF): Lean (proved) = reject, h11 = length:5, Node/llhttp = reject, Std.Http = reject
