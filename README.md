# HTTP/1.1 framing, proved unambiguous — and where real parsers disagree

Request smuggling happens when two parties on one connection — a proxy in front, a server behind it —
disagree about where one HTTP message ends and the next begins. This project writes RFC 9112 §6.1's
message-body-length rules down in Lean, **proves the property that rules smuggling out**, and then runs the
same byte streams through real HTTP parsers to see which ones diverge from that proved reference.

It needs no cryptography. The whole result is about parsing: a byte stream should have exactly one reading.

## The theorem

A desync is a disagreement between a reader that trusts `Content-Length` and a reader that trusts
`Transfer-Encoding` — the two sides an attacker plays against each other. Both are modelled as functions to
a framing verdict, and:

> **`no_desync`** — on every message the conformant checker `frame` accepts, the Content-Length-trusting
> reader and the Transfer-Encoding-trusting reader compute the *same* framing.

So a conformant front-end and a conformant back-end cannot be desynchronised. The messages where the two
readers *could* differ — both headers present, conflicting `Content-Length`, `chunked` not the final
coding, chunked on HTTP/1.0 — are exactly the ones `frame` rejects, and the theorem holds because it rejects
them. `no_desync` rests only on Lean's three standard axioms; [Tenet](https://github.com/keithadler/tenet),
an independent kernel, re-checks all 146 declarations.

## The boundary is exact, too

`no_desync` covers the framing *decision*. `Http1/Body.lean` and `Http1/BodyProof.lean` prove the layer
below — that once the decision is made, where the body ends is a determined function of the bytes, so a
message occupies a determined prefix of the connection:

> **`takeExact_append`** — a `Content-Length` body of length `n` followed by any continuation reads back as
> exactly that body, leaving exactly the continuation.
>
> **`readChunked_writeChunked`** — a chunked body written from non-empty payloads, followed by any
> continuation, reads back as exactly the concatenated payloads, leaving exactly the continuation. So the
> `0 CRLF CRLF` terminator fixes where a chunked message ends; nothing of the next request leaks into the
> body, and none of the body leaks into the next request.

The chunked proof is the substantial one: it goes through the hex chunk-size round-trip
(`readChunkSize_toHex`, itself resting on a base-16 inversion `toHexGo_inv`) and an induction over the chunk
list. And the header block itself has a determined boundary (`Http1/Header.lean`, `Http1/Message.lean`):

> **`readBlock_serBlock`** — a header block of non-empty, CR-free lines, closed by a blank line and followed
> by any continuation, reads back as exactly those lines, leaving exactly the continuation. A line is
> terminated only by CRLF, so a header ended by a bare LF is not recognised — the reader rejects rather than
> guessing a boundary, which is what keeps it in step with a CRLF-framing peer (this is the h11 bare-LF class
> of divergence, ruled out).
>
> **`parseField_serField`** — a header field splits at its first colon into a name and an OWS-trimmed value,
> and that split is unique: a canonical field reads back exactly. So a space before the colon or a second
> colon is pinned down, not guessed.
>
> **`message_boundary_length`, `message_boundary_chunked`** — a whole message (header block then body,
> length-delimited or chunked) followed by any continuation reads back as exactly that message.
>
> **`full_message_boundary_length`** — the top: raw bytes → the request line, the parsed `(name, value)`
> fields, the body, and the exact next-request bytes. The recovered fields are precisely the input to
> `frame`, so the framing verdict — and `no_desync` — apply to exactly what was written.

So the chain is complete: on an accepted message the framing is chosen unambiguously (`no_desync`), the
header/body split is at one determined offset (`readBlock_serBlock`), and the chosen framing ends the body at
one determined point (`takeExact_append` / `readChunked_writeChunked`). A well-formed message occupies a
determined prefix of the connection — there is no second place the next message could begin. Tenet re-checks all 382 declarations, 0 failed.

`Http1/Examples.lean` runs the classic vectors through the kernel with `decide +kernel`: `CL` + `TE` →
reject, conflicting `Content-Length` → reject, a clean chunked or single length → accept, and on a rejected
vector the two readers provably *disagree* (which is why it is rejected).

## What real parsers do with the same bytes

`test/harness/run.py` runs a corpus of raw request byte streams (`test/corpus/vectors.py`) through every
parser it can find and compares each to the proved spec. Full table:
[test/harness/RESULTS.md](test/harness/RESULTS.md). The parsers:

- **Lean (proved)** — the compiled `frame`, the function `no_desync` is about (the reference).
- **h11 0.16** — the Python parser behind hypercorn and uvicorn's h11 mode.
- **Node/llhttp** — Node's `http.Server`, whose parser is llhttp.
- **Std.Http** — Lean's own standard-library HTTP/1.1 framing (`Message.Head.getSize`).

Where they diverge from the proved reference (6 of 21 vectors):

| Vector | proved spec | h11 | Node/llhttp | Std.Http |
|---|---|---|---|---|
| both `Content-Length` and `Transfer-Encoding` | reject | **chunked** | reject | reject |
| the same, `Transfer-Encoding` first | reject | **chunked** | reject | reject |
| tab after the colon on `Transfer-Encoding` (with `Content-Length`) | reject | **chunked** | reject | reject |
| `Content-Length` ended by a bare LF, then `Transfer-Encoding` | reject | **chunked** | reject | reject |
| all header lines ended by a bare LF | reject | **length:5** | reject | reject |
| duplicate `Content-Length`, same value | length:5 | length:5 | **reject** | **reject** |

Read defensively, not as exploits — a divergence is smuggling *material*, and whether any specific
front-end/back-end pairing is exploitable depends on deployment. Two things stand out:

- **h11 resolves `Content-Length` + `Transfer-Encoding` in favour of `Transfer-Encoding`, and tolerates
  bare-LF line endings and tab-obfuscated headers**, where the proved spec, Node and Lean's `Std.Http` all
  reject. h11 is a sans-IO library that follows RFC 7230's older "Transfer-Encoding overrides" rule and
  leaves policy to the caller; but a CL-trusting proxy in front of an h11 back-end is exactly the CL.TE
  desync `no_desync` describes. Its bare-LF tolerance is the classic line-ending smuggling primitive.
- **Node and Lean's `Std.Http` reject duplicate `Content-Length` even when the values agree**, which the
  proved spec (and RFC 9112 §6.3.5, which *permits* collapsing them) and h11 accept. This is the safe
  direction — rejecting — and is noted for completeness.

### Item: Lean's own standard library

Lean 4's `Std.Http` ships a full HTTP/1.1 implementation. Its framing decision `Message.Head.getSize` agrees
with the proved spec on every vector except duplicate-agreeing `Content-Length`, where it is *stricter*
(rejects). That is a good result for the standard library: on this corpus it never frames a message a way
the proved spec would call ambiguous.

## Proxy x backend boundary harness

`test/smuggle/` runs the proved spec against real proxies and a real backend. It starts a Node/llhttp
backend and puts nginx, HAProxy and Caddy in front of it (each reverse-proxying to the backend), sends
ambiguous request streams — a main request plus a marker request — through each, and records what the
backend actually parsed. Comparing the columns shows whether the components frame the same bytes differently
(a desync) or agree. Needs nginx, haproxy, caddy on the PATH; everything runs on localhost.

```bash
python3 test/smuggle/run.py     # writes test/smuggle/RESULTS.md
```

On the current corpus the result is consistent, not a desync: Node and nginx reject every ambiguous payload,
while HAProxy and Caddy both strip `Content-Length` and use chunked (they agree on the framing, verified from
the raw bytes each forwards). No exploitable proxy-vs-proxy desync surfaced. The proved spec rejects all of
them, which is the safe reading. The harness is the tool; finding a genuine desync would need the deeper
`Transfer-Encoding`/`Content-Length` obfuscation families, the natural next extension.

## Running it

Build (needs [elan](https://github.com/leanprover/elan); toolchain pinned in `lean-toolchain`):

```bash
lake build
```

The proved spec as a CLI — reads a raw request on stdin, prints `reject` / `length:N` / `chunked`:

```bash
printf 'POST / HTTP/1.1\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\n\r\n' | .lake/build/bin/http1 frame
```

The differential harness (uses whichever of Python+h11, Node, and the two Lean binaries are present):

```bash
python3 test/harness/run.py
```

## Layout

| Path | What it is |
|---|---|
| `Http1/Framing.lean` | The framing model, `frame`, the two readers, and `no_desync` |
| `Http1/Examples.lean` | The classic desync vectors, checked by the kernel |
| `Http1/Parse.lean` | Raw request bytes → `Msg`, so `frame` runs on wire bytes |
| `Http1/Body.lean` | The length and chunked body readers; `takeExact_append` (length boundary exact) |
| `Http1/BodyProof.lean` | `readChunked_writeChunked` — the chunked boundary is exact |
| `Http1/Header.lean` | The line/block readers; `readBlock_serBlock` — the header boundary is unique |
| `Http1/Field.lean` | Field split at the first colon; `parseField_serField` — a field has one reading |
| `Http1/Message.lean` | `message_boundary_*` and `full_message_boundary_length` — bytes → fields, one reading |
| `Main.lean` | `http1 frame`, the proved spec as a CLI |
| `StdHttpDriver.lean` | `stdhttp`, a driver for Lean's own `Std.Http` framing |
| `test/corpus/vectors.py` | The raw byte corpus |
| `test/harness/` | The per-parser drivers and the runner |

## Scope and honesty

- The model covers RFC 9112 §6.1's framing decision, the header-block boundary, and the two body readers
  (length-delimited and chunked), with proofs that each fixes the boundary exactly — end to end, a message
  occupies a determined prefix. It does not model the full field grammar (obs-fold, chunk extensions,
  trailers); those are where a stricter reader should reject rather than guess, and the harness is what keeps
  the spec honest about them.
- The harness's shared header split is the harness's own; the `Std.Http` column tests that library's
  framing decision and its `Content-Length` / `Transfer-Encoding` parsers, not its byte tokenizer.
- A divergence from the proved spec is a conformance finding and a desync ingredient. It is **not** a claim
  that any particular deployment is exploitable, and no exploits are developed here. The point is the
  opposite: a proved, unambiguous reference to measure real parsers against, so divergences can be found
  and fixed.

## License

MIT.
