# Proxy x backend boundary results

Each payload is an ambiguous main request `/m-<name>` (both `Content-Length` and `Transfer-Encoding`, or an obfuscated variant) followed by a marker request `/s-<name>`. A cell shows what the **backend** parsed when the bytes were sent that way. `lean` is the proved spec's verdict (it rejects every payload). The question is whether two components frame the same bytes differently — that is the raw material of a desync.

| Payload | lean | direct | nginx | haproxy | caddy |
|---|---|---|---|---|---|
| `clte` | reject | !HPE_INVALID_TRANSFER_ENCODING | reject | /m-clte | /m-clte /s-clte |
| `tecl` | reject | !HPE_INVALID_CONTENT_LENGTH | reject | /m-tecl | /m-tecl /s-tecl |
| `te-space` | reject | !HPE_INVALID_HEADER_TOKEN | reject | reject | !ECONNRESET !ECONNRESET |
| `te-tab` | reject | !HPE_INVALID_CONTENT_LENGTH | reject | /m-te-tab | /m-te-tab /s-te-tab |
| `te-notlast` | reject | !HPE_INVALID_TRANSFER_ENCODING | reject | reject | reject |
| `te-dup` | reject | !HPE_INVALID_TRANSFER_ENCODING | reject | reject | reject |
| `cl-dup` | reject | !HPE_UNEXPECTED_CONTENT_LENGTH | reject | reject | reject |
| `cl-list` | reject | !HPE_INVALID_CONTENT_LENGTH | reject | reject | reject |
| `bare-lf` | reject | !HPE_CR_EXPECTED | reject | /m-bare-lf | /m-bare-lf /s-bare-lf |

## Reading

On this corpus the picture is consistent, not a desync:

- **direct (Node/llhttp)** and **nginx** reject every ambiguous payload (`reject` / an llhttp error).
- **haproxy** and **caddy** both resolve `Content-Length` + `Transfer-Encoding` the same way — they strip `Content-Length` and use chunked (verified from the raw bytes each forwards: the main request's body is empty). They *agree* on the framing. The only difference is that caddy forwards the trailing pipelined marker as its own request and haproxy does not, which is marker handling, not a boundary disagreement.

So no exploitable proxy-vs-proxy desync surfaced here: the two components that accept these payloads frame them identically, and the other two reject. The proved spec rejects all of them, which is the safe reading. Finding a genuine desync would need the deeper obfuscation families (many `Transfer-Encoding` / `Content-Length` mutations designed to make one parser see chunked and another see a length); that is the natural next extension of this harness.

Backend: Node/llhttp. Proxies: nginx, haproxy, caddy. All on localhost; instances started and stopped by the harness.
