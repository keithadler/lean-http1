"""The framing corpus: raw HTTP/1.1 request byte streams, each exercising one framing rule.

Every vector is exact bytes (CRLF line endings, explicit bodies). Each driver reads this same list and
reports how its parser frames the message. A disagreement between two parsers on one vector is a potential
request-smuggling desync.

Run `python vectors.py` to write vectors.json (name -> hex).
"""
import json
import os

CRLF = "\r\n"


def req(lines, body=b""):
    """Build request bytes from header lines (the blank line and body are added)."""
    head = CRLF.join(lines) + CRLF + CRLF
    return head.encode("latin-1") + body


# Each entry: (name, raw bytes, what it probes). "expected" is the RFC-conformant reading the proved spec
# gives; a parser that differs from it is nonconformant, and two parsers that differ from each other on a
# vector neither should accept is an exploitable desync.
VECTORS = [
    # --- valid controls ---
    ("valid-cl", req(["POST / HTTP/1.1", "Host: a", "Content-Length: 5"], b"hello"),
     "a single valid Content-Length"),
    ("valid-chunked", req(["POST / HTTP/1.1", "Host: a", "Transfer-Encoding: chunked"], b"5\r\nhello\r\n0\r\n\r\n"),
     "a clean chunked body"),
    ("valid-nobody", req(["GET / HTTP/1.1", "Host: a"]),
     "a request with no body headers"),
    ("valid-cl-dup-agree", req(["POST / HTTP/1.1", "Host: a", "Content-Length: 5", "Content-Length: 5"], b"hello"),
     "duplicate Content-Length that agree"),

    # --- CL.TE / TE.CL: both headers present ---
    ("cl-te", req(["POST / HTTP/1.1", "Host: a", "Content-Length: 6", "Transfer-Encoding: chunked"],
                  b"0\r\n\r\nX"),
     "both Content-Length and Transfer-Encoding (the classic desync)"),
    ("te-cl", req(["POST / HTTP/1.1", "Host: a", "Transfer-Encoding: chunked", "Content-Length: 6"],
                  b"0\r\n\r\nX"),
     "both headers, Transfer-Encoding first"),

    # --- Transfer-Encoding obfuscation (each has tripped a real proxy/server pair) ---
    ("te-space-cl", req(["POST / HTTP/1.1", "Host: a", "Transfer-Encoding : chunked", "Content-Length: 4"], b"1\r\nZ\r\n"),
     "space before the colon on Transfer-Encoding"),
    ("te-tab", req(["POST / HTTP/1.1", "Host: a", "Transfer-Encoding:\tchunked", "Content-Length: 4"], b"1\r\nZ\r\n"),
     "tab instead of space after the colon"),
    ("te-not-last", req(["POST / HTTP/1.1", "Host: a", "Transfer-Encoding: chunked, identity", "Content-Length: 4"], b"xxxx"),
     "chunked is not the final coding"),
    ("te-dup", req(["POST / HTTP/1.1", "Host: a", "Transfer-Encoding: chunked", "Transfer-Encoding: chunked"], b"0\r\n\r\n"),
     "two Transfer-Encoding fields"),
    ("te-xchunked", req(["POST / HTTP/1.1", "Host: a", "Transfer-Encoding: xchunked", "Content-Length: 4"], b"xxxx"),
     "an unrecognized coding that ends in 'chunked'"),
    ("te-chunked-cap", req(["POST / HTTP/1.1", "Host: a", "Transfer-Encoding: Chunked"], b"0\r\n\r\n"),
     "capitalized Chunked (must still be chunked)"),

    # --- Content-Length obfuscation ---
    ("cl-dup-conflict", req(["POST / HTTP/1.1", "Host: a", "Content-Length: 5", "Content-Length: 6"], b"hello"),
     "two conflicting Content-Length values"),
    ("cl-list-conflict", req(["POST / HTTP/1.1", "Host: a", "Content-Length: 5, 6"], b"hello"),
     "one Content-Length field with two values"),
    ("cl-plus", req(["POST / HTTP/1.1", "Host: a", "Content-Length: +5"], b"hello"),
     "a leading plus in Content-Length"),
    ("cl-hex", req(["POST / HTTP/1.1", "Host: a", "Content-Length: 0x5"], b"hello"),
     "a hex-looking Content-Length"),
    ("cl-space", req(["POST / HTTP/1.1", "Host: a", "Content-Length: 5 "], b"hello"),
     "trailing space in Content-Length (allowed OWS)"),
    ("cl-leading-space-val", req(["POST / HTTP/1.1", "Host: a", "Content-Length:  5"], b"hello"),
     "extra leading OWS in the value (allowed)"),
    ("cl-newline-inject", req(["POST / HTTP/1.1", "Host: a", "Content-Length: 5"], b"hello"),
     "baseline for length 5"),
    # --- bare LF line endings (RFC 9112 §2.2: only CRLF terminates a line; bare LF is a known desync) ---
    ("bare-lf-cl-te", (b"POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 6\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\nX"),
     "Content-Length terminated by a bare LF, then Transfer-Encoding"),
    ("bare-lf-headers", (b"POST / HTTP/1.1\nHost: a\nContent-Length: 5\n\nhello"),
     "all header lines terminated by bare LF"),
]


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    out = {name: raw.hex() for name, raw, _ in VECTORS}
    meta = {name: probe for name, _, probe in VECTORS}
    json.dump({"vectors": out, "probes": meta}, open(os.path.join(here, "vectors.json"), "w"), indent=1)
    print(f"wrote {len(VECTORS)} vectors to vectors.json")


if __name__ == "__main__":
    main()
