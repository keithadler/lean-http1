"""h11 framing driver: feed each corpus vector to h11 (the parser behind hypercorn/uvicorn's h11 mode) and
report how it frames the body. Output: one JSON line {name, verdict}.

verdict is one of: reject | length:N | chunked | until_close, matching the Lean oracle's tags.
"""
import json
import os
import sys

import h11


def frame_of(raw: bytes) -> str:
    conn = h11.Connection(h11.SERVER)
    try:
        conn.receive_data(raw)
        events = []
        while True:
            ev = conn.next_event()
            if ev is h11.NEED_DATA or ev is h11.PAUSED:
                break
            events.append(ev)
            if isinstance(ev, h11.EndOfMessage):
                break
    except h11.RemoteProtocolError:
        return "reject"

    req = next((e for e in events if isinstance(e, h11.Request)), None)
    if req is None:
        return "reject"
    # h11 exposes framing through the headers it accepted and the Data events it produced.
    hdrs = {k.lower(): v for k, v in req.headers}
    if b"transfer-encoding" in hdrs and b"chunked" in hdrs[b"transfer-encoding"].lower():
        return "chunked"
    if b"content-length" in hdrs:
        try:
            return f"length:{int(hdrs[b'content-length'])}"
        except ValueError:
            return "reject"
    return "length:0"


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    vecs = json.load(open(os.path.join(here, "..", "corpus", "vectors.json")))["vectors"]
    for name, hexs in vecs.items():
        raw = bytes.fromhex(hexs)
        try:
            v = frame_of(raw)
        except Exception as e:  # noqa: BLE001
            v = f"error:{type(e).__name__}"
        print(json.dumps({"name": name, "verdict": v}))


if __name__ == "__main__":
    main()
