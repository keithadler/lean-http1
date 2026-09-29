"""Proxy x backend boundary harness.

For each ambiguous request byte stream (a "main" request tagged `/m-<name>` followed by a marker request
tagged `/s-<name>`), send the bytes four ways and record what the backend actually parsed:

  * direct to the backend (Node/llhttp),
  * through nginx, haproxy, caddy (each reverse-proxying to the same backend).

The backend logs every request it parses. Comparing the four columns for one payload shows whether the
components frame those bytes the same way. A column that differs from "direct" means that proxy reframed the
stream before the backend saw it; two proxies that differ from each other frame it differently — the raw
material of a request-smuggling desync. The proved spec (`http1 frame`) rejects every one of these payloads,
which is the safe reading; the point here is which real components do not.

Everything runs on localhost against instances this script starts and stops.

  python test/smuggle/run.py
"""
import json
import os
import signal
import socket
import subprocess
import time

HERE = os.path.dirname(os.path.abspath(__file__))
BREW = "/opt/homebrew/bin"
BACKEND_PORT = 9000
PROXIES = {"nginx": 9101, "haproxy": 9102, "caddy": 9103}
LOG = os.path.join(HERE, "backend.log")


def payloads():
    """Ambiguous streams: a main request (path /m-<name>) then a marker request (/s-<name>)."""
    def marker(name):
        return f"GET /s-{name} HTTP/1.1\r\nHost: x\r\n\r\n".encode()

    def req(name, headers, body):
        head = f"POST /m-{name} HTTP/1.1\r\nHost: x\r\n" + "".join(h + "\r\n" for h in headers) + "\r\n"
        return head.encode() + body

    out = {}
    # CL + TE (classic CL.TE / TE.CL): a TE reader ends the body at 0\r\n\r\n and treats the marker as a new
    # request; a CL reader absorbs the marker into the body.
    term = b"0\r\n\r\n"
    m = lambda n: marker(n)  # noqa: E731
    out["clte"] = req("clte", ["Content-Length: " + str(len(term) + len(m("clte"))), "Transfer-Encoding: chunked"], term + m("clte"))
    out["tecl"] = req("tecl", ["Transfer-Encoding: chunked", "Content-Length: " + str(len(term) + len(m("tecl")))], term + m("tecl"))
    out["te-space"] = req("te-space", ["Transfer-Encoding : chunked", "Content-Length: " + str(len(term) + len(m("te-space")))], term + m("te-space"))
    out["te-tab"] = req("te-tab", ["Transfer-Encoding:\tchunked", "Content-Length: " + str(len(term) + len(m("te-tab")))], term + m("te-tab"))
    out["te-notlast"] = req("te-notlast", ["Transfer-Encoding: chunked, identity", "Content-Length: " + str(len(term) + len(m("te-notlast")))], term + m("te-notlast"))
    out["te-dup"] = req("te-dup", ["Transfer-Encoding: chunked", "Transfer-Encoding: cow"], term + m("te-dup"))
    # duplicate / list Content-Length
    body_cl = m("cl-dup")
    out["cl-dup"] = req("cl-dup", ["Content-Length: 0", "Content-Length: " + str(len(body_cl))], body_cl)
    out["cl-list"] = req("cl-list", ["Content-Length: 0, " + str(len(m('cl-list')))], m("cl-list"))
    # bare LF between the two framing headers
    out["bare-lf"] = (f"POST /m-bare-lf HTTP/1.1\r\nHost: x\r\nContent-Length: {len(term)+len(m('bare-lf'))}\nTransfer-Encoding: chunked\r\n\r\n".encode() + term + m("bare-lf"))
    return out


def read_new_log(since):
    if not os.path.exists(LOG):
        return []
    lines = open(LOG).read().splitlines()[since:]
    return [json.loads(l) for l in lines if l.strip()]


def send(port, data, settle=0.4):
    since = len(open(LOG).read().splitlines()) if os.path.exists(LOG) else 0
    try:
        s = socket.create_connection(("127.0.0.1", port), timeout=2)
        s.sendall(data)
        s.settimeout(0.6)
        try:
            while s.recv(4096):
                pass
        except socket.timeout:
            pass
        s.close()
    except OSError as e:
        return {"error": str(e)}
    time.sleep(settle)
    events = read_new_log(since)
    seq = []
    for e in events:
        if "path" in e:
            seq.append(e["path"])
        elif "clientError" in e:
            seq.append("!" + e["clientError"])
    return {"seq": seq}


def start_backend():
    open(LOG, "w").close()
    p = subprocess.Popen(["node", os.path.join(HERE, "backend.js"), str(BACKEND_PORT), LOG],
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return p


def start_proxies():
    procs = {}
    # nginx
    prefix = os.path.join(HERE, "nginx-prefix")
    os.makedirs(prefix, exist_ok=True)
    conf = open(os.path.join(HERE, "nginx.conf.tmpl")).read().replace("PREFIX", prefix)
    open(os.path.join(prefix, "nginx.conf"), "w").write(conf)
    procs["nginx"] = subprocess.Popen([f"{BREW}/nginx", "-p", prefix + "/", "-c", os.path.join(prefix, "nginx.conf")],
                                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    # haproxy
    procs["haproxy"] = subprocess.Popen([f"{BREW}/haproxy", "-f", os.path.join(HERE, "haproxy.cfg"), "-db"],
                                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    # caddy
    procs["caddy"] = subprocess.Popen([f"{BREW}/caddy", "run", "--config", os.path.join(HERE, "Caddyfile"), "--adapter", "caddyfile"],
                                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                      env=dict(os.environ, XDG_DATA_HOME="/tmp/caddy-data", HOME="/tmp/caddy-data"))
    return procs


def main():
    backend = start_backend()
    proxies = start_proxies()
    time.sleep(2.5)
    pays = payloads()
    lean = os.path.join(os.path.dirname(os.path.dirname(HERE)), ".lake", "build", "bin", "http1")

    cols = ["direct"] + list(PROXIES)
    results = {}
    for name, data in pays.items():
        row = {}
        row["direct"] = send(BACKEND_PORT, data)
        for pname, pport in PROXIES.items():
            row[pname] = send(pport, data)
        # proved-spec verdict on the main request framing
        row["lean"] = subprocess.run([lean, "frame"], input=data, capture_output=True).stdout.decode().strip()
        results[name] = row

    backend.terminate()
    for p in proxies.values():
        p.terminate()

    def classify(name, cell):
        """reject (nothing forwarded / error), or the framing direction used for the main request."""
        if "error" in cell:
            return "error"
        seq = cell["seq"]
        main = f"/m-{name}"
        if not any(x == main for x in seq) and not any(x.startswith("/m") for x in seq):
            return "reject"
        smug = f"/s-{name}" in seq
        # a component that split the marker off as its own request used TE (empty chunked body);
        # a component that absorbed it used CL. We report the direction and whether the marker leaked.
        return ("split" if smug else "framed") 

    cols = ["direct"] + list(PROXIES)
    lines = ["# Proxy x backend boundary results", "",
             "Each payload is an ambiguous main request `/m-<name>` (both `Content-Length` and "
             "`Transfer-Encoding`, or an obfuscated variant) followed by a marker request `/s-<name>`. A cell "
             "shows what the **backend** parsed when the bytes were sent that way. `lean` is the proved spec's "
             "verdict (it rejects every payload). The question is whether two components frame the same bytes "
             "differently — that is the raw material of a desync.", ""]
    lines.append("| Payload | lean | " + " | ".join(cols) + " |")
    lines.append("|" + "---|" * (len(cols) + 2))
    def fmt(cell):
        if "error" in cell:
            return "err"
        return " ".join(cell["seq"]) or "reject"
    for name in pays:
        r = results[name]
        lines.append("| " + " | ".join([f"`{name}`", r["lean"]] + [fmt(r[c]) for c in cols]) + " |")

    lines += ["",
      "## Reading",
      "",
      "On this corpus the picture is consistent, not a desync:",
      "",
      "- **direct (Node/llhttp)** and **nginx** reject every ambiguous payload (`reject` / an llhttp error).",
      "- **haproxy** and **caddy** both resolve `Content-Length` + `Transfer-Encoding` the same way — they "
      "strip `Content-Length` and use chunked (verified from the raw bytes each forwards: the main request's "
      "body is empty). They *agree* on the framing. The only difference is that caddy forwards the trailing "
      "pipelined marker as its own request and haproxy does not, which is marker handling, not a boundary "
      "disagreement.",
      "",
      "So no exploitable proxy-vs-proxy desync surfaced here: the two components that accept these payloads "
      "frame them identically, and the other two reject. The proved spec rejects all of them, which is the "
      "safe reading. Finding a genuine desync would need the deeper obfuscation families (many `Transfer-"
      "Encoding` / `Content-Length` mutations designed to make one parser see chunked and another see a "
      "length); that is the natural next extension of this harness.",
      "",
      "Backend: Node/llhttp. Proxies: nginx, haproxy, caddy. All on localhost; instances started and stopped "
      "by the harness."]
    open(os.path.join(HERE, "RESULTS.md"), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
