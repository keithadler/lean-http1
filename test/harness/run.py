"""Differential framing harness. Runs every available parser over the corpus and builds a matrix of how
each frames each vector. The Lean column is the proved spec (`no_desync`); every other column is a real
parser. Two parsers that frame the same vector differently are a potential request-smuggling desync.

    python test/harness/run.py

Writes test/harness/RESULTS.md and results.json. Each driver is a command that emits one JSON line
{name, verdict} per vector; missing runtimes are skipped.
"""
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
VENV = "/private/tmp/claude-501/-Users-admin/471a0966-7f97-4ce7-a941-7d9d26f48c88/scratchpad/cmsvenv/bin/python"
PY = VENV if os.path.exists(VENV) else sys.executable

# (column name, description, command). The first must be the Lean oracle.
DRIVERS = [
    ("Lean (proved)", "the spec `no_desync` is about", [PY, os.path.join(HERE, "driver_lean.py")]),
    ("h11", "h11 0.16 (Python; hypercorn, uvicorn)", [PY, os.path.join(HERE, "driver_h11.py")]),
    ("Node/llhttp", "Node http.Server (llhttp)", ["node", os.path.join(HERE, "driver_node.js")]),
    ("Std.Http", "Lean's own standard library HTTP/1.1 parser",
     [PY, os.path.join(HERE, "driver_stdhttp.py")]),
]


def run_driver(cmd):
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None
    if out.returncode != 0 and not out.stdout.strip():
        return None
    res = {}
    for line in out.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            o = json.loads(line)
            res[o["name"]] = o["verdict"]
    return res or None


def main():
    subprocess.run([PY, os.path.join(ROOT, "test", "corpus", "vectors.py")], check=True)
    corpus = json.load(open(os.path.join(ROOT, "test", "corpus", "vectors.json")))
    names = list(corpus["vectors"])
    probes = corpus["probes"]

    cols, results = [], {}
    for col, desc, cmd in DRIVERS:
        r = run_driver(cmd)
        if r is not None:
            cols.append((col, desc))
            results[col] = r

    oracle = results[cols[0][0]]
    lines = ["# HTTP/1.1 framing: differential results", "",
             "Each row is a raw request byte stream (`test/corpus/vectors.py`). Each column is a parser's "
             "framing verdict: `reject`, `length:N`, or `chunked`. **Lean (proved)** is the reference the "
             "`no_desync` theorem is about; a cell that differs from it is **bold**. Two real parsers that "
             "differ on one row are a potential request-smuggling desync.", ""]
    header = "| Vector | probes | " + " | ".join(c for c, _ in cols) + " |"
    lines.append(header)
    lines.append("|" + "---|" * (len(cols) + 2))
    disagreements = []
    for name in names:
        ref = oracle.get(name, "-")
        row = [f"`{name}`", probes.get(name, "")]
        differ_from_ref = False
        verdicts = {}
        for col, _ in cols:
            v = results[col].get(name, "-")
            verdicts[col] = v
            if col != cols[0][0] and v != ref and v != "-":
                row.append(f"**{v}**")
                differ_from_ref = True
            else:
                row.append(v)
        lines.append("| " + " | ".join(row) + " |")
        distinct = set(v for v in verdicts.values() if v != "-")
        if len(distinct) > 1:
            disagreements.append((name, verdicts))

    lines += ["", f"Parsers: {len(cols)}. Vectors: {len(names)}. "
              f"Rows where parsers disagree: {len(disagreements)}.", ""]
    for col, desc in cols:
        lines.append(f"- **{col}**: {desc}")
    lines += ["", "## Where parsers disagree", ""]
    for name, verdicts in disagreements:
        lines.append(f"- `{name}` ({probes.get(name,'')}): "
                     + ", ".join(f"{c} = {v}" for c, v in verdicts.items()))

    open(os.path.join(HERE, "RESULTS.md"), "w").write("\n".join(lines) + "\n")
    json.dump({"columns": [c for c, _ in cols], "results": results, "probes": probes},
              open(os.path.join(HERE, "results.json"), "w"), indent=1)
    print("\n".join(lines))
    print(f"\n{len(disagreements)} of {len(names)} vectors frame differently across {len(cols)} parsers.")


if __name__ == "__main__":
    main()
