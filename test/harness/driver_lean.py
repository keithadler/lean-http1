"""Lean oracle driver: run each corpus vector through the compiled `http1 frame`, the proved spec.
Output: one JSON line {name, verdict} per vector.
"""
import json
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
BIN = os.path.join(ROOT, ".lake", "build", "bin", "http1")


def main():
    vecs = json.load(open(os.path.join(HERE, "..", "corpus", "vectors.json")))["vectors"]
    for name, hexs in vecs.items():
        raw = bytes.fromhex(hexs)
        out = subprocess.run([BIN, "frame"], input=raw, capture_output=True).stdout.decode().strip()
        print(json.dumps({"name": name, "verdict": out or "error"}))


if __name__ == "__main__":
    main()
