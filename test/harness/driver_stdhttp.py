"""Std.Http driver: run each corpus vector through the compiled `stdhttp`, which reports the verdict of
Lean's standard-library body-length decision (Std.Http.Message.Head.getSize)."""
import json, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
BIN = os.path.join(ROOT, ".lake", "build", "bin", "stdhttp")
def main():
    vecs = json.load(open(os.path.join(HERE, "..", "corpus", "vectors.json")))["vectors"]
    for name, hexs in vecs.items():
        out = subprocess.run([BIN], input=bytes.fromhex(hexs), capture_output=True).stdout.decode().strip()
        print(json.dumps({"name": name, "verdict": out or "error"}))
if __name__ == "__main__":
    main()
