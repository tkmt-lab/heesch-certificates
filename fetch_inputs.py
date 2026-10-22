"""Download Kaplan's dataset files from their original URLs and verify sizes and SHA-256.

Usage: python3 -B fetch_inputs.py --directory DIR [--only selected]

The files are listed in inputs/kaplan-files.json. They are not redistributed in this packet
(the dataset page states no licence). Files already present with the right hash are kept.
Then `python3 -B checkers/check_all_witnesses.py --inputs DIR` compares every shape and its
(Hc, Hh) with Kaplan's files.
"""
import argparse
import hashlib
import json
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--directory", type=Path, required=True)
    p.add_argument("--only", choices=["selected"], help="only the files that contain selected shapes")
    a = p.parse_args()
    files = json.loads((ROOT / "inputs/kaplan-files.json").read_text())["files"]
    for r in files:
        if a.only == "selected" and r["role"] != "selected":
            continue
        dest = a.directory / r["family"] / r["name"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        if dest.exists() and dest.stat().st_size == r["bytes"] and hashlib.sha256(dest.read_bytes()).hexdigest() == r["sha256"]:
            continue
        req = urllib.request.Request(r["url"], headers={"User-Agent": "heesch-certificates fetch_inputs.py"})
        with urllib.request.urlopen(req, timeout=120) as src:
            data = src.read(r["bytes"] + 1)
        assert len(data) == r["bytes"] and hashlib.sha256(data).hexdigest() == r["sha256"], ("hash mismatch", r["url"])
        dest.write_bytes(data)
        print(r["family"], r["name"], "downloaded and verified")
    print(json.dumps(dict(status="PASS", directory=str(a.directory))))


if __name__ == "__main__":
    main()
