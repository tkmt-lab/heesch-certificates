"""Check all lower-bound witnesses with both geometric checkers.

Usage: python3 -B checkers/check_all_witnesses.py [--inputs DIR] [--output FILE]

check_witness.py (first checker) and geometry.py (second checker, written separately from
FORMAT.md, standard library only) are run on every witness in witnesses/*/*.jsonl. Neither
imports the CNF generator. With --inputs (a directory filled by fetch_inputs.py), every
shape and its (Hc, Hh) are also compared with Kaplan's files.
"""
import argparse
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "checkers"))
import check_witness as first  # noqa: E402
import geometry as second  # noqa: E402


def kaplan_rows(path):
    """Kaplan's file: two lines per shape, cell coordinates and 'Hc = a Hh = b'."""
    lines = [s.strip() for s in Path(path).read_text().splitlines() if s.strip()]
    assert len(lines) % 2 == 0
    out = []
    for a, b in zip(lines[::2], lines[1::2]):
        nums = list(map(int, a.split()))
        ref = b.replace("=", " ").split()
        out.append(dict(shape=frozenset(zip(nums[::2], nums[1::2])),
                        Hc=int(ref[ref.index("Hc") + 1]), Hh=int(ref[ref.index("Hh") + 1])))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inputs", type=Path)
    ap.add_argument("--output", type=Path)
    a = ap.parse_args()
    t0 = time.time()
    n_shapes = n_first = n_second = n_ref = 0
    values = {}
    for path in sorted((ROOT / "witnesses").glob("*/*.jsonl")):
        ref = kaplan_rows(a.inputs / path.parent.name / (path.stem + ".txt")) if a.inputs else None
        for line in path.read_text().splitlines():
            r = json.loads(line)
            n_shapes += 1
            F = first.FAMILIES[r["family"]]()
            served = set()
            for w in r["witnesses"]:
                err = first.check_witness(r["shape"], w, F)
                assert err is None, (path.name, r["index"], err)
                for s in w["serves"]:
                    assert r[s] == w["k"], (path.name, r["index"], s)
                    served.add(s)
                n_first += 1
            assert served == {"Hc", "Hh"}, (path.name, r["index"])
            reference = None
            if ref is not None:
                reference = dict(shape=ref[r["index"]]["shape"], Hc=ref[r["index"]]["Hc"], Hh=ref[r["index"]]["Hh"])
                n_ref += 1
            out = second.check_row(r, reference)
            assert out["status"] == "PASS"
            n_second += len(out["witnesses"])
            key = (r["family"], r["Hc"], r["Hh"])
            values[key] = values.get(key, 0) + 1
    result = dict(status="PASS", shapes=n_shapes, witnesses_first_checker=n_first, witnesses_second_checker=n_second,
                  compared_with_kaplan_files=n_ref,
                  values={f"{f} Hc={c} Hh={h}": n for (f, c, h), n in sorted(values.items())},
                  seconds=round(time.time() - t0, 1))
    assert n_shapes == 3964 and n_first == n_second == 6574
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
