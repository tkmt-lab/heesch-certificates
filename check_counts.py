"""Recompare the maximal-corona counts of the two implementations and check them geometrically.

Usage: python3 -B check_counts.py [--output FILE]

For each of the 30 shape-variant combinations in counts/table.json, reads
counts/inner-parts/<case>.json.gz and checks:
  1. both implementations list the same set of inner parts (layers <= k-1), in cell coordinates;
  2. the prefix counts N_1..N_{k-1} (distinct restrictions of the inner parts to layers <= j)
     equal both implementations' recorded prefix counts;
  3. every per-inner-part outer completion count of the first implementation that is valid
     equals the second's, and each side's total is the sum of its per-inner-part counts;
  4. every inner part is a (k-1)-corona whose unions P_0..P_{k-1} are discs (both checkers),
     and every completed corona recorded by the second implementation is a k-corona of the
     variant (Hh: P_0..P_{k-1} discs; Hc: also P_k) extending its inner part;
  5. the derived statements of Section 9.3: unique inner parts and minimum completion counts.
Uses only checkers/ (no SAT solver). The outer counts themselves are not recomputed here.
"""
import argparse
import gzip
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "checkers"))
import check_witness as first  # noqa: E402
import geometry as second  # noqa: E402


def key(tiles, upto):
    return tuple(sorted((lv, tuple(sorted(tuple(c) for c in cs))) for lv, cs in tiles if lv <= upto))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path)
    a = ap.parse_args()
    t0 = time.time()
    table = json.loads((ROOT / "counts/table.json").read_text())
    rows = table["rows"]
    assert len(rows) == 30
    full_agree, unique_hh, unique_hc, min_outer, n_inner, n_coronas = [], [], [], [], 0, 0
    for row in rows:
        d = json.loads(gzip.decompress((ROOT / f"counts/inner-parts/{row['case']}.json.gz").read_bytes()))
        k, var = d["k"], d["variant"]
        F = first.FAMILIES[d["family"]]()
        A = [key(x["tiles"], k - 1) for x in d["first"]]
        B = [key(x["tiles"], k - 1) for x in d["second"]]
        assert len(set(A)) == len(A) and len(set(B)) == len(B), row["case"]
        assert set(A) == set(B), ("inner sets differ", row["case"])
        for j in range(1, k):
            nj = len({tuple(t for t in p if t[0] <= j) for p in B})
            assert row["first"]["prefix_counts"][str(j)] == nj, (row["case"], j)
            assert row["second"]["prefix_counts"][str(j)] == nj, (row["case"], j)
        assert row["first"]["inner_parts"] == row["second"]["inner_parts"] == len(B)
        sec = {p: x["outer"] for p, x in zip(B, d["second"])}
        assert row["second"]["total"] == sum(sec.values()), row["case"]
        compared = 0
        for p, x in zip(A, d["first"]):
            if x["outer"] is not None and x["outer_status"] == "complete":
                assert x["outer"] == sec[p], ("outer count differs", row["case"])
                compared += 1
        complete = row["first"]["total"] is not None
        if complete:
            assert compared == len(A) and row["first"]["total"] == sum(x["outer"] for x in d["first"])
            fproof = row["first"]["inner_exhaustion_proof"] or (row["first"]["full_enumeration"] or {}).get("proof")
            assert fproof["drat_trim"] == "s VERIFIED", row["case"]  # inner or full enumeration exhausted
            assert row["second"]["inner_exhaustion_proof"]["drat_trim"] == "s VERIFIED"
            full_agree.append(row["case"])
            if len(B) == 1:
                (unique_hh if var == "Hh" else unique_hc).append(row["case"])
            min_outer.append((min(sec.values()), row["case"]))
        for x in d["second"]:
            inner = [[lv, cs] for lv, cs in x["tiles"]]
            w = dict(serves=["Hc"], k=k - 1, tiles=inner)
            assert first.check_witness(d["shape"], w, F) is None, row["case"]
            second.check_witness(d["family"], second.cells(d["shape"], d["family"]), w, {"Hc": k - 1, "Hh": k - 1})
            n_inner += 1
            cw = x["completed_corona"]
            assert cw["k"] == k and key(cw["tiles"], k - 1) == key(x["tiles"], k - 1)
            serves = ["Hc"] if var == "Hc" else ["Hh"]
            cw = dict(serves=serves, k=k, tiles=cw["tiles"])
            assert first.check_witness(d["shape"], cw, F) is None, row["case"]
            second.check_witness(d["family"], second.cells(d["shape"], d["family"]), cw, {"Hc": k, "Hh": k})
            n_coronas += 1
    assert len(full_agree) == 28
    assert min(min_outer)[0] == 2 and min(min_outer)[1] == "omino-17omino_2up-192-Hc"
    assert len(unique_hh) == 6 and len(unique_hc) == 4
    result = dict(status="PASS", combinations=len(rows), fully_compared=len(full_agree),
                  inner_parts_checked=n_inner, completed_coronas_checked=n_coronas,
                  unique_inner_Hh=sorted(unique_hh), unique_inner_Hc=sorted(unique_hc),
                  minimum_outer_completions=min(min_outer)[0], seconds=round(time.time() - t0, 1))
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
