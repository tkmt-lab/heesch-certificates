"""Check the records of the restricted search (Section 10 of the article).

Usage: python3 -B check_search.py [--output FILE]

1. search/candidates.jsonl.gz decompresses to the candidate list with the SHA-256 stated in the
   article's records; every candidate has 20-28 cells, is edge-connected, has no hole and no
   pinch vertex, is in canonical form under the 8 symmetries and translation, and its id is the
   SHA-256 of that form.
2. Every candidate classified as a periodic tiler has a lattice certificate in
   search/periodic-tilings.jsonl.gz; each certificate is checked with integer determinants:
   the copies are congruent to the shape, the lattice index equals the number of cells per
   fundamental domain, and no two cells of the domain are congruent modulo the lattice (so the
   translates cover the plane without overlap).
3. The classification counts by cell number equal Table 7 of the article.
4. Every saved satisfying patch (513) passes both geometric checkers as a corona with its k.
No SAT solver is used; the UNSAT outcomes are records (see search/solver-crosscheck.json and
recheck_certificates.py --search-samples for the checks that exist).
"""
import argparse
import collections
import gzip
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "checkers"))
import check_witness as first  # noqa: E402
import geometry as second  # noqa: E402

CANDIDATES_SHA256 = "5fb662257aaccbedeb699bfa966ba128b4a41cf9e52704875622ac579b6817ab"
TABLE7 = {20: (962, 770, 488), 21: (38, 56, 11), 22: (53, 85, 10), 23: (76, 102, 4), 24: (57, 57, 22),
          25: (107, 95, 8), 26: (70, 69, 15), 27: (90, 65, 10), 28: (62, 52, 8)}


def canonical(shape):
    variants = []
    for swap in (False, True):
        for sx in (-1, 1):
            for sy in (-1, 1):
                t = [(sx * (y if swap else x), sy * (x if swap else y)) for x, y in shape]
                x0 = min(x for x, y in t); y0 = min(y for x, y in t)
                variants.append(tuple(sorted((x - x0, y - y0) for x, y in t)))
    return min(variants)


def topology(shape):
    s = {tuple(c) for c in shape}
    assert len(s) == len(shape)

    def nb(c):
        x, y = c
        return ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1))

    def component(start, allowed):
        seen = {start}; todo = [start]
        while todo:
            for c in nb(todo.pop()):
                if c in allowed and c not in seen:
                    seen.add(c); todo.append(c)
        return seen
    assert component(next(iter(s)), s) == s
    x0 = min(x for x, y in s) - 1; x1 = max(x for x, y in s) + 1
    y0 = min(y for x, y in s) - 1; y1 = max(y for x, y in s) + 1
    outside = {(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1)} - s
    assert component((x0, y0), outside) == outside
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            around = [(x, y) in s, (x + 1, y) in s, (x + 1, y + 1) in s, (x, y + 1) in s]
            assert around not in ([True, False, True, False], [False, True, False, True])


def periodic(shape, p):
    a, b, d = p["a"], p["b"], p["d"]
    assert a > 0 and d > 0 and 0 <= b < a
    copies = p.get("copies", [shape])
    det = a * d
    assert det == p["index"] == len(shape) * len(copies)
    for tile in copies:
        assert len(tile) == len(shape) and canonical(tile) == canonical(shape)
    points = [tuple(c) for tile in copies for c in tile]
    # v-u lies in the lattice spanned by (a,0),(b,d) iff both Cramer numerators are divisible by det.
    for i, (x, y) in enumerate(points):
        for X, Y in points[:i]:
            dx, dy = x - X, y - Y
            assert (dx * d - dy * b) % det or (a * dy) % det
    return len(copies)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path)
    a = ap.parse_args()
    t0 = time.time()
    raw = gzip.decompress((ROOT / "search/candidates.jsonl.gz").read_bytes())
    assert hashlib.sha256(raw).hexdigest() == CANDIDATES_SHA256
    cands = [json.loads(l) for l in raw.decode().splitlines()]
    by_id = {c["id"]: c for c in cands}
    assert len(by_id) == len(cands) == 3442
    for c in cands:
        assert 20 <= c["cells"] == len(c["shape"]) <= 28
        topology(c["shape"])
        form = canonical(c["shape"])
        assert form == tuple(map(tuple, c["shape"]))
        assert hashlib.sha256(json.dumps(form, separators=(",", ":")).encode()).hexdigest() == c["id"]
    cls = {}
    for l in (ROOT / "search/classification.jsonl").read_text().splitlines():
        r = json.loads(l)
        assert r["id"] in by_id and r["id"] not in cls and r["cells"] == by_id[r["id"]]["cells"]
        cls[r["id"]] = r["classification"]
    assert set(cls) == set(by_id)
    table = collections.defaultdict(collections.Counter)
    for i, c in cls.items():
        table[by_id[i]["cells"]][c] += 1
    for n, (k1, k3, per) in TABLE7.items():
        assert (table[n]["K1_UNSAT"], table[n]["K3_UNSAT"], table[n]["periodic_tiler"]) == (k1, k3, per), n
    tiled = collections.Counter()
    certified = {}
    for l in gzip.decompress((ROOT / "search/periodic-tilings.jsonl.gz").read_bytes()).decode().splitlines():
        r = json.loads(l)
        certified[r["id"]] = periodic(by_id[r["id"]]["shape"], r["lattice"])
    periodic_ids = [i for i, c in cls.items() if c == "periodic_tiler"]
    assert all(i in certified for i in periodic_ids)
    tiled.update(certified[i] for i in periodic_ids)
    assert dict(tiled) == {1: 65, 2: 413, 4: 98}, dict(tiled)
    F = first.square_family()
    ks = collections.Counter()
    for l in gzip.decompress((ROOT / "search/sat-patches.jsonl.gz").read_bytes()).decode().splitlines():
        r = json.loads(l)
        w = dict(r["witness"], serves=["Hh"])
        assert first.check_witness(r["shape"], w, F) is None, r["id"]
        second.check_witness("omino", second.cells(r["shape"], "omino"), w, {"Hh": w["k"], "Hc": w["k"]})
        ks[w["k"]] += 1
    assert dict(ks) == {3: 511, 4: 1, 5: 1}, dict(ks)
    result = dict(status="PASS", candidates=len(cands), periodic_tilers=len(periodic_ids),
                  tilings_by_copies={str(k): v for k, v in sorted(tiled.items())},
                  satisfying_patches={str(k): v for k, v in sorted(ks.items())},
                  seconds=round(time.time() - t0, 1))
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
