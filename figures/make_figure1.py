"""Regenerate the TikZ body of Figure 1 (the unique inner part of 11-omino #2, k = Hh = 3).

Usage: python3 -B figures/make_figure1.py [OUT.tex] [--check]

Reads counts/inner-parts/omino-11omino_2up-2-Hh.json.gz, asserts that both implementations
record the same single inner part, checks it (congruence, disjointness, Halo(P0) in P1, (P3),
no holes in P1, P2), and writes the \\fill and \\draw lines. With --check, the output must equal
the body of the tikzpicture in the article source.
"""
import gzip
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper-heesch-certificates-v2.1-en.tex"


def norm(T):
    mx = min(x for x, y in T); my = min(y for x, y in T)
    return frozenset((x - mx, y - my) for x, y in T)


def holes(P):
    xs = [x for x, y in P]; ys = [y for x, y in P]
    box = {(x, y) for x in range(min(xs) - 1, max(xs) + 2) for y in range(min(ys) - 1, max(ys) + 2)}
    out = box - P; seen = set(); st = [(min(xs) - 1, min(ys) - 1)]
    while st:
        p = st.pop()
        if p in seen or p not in out:
            continue
        seen.add(p); x, y = p; st += [(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)]
    return out - seen


def body():
    d = json.loads(gzip.decompress((ROOT / "counts/inner-parts/omino-11omino_2up-2-Hh.json.gz").read_bytes()))
    assert len(d["first"]) == len(d["second"]) == 1
    inn = [(l, frozenset(map(tuple, c))) for l, c in d["second"][0]["tiles"]]
    assert set(inn) == {(l, frozenset(map(tuple, c))) for l, c in d["first"][0]["tiles"]}, "implementations differ"
    S = frozenset(map(tuple, d["shape"]))
    inn.sort(key=lambda t: (t[0], sorted(t[1])))
    assert inn[0] == (0, S)
    isos = [lambda x, y: (x, y), lambda x, y: (-y, x), lambda x, y: (-x, -y), lambda x, y: (y, -x),
            lambda x, y: (-x, y), lambda x, y: (y, x), lambda x, y: (x, -y), lambda x, y: (-y, -x)]
    forms = {norm(frozenset(f(*c) for c in S)) for f in isos}
    cells = {}
    for i, (l, c) in enumerate(inn):
        assert norm(c) in forms
        for x in c:
            assert x not in cells
            cells[x] = (i, l)
    N8 = [(dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)]

    def halo(P):
        return {(x + dx, y + dy) for x, y in P for dx, dy in N8} - set(P)
    P0 = set(S); P1 = P0 | {x for l, c in inn if l == 1 for x in c}; P2 = set(cells)
    assert halo(P0) <= P1
    for l, c in inn:
        if l == 1:
            assert c & halo(P0)
        if l == 2:
            assert c & halo(P1) and not (c & P1)
    assert not holes(P1) and not holes(P2)
    assert [sum(1 for l, c in inn if l == j) for j in (1, 2)] == [6, 12]
    shade = {0: "black!55", 1: "black!25", 2: "black!8"}
    out = [f"\\fill[{shade[l]}] ({x},{y}) rectangle +(1,1);" for (x, y), (i, l) in sorted(cells.items())]
    seg = set()
    for (x, y), (i, l) in cells.items():
        for (dx, dy), s in (((1, 0), ((x + 1, y), (x + 1, y + 1))), ((-1, 0), ((x, y), (x, y + 1))),
                            ((0, 1), ((x, y + 1), (x + 1, y + 1))), ((0, -1), ((x, y), (x + 1, y)))):
            n = cells.get((x + dx, y + dy))
            if n is None or n[0] != i:
                seg.add(tuple(sorted(s)))
    out += [f"\\draw ({a[0]},{a[1]})--({b[0]},{b[1]});" for a, b in sorted(seg)]
    return "\n".join(out) + "\n"


def main():
    text = body()
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if args:
        Path(args[0]).write_text(text)
    if "--check" in sys.argv:
        tex = PAPER.read_text()
        lines = [l for l in tex.splitlines() if l.startswith(("\\fill[black!", "\\draw ("))]
        assert "\n".join(lines) + "\n" == text, "figure body differs from the article"
        print(json.dumps(dict(status="PASS", figure=1, lines=len(lines))))


if __name__ == "__main__":
    main()
