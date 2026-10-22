#!/usr/bin/env python3
"""Geometric check of lower-bound witnesses, independent of the SAT encoding.

usage: check_witness.py WITNESS.jsonl [...]
It does not import encode.py / heesch.py / grids.py.  Only the definition of a k-corona
(Kaplan 2022, section 2.1) is used; see FORMAT.md for the file format and the checks.
For each witness with value k and the list of values it serves (Hc and/or Hh):
  W1 exactly one tile of level 0, equal (as a set of cells) to the shape in the file;
  W2 every tile is an image of the shape under a symmetry of the grid plus a translation;
  W3 tiles are pairwise disjoint; levels are 0..k and every level 1..k is non-empty;
  W4 for j < k: Halo(P_j) is contained in P_{j+1}   (P_j = union of tiles of level <= j);
  W5 for j >= 1: every tile of level j has a cell in Halo(P_{j-1});
  W6 P_j is a closed topological disc for j <= k-1, and also for j = k if Hc is served
     (cells edge-connected, complement edge-connected, no vertex where the cells meet
     only diagonally).
"""
import json, sys

FAMILIES = {}


def square_family():
    nbr = [(dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0)]
    edge = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    mats = [(a, b, c, d) for a in (-1, 0, 1) for b in (-1, 0, 1) for c in (-1, 0, 1) for d in (-1, 0, 1)
            if a * d - b * c in (1, -1) and a * a + c * c == 1 and b * b + d * d == 1 and a * b + c * d == 0]
    assert len(mats) == 8

    def images(cells):
        for a, b, c, d in mats:
            yield [(a * x + b * y, c * x + d * y) for x, y in cells]

    def vertex_pinch(occ):
        # vertices are (x, y) = lower-left corner of cell (x, y); cells around vertex v:
        # (vx-1, vy-1), (vx, vy-1), (vx-1, vy), (vx, vy)
        vs = {(x + i, y + j) for x, y in occ for i in (0, 1) for j in (0, 1)}
        bad = []
        for vx, vy in vs:
            sw, se, nw, ne = ((vx - 1, vy - 1) in occ, (vx, vy - 1) in occ, (vx - 1, vy) in occ, (vx, vy) in occ)
            if (sw and ne and not se and not nw) or (se and nw and not sw and not ne):
                bad.append((vx, vy))
        return bad

    return dict(nbr=nbr, edge=edge, images=images, pinch=vertex_pinch, valid=lambda x, y: True, step=1, margin=2)


FAMILIES['omino'] = square_family


def _hex_mats():
    # rotation by 60 degrees and reflection in the v axis, basis v=(1,0), w=(1/2, sqrt3/2)
    A = (0, -1, 1, 1); B = (1, 1, 0, -1)
    mul = lambda m, n: (m[0] * n[0] + m[1] * n[2], m[0] * n[1] + m[1] * n[3],
                        m[2] * n[0] + m[3] * n[2], m[2] * n[1] + m[3] * n[3])
    out, R = [], (1, 0, 0, 1)
    for i in range(6):
        out += [R, mul(R, B)]; R = mul(A, R)
    return out


def hex_family():
    nbr = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)]
    mats = _hex_mats()

    def images(cells):
        for a, b, c, d in mats:
            yield [(a * x + b * y, c * x + d * y) for x, y in cells]
    # three hexagons meet at each vertex and any two of them share an edge, so a union of
    # hexagons has no vertex where cells meet only at a point
    return dict(nbr=nbr, edge=nbr, images=images, pinch=lambda occ: [], valid=lambda x, y: True, step=1, margin=2)


def iamond_family():
    import math
    valid = lambda x, y: (x - y) % 3 == 0 and x % 3 in (0, 1)
    VB, VG = ((-1, 2), (-1, -1), (2, -1)), ((1, -2), (1, 1), (-2, 1))
    verts = lambda x, y: {(x + a, y + b) for a, b in (VB if x % 3 == 0 else VG)}
    # touch = share a vertex, edge = share two vertices (computed from the vertex sets)
    def rel(cx, cy, need):
        out = []
        for x in range(cx - 6, cx + 7):
            for y in range(cy - 6, cy + 7):
                if (x, y) != (cx, cy) and valid(x, y) and len(verts(cx, cy) & verts(x, y)) >= need:
                    out.append((x - cx, y - cy))
        return out
    nb = {0: rel(0, 0, 1), 1: rel(1, 1, 1)}; ed = {0: rel(0, 0, 2), 1: rel(1, 1, 2)}
    nbr_of = lambda x, y: [(x + a, y + b) for a, b in nb[x % 3]]
    edge_of = lambda x, y: [(x + a, y + b) for a, b in ed[x % 3]]
    maps = []
    for a, b, c, d in _hex_mats():
        for ux in range(-3, 4):
            done = False
            for uy in range(-3, 4):
                f = lambda x, y: (a * x + b * y + ux, c * x + d * y + uy)
                if all(valid(*f(x, y)) and {f(*v) for v in verts(x, y)} == verts(*f(x, y)) for x, y in ((0, 0), (1, 1))):
                    maps.append((a, b, c, d, ux, uy)); done = True; break
            if done:
                break
    assert len(maps) == 12

    def images(cells):
        for a, b, c, d, ux, uy in maps:
            yield [(a * x + b * y + ux, c * x + d * y + uy) for x, y in cells]

    def pinch(occ):
        bad = []
        for v in {v for x, y in occ for v in verts(x, y)}:
            vx, vy = v
            around = [(x, y) for x in range(vx - 3, vx + 4) for y in range(vy - 3, vy + 4)
                      if valid(x, y) and v in verts(x, y)]
            assert len(around) == 6
            ang = lambda c: math.atan2((c[1] - vy) * math.sqrt(3) / 2, (c[0] - vx) + (c[1] - vy) / 2)
            ring = [c in occ for c in sorted(around, key=ang)]
            runs = sum(1 for i in range(6) if ring[i] and not ring[i - 1])
            if runs >= 2:
                bad.append(v)
        return bad
    return dict(nbr_of=nbr_of, edge_of=edge_of, images=images, pinch=pinch, valid=valid, step=3, margin=6)


FAMILIES['hex'] = hex_family
FAMILIES['iamond'] = iamond_family


def canon(cells, step=1):
    """translate by a vector of step*Z^2 so that the smallest cell is in [0, step)^2"""
    mx = min(x for x, y in cells); my = min(y for x, y in cells)
    mx, my = step * (mx // step), step * (my // step)
    return tuple(sorted((x - mx, y - my) for x, y in cells))


def nbrs(F, c, kind):
    if kind + '_of' in F:
        return F[kind + '_of'](*c)
    return [(c[0] + dx, c[1] + dy) for dx, dy in F[kind]]


def halo(occ, F):
    return {n for c in occ for n in nbrs(F, c, 'nbr') if F['valid'](*n)} - occ


def components(cells, F):
    cells = set(cells); comps = []
    while cells:
        st = [cells.pop()]; comp = set(st)
        while st:
            c = st.pop()
            for n in nbrs(F, c, 'edge'):
                if n in cells:
                    cells.discard(n); comp.add(n); st.append(n)
        comps.append(comp)
    return comps


def holes(occ, F):
    m = F.get('margin', 2)
    xs = [x for x, y in occ]; ys = [y for x, y in occ]
    x0, x1, y0, y1 = min(xs) - m, max(xs) + m, min(ys) - m, max(ys) + m
    box = {(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1)
           if (x, y) not in occ and F['valid'](x, y)}
    comps = components(box, F)
    # a component with a cell outside the bounding box of occ is unbounded (from such a cell
    # one can walk away from occ along edge-adjacent cells); the others are holes
    return [c for c in comps if all(min(xs) <= x <= max(xs) and min(ys) <= y <= max(ys) for x, y in c)]


def is_disc(occ, F):
    if len(components(occ, F)) != 1:
        return False, 'not edge-connected'
    h = holes(occ, F)
    if h:
        return False, f'{len(h)} hole(s), sizes {[len(c) for c in h]}'
    p = F['pinch'](occ)
    if p:
        return False, f'pinch vertex {p[0]}'
    return True, ''


def check_witness(shape, w, F):
    k = w['k']
    tiles = [(lv, [tuple(c) for c in cs]) for lv, cs in w['tiles']]
    S = [tuple(c) for c in shape]
    st = F['step']
    forms = {canon(im, st) for im in F['images'](S)}
    lv0 = [cs for lv, cs in tiles if lv == 0]
    if len(lv0) != 1 or set(lv0[0]) != set(S) or len(lv0[0]) != len(S):
        return 'W1 level-0 tile is not the shape'
    for lv, cs in tiles:
        if len(set(cs)) != len(S) or canon(cs, st) not in forms:
            return f'W2 a tile of level {lv} is not congruent to the shape'
        if not (0 <= lv <= k):
            return f'W3 level {lv} out of range'
    allc = [c for lv, cs in tiles for c in cs]
    if len(allc) != len(set(allc)):
        return 'W3 tiles overlap'
    for j in range(1, k + 1):
        if not any(lv == j for lv, cs in tiles):
            return f'W3 level {j} empty'
    P = [set(c for lv, cs in tiles if lv <= j for c in cs) for j in range(k + 1)]
    for j in range(k):
        miss = halo(P[j], F) - P[j + 1]
        if miss:
            return f'W4 halo of P_{j} not covered by P_{j + 1}: {sorted(miss)[:3]}'
    for lv, cs in tiles:
        if lv >= 1:
            if not (set(cs) & halo(P[lv - 1], F)):
                return f'W5 a tile of level {lv} does not touch P_{lv - 1}'
    top = k if 'Hc' in w['serves'] else k - 1
    for j in range(0, top + 1):
        ok, why = is_disc(P[j], F)
        if not ok:
            return f'W6 P_{j} is not a disc: {why}'
    return None


def main():
    nok = nbad = 0
    by_value = {}
    for path in sys.argv[1:]:
        for line in open(path):
            rec = json.loads(line)
            F = FAMILIES[rec['family']]()
            claimed = {'Hc': rec['Hc'], 'Hh': rec['Hh']}
            served = set()
            for w in rec['witnesses']:
                err = check_witness(rec['shape'], w, F)
                for s in w['serves']:
                    if claimed[s] != w['k']:
                        err = err or f'witness k={w["k"]} but {s}={claimed[s]}'
                    served.add(s)
                if err:
                    nbad += 1
                    print(f"FAIL {rec['file']} #{rec['index']} serves={w['serves']}: {err}")
                else:
                    nok += 1
            if served != {'Hc', 'Hh'}:
                nbad += 1
                print(f"FAIL {rec['file']} #{rec['index']}: values without witness {sorted({'Hc', 'Hh'} - served)}")
            key = (rec['file'], rec['Hc'], rec['Hh'])
            by_value[key] = by_value.get(key, 0) + 1
    for k in sorted(by_value):
        print(f'  {k[0]} Hc={k[1]} Hh={k[2]}: {by_value[k]} shapes')
    print(f'witnesses OK {nok}, FAIL {nbad}')
    sys.exit(1 if nbad else 0)


if __name__ == '__main__':
    main()
