"""CNF encoding of "the shape S has a K-level packing" (the relaxed corona problem).

Mathematical definition (see FORMAT.md, section 4):
  levels 0..K, level 0 is the fixed copy T0 = S (coordinates as in the data file).
  A relaxed K-patch is a set of copies of S with levels such that
    (P1) copies are pairwise disjoint (as sets of cells), T0 is the only copy at level 0;
    (P2) for j < K, every cell of Halo(P_j) is covered by P_{j+1}
         (P_j = union of the copies of level <= j);
    (P3) every copy of level j >= 1 touches P_{j-1}
         (it has a cell in Halo(P_{j-1}), i.e. shares a boundary point with it).
  No condition about holes.  The CNF is satisfiable iff a relaxed K-patch exists.

Variables
  t[p,j]  copy p (an orientation + translation) is used at level j        (j in Lambda(p))
  y[c,j]  cell c (not in T0) is covered by a copy of level <= j           (c in R_j)
  aux     sequential-counter variables for "at most one copy per cell"

Static pruning (each step is implied by (P1)-(P3), so it only removes impossible
(p,j); proofs in FORMAT.md):
  d(c) = graph distance from T0 in the touch graph.  Since P_j contains Halo(P_{j-1}),
         every cell with d(c) <= j lies in P_j; so a copy of level j has all cells with
         d >= j.  Units: y[c, d(c)] for 1 <= d(c) <= K.
  R_j  = cells that some allowed (p, j'), j' <= j, can cover (R_0 = T0).
  (p,j) is allowed only if p is disjoint from T0, min d over p >= j, Halo(p) meets
  R_{j-1} (for j = 1: meets T0), and (if j < K) Halo(p) is inside R_{j+1}.
  These conditions are iterated to a fixpoint.
"""
from grids import W, OFF, key, unkey


class Encoding:
    def __init__(self, grid, shape_xy, K):
        self.g = grid
        self.K = K
        self.shape_xy = [tuple(c) for c in shape_xy]
        self.T0 = frozenset(key(x, y) for x, y in self.shape_xy)
        oris = grid.orientations(self.shape_xy)
        self.ori_xy = oris
        self.ori_off = [tuple(x * W + y for x, y in o) for o in oris]
        self.ori_halo = [tuple(sorted(grid.halo_off(o))) for o in self.ori_off]

    # ------------------------------------------------------------------ build
    def build(self, max_rounds=6):
        K, T0, NBR = self.K, self.T0, self.g.NBR
        # distances from T0 in the touch graph, up to K
        d = {c: 0 for c in T0}
        front = list(T0)
        vk = self.g.valid_key
        for r in range(1, K + 1):
            nf = []
            for c in front:
                for e in NBR:
                    n = c + e
                    if n not in d and (vk is None or vk(n)):
                        d[n] = r; nf.append(n)
            front = nf
        self.d = d
        Kp1 = K + 1
        cells, halos, lam, ids = [], [], [], []
        seen = set()
        R = [set(T0)]
        prev = set()
        tok = self.g.translation_ok
        for j in range(1, K + 1):
            newc = R[j - 1] - prev
            prev = set(R[j - 1])
            for c in newc:
                for o, hal in enumerate(self.ori_halo):
                    base = o << 26
                    for h in hal:
                        t = c - h
                        kk = base + t
                        if kk in seen:
                            continue
                        seen.add(kk)
                        tx, ty = unkey(t)
                        if not tok(tx, ty):
                            continue
                        cs = tuple(t + q for q in self.ori_off[o])
                        mind = Kp1
                        bad = False
                        for q in cs:
                            if q in T0:
                                bad = True; break
                            dq = d.get(q, Kp1)
                            if dq < mind:
                                mind = dq
                        if bad:
                            continue
                        hi = min(K, mind)
                        if j > hi:
                            continue
                        cells.append(cs)
                        halos.append(tuple(t + q for q in hal))
                        lam.append([j, hi])
                        ids.append((o, t))
            Rj = set(R[j - 1])
            for i, (lo, hi) in enumerate(lam):
                if lo <= j <= hi:
                    Rj.update(cells[i])
            R.append(Rj)
        # fixpoint pruning
        self.rounds = 0
        for rnd in range(max_rounds):
            self.rounds = rnd + 1
            changed = False
            for i in range(len(lam)):
                if lam[i] is None:
                    continue
                lo, hi = lam[i]
                hal = halos[i]
                newlo = None
                for j in range(lo, hi + 1):
                    if j == 1:
                        tch = any(h in T0 for h in hal)
                    else:
                        Rm = R[j - 1]
                        tch = any(h in Rm for h in hal)
                    if not tch:
                        continue
                    if j < K:
                        Rp = R[j + 1]
                        if not all(h in Rp for h in hal):
                            continue
                    newlo = j
                    break
                if newlo is None:
                    lam[i] = None; changed = True
                elif newlo != lo:
                    lam[i] = [newlo, hi]; changed = True
            if not changed:
                break
            R = [set(T0)]
            for j in range(1, K + 1):
                Rj = set(R[j - 1])
                for i, lh in enumerate(lam):
                    if lh is not None and lh[0] <= j <= lh[1]:
                        Rj.update(cells[i])
                R.append(Rj)
        keep = [i for i in range(len(lam)) if lam[i] is not None]
        keep.sort(key=lambda i: ids[i])
        self.P = [cells[i] for i in keep]
        self.H = [halos[i] for i in keep]
        self.L = [tuple(lam[i]) for i in keep]
        self.ids = [ids[i] for i in keep]
        self.R = R
        # first level at which a cell can be covered
        first = {}
        for j in range(K, 0, -1):
            for c in R[j]:
                if c not in T0:
                    first[c] = j
        self.first = first
        self.cellorder = sorted(first)
        self.stats = dict(K=K, placements=len(self.P), placement_levels=sum(h - l + 1 for l, h in self.L),
                          cells=len(first), prune_rounds=self.rounds)
        return self.stats

    # ------------------------------------------------------------------ emit
    def emit(self, add, varmap=None):
        """Emit the clauses through add(list_of_ints).  Deterministic numbering.
        varmap, if given, is called as varmap(var, description_tuple)."""
        K, T0 = self.K, self.T0
        nv = 0
        tv = {}
        for i, (lo, hi) in enumerate(self.L):
            for j in range(lo, hi + 1):
                nv += 1; tv[(i, j)] = nv
                if varmap:
                    varmap(nv, ('t', i, j))
        yv = {}
        for c in self.cellorder:
            for j in range(self.first[c], K + 1):
                nv += 1; yv[(c, j)] = nv
                if varmap:
                    varmap(nv, ('y', c, j))
        self.tv, self.yv = tv, yv
        ncl = 0
        # (F) units: d(c) = r <= K  =>  y[c, r]
        bad = False
        for c, r in sorted(self.d.items()):
            if 1 <= r <= K:
                v = yv.get((c, r))
                if v is None:
                    bad = True
                else:
                    add([v]); ncl += 1
        if bad:
            nv += 1
            add([nv]); add([-nv]); ncl += 2
            if varmap:
                varmap(nv, ('contradiction',))
        cover = {}
        for i, cs in enumerate(self.P):
            for c in cs:
                cover.setdefault(c, []).append(i)
        for c in self.cellorder:
            f = self.first[c]
            lst = cover.get(c, [])
            for j in range(f, K + 1):
                if j > f:
                    add([-yv[(c, j - 1)], yv[(c, j)]]); ncl += 1
                cl = [-yv[(c, j)]]
                if j > f:
                    cl.append(yv[(c, j - 1)])
                for i in lst:
                    lo, hi = self.L[i]
                    if lo <= j <= hi:
                        cl.append(tv[(i, j)])
                add(cl); ncl += 1
            # at most one copy covers c (sequential counter, Sinz 2005)
            xs = []
            for i in lst:
                lo, hi = self.L[i]
                for j in range(lo, hi + 1):
                    xs.append(tv[(i, j)])
            m = len(xs)
            if m >= 2:
                s = []
                for a in range(m - 1):
                    nv += 1; s.append(nv)
                    if varmap:
                        varmap(nv, ('amo', c, a))
                add([-xs[0], s[0]]); ncl += 1
                for a in range(1, m - 1):
                    add([-xs[a], s[a]]); add([-s[a - 1], s[a]]); add([-xs[a], -s[a - 1]]); ncl += 3
                add([-xs[m - 1], -s[m - 2]]); ncl += 1
        for i, (lo, hi) in enumerate(self.L):
            cs, hal = self.P[i], self.H[i]
            touchT0 = any(h in T0 for h in hal)
            for j in range(lo, hi + 1):
                v = tv[(i, j)]
                for c in cs:
                    add([-v, yv[(c, j)]]); ncl += 1
                if j < K:
                    for h in hal:
                        if h not in T0:
                            add([-v, yv[(h, j + 1)]]); ncl += 1
                if j >= 2 and not touchT0:
                    cl = [-v]
                    for h in hal:
                        w = yv.get((h, j - 1))
                        if w is not None:
                            cl.append(w)
                    add(cl); ncl += 1
        self.nvars = nv
        self.nbase = ncl
        return nv, ncl

    # ------------------------------------------------------------------ decode
    def decode(self, model):
        """List of (level, cells-keys) of the copies used, level 0 first."""
        pos = set(l for l in model if l > 0)
        tiles = [(0, tuple(sorted(self.T0)))]
        for (i, j), v in self.tv.items():
            if v in pos:
                tiles.append((j, tuple(sorted(self.P[i]))))
        tiles.sort()
        return tiles, [(i, j) for (i, j), v in self.tv.items() if v in pos]

    def hole_clause(self, j, hole, used):
        """Clause forbidding: every copy in `used` that borders `hole` is present with its
        level, and no cell of `hole` is covered at level <= j.  `used` = [(i, level)]
        with level <= j.  Returns (clause, enclosing copies as (level, cells))."""
        EDGE = self.g.EDGE
        bnd = {c + e for c in hole for e in EDGE} - set(hole)
        enc = []
        for (i, lv) in used:
            if lv <= j and bnd.intersection(self.P[i]):
                enc.append((i, lv))
        encT0 = bool(bnd & self.T0)
        cl = [-self.tv[(i, lv)] for i, lv in sorted(enc)]
        for c in sorted(hole):
            v = self.yv.get((c, j))
            if v is not None:
                cl.append(v)
        info = dict(level=j, hole=sorted(unkey(c) for c in hole),
                    enclosing=[[lv, sorted(unkey(c) for c in self.P[i])] for i, lv in sorted(enc)]
                    + ([[0, sorted(self.shape_xy)]] if encT0 else []))
        return cl, info
