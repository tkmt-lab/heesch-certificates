"""Heesch numbers Hc, Hh of one polyform with witnesses and DRAT certificates.

modes for a K-level search
  'relaxed' : no hole condition at all (only for diagnostics)
  'Hh'      : P_1..P_{K-1} must have no holes (outermost corona may have holes)
  'Hc'      : P_1..P_K must have no holes
Holes are found after the fact in a model; each one is excluded by a clause
(see Encoding.hole_clause) and the solver is called again (lazy hole elimination, as in
Kaplan 2022, section 3.2, but with the hole cells in the clause so that it stays sound).
"""
import hashlib, os, subprocess, sys, time
from pysat.solvers import Cadical153, Lingeling, Glucose4
import pysolvers
from grids import holes_keys, unkey
from encode import Encoding

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DRAT_TRIM = os.environ.get('DRAT_TRIM', os.path.join(ROOT, 'tools', 'drat-trim', 'drat-trim'))


SOLVERS = {'cadical153': (Cadical153, 'cadical', 'cadical153_tracepr'),
           'lingeling': (Lingeling, 'lingeling', 'lingeling_tracepr'),
           'glucose4': (Glucose4, 'glucose', 'glucose41_tracepr')}
LEAN = {'elim': 0, 'subsume': 0, 'vivify': 0, 'probe': 0}
AUTO_THRESHOLD = (350000, 700000)   # m = placement-levels x tile size
PROOF_FORMAT = {'cadical153': 'binary DRAT (CaDiCaL 1.5.3 via python-sat)',
                'lingeling': 'text DRAT (Lingeling via python-sat)',
                'glucose4': 'DRUP (Glucose 4.1 via python-sat)'}


class DimacsWriter:
    HDR = 40

    def __init__(self, path):
        self.f = open(path, 'w', buffering=1 << 20)
        self.f.write(' ' * (self.HDR - 1) + '\n')
        self.n = 0
        self.maxv = 0

    def add(self, cl):
        self.f.write(' '.join(map(str, cl)) + ' 0\n')
        self.n += 1

    def close(self, nvars):
        self.f.flush()
        self.f.seek(0)
        h = f'p cnf {nvars} {self.n}'
        assert len(h) < self.HDR
        self.f.write(h + ' ' * (self.HDR - 1 - len(h)))
        self.f.close()


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        while True:
            b = f.read(1 << 22)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def holes_by_level(grid, tiles, levels):
    """tiles: [(level, cell keys)].  Returns [(j, hole)] for j in levels."""
    out = []
    for j in levels:
        occ = set()
        for lv, cs in tiles:
            if lv <= j:
                occ.update(cs)
        for h in holes_keys(occ, grid.EDGE, grid.valid_key, grid.hole_margin):
            out.append((j, h))
    return out


def check_levels(mode, K):
    if mode == 'relaxed':
        return []
    if mode == 'Hh':
        return list(range(1, K))
    return list(range(1, K + 1))


class Run:
    """One K-level search: encoding, solver, optional CNF file and DRAT trace."""

    def __init__(self, grid, shape, K, mode, cnf_path=None, drat_path=None, blocks=None, opts=None,
                 solver='cadical153'):
        self.grid, self.K, self.mode = grid, K, mode
        t0 = time.time()
        self.enc = Encoding(grid, shape, K)
        self.stats = dict(self.enc.build())
        if solver == 'auto':
            # size of the cell/copy incidence; CaDiCaL needs ~1 GB near 4.5e5 (17-omino, 4 levels)
            m = self.stats['placement_levels'] * len(shape)
            if m <= AUTO_THRESHOLD[0]:
                solver, opts = 'cadical153', dict(LEAN)
            elif m <= AUTO_THRESHOLD[1]:
                solver, opts = 'glucose4', None
            else:
                solver, opts = 'lingeling', None
        self.solver = solver
        self.opts = opts
        self.stats['solver'] = solver
        cls, attr, tr = SOLVERS[solver]
        self.s = cls()
        if opts:
            self.s.configure(opts)
        self.drat_f = None
        if drat_path:
            self.drat_f = open(drat_path, 'w+b')
            self.s.prfile = self.drat_f
            self.s.prfp = getattr(pysolvers, tr)(getattr(self.s, attr), self.drat_f)
        self.w = DimacsWriter(cnf_path) if cnf_path else None
        add_s = self.s.add_clause
        if self.w:
            wadd = self.w.add

            def add(cl):
                add_s(cl); wadd(cl)
        else:
            add = add_s
        self.add = add
        nv, ncl = self.enc.emit(add)
        self.blocks = []
        self.inner_filled_holes = 0
        if blocks:
            for info in blocks:
                cl = self.clause_from_info(info)
                add(cl)
                self.blocks.append(info)
        self.stats['vars'] = nv
        self.stats['base_clauses'] = ncl
        self.stats['encode_s'] = round(time.time() - t0, 3)

    def clause_from_info(self, info):
        """Rebuild a hole-blocking clause from its geometric description."""
        from grids import key
        enc = self.enc
        idx = {tuple(sorted(cs)): i for i, cs in enumerate(enc.P)}
        lits = []
        for lv, cells in info['enclosing']:
            if lv == 0:
                continue
            i = idx[tuple(sorted(key(x, y) for x, y in cells))]
            lits.append(-enc.tv[(i, lv)])
        lits.sort(key=abs)
        j = info['level']
        for x, y in info['hole']:
            v = enc.yv.get((key(x, y), j))
            if v is not None:
                lits.append(v)
        return lits

    def solve(self, max_rounds=100000):
        t0 = time.time()
        rounds = 0
        levels = check_levels(self.mode, self.K)
        while True:
            rounds += 1
            ok = self.s.solve()
            if not ok:
                self.stats['solve_s'] = round(time.time() - t0, 3)
                self.stats['rounds'] = rounds
                return False, None
            tiles, used = self.enc.decode(self.s.get_model())
            hs = holes_by_level(self.grid, tiles, levels)
            if not hs:
                self.stats['solve_s'] = round(time.time() - t0, 3)
                self.stats['rounds'] = rounds
                return True, tiles
            if rounds >= max_rounds:
                raise RuntimeError('too many hole rounds')
            for j, h in hs:
                if j < self.K:
                    # a hole of an inner patch P_j; it is filled by copies of higher level
                    # (otherwise the halo condition would fail).  Count for the record.
                    self.inner_filled_holes += 1
                cl, info = self.enc.hole_clause(j, h, used)
                self.add(cl)
                self.blocks.append(info)

    def finish(self):
        """Close files.  Returns (nvars, nclauses written)."""
        nv = self.enc.nvars
        if self.drat_f:
            pysolvers.flushpr(self.s.prfp)
        self.s.delete()
        if self.drat_f:
            self.drat_f.close()
        if self.w:
            self.w.close(nv)
            return nv, self.w.n
        return nv, None


def _progress(tag, st):
    print(f"  [{tag}] K={st['K']} {st['mode']} {'SAT' if st['sat'] else 'UNSAT'} rounds={st.get('rounds')} "
          f"blocks={st['blocks']} solver={st.get('solver')} encode={st['encode_s']}s solve={st.get('solve_s')}s "
          f"clauses={st['base_clauses']}", file=sys.stderr, flush=True)


def tiles_xy(tiles):
    return [[lv, [list(unkey(c)) for c in cs]] for lv, cs in tiles]


def run_drat_trim(cnf, drat, cap_mb=1000, cap_s=1800, tlimit=1700):
    t0 = time.time()
    # cap_mb is not enforced here; limit memory outside (ulimit, container).  cap_s is a timeout.
    p = subprocess.run([DRAT_TRIM, cnf, drat, '-t', str(tlimit)], capture_output=True, text=True,
                       timeout=cap_s)
    dt = time.time() - t0
    res = None
    vt = None
    for line in p.stdout.splitlines():
        if line.startswith('s '):
            res = line.strip()
        if 'verification time' in line:
            try:
                vt = float(line.split(':')[1].split()[0])
            except Exception:
                pass
    return dict(result=res, returncode=p.returncode, wall_s=round(dt, 3), verification_s=vt,
                stderr=p.stderr.strip()[-300:] if p.returncode else '')


def _finalize(rec, ok, cnf, drat, nv, nc, defer, keep):
    if ok:
        rec['error'] = 'SAT: not a certificate'
    else:
        rec['cnf'] = dict(sha256=sha256_file(cnf), bytes=os.path.getsize(cnf), vars=nv, clauses=nc)
        rec['drat'] = dict(sha256=sha256_file(drat), bytes=os.path.getsize(drat), format=PROOF_FORMAT[rec['solver']])
        if defer:
            rec['drat_trim'] = dict(result=None, pending=dict(cnf=cnf, drat=drat))
            keep = True
        else:
            rec['drat_trim'] = run_drat_trim(cnf, drat)
    if not keep:
        for p in (cnf, drat):
            if os.path.exists(p):
                os.remove(p)
    return rec


def certify(grid, shape, K, mode, blocks, cache_dir, tag, keep=False, defer=False, opts=None, solver='cadical153'):
    """Fresh solve of base CNF + blocks with proof, then drat-trim.  Returns a record.
    defer=True: keep the CNF and DRAT files and do not run drat-trim (see drat_pending.py)."""
    os.makedirs(cache_dir, exist_ok=True)
    cnf = os.path.join(cache_dir, tag + '.cnf')
    drat = os.path.join(cache_dir, tag + '.drat')
    r = Run(grid, shape, K, 'relaxed', cnf, drat, blocks=blocks, opts=opts, solver=solver)
    ok, _ = r.solve()
    nv, nc = r.finish()
    rec = dict(K=K, mode=mode, n_blocks=len(blocks), encode=r.stats, solver=r.solver, solver_options=r.opts or {})
    del r
    import gc; gc.collect()
    return _finalize(rec, ok, cnf, drat, nv, nc, defer, keep)


def heesch(grid, shape, maxK=5, cert_dir=None, tag='x', defer=False, opts=None, solver='cadical153'):
    """Compute Hh and Hc.  Returns a dict with values, witnesses, certificate records."""
    out = dict(steps=[])
    t0 = time.time()
    wit_h = [(0, None)]
    Hh = None
    cert_h = None
    rec_h = None      # certificate made during the first solve (no hole clause was needed)
    for K in range(1, maxK + 1):
        cnf = drat = None
        if cert_dir is not None:
            os.makedirs(cert_dir, exist_ok=True)
            cnf = os.path.join(cert_dir, tag + f'_K{K}_Hh.cnf')
            drat = os.path.join(cert_dir, tag + f'_K{K}_Hh.drat')
        r = Run(grid, shape, K, 'Hh', cnf, drat, opts=opts, solver=solver)
        ok, tiles = r.solve()
        nv, nc = r.finish()
        out["steps"].append(dict(mode="Hh", sat=ok, blocks=len(r.blocks),
                                 inner_filled_holes=r.inner_filled_holes, **r.stats))
        _progress(tag, out['steps'][-1])
        if ok:
            wit_h = tiles
            for p in (cnf, drat):
                if p and os.path.exists(p):
                    os.remove(p)
        else:
            Hh = K - 1
            cert_h = (K, 'Hh', r.blocks)
            if cert_dir is not None:
                if not r.blocks:
                    rec_h = dict(K=K, mode='Hh', n_blocks=0, encode=dict(r.stats), solver=r.solver,
                                 solver_options=r.opts or {}, proof_from='first solve')
                    r = None
                    rec_h = _finalize(rec_h, False, cnf, drat, nv, nc, defer, False)
                else:
                    r = None
                    for p in (cnf, drat):
                        if os.path.exists(p):
                            os.remove(p)
            break
    if Hh is None:
        out.update(Hh=f'>={maxK}', Hc=None, time_s=round(time.time() - t0, 3))
        return out
    T0 = Encoding(grid, shape, 1).T0
    if Hh == 0:
        Hc = 0
        wit_c = None
        cert_c = None
    else:
        top = holes_by_level(grid, wit_h, [Hh])
        if not top:
            Hc, wit_c, cert_c = Hh, None, None
        else:
            r = Run(grid, shape, Hh, 'Hc', opts=opts, solver=solver)
            ok, tiles = r.solve()
            r.finish()
            out["steps"].append(dict(mode="Hc", sat=ok, blocks=len(r.blocks),
                                     inner_filled_holes=r.inner_filled_holes, **r.stats))
            _progress(tag, out['steps'][-1])
            if ok:
                Hc, wit_c, cert_c = Hh, tiles, None
            else:
                Hc = Hh - 1
                wit_c = [t for t in wit_h if t[0] <= Hh - 1]
                cert_c = (Hh, 'Hc', r.blocks)
    out['Hh'], out['Hc'] = Hh, Hc
    T0t = [(0, tuple(sorted(T0)))]
    wits = []
    if Hh == 0:
        wits.append(dict(serves=['Hc', 'Hh'], k=0, tiles=tiles_xy(T0t)))
    elif wit_c is None:
        wits.append(dict(serves=['Hc', 'Hh'], k=Hh, tiles=tiles_xy(wit_h)))
    else:
        wits.append(dict(serves=['Hh'], k=Hh, tiles=tiles_xy(wit_h)))
        wits.append(dict(serves=['Hc'], k=Hc, tiles=tiles_xy(wit_c) if Hc > 0 else tiles_xy(T0t)))
    out['witnesses'] = wits
    out['value_time_s'] = round(time.time() - t0, 3)
    if cert_dir is not None:
        r = None
        import gc; gc.collect()
        certs = []
        K, mode, blocks = cert_h
        rec = rec_h or certify(grid, shape, K, mode, blocks, cert_dir, tag + f'_K{K}_{mode}', defer=defer, opts=opts, solver=solver)
        rec['serves'] = ['Hh', 'Hc'] if cert_c is None else ['Hh']
        rec['blocks'] = blocks
        certs.append(rec)
        if cert_c is not None:
            K, mode, blocks = cert_c
            rec = certify(grid, shape, K, mode, blocks, cert_dir, tag + f'_K{K}_{mode}', defer=defer, opts=opts, solver=solver)
            rec['serves'] = ['Hc']
            rec['blocks'] = blocks
            certs.append(rec)
        out['certificates'] = certs
    out['time_s'] = round(time.time() - t0, 3)
    return out
