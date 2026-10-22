#!/usr/bin/env python3
"""Restricted search for finite-Hh=4 polyominoes (Section 10 of the article).

generate: build the candidate list from the five Hh=3 polyominoes (witnesses/omino) and Kaplan's
19omino_2up.txt (fetch_inputs.py); `python3 -B search/search.py generate --inputs DIR` writes
candidates.jsonl and generation.json to $SEARCH_OUTPUT (default ./search-output).
one/search/controls: the SAT screening and periodic-tiling search (uses generator/).
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import random
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent  # packet root
# All outputs (candidates, generation record, attempt records, runtime/) go to SEARCH_OUTPUT.
B = Path(os.environ.get('SEARCH_OUTPUT', 'search-output')).resolve()
B.mkdir(parents=True, exist_ok=True)
sys.path[:0] = [str(ROOT / 'checkers'), str(ROOT / 'generator')]
from check_witness import check_witness, is_disc, square_family

F = square_family()
EDGE = ((1, 0), (-1, 0), (0, 1), (0, -1))
SALT = bytes.fromhex('523031332d422d32303236313032322d7631').decode()  # the original run's fixed salt, unchanged
SOURCE_NAMES = ('encode.py', 'heesch.py', 'grids.py', 'check_witness.py')


def src_path(name):
    return ROOT / ('checkers' if name == 'check_witness.py' else 'generator') / name


def utc():
    return datetime.now(timezone.utc).isoformat()


def dump(path, obj):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    tmp = Path(str(path) + '.tmp')
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')
    tmp.replace(path)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def norm(shape):
    mx = min(x for x, y in shape)
    my = min(y for x, y in shape)
    return tuple(sorted((x-mx, y-my) for x, y in shape))


def canon(shape):
    return min(norm(im) for im in F['images'](shape))


def identity(shape):
    return hashlib.sha256(json.dumps(canon(shape), separators=(',', ':')).encode()).hexdigest()


def rank(shape):
    return hashlib.sha256((SALT + identity(shape)).encode()).hexdigest()


def valid(shape):
    return is_disc({tuple(c) for c in shape}, F)[0]


def additions(shape):
    s = set(shape)
    for c in sorted({(x+dx, y+dy) for x, y in s for dx, dy in EDGE} - s):
        t = s | {c}
        if valid(t):
            yield canon(t)


def stretch(shape, axis, cut, amount):
    out = set()
    for cell in shape:
        c = list(cell)
        if c[axis] > cut:
            c[axis] += amount
        out.add(tuple(c))
        if cell[axis] == cut:
            for j in range(1, amount+1):
                c = list(cell)
                c[axis] += j
                out.add(tuple(c))
    return canon(out)


def period_one(shape):
    """Exhibit one-copy translational tiling by a lattice of index |S|.

    HNF generators are (a,0),(b,d), a*d=|S|, 0<=b<a.
    All |S| cells must represent distinct quotient classes.
    """
    n = len(shape)
    for a in range(1, n+1):
        if n % a:
            continue
        d = n // a
        for b in range(a):
            residues = {((x - (y//d)*b) % a, y % d) for x, y in shape}
            if len(residues) == n:
                out = dict(a=a, b=b, d=d, index=n)
                assert check_period(shape, out)
                return out
    return None


def check_period(shape, p):
    """Separate pair-difference check; no use of the quotient reduction above."""
    a, b, d = p['a'], p['b'], p['d']
    if not (a > 0 and d > 0 and 0 <= b < a and a*d == len(shape)):
        return False
    for i, (x, y) in enumerate(shape):
        for X, Y in shape[:i]:
            dx, dy = x-X, y-Y
            if dy % d == 0 and (dx - (dy//d)*b) % a == 0:
                return False
    return True


def period_two(shape):
    """Find, never infer from absence, a two-copy periodic tiling."""
    shape = canon(shape)
    n = len(shape)
    orientations = sorted({norm(im) for im in F['images'](shape)})
    for a in range(1, 2*n+1):
        if (2*n) % a:
            continue
        d = 2*n//a
        for b in range(a):
            def q(x, y):
                return ((x-(y//d)*b) % a, y % d)
            first = {q(x,y) for x,y in shape}
            if len(first) != n:
                continue
            rest = {(x,y) for x in range(a) for y in range(d)} - first
            u, v = min(rest)
            for ori in orientations:
                for x,y in ori:
                    dx, dy = u-x, v-y
                    tile = [(X+dx,Y+dy) for X,Y in ori]
                    if {q(X,Y) for X,Y in tile} == rest:
                        p = dict(a=a,b=b,d=d,index=2*n,copies=[shape,tile])
                        assert check_period_copies(shape,p)
                        return p
    return None


def check_period_copies(shape,p):
    """Check congruences and all pair differences in the entire fundamental patch."""
    a,b,d = p['a'],p['b'],p['d']
    copies = p['copies']
    if not (a > 0 and d > 0 and 0 <= b < a and a*d == len(shape)*len(copies)):
        return False
    if any(canon(tile) != canon(shape) for tile in copies):
        return False
    patch = [tuple(c) for tile in copies for c in tile]
    for i,(x,y) in enumerate(patch):
        for X,Y in patch[:i]:
            dx,dy=x-X,y-Y
            if dy % d == 0 and (dx-(dy//d)*b) % a == 0:
                return False
    return True


def period_many(shape, counts=(3,4,6), seconds=6, node_cap=50000):
    """Bounded exact cover on quotient lattices; only a checked tiling is a verdict.

    Fix the first tile at the origin. Other rows are all orientations and quotient
    translations with no duplicate residue and no intersection with that tile.
    A missing result (including budget expiry) says nothing about non-tiling.
    """
    shape = canon(shape)
    n = len(shape)
    orientations = sorted({norm(im) for im in F['images'](shape)})
    start = time.monotonic()
    nodes = 0
    lattices = 0
    class Budget(Exception):
        pass
    def budget():
        if time.monotonic()-start > seconds or nodes >= node_cap:
            raise Budget
    try:
        for count in counts:
            area = n*count
            for a in range(1,area+1):
                if area % a:
                    continue
                d = area//a
                for b in range(a):
                    budget()
                    lattices += 1
                    def mask(tile):
                        r=0
                        for x,y in tile:
                            bit = 1 << (((x-(y//d)*b)%a)*d+y%d)
                            if r & bit:
                                return None
                            r |= bit
                        return r
                    first = mask(shape)
                    if first is None:
                        continue
                    remaining = ((1<<area)-1) ^ first
                    rows = {}
                    for ori in orientations:
                        for dx in range(a):
                            budget()
                            for dy in range(d):
                                tile=[(x+dx,y+dy) for x,y in ori]
                                m=mask(tile)
                                if m is not None and not (m & first):
                                    rows.setdefault(m,tile)
                    by_cell={i:[] for i in range(area) if remaining & (1<<i)}
                    for m in rows:
                        bits=m
                        while bits:
                            t=bits & -bits
                            by_cell[t.bit_length()-1].append(m)
                            bits-=t
                    def cover(left):
                        nonlocal nodes
                        nodes+=1
                        budget()
                        if not left:
                            return []
                        options=None
                        bits=left
                        while bits:
                            t=bits & -bits
                            opts=[m for m in by_cell[t.bit_length()-1] if (m & left)==m]
                            if not opts:
                                return None
                            if options is None or len(opts)<len(options):
                                options=opts
                                if len(opts)==1:
                                    break
                            bits-=t
                        for m in options:
                            result=cover(left ^ m)
                            if result is not None:
                                return [m]+result
                        return None
                    result=cover(remaining)
                    if result is not None:
                        p=dict(a=a,b=b,d=d,index=area,copies=[shape]+[rows[m] for m in result])
                        assert len(p['copies'])==count and check_period_copies(shape,p)
                        return dict(status='tiler',certificate=p,elapsed_s=round(time.monotonic()-start,3),nodes=nodes,lattices=lattices)
    except Budget:
        return dict(status='budget',elapsed_s=round(time.monotonic()-start,3),nodes=nodes,lattices=lattices)
    return dict(status='not_found',elapsed_s=round(time.monotonic()-start,3),nodes=nodes,lattices=lattices)


def seeds():
    out = []
    for path in sorted((ROOT / 'witnesses/omino').glob('*.jsonl')):
        for line in path.read_text().splitlines():
            rec = json.loads(line)
            if rec['Hh'] == 3:
                out.append(rec)
    assert len(out) == 5
    return out


def generate(args):
    started = utc()
    ss = seeds()
    manifest = dict(files=[dict(f, path=f['family'] + '/' + f['name']) for f in
                           json.loads((ROOT / 'inputs/kaplan-files.json').read_text())['files'] if f['family'] == 'omino'])
    inputs = []
    for item in manifest['files']:
        path = Path(args.inputs) / item['path']
        digest = sha(path)
        assert digest == item['sha256'], str(path)
        inputs.append(dict(path=str(path), sha256=digest, bytes=path.stat().st_size))
    selected = {}
    generated = Counter()

    def add(shape, family, origin):
        shape = canon(shape)
        if not (20 <= len(shape) <= 28 and valid(shape)):
            return
        generated[family] += 1
        ident = identity(shape)
        if ident not in selected:
            selected[ident] = dict(id=ident, cells=len(shape), shape=shape, families=[], origins=[])
        r = selected[ident]
        if family not in r['families']:
            r['families'].append(family)
        if origin not in r['origins']:
            r['origins'].append(origin)

    for s in ss:
        shape = canon(s['shape'])
        origin = dict(file=s['file'], index=s['index'], original_cells=len(shape))
        stage1 = set()
        for axis in (0, 1):
            for cut in sorted({c[axis] for c in shape}):
                for amount in (1, 2, 3):
                    t = stretch(shape, axis, cut, amount)
                    if len(t) <= 28 and valid(t):
                        stage1.add(t)
                        add(t, 'strip', dict(**origin, edits=[[axis, cut, amount]]))
        for t in sorted(stage1):
            for axis in (0, 1):
                for cut in sorted({c[axis] for c in t}):
                    for amount in (1, 2, 3):
                        u = stretch(t, axis, cut, amount)
                        add(u, 'strip2', dict(**origin, intermediate=identity(t), edit=[axis, cut, amount]))
        for ax, ay in ((2, 1), (1, 2), (2, 2)):
            if len(shape)*ax*ay <= 28:
                t = {(ax*x+i, ay*y+j) for x, y in shape for i in range(ax) for j in range(ay)}
                add(t, 'inflate', dict(**origin, scale=[ax, ay]))
        rng = random.Random(SALT + identity(shape))
        for walk in range(128):
            t = shape
            path_ids = []
            while len(t) < 20:
                opts = sorted(set(additions(t)))
                if not opts:
                    break
                t = opts[rng.randrange(len(opts))]
                path_ids.append(identity(t))
            if len(t) == 20:
                add(t, 'grow_H3', dict(**origin, walk=walk, path=path_ids))

    path = Path(args.inputs) / 'omino/19omino_2up.txt'
    lines = path.read_text().splitlines()
    all_children = set()
    parent_counts = []
    for i in range(0, len(lines), 2):
        coords = list(map(int, lines[i].split()))
        s = list(zip(coords[::2], coords[1::2]))
        assert len(s) == 19 and 'Hh' in lines[i+1]
        opts = sorted(set(additions(s)), key=rank)
        all_children.update(identity(t) for t in opts)
        parent_counts.append(len(opts))
        for t in opts[:2]:
            add(t, 'grow19', dict(file=path.name, index=i//2, original_cells=19))
    assert len(parent_counts) == 767
    priority = {'inflate': 0, 'strip': 1, 'strip2': 2, 'grow_H3': 3, 'grow19': 4}
    cases = sorted(selected.values(), key=lambda r: (min(priority[f] for f in r['families']), rank(r['shape'])))
    for r in cases:
        r['period_one'] = period_one(r['shape'])
    with (B / 'candidates.jsonl').open('w') as f:
        for r in cases:
            f.write(json.dumps(r, separators=(',', ':')) + '\n')
    summary = dict(started_utc=started, ended_utc=utc(), salt=SALT,
                   input_files=inputs, controls=[dict(file=s['file'], index=s['index'], cells=len(s['shape'])) for s in ss],
                   generated_before_cross_family_dedup=dict(generated), selected_distinct=len(cases),
                   selected_by_cells=dict(Counter(r['cells'] for r in cases)),
                   selected_by_family=dict(Counter(f for r in cases for f in r['families'])),
                   grow19_parents=len(parent_counts), grow19_all_distinct_children=len(all_children),
                   grow19_all_ids_sha256=hashlib.sha256('\n'.join(sorted(all_children)).encode()).hexdigest(),
                   grow19_children_per_parent=dict(Counter(parent_counts)),
                   one_copy_tilers=sum(r['period_one'] is not None for r in cases),
                   candidates_sha256=sha(B / 'candidates.jsonl'), source_code_sha256={n: sha(src_path(n)) for n in SOURCE_NAMES})
    dump(B / 'generation.json', summary)
    print(json.dumps({k:v for k,v in summary.items() if k not in ('input_files','grow19_children_per_parent','source_code_sha256')}), flush=True)


def one(args):
    from heesch import Run, LEAN, tiles_xy
    from grids import SquareGrid
    case = json.loads(Path(args.case).read_text())
    out = dict(id=case['id'], K=args.K, cells=len(case['shape']), status='started', started_utc=utc())
    dump(args.output, out)
    t = time.monotonic()
    run = None
    try:
        assert valid(case['shape'])
        options = dict(LEAN) if args.solver == 'cadical153' else None
        if args.precheck and args.K == 3:
            run = Run(SquareGrid(), case['shape'], 1, 'Hh', opts=options, solver=args.solver)
            pre_ok, pre_tiles = run.solve(max_rounds=2000)
            pre_stats = dict(run.stats)
            if pre_ok:
                pre_w = dict(serves=['Hh'], k=1, tiles=tiles_xy(pre_tiles))
                assert check_witness(case['shape'], pre_w, F) is None
            run.finish()
            run = None
            out['precheck'] = dict(K=1, sat=pre_ok, stats=pre_stats)
            if not pre_ok:
                out.update(K=1, requested_K=3, status='UNSAT', stats=pre_stats, blocks=0)
                return
        run = Run(SquareGrid(), case['shape'], args.K, 'Hh', opts=options, solver=args.solver)
        out.update(status='encoded', stats=run.stats)
        dump(args.output, out)
        ok, tiles = run.solve(max_rounds=2000)
        out.update(status='SAT' if ok else 'UNSAT', stats=run.stats, blocks=len(run.blocks))
        if ok:
            w = dict(serves=['Hh'], k=args.K, tiles=tiles_xy(tiles))
            err = check_witness(case['shape'], w, F)
            if err:
                raise RuntimeError(err)
            out.update(witness=w, geometric_check='PASS')
        run.finish()
        run = None
    except Exception as exc:
        out.update(status='error', error=repr(exc))
    finally:
        if run is not None:
            run.finish()
        # macOS reports bytes for ru_maxrss.
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        out.update(ended_utc=utc(), elapsed_s=round(time.monotonic()-t, 3), peak_rss_mib=round(rss/(1024*1024), 3))
        dump(args.output, out)
        print(json.dumps({k:v for k,v in out.items() if k != 'witness'}), flush=True)


def invoke(case, K, budget, solver, tag='search', precheck=False):
    runtime = B / 'runtime'
    runtime.mkdir(exist_ok=True)
    ident = case['id'][:16]
    stem = f'{tag}-{ident}-K{K}-{solver}'
    inp, out, log = (runtime / (stem + ext) for ext in ('.input.json', '.output.json', '.log'))
    dump(inp, case)
    # A fresh tag / shape / K is required: never pass a stale successful file as a retry.
    if out.exists():
        raise RuntimeError(f'refusing to overwrite {out}')
    # The original runs used a local wrapper capping memory (1600 MB) and time (budget s); exit codes 124/137
    # meant timeout/memory kill. Set SEARCH_CAP to an equivalent command prefix (empty: no cap).
    command = ['nice', '-n', '15', *os.environ.get('SEARCH_CAP', '').split(),
               sys.executable, str(Path(__file__).resolve()), 'one', '--case', str(inp), '--K', str(K),
               '--output', str(out), '--solver', solver]
    if precheck:
        command.append('--precheck')
    t0, started = time.monotonic(), utc()
    with log.open('w') as f:
        result = subprocess.run(command, stdout=f, stderr=subprocess.STDOUT,
                                env=dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1',
                                         VECLIB_MAXIMUM_THREADS='1', NUMEXPR_NUM_THREADS='1'))
    record = json.loads(out.read_text()) if out.exists() else dict(id=case['id'], K=K, status='no_output')
    record.update(tag=tag, solver=solver, cells=case['cells'], families=case['families'],
                  command=command, supervisor_started_utc=started, supervisor_ended_utc=utc(),
                  wall_s=round(time.monotonic()-t0, 3), returncode=result.returncode)
    if result.returncode:
        record['last_worker_status'] = record['status']
        record['status'] = {124:'timeout', 137:'memory_kill'}.get(result.returncode, 'process_error')
        record['log_tail'] = log.read_text()[-1600:]
        record.pop('witness', None)
    return record


def controls(args):
    checks = []
    for s in seeds():
        assert is_disc(set(map(tuple, s['shape'])), F)[0]
        for w in s['witnesses']:
            assert check_witness(s['shape'], w, F) is None
        assert period_one(s['shape']) is None
        checks.append(dict(kind='existing_witness_and_not_one_copy_tiler', file=s['file'], index=s['index'], result='PASS'))
    for shape in ([(0,0)], [(0,0),(1,0)], [(0,0),(1,0),(0,1)], [(x,y) for x in range(5) for y in range(4)]):
        p = period_one(shape)
        assert p and check_period(shape, p)
        bad = dict(p, a=p['a']+1)
        assert not check_period(shape, bad)
        checks.append(dict(kind='known_translational_tiler', cells=len(shape), lattice=p, result='PASS'))
    dump(B / 'controls-static.json', dict(utc=utc(), checks=checks))
    # Smallest known Hh=3 shape: positive K3 and negative K4, no new-value claim.
    s = min(seeds(), key=lambda s: len(s['shape']))
    case = dict(id=identity(s['shape']), shape=s['shape'], cells=len(s['shape']), families=['control_known_H3'])
    rows = []
    for K in (3,4):
        r = invoke(case, K, 180, args.solver, args.tag)
        w = r.pop('witness', None)
        if w:
            dump(B / f'control-K{K}-witness.json', dict(shape=s['shape'], witness=w))
        rows.append(r)
        dump(B / 'controls-solver.json', rows)
        print(json.dumps(r), flush=True)
    assert [r['status'] for r in rows] == ['SAT', 'UNSAT'], 'control not resolved as expected'


def search(args):
    started = time.monotonic()
    started_utc = utc()
    cases = [json.loads(l) for l in (B/'candidates.jsonl').read_text().splitlines()]
    attempts_path = B / (args.tag + '-attempts.jsonl')
    done = set()
    if attempts_path.exists():
        for l in attempts_path.read_text().splitlines():
            r = json.loads(l)
            done.add(r['id'])
    for previous in args.skip_attempts:
        for l in Path(previous).read_text().splitlines():
            done.add(json.loads(l)['id'])
    cases = [r for r in cases if r['id'] not in done]
    if args.limit:
        cases = cases[:args.limit]
    statuses = Counter()
    finished = 0
    def work(case):
        if case['period_one']:
            return dict(id=case['id'], cells=case['cells'], families=case['families'], status='one_copy_tiler',
                        lattice=case['period_one'], wall_s=0, K=None, tag=args.tag)
        return invoke(case, 3, args.budget, args.solver, args.tag, args.precheck)
    # Keep at most jobs live; do not queue the full population beyond the wall budget.
    with attempts_path.open('a', buffering=1) as f, ThreadPoolExecutor(max_workers=args.jobs) as pool:
        queue = iter(cases)
        pending = {}
        def schedule():
            if time.monotonic()-started >= args.seconds or (B/'STOP').exists():
                return False
            c = next(queue, None)
            if c is None:
                return False
            pending[pool.submit(work,c)] = c
            return True
        for _ in range(args.jobs):
            schedule()
        while pending:
            fut = next(as_completed(pending))
            case = pending.pop(fut)
            r = fut.result()
            w = r.pop('witness', None)
            if w:
                with (B/'witnesses.jsonl').open('a') as wf:
                    wf.write(json.dumps(dict(id=case['id'], shape=case['shape'], witness=w, solver=args.solver))+'\n')
            f.write(json.dumps(r, separators=(',',':'))+'\n')
            statuses[r['status']] += 1
            finished += 1
            if r['status'] == 'SAT':
                tiling = period_two(case['shape'])
                tiling_search = None
                if tiling is None:
                    tiling_search = period_many(case['shape'])
                    tiling = tiling_search.get('certificate')
                if tiling:
                    f.write(json.dumps(dict(id=case['id'], cells=case['cells'], families=case['families'],
                         status='periodic_tiler', lattice=tiling, periodic_search=tiling_search,
                         K=None, tag=args.tag),separators=(',',':'))+'\n')
                    print('periodic '+case['id'][:16],flush=True)
                    schedule()
                    continue
                # Escalations are serialized within each worker; never >jobs solver children.
                r4 = invoke(case, 4, 180, args.solver, args.tag+'-escalate')
                r4['periodic_search'] = tiling_search
                w4 = r4.pop('witness', None)
                if w4:
                    with (B/'witnesses.jsonl').open('a') as wf:
                        wf.write(json.dumps(dict(id=case['id'], shape=case['shape'], witness=w4, solver=args.solver))+'\n')
                f.write(json.dumps(r4,separators=(',',':'))+'\n')
                print('K4 '+json.dumps({k:v for k,v in r4.items() if k != 'command'}),flush=True)
                if r4['status'] == 'SAT':
                    # Pause population work for a deliberate K5 proof; no automatic claim.
                    dump(B/'K4-candidate.json', case)
                    (B/'STOP').write_text('K4 witness found: prepare serialized K5 certification\n')
            if finished % 10 == 0 or r['status'] in ('SAT','memory_kill','error','process_error'):
                print(json.dumps(dict(utc=utc(), finished=finished, status=dict(statuses), elapsed_s=round(time.monotonic()-started,1))), flush=True)
            schedule()
    dump(B/(args.tag+'-run.json'),dict(started_utc=started_utc, ended_utc=utc(), seconds=round(time.monotonic()-started,3),
         configured_seconds=args.seconds, configured_jobs=args.jobs, budget_per_K3=args.budget, finished=finished,
         precheck_K1=args.precheck,
         statuses=dict(statuses), solver=args.solver, stop_file=(B/'STOP').exists(),
         attempts_sha256=sha(attempts_path), source_code_sha256={n:sha(src_path(n)) for n in SOURCE_NAMES}, driver_sha256=sha(__file__)))


def main():
    p=argparse.ArgumentParser()
    sp=p.add_subparsers(dest='action', required=True)
    g=sp.add_parser('generate'); g.add_argument('--inputs', required=True)
    o=sp.add_parser('one'); o.add_argument('--case', required=True); o.add_argument('--K', type=int, required=True)
    o.add_argument('--output', required=True); o.add_argument('--solver',default='cadical153')
    o.add_argument('--precheck',action='store_true')
    c=sp.add_parser('controls'); c.add_argument('--solver',default='cadical153'); c.add_argument('--tag',default='control-v2')
    s=sp.add_parser('search'); s.add_argument('--jobs',type=int,default=1); s.add_argument('--budget',type=int,default=90)
    s.add_argument('--seconds',type=int,default=600); s.add_argument('--limit',type=int,default=0)
    s.add_argument('--tag',default='pilot'); s.add_argument('--solver',default='cadical153')
    s.add_argument('--skip-attempts',nargs='*',default=[])
    s.add_argument('--precheck',action='store_true')
    args=p.parse_args()
    assert getattr(args,'jobs',1) in (1,2)
    {'generate':generate, 'one':one, 'controls':controls, 'search':search}[args.action](args)


if __name__ == '__main__':
    main()
