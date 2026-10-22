"""Regenerate upper-bound CNFs, re-solve them with the recorded solver and check the proofs.

Usage:
  python3 -B recheck_certificates.py --sample [--output FILE]       # ci/certificate-sample.json (CI)
  python3 -B recheck_certificates.py --all [--min-free-gb 10]       # all 5,019 (hours)
  python3 -B recheck_certificates.py --name hex_15hex_3up_0315_0    # one certificate
  python3 -B recheck_certificates.py --cnf-only --all               # only regenerate CNFs and compare SHA-256
  python3 -B recheck_certificates.py --search-samples               # the two sampled screening proofs of the search

For each certificate the CNF is regenerated with generator/ (deterministic) and must have the
recorded SHA-256 and size. Unless --cnf-only, the recorded solver (python-sat, with the recorded
options) solves it again with proof output; the result must be UNSAT and drat-trim must print
"s VERIFIED". The proof's SHA-256 is compared with the recorded one for information only (a
different python-sat build may write a different but equally valid proof). Files are written to
a temporary directory (--workdir) and deleted after each certificate.
Needs: python-sat==1.9.dev17 (requirements.txt) and drat-trim (tools/build_drat_trim.sh, or set
DRAT_TRIM). Memory: most certificates need well under 1 GB; the largest about 3 GB.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "generator"))


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def certificates():
    for p in sorted((ROOT / "certificates").glob("*/*.jsonl")):
        for line in p.read_text().splitlines():
            yield json.loads(line)


def drat_trim(cnf, proof, timeout):
    exe = os.environ.get("DRAT_TRIM", str(ROOT / "tools/drat-trim/drat-trim"))
    t0 = time.time()
    p = subprocess.run([exe, cnf, proof, "-t", str(timeout)], capture_output=True, text=True, timeout=timeout + 60)
    status = [l.strip() for l in p.stdout.splitlines() if l.startswith("s ")]
    return dict(result=status[-1] if status else None, returncode=p.returncode, wall_s=round(time.time() - t0, 2))


def recheck(c, family, workdir, cnf_only, timeout):
    from grids import GRIDS
    from heesch import Run
    cnf = os.path.join(workdir, "x.cnf")
    proof = None if cnf_only else os.path.join(workdir, "x.proof")
    t0 = time.time()
    r = Run(GRIDS[family](), [tuple(x) for x in c["shape"]], c["K"], "relaxed", cnf, proof, blocks=c["blocks"],
            opts=c.get("solver_options") or None, solver=c.get("solver", "cadical153"))
    out = dict(name=c.get("name") or c.get("id"), K=c["K"], mode=c["mode"], solver=r.solver)
    if proof:
        sat, _ = r.solve()
        out["solve"] = "SAT" if sat else "UNSAT"
    r.finish()
    out["cnf_sha256_match"] = sha(cnf) == c["cnf"]["sha256"] and os.path.getsize(cnf) == c["cnf"]["bytes"]
    if proof:
        out["proof_bytes"] = os.path.getsize(proof)
        out["proof_sha256_equal_to_record"] = sha(proof) == c["proof"]["sha256"]
        out["drat_trim"] = drat_trim(cnf, proof, timeout) if out["solve"] == "UNSAT" else None
    for p in (cnf, proof):
        if p and os.path.exists(p):
            os.remove(p)
    out["seconds"] = round(time.time() - t0, 2)
    ok = out["cnf_sha256_match"] and (cnf_only or (out["solve"] == "UNSAT" and out["drat_trim"]["result"] == "s VERIFIED"))
    out["status"] = "PASS" if ok else "FAIL"
    return out


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--sample", action="store_true")
    g.add_argument("--all", action="store_true")
    g.add_argument("--name", action="append")
    g.add_argument("--search-samples", action="store_true")
    ap.add_argument("--cnf-only", action="store_true")
    ap.add_argument("--workdir")
    ap.add_argument("--output", type=Path)
    ap.add_argument("--timeout", type=int, default=3600, help="drat-trim time limit per proof (s)")
    ap.add_argument("--min-free-gb", type=float, default=10.0)
    a = ap.parse_args()
    if a.search_samples:
        rows = [(r, "omino") for r in json.loads((ROOT / "search/sample-certificates.json").read_text())["rows"]]
    else:
        allc = {c["name"]: c for c in certificates()}
        if a.all:
            names = sorted(allc, key=lambda n: allc[n]["cnf"]["bytes"] + allc[n]["proof"]["bytes"])
        elif a.sample:
            names = json.loads((ROOT / "ci/certificate-sample.json").read_text())["names"]
        else:
            names = a.name
        rows = [(allc[n], allc[n]["family"]) for n in names]
    workdir = a.workdir or tempfile.mkdtemp(prefix="heesch-recheck-")
    os.makedirs(workdir, exist_ok=True)
    t0 = time.time()
    results = []
    try:
        for i, (c, fam) in enumerate(rows, 1):
            free = shutil.disk_usage(workdir).free / 1e9
            need = (c["cnf"]["bytes"] + (0 if a.cnf_only else 2 * c["proof"]["bytes"])) / 1e9 + 1
            assert free > max(need, a.min_free_gb if a.all else 1), f"not enough free disk in {workdir}: {free:.1f} GB"
            r = recheck(c, fam, workdir, a.cnf_only, a.timeout)
            results.append(r)
            print(json.dumps(r), flush=True)
    finally:
        if not a.workdir:
            shutil.rmtree(workdir, ignore_errors=True)
    summary = dict(status="PASS" if results and all(r["status"] == "PASS" for r in results) else "FAIL",
                   certificates=len(results), cnf_only=a.cnf_only,
                   proof_hash_equal_to_record=sum(1 for r in results if r.get("proof_sha256_equal_to_record")),
                   seconds=round(time.time() - t0, 1))
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(dict(summary=summary, results=results), indent=1) + "\n")
    print(json.dumps(summary))
    sys.exit(0 if summary["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
