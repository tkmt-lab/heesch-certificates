"""The fast checks run by CI (the Lean checks are a separate CI job, see formal/README.md).

Usage: python3 -B ci_check.py [--output DIR] [--skip-certificates]

Steps (each must print status PASS):
  1. checkers/check_all_witnesses.py   both geometric checkers on all 6,574 witnesses
  2. check_counts.py                   the two counting implementations, recompared and checked geometrically
  3. check_search.py                   the restricted-search records
  4. figures/make_figure1.py --check   Figure 1 regenerated from the count records equals the article's
  5. recheck_certificates.py --sample  CNF regeneration (SHA-256), fresh solve and drat-trim on the CI sample
     recheck_certificates.py --search-samples   the two sampled screening proofs of the search
Needs python-sat (requirements.txt) and drat-trim (sh tools/build_drat_trim.sh, or DRAT_TRIM) for step 5.
"""
import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def run(name, args, out):
    t0 = time.time()
    cmd = [sys.executable, "-B", *args]
    if out:
        cmd += ["--output", str(out / f"{name}.json")]
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    last = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ""
    ok = p.returncode == 0 and '"status": "PASS"' in last
    print(json.dumps(dict(step=name, status="PASS" if ok else "FAIL", seconds=round(time.time() - t0, 1))), flush=True)
    if not ok:
        print(p.stdout[-4000:], p.stderr[-4000:], file=sys.stderr)
    return ok, round(time.time() - t0, 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path)
    ap.add_argument("--skip-certificates", action="store_true")
    a = ap.parse_args()
    if a.output:
        a.output.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    steps = [("witnesses", ["checkers/check_all_witnesses.py"]),
             ("counts", ["check_counts.py"]),
             ("search", ["check_search.py"])]
    if not a.skip_certificates:
        steps += [("certificates-sample", ["recheck_certificates.py", "--sample"]),
                  ("search-proof-samples", ["recheck_certificates.py", "--search-samples"])]
    results = {}
    for name, args in steps:
        results[name] = run(name, args, a.output)
    t1 = time.time()
    p = subprocess.run([sys.executable, "-B", "figures/make_figure1.py", "--check"], cwd=ROOT, capture_output=True, text=True)
    results["figure1"] = (p.returncode == 0 and '"PASS"' in p.stdout, round(time.time() - t1, 1))
    print(json.dumps(dict(step="figure1", status="PASS" if results["figure1"][0] else "FAIL")), flush=True)
    ok = all(v[0] for v in results.values())
    summary = dict(status="PASS" if ok else "FAIL", steps={k: dict(status="PASS" if v[0] else "FAIL", seconds=v[1])
                                                           for k, v in results.items()},
                   seconds=round(time.time() - t0, 1))
    if a.output:
        (a.output / "ci-summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps(summary))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
