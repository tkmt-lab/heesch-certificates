"""Synthetic checker failure controls, not checks of mathematical proof validity.

Run from the packet root: python3 -B ci/test_recheck_certificates.py
Needs the pinned python-sat dependency; no drat-trim build or network is needed.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import recheck_certificates as checker

NAME = "omino_10omino_0up_0000_0"


class CheckerFailureControls(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="heesch-checker-test-")
        self.addCleanup(self.directory.cleanup)
        self.work = Path(self.directory.name)
        self.exe = self.work / "checker"

    def fake_checker(self, body):
        self.exe.write_text("#!/bin/sh\n" + body + "\n")
        self.exe.chmod(0o755)
        return dict(os.environ, DRAT_TRIM=str(self.exe))

    def run_cli(self, body, expected_status, expected_code, expected_result, checker_code):
        env = self.fake_checker(body)
        output = self.work / "result.json"
        proc = subprocess.run(
            [sys.executable, "-B", "recheck_certificates.py", "--name", NAME,
             "--output", str(output)],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(proc.returncode, expected_code, proc.stdout + proc.stderr)
        rows = [json.loads(line) for line in proc.stdout.splitlines()]
        self.assertEqual(len(rows), 2)
        result, summary = rows
        self.assertTrue(result["cnf_sha256_match"])
        self.assertEqual(result["solve"], "UNSAT")
        self.assertEqual(result["drat_trim"]["result"], expected_result)
        self.assertEqual(result["drat_trim"]["returncode"], checker_code)
        self.assertEqual(result["status"], expected_status)
        self.assertEqual(summary["status"], expected_status)
        self.assertEqual(json.loads(output.read_text()), dict(summary=summary, results=[result]))

    def test_verified_and_zero_exit(self):
        self.run_cli("echo 's VERIFIED'\nexit 0", "PASS", 0, "s VERIFIED", 0)

    def test_verified_and_nonzero_exit(self):
        self.run_cli("echo 's VERIFIED'\nexit 7", "FAIL", 1, "s VERIFIED", 7)

    def test_missing_success_line(self):
        self.run_cli("echo 'c finished'\nexit 0", "FAIL", 1, None, 0)

    def test_malformed_success_line(self):
        self.run_cli("echo 's VERIFIED extra'\nexit 0", "FAIL", 1, "s VERIFIED extra", 0)

    def test_later_failure_status(self):
        self.run_cli("echo 's VERIFIED'\necho 's NOT VERIFIED'\nexit 0",
                     "FAIL", 1, "s NOT VERIFIED", 0)

    def test_timeout_after_success_line(self):
        # Shorten only the watchdog in this test; keep the production subprocess
        # call and a real sleeping checker. Even an earlier success line must not
        # turn a timeout into PASS. subprocess.run kills and waits for this child.
        env = self.fake_checker("echo 's VERIFIED'\nexec sleep 5")
        record = next(c for c in checker.certificates() if c["name"] == NAME)
        real_run = subprocess.run

        def short_watchdog(*args, **kwargs):
            self.assertEqual(kwargs["timeout"], 61)
            kwargs["timeout"] = 0.1
            return real_run(*args, **kwargs)

        with patch.dict(os.environ, env), patch.object(checker.subprocess, "run", side_effect=short_watchdog):
            with self.assertRaises(subprocess.TimeoutExpired) as expired:
                checker.recheck(record, record["family"], str(self.work), False, 1)
        self.assertIn(b"s VERIFIED", expired.exception.output)


if __name__ == "__main__":
    unittest.main(verbosity=2)
