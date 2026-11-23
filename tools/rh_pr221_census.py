#!/usr/bin/env python3
"""Deterministic, source-only RH Lean census. This does NOT verify proofs.

Count newline-terminated physical lines, matching 'wc -l'. Count files and
bytes among tracked src/**/*.lean files (not generated artifacts or archives).
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT_GUARDS = ("src/Main.lean", "src/Statements.lean")


def census(root: Path):
    raw = subprocess.check_output(["git", "ls-files", "-z", "--", "src"], cwd=root)
    paths = sorted(os.fsdecode(x) for x in raw.split(b"\0") if x and x.endswith(b".lean"))
    lines = byte_count = missing_final_newline = 0
    root_sha = {}
    for relative in paths:
        data = (root / relative).read_bytes()
        byte_count += len(data)
        lines += data.count(b"\n")
        missing_final_newline += int(bool(data) and not data.endswith(b"\n"))
        if relative in ROOT_GUARDS:
            root_sha[relative] = hashlib.sha256(data).hexdigest()
    return {
        "counting_rule": "tracked src/**/*.lean files; wc -l newline count; byte lengths",
        "lean_files": len(paths),
        "lean_lines": lines,
        "lean_source_bytes": byte_count,
        "files_missing_trailing_newline": missing_final_newline,
        "entrypoint_sha256": root_sha,
    }


def compare(before, after):
    return {
        "before": before,
        "after": after,
        "difference": {k: after[k] - before[k]
                       for k in ("lean_files", "lean_lines", "lean_source_bytes",
                                 "files_missing_trailing_newline")},
        "entrypoints_unchanged": all(
            before["entrypoint_sha256"].get(k) == after["entrypoint_sha256"].get(k)
            for k in ROOT_GUARDS),
        "warning": ("Source equality is not elaborated type equality; "
                    "a Lean kernel rebuild and axiom audit are separate obligations."),
    }


class CensusTests(unittest.TestCase):
    def test_wc_count_and_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "src").mkdir()
            f = root / "src" / "Main.lean"
            f.write_bytes(b"theorem x : True := by trivial\n")
            (root / "src" / "Statements.lean").write_bytes(b"theorem y : True := by trivial")
            subprocess.run(["git", "add", "src"], cwd=root, check=True)
            old = census(root)
            self.assertEqual((old["lean_files"], old["lean_lines"],
                              old["files_missing_trailing_newline"]), (2, 1, 1))
            f.write_bytes(b"theorem x : True := by trivial\n\n")
            new = census(root)
            self.assertEqual(compare(old, new)["difference"]["lean_lines"], 1)
            self.assertFalse(compare(old, new)["entrypoints_unchanged"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path("."))
    ap.add_argument("--output", type=Path)
    ap.add_argument("--before", type=Path, help="Compare with previous JSON census")
    ap.add_argument("--test", action="store_true")
    args = ap.parse_args()
    if args.test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(CensusTests)
        raise SystemExit(not unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful())
    current = census(args.root)
    result = compare(json.loads(args.before.read_text()), current) if args.before else current
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
