#!/usr/bin/env python3
"""Fail-closed source-level preflight for the upstream RH #221 integration.

This intentionally does not check Lean proof terms or assert elaborated theorem
equivalence. Those require a clean comparator/kernel build.
"""
import json
from pathlib import Path
import re
import subprocess
import sys
import unittest

EXPECTED_SRC_TREE = "84e5e9889142f86f47b3156b54009f65fc274f82"
BLOBS = {
    "lakefile.toml": "791d9017ddf8a775698ad9c05254aa97d42f6a10",
    "lake-manifest.json": "8a747b58a34565cc6cb5341b86544aa5d3a20a2d",
    "lean-toolchain": "0e037f58f9a1aa2d5139277bcc4be0061ebeeb05",
    "comparator.json": "e989bcf90ff0c487a7146319a026e661a5bad47c",
    "export-targets.txt": "e2d4c02bac8a1411eae85af0376c1aad3b6b5294",
    "src/Main.lean": "67c65badc15f80a1db65df1c84dc7a4928fc410f",
    "src/Statements.lean": "23b01f745b80075e377c415abae96ece3570d0b0",
    "src/Challenge.lean": "9677ace64b3a5e8b1a571d82d52ee13c53b08026",
}
FINAL_TYPES = {
    "riemannHypothesis": "RiemannHypothesis",
    "riemannZeta_eq_zero_re": "RiemannZetaZerosOnLine",
    "LFunction_ne_zero_of_half_lt_re": "DirichletLNonvanishingRightOfHalf",
    "LFunction_eq_zero_re": "DirichletLZerosOnLine",
    "LFunction_eq_zero_re_of_isPrimitive": "PrimitiveDirichletLZerosOnLine",
}
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
THEOREM_DECLARATION = re.compile(
    r"(?m)^theorem\s+([A-Za-z0-9_]+)\s*:\s*([A-Za-z0-9_.]+)\s*:="
)


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=root, text=True, stderr=subprocess.PIPE
    ).strip()


def inspect(root: Path) -> dict:
    errors = []
    observed_tree = git(root, "rev-parse", "HEAD:src")
    if observed_tree != EXPECTED_SRC_TREE:
        errors.append(f"src tree mismatch {observed_tree} != {EXPECTED_SRC_TREE}")
    for path, expected_sha in BLOBS.items():
        observed = git(root, "hash-object", path)
        if observed != expected_sha:
            errors.append(f"{path}: blob {observed} != pinned {expected_sha}")
    config = json.loads((root / "comparator.json").read_text())
    actual_names = config["theorem_names"]
    if actual_names != list(FINAL_TYPES):
        errors.append(f"Comparator roots mismatch: {actual_names}")
    if set(config["permitted_axioms"]) != ALLOWED_AXIOMS or len(config["permitted_axioms"]) != len(ALLOWED_AXIOMS):
        errors.append("Comparator axiom whitelist differs from pinned three")
    if config.get("solution_module") != "Main" or config.get("challenge_module") != "Challenge":
        errors.append("Comparator challenge or solution module mismatch")
    if set(config.get("external_kernels", {})) != {"Lean paranoid", "nanoda"}:
        errors.append("Missing or extra independent kernel configuration")
    exports = (root / "export-targets.txt").read_text().split()
    for name in FINAL_TYPES:
        if exports.count(name) != 1:
            errors.append(f"Export roots: {name} appears {exports.count(name)} times")
    for name in ALLOWED_AXIOMS:
        if exports.count(name) != 1:
            errors.append(f"Export axiom: {name} appears {exports.count(name)} times")
    for file in ("src/Main.lean", "src/Challenge.lean"):
        declarations = dict(THEOREM_DECLARATION.findall((root / file).read_text()))
        for theorem, typename in FINAL_TYPES.items():
            if declarations.get(theorem) != typename:
                errors.append(f"{file} missing {theorem} : {typename}")
    return {
        "status": "passed" if not errors else "failed",
        "source_tree": observed_tree,
        "source_blobs_checked": len(BLOBS),
        "final_theorem_declarations": list(FINAL_TYPES),
        "permitted_axioms": sorted(ALLOWED_AXIOMS),
        "checks": ["source tree", "build inputs", "comparator and external-kernel configuration",
                   "export roots", "five source declaration signatures"],
        "errors": errors,
        "not_verified": ["elaborated theorem type equivalence",
                         "Lean kernel proof checking", "axiom closure",
                         "independent external kernel replay", "clean build",
                         "proof dependency graph"],
    }


class PreflightUnitTests(unittest.TestCase):
    def test_theorem_parser(self):
        sample = "module\n\ntheorem a : P := by\n  trivial\n" \
                 "theorem b : Q := by\n  trivial\n"
        self.assertEqual(dict(THEOREM_DECLARATION.findall(sample)), {"a": "P", "b": "Q"})

    def test_whitelist_is_three_trusted_axioms(self):
        self.assertEqual(ALLOWED_AXIOMS, {"propext", "Quot.sound", "Classical.choice"})

    def test_five_distinct_theorems(self):
        self.assertEqual(len(FINAL_TYPES), len(set(FINAL_TYPES.values())))


if __name__ == "__main__":
    if "--test" in sys.argv:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(PreflightUnitTests)
        raise SystemExit(0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1)
    root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(".").resolve()
    evidence = inspect(root)
    print(json.dumps(evidence, indent=2, sort_keys=True))
    raise SystemExit(0 if not evidence["errors"] else 1)
