import tempfile
import unittest
from pathlib import Path

from construction_atlas import scan, rank


class ConstructionAtlasTests(unittest.TestCase):
    def make_tree(self, td):
        base = Path(td) / "src" / "Development" / "AbelianVarietyTheory" / "Proofs"
        base.mkdir(parents=True)
        body = "\n".join(["  have h : True := by trivial"] * 14
                         + ["  exact GlobalTheory.HTPullEvery.exists_objMap"])
        for name, statement in (("One", "True"), ("Two", "Nat.zero = 0")):
            (base / (name + ".lean")).write_text(
                "import Mathlib\n"
                + "theorem " + name + " : " + statement + " := by\n" + body + "\n"
            )
        return Path(td) / "src"

    def test_cross_statement_identical_proofs_are_candidates_not_certificates(self):
        with tempfile.TemporaryDirectory() as td:
            records, census = scan(self.make_tree(td),
                                   "Development/AbelianVarietyTheory/Proofs", 10)
            self.assertEqual(len(records), 2)
            self.assertEqual(census["candidate_source_proofs"], 2)
            found = rank(records, max_groups=10, min_members=2)
            group = next(g for g in found["groups"]
                         if g["class"] == "identical_proof_text")
            self.assertEqual(group["distinct_statement_digests"], 2)
            self.assertEqual(group["modules"], 2)
            self.assertGreater(group["hypothetical_reusable_body_upper_bound"], 0)
            self.assertIn("No mathematical equivalence", group["caveat"])
            self.assertIn("cannot be added", found["integrity"])

    def test_short_proofs_do_not_extrapolate(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "src" / "Development" / "AbelianVarietyTheory" / "Proofs"
            root.mkdir(parents=True)
            (root / "Short.lean").write_text("theorem short : True := by\n  trivial\n")
            records, census = scan(Path(td) / "src",
                                   "Development/AbelianVarietyTheory/Proofs", 10)
            self.assertEqual(records, [])
            self.assertEqual(census["excluded_short_proof"], 1)

    def test_missing_source_fails_closed(self):
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaisesRegex(ValueError, "missing analysis subtree"):
                scan(Path(td), "not-an-existing-tree", 10)


if __name__ == "__main__":
    unittest.main()
