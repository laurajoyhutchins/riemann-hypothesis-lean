"""Synthetic, fail-closed tests for premise anti-unification (not Lean proofs)."""
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from premise_antiunification import extract, top_level_positions, census, rank


class ImplicationTemplateTests(unittest.TestCase):
    def test_same_conclusion_different_premises(self):
        with TemporaryDirectory() as temp:
            base = Path(temp) / "src"
            root = base / "Development/AbelianVarietyTheory/Proofs"
            root.mkdir(parents=True)
            (root / "A.lean").write_text(
                "theorem h1 : ∀ (x : Nat), P x → x = x := by\n"
                "  rfl\n",
                encoding="utf-8"
            )
            (root / "B.lean").write_text(
                "theorem h2 : ∀ (x : Nat), Q x → x = x := by\n"
                "  rfl\n",
                encoding="utf-8"
            )
            groups, stats = census(base)
            self.assertEqual(stats["qualified_implication_headers"], 2)
            out = rank(groups, min_proof=1)
            self.assertEqual(out["qualifying_families_before_limit"], 1)
            family = out["families"][0]
            self.assertEqual(family["distinct_premises"], 2)
            self.assertEqual(family["premises"], ["P x", "Q x"])

    def test_no_compression_without_distinct_hypotheses(self):
        with TemporaryDirectory() as temp:
            base = Path(temp) / "src"
            root = base / "Development/AbelianVarietyTheory/Proofs"
            root.mkdir(parents=True)
            for name in ["A", "B"]:
                (root / (name + ".lean")).write_text(
                    "theorem t : ∀ (x : Nat), P x → x = x := by\n  rfl\n",
                    encoding="utf-8"
                )
            groups, _ = census(base)
            self.assertEqual(rank(groups, min_proof=1)["qualifying_families_before_limit"], 0)

    def test_no_conflation_when_conclusion_differs(self):
        left = "theorem a : ∀ (x : Nat), P x → x = x"
        right = "theorem b : ∀ (x : Nat), Q x → x < x"
        self.assertNotEqual(extract(left)[2], extract(right)[2])

    def test_parenthesized_implication_not_mistaken_for_outer_arrow(self):
        t = "theorem x : ∀ (n : Nat), (P n → Q n) → R n"
        self.assertEqual(extract(t), ("∀ (n : Nat),", "(P n → Q n)", "R n"))

    def test_malformed_scope_rejected(self):
        self.assertIsNone(top_level_positions("∀ (x : Nat], P x → Q x"))
        self.assertIsNone(extract("theorem x : ∀ (x : Nat], P x → Q x"))
        self.assertIsNone(extract("theorem x : P x → Q x"))

    def test_source_root_must_exist(self):
        with TemporaryDirectory() as temp:
            with self.assertRaises(ValueError):
                census(Path(temp))


if __name__ == "__main__":
    unittest.main()
