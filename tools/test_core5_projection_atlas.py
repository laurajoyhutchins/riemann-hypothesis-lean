"""Hermetic tests for the Core5 source-projection candidate miner."""
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from core5_projection_atlas import collect, rank


class Core5ProjectionTests(unittest.TestCase):
    def test_projection_family_and_distinct_conclusion(self):
        with TemporaryDirectory() as d:
            src = Path(d)
            root = src / "Development" / "AbelianVarietyTheory" / "Proofs"
            root.mkdir(parents=True)
            (root / "Core.lean").write_text(
                "theorem first : ∀ (R F : Nat), GlobalTheory.Hk3.Core R F → "
                "R = F := by\n  omega\n\n"
                "theorem mismatch : ∀ (R F : Nat), GlobalTheory.Hk3.Core R F → "
                "R < F := by\n  omega\n", encoding="utf-8"
            )
            (root / "Five.lean").write_text(
                "theorem second : ∀ (R F : Nat), GlobalTheory.Core5 R F → "
                "R = F := by\n  omega\n", encoding="utf-8"
            )
            records, stats = collect(src)
            result = rank(records)
            self.assertEqual(stats["scanned_modules"], 2)
            self.assertEqual(result["families_before_output_limit"], 1)
            self.assertEqual(result["families"][0]["members"], 2)
            self.assertEqual(set(result["families"][0]["tiers"]), {"core", "core5"})

    def test_char_projection_and_refuse_same_tier(self):
        with TemporaryDirectory() as d:
            src = Path(d)
            root = src / "Development" / "AbelianVarietyTheory" / "Proofs"
            root.mkdir(parents=True)
            (root / "Char.lean").write_text(
                "theorem first : ∀ (R F : Nat), R.Char F → R = F := by\n  omega\n",
                encoding="utf-8"
            )
            (root / "Five.lean").write_text(
                "theorem second : ∀ (R F : Nat), GlobalTheory.Core5 R F → "
                "R = F := by\n  omega\n",
                encoding="utf-8"
            )
            records, _ = collect(src)
            self.assertEqual(rank(records)["families_before_output_limit"], 1)
            (root / "Five.lean").write_text(
                "theorem second : ∀ (R F : Nat), R.Char F → R = F := by\n  omega\n",
                encoding="utf-8"
            )
            records, _ = collect(src)
            self.assertEqual(rank(records)["families_before_output_limit"], 0)

    def test_missing_root_fails_closed(self):
        with TemporaryDirectory() as d:
            with self.assertRaises(ValueError):
                collect(Path(d))


if __name__ == "__main__":
    unittest.main()
