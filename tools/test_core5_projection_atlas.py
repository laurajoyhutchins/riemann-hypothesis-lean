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

    def test_core_no_chain_is_separate_unverified_bridge(self):
        with TemporaryDirectory() as d:
            src = Path(d)
            root = src / "Development" / "AbelianVarietyTheory" / "Proofs"
            root.mkdir(parents=True)
            (root / "Chain.lean").write_text(
                "theorem chain : ∀ (R F : Nat), GlobalTheory.Hk3.CoreNoChain R F → "
                "R = F := by\n  trivial\n",
                encoding="utf-8"
            )
            (root / "Five.lean").write_text(
                "theorem five : ∀ (R F : Nat), GlobalTheory.Core5 R F → "
                "R = F := by\n  trivial\n",
                encoding="utf-8"
            )
            candidates, _ = collect(src)
            result = rank(candidates)
            self.assertEqual(result["families_before_output_limit"], 1)
            family = result["families"][0]
            self.assertEqual(set(family["tiers"]), {"core_no_chain", "core5"})
            self.assertTrue(family["needs_unverified_bridge"])
            self.assertIn("CoreNoChain to Core5", family["bridge_obligation"])
            # No Core5 theorem means there is no established donor to reuse.
            (root / "Five.lean").unlink()
            records, _ = collect(src)
            self.assertEqual(rank(records)["families_before_output_limit"], 0)

    def test_missing_root_fails_closed(self):
        with TemporaryDirectory() as d:
            with self.assertRaises(ValueError):
                collect(Path(d))


if __name__ == "__main__":
    unittest.main()
