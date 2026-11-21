"""Hermetic regression tests for source-line accounting only; not a Lean proof test."""
import tempfile
import unittest
from pathlib import Path

from enrich_census import physical_lines, audit


class CensusLineTests(unittest.TestCase):
    def test_physical_lines(self):
        for data, want in [(b"", 0), (b"a", 1), (b"a\n", 1),
                           (b"a\nb", 2), (b"a\n\n", 2)]:
            self.assertEqual(physical_lines(data), want)

    def test_upper_bound_is_not_a_verified_saving(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "src"
            (source / "Development").mkdir(parents=True)
            (source / "Main.lean").write_text("theorem t : True := trivial\n")
            (source / "Development/Dead.lean").write_text(
                "theorem dead : True := trivial\n"
            )
            tsv = root / "declarations.tsv"
            tsv.write_text(
                "module\ttotal\texpression_reachable\tblock_reachable\tblock_unreachable\n"
                "Main\t1\t1\t1\t0\n"
                "Development.Dead\t1\t0\t0\t1\n"
            )
            report = audit(source, tsv, root / "out")
            self.assertEqual(report["physical_source_lines"], 2)
            self.assertEqual(report["block_unreachable"], 1)
            self.assertEqual(report["candidate_whole_module_lines_upper_bound"], 1)
            self.assertEqual(report["verified_prunable_lines"], 0)

    def test_invalid_census_fails_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "src"
            source.mkdir()
            (source / "Main.lean").write_text("theorem t : True := trivial\n")
            tsv = root / "declarations.tsv"
            tsv.write_text(
                "module\ttotal\texpression_reachable\tblock_reachable\tblock_unreachable\n"
                "Main\t1\t1\t0\t1\n"
            )
            with self.assertRaises(ValueError):
                audit(source, tsv, root / "out")


if __name__ == "__main__":
    unittest.main()
