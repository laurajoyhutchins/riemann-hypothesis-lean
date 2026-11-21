"""Structural profiler fixtures; full 175k-module scans run only on demand."""
import tempfile
import unittest
from pathlib import Path

from structural_profile import audit


class StructuralProfileTests(unittest.TestCase):
    def test_counts_paired_statements_without_certifying_redundancy(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = Path(tmp)
            (src / "Theorem.lean").write_text("theorem a : True := trivial\n")
            (src / "TheoremStatement.lean").write_text(
                "import Theorem\ntheorem b : True := by\n  first | exact _root_.a\n"
            )
            (src / "Empty.lean").write_text("namespace N\nend N\n")
            report = audit(src)
            self.assertEqual(report["files"], 3)
            self.assertEqual(report["overall"]["physical"], 6)
            self.assertEqual(report["paired_statement_counts"]["all"], 1)
            self.assertEqual(report["paired_statement_counts"]["single_theorem_forward"], 1)
            self.assertEqual(report["no_decl"]["no_declaration_files"], 1)
            self.assertIn("not verified semantics", report["important_limit"])

    def test_counts_empty_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            report = audit(Path(tmp))
            self.assertEqual(report["files"], 0)


if __name__ == "__main__":
    unittest.main()
