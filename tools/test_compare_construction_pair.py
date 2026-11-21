import tempfile
import unittest
from pathlib import Path

from compare_construction_pair import compare, read_decl


class PairEvidenceTests(unittest.TestCase):
    def test_identical_proof_not_equivalent_statement(self):
        with tempfile.TemporaryDirectory() as td:
            a, b = Path(td) / "A.lean", Path(td) / "B.lean"
            a.write_text("theorem shared : True := by\n  trivial\n")
            b.write_text("import A\n\ntheorem shared : 1 = 1 := by\n  trivial\n")
            left, right = read_decl(a, "shared"), read_decl(b, "shared")
            evidence = compare(left, right)
            self.assertTrue(evidence["proof_text_identical"])
            self.assertFalse(evidence["statements_text_identical"])
            self.assertIn("A", evidence["right_direct_imports"])
            self.assertIn("no theorem equivalence", evidence["classification"])

    def test_missing_or_ambiguous_decl_refused(self):
        with tempfile.TemporaryDirectory() as td:
            f = Path(td) / "A.lean"
            f.write_text("theorem shared : True := by\n  trivial\n"
                         "theorem shared : True := by\n  trivial\n")
            with self.assertRaisesRegex(ValueError, "expected exactly one"):
                read_decl(f, "shared")
            with self.assertRaisesRegex(ValueError, "expected exactly one"):
                read_decl(f, "missing")


if __name__ == "__main__":
    unittest.main()
