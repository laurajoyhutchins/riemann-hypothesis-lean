"""Offline regression tests for the adapter to patrik-cihal/lean-graph."""
import hashlib
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from rh_lean_graph import RH_ROOTS, generate_driver, git_blob_sha, verify_extractor


class LeanGraphAdapterTests(unittest.TestCase):
    def test_git_blob_hash(self):
        data = b"hello\n"
        expected = hashlib.sha1(b"blob 6\0hello\n").hexdigest()
        self.assertEqual(git_blob_sha(data), expected)

    def test_pinned_source_rejects_substitution(self):
        with self.assertRaisesRegex(ValueError, "differs"):
            verify_extractor(b"import Lean\n")

    def test_five_roots_delegate_to_upstream_function(self):
        src = generate_driver("import Lean\n-- upstream functions here", RH_ROOTS, 2)
        self.assertIn("import Main\nimport Lean", src)
        self.assertEqual(src.count("#eval serializeAndWriteToFile"), 5)
        for root in RH_ROOTS:
            self.assertIn(f"(Source.Constant `(@{root})) 2", src)

    def test_select_root_and_depth_without_reimplementing_graph(self):
        src = generate_driver("import Lean", ("UpperTheory.FinalTheorems.everyCharacter",), 9)
        self.assertIn("UpperTheory.FinalTheorems.everyCharacter)) 9", src)
        self.assertNotIn("riemannHypothesis))", src)

    def test_reject_invalid_root_name_or_depth(self):
        for name in ("", "X); unsafe", "a b", "X..Y"):
            with self.assertRaises(ValueError):
                generate_driver("import Lean", (name,), 2)
        with self.assertRaises(ValueError):
            generate_driver("import Lean", RH_ROOTS, 0)
        with self.assertRaises(ValueError):
            generate_driver("import Lean", ("riemannHypothesis", "riemannHypothesis"), 2)


if __name__ == "__main__":
    unittest.main()
