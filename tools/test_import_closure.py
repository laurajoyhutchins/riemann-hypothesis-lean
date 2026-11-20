"""Small deterministic import-closure fixtures, independent of the RH archive."""
import tempfile
import unittest
from pathlib import Path

from import_closure import compare, parse_imports, transitive_modules


class ImportGraphTests(unittest.TestCase):
    def test_parse_import_forms_and_reject_unknown(self):
        deps, warnings = parse_imports(
            b"import Statements\npublic import all Formalism.A\n"
            b"private import Development.X -- comment\n", "test.lean"
        )
        self.assertEqual(deps, ["Statements", "Formalism.A", "Development.X"])
        self.assertEqual(warnings, [])
        _, bad = parse_imports(b"import ?invalid\n", "test.lean")
        self.assertTrue(bad)

    def test_direct_import_exposes_only_unused_branch(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            src = root / "src"
            (src / "Supplements/Kernels").mkdir(parents=True)
            (src / "Development").mkdir()
            source = {
                "Main.lean": "import Statements\nimport Supplements.Kernels.Direct\n",
                "Statements.lean": "import Mathlib\n",
                "Supplements/Kernels/Direct.lean": "import Development.Used\n",
                "Supplements/Kernels/All.lean": "import Supplements.Kernels.Direct\nimport Development.Unused\n",
                "Development/Used.lean": "theorem used : True := trivial\n",
                "Development/Unused.lean": "theorem unused : True := trivial\n",
                "Supplement.lean": "theorem separate : True := trivial\n",
            }
            for p, text in source.items():
                (src / p).write_text(text)
            # Change the required MainTheorems naming to match the real tool's guard.
            (src / "Supplements/Kernels/MainTheorems.lean").write_text("import Development.Used\n")
            (src / "Main.lean").write_text(
                "import Statements\nimport Supplements.Kernels.MainTheorems\n"
            )
            (src / "Supplements/Kernels/MainTheoremsAll.lean").write_text(
                "import Supplements.Kernels.MainTheorems\nimport Development.Unused\n"
            )
            report = compare(
                src, root / "analysis",
                ["Statements", "Supplements.Kernels.MainTheoremsAll"]
            )
            self.assertEqual(report["candidate_removed_import_modules"], 2)
            self.assertEqual(report["candidate_removed_import_lines"], 3)
            self.assertEqual(report["verified_removed_source_lines"], 0)
            self.assertEqual(report["newly_reachable_modules"], 0)
            self.assertTrue((root / "analysis/rh-import-pruning-candidates.tsv").exists())

    def test_cycle(self):
        self.assertEqual(transitive_modules({"A": ["B"], "B": ["A"]}, "A"), {"A", "B"})

    def test_missing_original_import_is_not_silently_accepted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "src"
            (root / "Supplements/Kernels").mkdir(parents=True)
            (root / "Main.lean").write_text("import Supplements.Kernels.MainTheorems\n")
            (root / "Supplements/Kernels/MainTheorems.lean").write_text("")
            with self.assertRaises(ValueError):
                compare(root, Path(tmp) / "out", ["Missing"], require_original_all=True)


if __name__ == "__main__":
    unittest.main()
