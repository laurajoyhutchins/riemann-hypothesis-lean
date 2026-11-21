"""Deterministic reverse-import planning fixtures; no RH corpus required."""
import unittest

from ci_import_impact import plan_impact


class ImpactTests(unittest.TestCase):
    def setUp(self):
        self.imports = {
            "Main": ["Proof", "Statements"],
            "Proof": ["Foundation"],
            "Foundation": ["Mathlib"],
            "Statements": ["Mathlib"],
            "Independent": [],
        }
        self.sizes = {name: n for name, n in zip(self.imports, (10, 20, 30, 40, 50))}

    def test_leaf_change_rebuilds_reverse_importers_not_unrelated_modules(self):
        report, modules = plan_impact(
            self.imports, self.sizes, ["src/Foundation.lean"]
        )
        self.assertEqual(modules, ["Foundation", "Main", "Proof"])
        self.assertEqual(report["import_affected_physical_lines"], 60)
        self.assertFalse(report["proof_verified"])
        self.assertEqual(report["unresolved_local_imports"], [])

    def test_new_unimported_file_is_in_scope(self):
        imports = {**self.imports, "Fresh": []}
        sizes = {**self.sizes, "Fresh": 7}
        report, modules = plan_impact(imports, sizes, ["src/Fresh.lean"])
        self.assertEqual(modules, ["Fresh"])
        self.assertEqual(report["import_affected_modules"], 1)

    def test_deleted_module_preserves_dangling_dependent_signal(self):
        imports = {k: v for k, v in self.imports.items() if k != "Foundation"}
        sizes = {k: v for k, v in self.sizes.items() if k != "Foundation"}
        report, modules = plan_impact(imports, sizes, ["src/Foundation.lean"])
        self.assertEqual(modules, ["Main", "Proof"])
        self.assertEqual(report["changed_modules_absent_from_head"], ["Foundation"])
        self.assertEqual(report["unresolved_local_imports"], ["Foundation"])

    def test_global_inputs_invalidate_every_module(self):
        report, modules = plan_impact(
            self.imports, self.sizes, ["lake-manifest.json"]
        )
        self.assertEqual(set(modules), set(self.imports))
        self.assertEqual(report["global_invalidation_reasons"], ["lake-manifest.json"])

    def test_nonlean_source_is_global_because_elaboration_inputs_are_unknown(self):
        report, modules = plan_impact(
            self.imports, self.sizes, ["src/data/coefficients.txt"]
        )
        self.assertEqual(set(modules), set(self.imports))
        self.assertEqual(len(report["global_invalidation_reasons"]), 1)

    def test_multiple_changes_deduplicated(self):
        report, modules = plan_impact(
            self.imports, self.sizes,
            ["src/Foundation.lean", "src/Proof.lean", "src/Foundation.lean"]
        )
        self.assertEqual(modules, ["Foundation", "Main", "Proof"])
        self.assertEqual(len(report["changed_paths"]), 2)

    def test_invalid_paths_refused(self):
        with self.assertRaises(ValueError):
            plan_impact(self.imports, self.sizes, ["src/../hidden.lean"])

    def test_graph_consistency_refused(self):
        with self.assertRaises(ValueError):
            plan_impact(self.imports, {"Main": 1}, ["src/Main.lean"])


if __name__ == "__main__":
    unittest.main()
