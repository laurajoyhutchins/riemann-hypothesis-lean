"""Tests for source import footprints. These do not verify Lean proofs."""
import unittest
from shared_spine_import_cut import analyze


class ImportFootprintTests(unittest.TestCase):
    def test_shared_and_exclusive_import_closure(self):
        graph = {
            "Root": ["A", "B"],
            "A": ["C"],
            "B": ["C", "D"],
            "C": [],
            "D": [],
            "Unused": [],
        }
        sizes = {"Root": 6, "A": 10, "B": 20, "C": 30, "D": 40, "Unused": 50}
        report = analyze(graph, sizes, "Root")
        by_name = {x["direct_import"]: x for x in report["direct_import_footprints"]}
        self.assertEqual(report["shared_by_multiple_direct_imports"], {
            "source_modules": 1, "physical_source_lines": 30
        })
        self.assertEqual(report["unique_source_footprint"], {
            "source_modules": 4, "physical_source_lines": 100
        })
        self.assertEqual(by_name["A"]["exclusive_source_lines"], 10)
        self.assertEqual(by_name["A"]["all_reachable_source_lines_through_import"], 40)
        self.assertEqual(by_name["B"]["exclusive_source_lines"], 60)
        self.assertEqual(by_name["B"]["all_reachable_source_lines_through_import"], 90)

    def test_detects_reachable_cycles(self):
        graph = {"Root": ["A"], "A": ["B"], "B": ["A"]}
        with self.assertRaisesRegex(ValueError, "cycle"):
            analyze(graph, {x: 1 for x in graph}, "Root")

    def test_detects_disconnected_cycles(self):
        graph = {"Root": ["A"], "A": [], "X": ["Y"], "Y": ["X"]}
        with self.assertRaisesRegex(ValueError, "cycle"):
            analyze(graph, {x: 1 for x in graph}, "Root")

    def test_refuses_unknown_local_name(self):
        graph = {"Proof.Root": ["Proof.X"], "Proof.Helper": []}
        with self.assertRaisesRegex(ValueError, "unresolved internal"):
            analyze(graph, {x: 1 for x in graph}, "Proof.Root")

    def test_allows_external_package_import(self):
        graph = {"Proof.Root": ["Proof.A", "Mathlib"], "Proof.A": []}
        report = analyze(graph, {x: 1 for x in graph}, "Proof.Root")
        self.assertEqual(report["distinct_local_direct_imports"], 1)
        self.assertEqual(report["direct_imports"], 2)


if __name__ == "__main__":
    unittest.main()
