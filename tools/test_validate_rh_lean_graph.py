"""Genuine upstream-schema, fail-closed validation tests (not RH build tests)."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent))
from validate_rh_lean_graph import inspect_graph, publish_graphs
from rh_lean_graph import generate_driver, RH_ROOTS, COMBINED_FILE


def node(name, refs=(), category="Theorem"):
    return {"name": name, "references": list(refs),
            "constCategory": category, "constType": "True"}


class GraphValidationTests(unittest.TestCase):
    def test_root_and_external_references_are_explicit(self):
        data, meta = inspect_graph([node("Main.entry", ["Other.lemma"])], ("Main.entry",))
        self.assertEqual(len(data), 1)
        self.assertEqual(meta["external_reference_count"], 1)
        self.assertFalse(meta["complete_lean_dependency_closure"])

    def test_malformed_and_missing_roots_refused(self):
        for bad in ([node("a"), node("a")], [node("a", ["x", "x"])],
                    [node("a", category="Garbage")], [{"name": "a"}]):
            with self.assertRaises(ValueError):
                inspect_graph(bad, ("a",))
        with self.assertRaises(ValueError):
            inspect_graph([node("a")], ("missing",))

    def test_canonical_output_and_comparison(self):
        with tempfile.TemporaryDirectory() as dirname:
            path = Path(dirname)
            nodes = [node("Leaf"), node("Main.entry", ["Leaf"])]
            (path / "Main.entry.json").write_text(json.dumps(nodes[::-1]))
            (path / COMBINED_FILE).write_text(json.dumps(nodes))
            first = publish_graphs(path, path / "first", ("Main.entry",), 3)
            second = publish_graphs(path, path / "second", ("Main.entry",), 3)
            self.assertEqual(first, second)
            self.assertTrue(first["graphs"][COMBINED_FILE]["closed_under_emitted_edges"])
            self.assertEqual((path / "first" / COMBINED_FILE).read_bytes(),
                             (path / "second" / COMBINED_FILE).read_bytes())

    def test_combined_refuses_missing_nodes(self):
        with tempfile.TemporaryDirectory() as dirname:
            path = Path(dirname)
            (path / "Main.entry.json").write_text(json.dumps([node("Main.entry", ["Leaf"]), node("Leaf")]))
            (path / COMBINED_FILE).write_text(json.dumps([node("Main.entry", ["Leaf"])]))
            with self.assertRaisesRegex(ValueError, "combined graph"):
                publish_graphs(path, path / "out", ("Main.entry",), 3)

    def test_require_closed_refuses_incomplete(self):
        with tempfile.TemporaryDirectory() as dirname:
            path = Path(dirname)
            (path / "Main.entry.json").write_text(json.dumps([node("Main.entry", ["Leaf"])]))
            (path / COMBINED_FILE).write_text(json.dumps([node("Main.entry", ["Leaf"])]))
            with self.assertRaisesRegex(ValueError, "not a closed graph"):
                publish_graphs(path, path / "out", ("Main.entry",), 1, require_closed=True)
            self.assertFalse((path / "out").exists())

    def test_generation_import_and_strict_combined(self):
        source = generate_driver("import Lean", ("MiniMain.entry",), 2, "MiniMain")
        self.assertIn("import MiniMain\nimport Lean", source)
        self.assertIn("getUsedConstantGraph roots 2", source)
        self.assertIn("getRelevantConstsFromConst name", source)
        self.assertIn("#check @MiniMain.entry", source)
        self.assertIn("RH-combined.json", source)


if __name__ == "__main__":
    unittest.main()
