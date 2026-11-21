"""Small, hermetic tests for exact expression-reference dependency traversal."""
import io
import json
import unittest

from export_exact_graph import analyze


def make_stream():
    def line(x):
        return (json.dumps(x, separators=(",", ":")) + "\n").encode()
    rows = [line({"meta": {"format": {"version": "3.1.0"}}})]
    for i, name in enumerate(("p", "q", "a", "b", "first", "second", "unused"), 1):
        rows.append(line({"in": i, "str": {"pre": 0, "str": name}}))
    rows.extend(line(x) for x in [
        {"sort": 0, "ie": 0},
        {"const": {"name": 1, "us": []}, "ie": 1},
        {"const": {"name": 2, "us": []}, "ie": 2},
        {"const": {"name": 3, "us": []}, "ie": 3},
        {"const": {"name": 4, "us": []}, "ie": 4},
        {"app": {"fn": 3, "arg": 4}, "ie": 5},
    ])
    for i, value in enumerate((0, 0, 1, 2, 3, 5, 0), 1):
        rows.append(line({"thm": [{"name": i, "type": 0, "value": value,
                                   "all": [i], "levelParams": []}]}))
    return rows


class ExactGraphTests(unittest.TestCase):
    def test_separate_root_closures_and_overlap(self):
        report, members = analyze(make_stream(), roots=("first", "second"))
        self.assertEqual(report["exported_declarations"], 7)
        self.assertEqual(report["expression_nodes"], 6)
        self.assertEqual(report["per_root_declaration_count"], {"first": 3, "second": 5})
        self.assertEqual(report["per_root_exclusive"], {"first": 1, "second": 3})
        self.assertEqual(report["pairwise_intersection_declarations"]["first & second"], 2)
        self.assertEqual(report["union_of_five"], 6)
        self.assertEqual(report["exported_declarations_outside_five_union"], 1)
        self.assertEqual(report["unresolved_constant_id_count"], 0)
        self.assertEqual(dict((name, mask) for name, _, mask in members)["unused"], 0)

    def test_reject_forward_expression_edges(self):
        rows = make_stream()
        index = next(i for i, line in enumerate(rows) if b'"ie":5' in line)
        rows[index] = b'{"app":{"fn":8,"arg":4},"ie":5}\n'
        with self.assertRaises(ValueError):
            analyze(rows, roots=("first", "second"))

    def test_missing_constant_is_reported(self):
        rows = make_stream()
        # Replace value with a reference to an introduced but undeclared name.
        rows.insert(-1, b'{"ie":6,"const":{"name":7,"us":[]}}\n')
        rows[-1] = b'{"thm":[{"name":7,"type":0,"value":6,"all":[7],"levelParams":[]}]}\n'
        report, members = analyze(rows, roots=("first", "second"))
        self.assertEqual(report["unresolved_constant_id_count"], 0)
        self.assertTrue(members)


if __name__ == "__main__":
    unittest.main()
