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
        rows.insert(8, b'{"in":8,"str":{"pre":0,"str":"ghost"}}\n')
        thm = next(i for i, line in enumerate(rows) if b'"thm"' in line)
        rows.insert(thm, b'{"ie":6,"const":{"name":8,"us":[]}}\n')
        first = next(i for i, line in enumerate(rows) if b'"name":5' in line
                     and b'"thm"' in line)
        rows[first] = rows[first].replace(b'"value":3', b'"value":6')
        report, _ = analyze(rows, roots=("first", "second"))
        self.assertEqual(report["unresolved_constant_id_count"], 1)
        self.assertEqual(report["unresolved_constant_ids"], [8])
        self.assertEqual(report["unresolved_constant_names"], ["ghost"])


if __name__ == "__main__":
    unittest.main()
