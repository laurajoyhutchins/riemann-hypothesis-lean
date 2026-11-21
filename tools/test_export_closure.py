"""Conservative exact exported theorem-type index tests."""
import io
import unittest

from export_closure import consume, exact_type_families


class TypeIndexTests(unittest.TestCase):
    def test_groups_by_expression_and_ordered_universe_parameters(self):
        names = ["", "u", "v", "w", "a", "b", "c", "d", "e"]
        rows = [
            (4, 10, (1,)), (5, 10, (1,)), # identical type and universe params
            (6, 10, (2,)),                 # different universe parameter name
            (7, 11, (1,)),                 # different expression
            (8, 10, (1,)),
        ]
        repeated, members, keys = exact_type_families(rows, names)
        self.assertEqual(repeated, {(10, (1,)): 3})
        self.assertEqual(members[(10, (1,))], ["a", "b", "e"])
        self.assertEqual(keys, [(10, (1,))])

    def test_stream_five_roots_and_identical_type(self):
        roots = [
            "riemannHypothesis",
            "riemannZeta_eq_zero_re",
            "LFunction_ne_zero_of_half_lt_re",
            "LFunction_eq_zero_re",
            "LFunction_eq_zero_re_of_isPrimitive",
        ]
        lines = [b'{"meta":{"format":{"version":"3.1.0"}}}']
        for i, name in enumerate(roots, 1):
            lines.append(('{"in":%d,"str":{"pre":0,"str":"%s"}}' % (i, name)).encode())
        # All five fake declarations share type expr #7; the parser does not
        # pretend that this test fixture constitutes a kernel proof.
        for i in range(1, 6):
            lines.append(('{"thm":{"name":%d,"type":7,"levelParams":[],"value":9,"all":[]}}' % i).encode())
        result = consume(lines)
        self.assertEqual(result["report"]["exact_type_index"]["repeated_family_count"], 1)
        self.assertEqual(result["report"]["exact_type_index"]["theorems_in_repeated_families"], 5)
        self.assertEqual(result["report"]["exact_type_index"]["largest_family_size"], 5)

    def test_reject_bad_type_index_and_level_parameters(self):
        prefix = [b'{"in":1,"str":{"pre":0,"str":"riemannHypothesis"}}']
        with self.assertRaises(ValueError):
            consume(prefix + [b'{"thm":{"name":1,"type":"bad","levelParams":[]}}'], require_roots=False)
        with self.assertRaises(ValueError):
            consume(prefix + [b'{"thm":{"name":1,"type":1,"levelParams":["oops"]}}'], require_roots=False)


if __name__ == "__main__":
    unittest.main()
