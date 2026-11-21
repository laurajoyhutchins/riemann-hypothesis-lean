"""Lean Graph interoperability tests using the exporter-format synthetic fixture."""
import tempfile
from pathlib import Path
import unittest

from export_lean_graph import project, references
from rh_graph_explorer import GraphStore, build_index
from test_export_exact_graph import make_stream


class AdapterTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        path = Path(self.tmp.name) / 'index'
        build_index(make_stream(), path, roots=('first', 'second'))
        self.store = GraphStore(path)
        self.addCleanup(self.store.close)

    def test_upstream_schema_and_root_boundary(self):
        data, receipt = project(self.store, ('first', 'second'), depth=0)
        self.assertEqual({d['name'] for d in data}, {'first', 'second'})
        self.assertTrue(all(set(d) == {'name', 'references', 'constCategory', 'constType'}
                            and d['constCategory'] == 'Theorem' for d in data))
        self.assertEqual([d['references'] for d in data], [[], []])
        self.assertEqual(receipt['boundary_count'], 2)
        self.assertFalse(receipt['complete_transitive_closure'])

    def test_exact_value_refs_and_shared_nodes(self):
        first = self.store.declaration('first')
        self.assertEqual(references(self.store, first, 20), {3})
        data, receipt = project(self.store, ('first', 'second'), depth=1)
        keyed = {d['name']: d for d in data}
        self.assertEqual(keyed['first']['references'], ['a'])
        self.assertEqual(keyed['second']['references'], ['a', 'b'])
        self.assertIn('a', keyed)
        self.assertIn('b', keyed)
        self.assertEqual(len(keyed), receipt['node_count'])

    def test_expansion_uses_type_and_value_dag(self):
        data, _ = project(self.store, ('first', 'second'), depth=2)
        self.assertIn('p', {d['name'] for d in data})
        self.assertIn('q', {d['name'] for d in data})

    def test_resource_exhaustion_fails_closed(self):
        with self.assertRaisesRegex(ValueError, 'node budget exhausted'):
            project(self.store, ('first', 'second'), depth=2, max_nodes=2)
        with self.assertRaisesRegex(ValueError, 'node budget exhausted'):
            project(self.store, ('first', 'second'), depth=0, max_nodes=1)
        with self.assertRaisesRegex(ValueError, 'expression budget exhausted'):
            project(self.store, ('first',), depth=1, max_expr=1)
        with self.assertRaisesRegex(ValueError, 'missing or non-theorem'):
            project(self.store, ('missing',), depth=1)


if __name__ == '__main__':
    unittest.main()
