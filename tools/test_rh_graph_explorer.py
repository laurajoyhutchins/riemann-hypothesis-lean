"""Hermetic tests for faithful on-demand Lean Expr inspection."""
import io
import json
from http.server import HTTPServer
from pathlib import Path
import tempfile
import threading
import unittest
from urllib.error import HTTPError
from urllib.request import urlopen

from rh_graph_explorer import GraphStore, build_index, handler_factory
from test_export_exact_graph import make_stream


class ExplorerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.index = Path(self.tmp.name) / 'index'

    def build(self, rows=None):
        return build_index(rows or make_stream(), self.index, roots=('first', 'second'))

    def test_lossless_nodes_shared_ids_and_declaration_search(self):
        manifest = self.build()
        self.assertEqual(manifest['expression_count'], 6)
        self.assertEqual(manifest['unresolved_constant_count'], 0)
        store = GraphStore(self.index)
        self.addCleanup(store.close)
        self.assertEqual(store.find('s'), ['second'])
        self.assertEqual(store.declaration('first')['expression_roots'], [0, 3])
        self.assertIsNone(store.declaration('unknown'))
        app = store.expression(5)
        self.assertEqual(app['kind'], 'app')
        self.assertEqual(app['children'], [{'role':'fn','id':3}, {'role':'arg','id':4}])
        self.assertEqual(app['raw']['app'], {'fn': 3, 'arg': 4})
        self.assertEqual(store.expression(3)['reference']['name'], 'a')
        self.assertTrue(store.expression(3)['reference']['defined'])
        # Expression nodes are indexed by immutable exporter IDs, not duplicated.
        self.assertEqual(store.expression(3)['id'], 3)
        with self.assertRaises(ValueError):
            store.expression(6)

    def test_reject_unresolved_constants_without_publishing_index(self):
        rows=make_stream()
        rows.insert(8, b'{"in":8,"str":{"pre":0,"str":"ghost"}}\n')
        thm = next(i for i,l in enumerate(rows) if b'"thm"' in l)
        rows.insert(thm, b'{"ie":6,"const":{"name":8,"us":[]}}\n')
        with self.assertRaisesRegex(ValueError,'unresolved'):
            self.build(rows)
        self.assertFalse(self.index.exists())

    def test_missing_roots_rejected(self):
        with self.assertRaisesRegex(ValueError,'missing or non-theorem'):
            build_index(make_stream(),self.index, roots=('this_does_not_exist',))
        self.assertFalse(self.index.exists())

    def test_malformed_expr_refused(self):
        rows = make_stream()
        i=next(i for i, l in enumerate(rows) if b'"ie":5' in l)
        rows[i]=b'{"ie":5,"app":{"fn":9,"arg":4}}\n'
        with self.assertRaisesRegex(ValueError,'out of range|invalid Expr|children'):
            self.build(rows)
        self.assertFalse(self.index.exists())

    def test_block_boundaries_preserve_raw_string(self):
        rows=make_stream()
        pos=next(i for i,v in enumerate(rows) if b'"thm"' in v)
        rows.insert(pos, (json.dumps({'ie':6,'strVal':'ab\n'+'z'*1100000}, separators=(',',':'))+'\n').encode())
        manifest=self.build(rows)
        self.assertGreaterEqual(manifest['compressed_blocks'],2)
        store=GraphStore(self.index); self.addCleanup(store.close)
        self.assertEqual(len(store.expression(6)['raw']['strVal']),1100003)
        self.assertEqual(store.expression(0)['kind'],'sort')

    def test_http_endpoints_and_bad_query(self):
        self.build()
        store=GraphStore(self.index)
        server=HTTPServer(('127.0.0.1',0), handler_factory(self.index, Path(__file__).with_name('rh_graph_viewer.html')))
        server.store=store
        thread=threading.Thread(target=server.serve_forever,daemon=True)
        thread.start()
        self.addCleanup(lambda: (server.shutdown(),thread.join(2),server.server_close(),store.close()))
        root=f'http://127.0.0.1:{server.server_port}'
        with urlopen(root+'/api/expression?id=5') as r:
            self.assertEqual(json.load(r)['kind'],'app')
        with urlopen(root+'/api/declaration?name=first') as r:
            self.assertEqual(json.load(r)['name'],'first')
        with urlopen(root+'/api/find?q=fi') as r:
            self.assertEqual(json.load(r)['matches'],['first'])
        with urlopen(root+'/') as r:
            self.assertIn(b'RH proof explorer',r.read())
        with self.assertRaises(HTTPError) as ctx:
            urlopen(root+'/api/expression?id=999')
        self.assertEqual(ctx.exception.code,400)

if __name__=='__main__': unittest.main()