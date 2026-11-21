"""Fixture tests for the conservative Lean source module graph."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from proof_import_graph import GraphError, closure, header_imports, inventory, main, report


class ModuleGraphTests(unittest.TestCase):
    def test_import_header_handles_nested_comments(self):
        source = '''/- outer /- inner import Bad -/ outer -/
prelude
import Mathlib -- package
import A.B
/- import Bad -/
public import all A.C
set_option maxHeartbeats 100
#eval "import Bad"
'''
        self.assertEqual(header_imports(source, 'Example'), ('Mathlib', 'A.B', 'A.C'))

    def test_invalid_header_rejected(self):
        with self.assertRaises(GraphError):
            header_imports('import A.B more\n', 'Test')

    def test_module_closure_and_comparison(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'src'
            (root / 'A').mkdir(parents=True)
            (root / 'Main.lean').write_text('import A.Heavy\nimport Mathlib\n', encoding='utf8')
            (root / 'MainMinimal.lean').write_text('import A.Common\n', encoding='utf8')
            (root / 'A' / 'Heavy.lean').write_text('import A.Common\n', encoding='utf8')
            (root / 'A' / 'Common.lean').write_text('theorem x : True := trivial\n', encoding='utf8')
            (root / 'A' / 'Unused.lean').write_text('theorem u : True := trivial\n', encoding='utf8')
            mods = inventory(root)
            self.assertEqual(closure('Main', mods), {'Main', 'A.Heavy', 'A.Common'})
            data = report(mods, ['Main', 'MainMinimal'], {'Mathlib'})
            self.assertEqual(data['import_comparison']['only_left'], ['A.Heavy'])
            self.assertEqual(data['import_comparison']['only_right'], [])
            self.assertEqual(data['closures']['Main']['files'], 3)
            self.assertEqual(main([str(root), '--root', 'Main', '--output', str(Path(directory) / 'result.json')]), 0)

    def test_unknown_import_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'src'
            root.mkdir()
            (root / 'Main.lean').write_text('import Imagined.Foo\n', encoding='utf8')
            with self.assertRaisesRegex(GraphError, 'unresolved imports'):
                report(inventory(root), ['Main'], {'Mathlib'})

    def test_missing_root_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'src'
            root.mkdir()
            (root / 'A.lean').write_text('import Mathlib\n', encoding='utf8')
            with self.assertRaisesRegex(GraphError, 'not found'):
                report(inventory(root), ['Missing'], {'Mathlib'})


if __name__ == '__main__':
    unittest.main()
