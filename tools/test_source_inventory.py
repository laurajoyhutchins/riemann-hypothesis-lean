"""Source-size and five-statement boundary checks on tiny synthetic trees."""
import tempfile
import unittest
from pathlib import Path

from source_inventory import EXPECTED, count, verify_surface


class InventoryTests(unittest.TestCase):
    def test_lean_line_count_and_exact_source_boundary(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = Path(tmp)
            (src / "Main.lean").write_text("\n".join(EXPECTED) + "\n")
            (src / "Extra.lean").write_bytes(b"theorem example : True := trivial")
            verify_surface(src / "Main.lean")
            result = count(src)
            self.assertEqual(result["files"], 2)
            self.assertEqual(result["physical_lines"], 6)
            self.assertEqual(result["nonblank_lines"], 6)

    def test_edited_final_statement_is_not_silently_accepted(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Main.lean"
            path.write_text("\n".join(EXPECTED).replace(
                "theorem riemannHypothesis :", "theorem somethingElse :"
            ))
            with self.assertRaises(ValueError):
                verify_surface(path)


if __name__ == "__main__":
    unittest.main()
