"""Source-level audit for explicitly recorded proof-sharing changes."""
import hashlib
import tempfile
import unittest
from pathlib import Path

from pruning_contract import verify_proof_refactors


class ProofRefactorContractTests(unittest.TestCase):
    def test_exact_blob_and_line_accounting(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "src"
            source.mkdir()
            target = source / "Shared.lean"
            raw = b"theorem t : True := True.intro\\n"
            target.write_bytes(raw)
            current_sha = hashlib.sha1(
                b"blob " + str(len(raw)).encode() + b"\\0" + raw
            ).hexdigest()
            row = dict(
                path="src/Shared.lean",
                original_blob_sha="a" * 40,
                current_blob_sha=current_sha,
                original_lines=10,
                current_lines=1,
                declaration="t",
            )
            self.assertEqual(verify_proof_refactors(source, [row]), 9)
            target.write_bytes(raw + b"\\n")
            with self.assertRaisesRegex(ValueError, "blob drift"):
                verify_proof_refactors(source, [row])

    def test_duplicate_paths_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "src"
            source.mkdir()
            with self.assertRaisesRegex(ValueError, "duplicate"):
                verify_proof_refactors(source, [
                    {"path": "src/A.lean"}, {"path": "src/A.lean"}
                ])


if __name__ == "__main__":
    unittest.main()
