"""No-network tests for the community-schema RH build-input identity."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from rh_ci_identity import (
    FINGERPRINT_FIELDS, fingerprint, source_identity,
)


class SourceIdentityTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="rh-ci-identity-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.run_git("init", "-q")
        self.run_git("config", "user.name", "CI")
        self.run_git("config", "user.email", "ci@example.invalid")
        (self.root / "src").mkdir()
        (self.root / "src/Proof.lean").write_text("theorem p : True := trivial\n")
        (self.root / "lakefile.toml").write_text('name = "tree"\nsrcDir = "src"\n')
        (self.root / "lake-manifest.json").write_text('{"version": 1}\n')
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
        (self.root / "README.md").write_text("Original documentation\n")
        self.commit()

    def run_git(self, *args):
        return subprocess.check_output(
            ["git", "-C", str(self.root), *args],
            text=True, stderr=subprocess.STDOUT,
        ).strip()

    def commit(self):
        self.run_git("add", "-A")
        self.run_git("commit", "-qm", "fixture")

    def test_community_canonical_fingerprint(self):
        data = source_identity(self.root)
        fields = {key: data[key] for key in FINGERPRINT_FIELDS}
        expected = hashlib.sha256(
            json.dumps(fields, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        self.assertEqual(data["input_fingerprint"], expected)
        self.assertEqual(data["schema"], 1)
        self.assertEqual(data["repository"], "laurajoyhutchins/riemann-hypothesis-lean")
        self.assertFalse(data["proof_verified"])

    def test_documentation_commit_can_reuse_same_candidate_identity(self):
        before = source_identity(self.root)
        (self.root / "README.md").write_text("New documentation\n")
        self.commit()
        after = source_identity(self.root)
        self.assertNotEqual(after["candidate_head"], before["candidate_head"])
        self.assertEqual(after["input_fingerprint"], before["input_fingerprint"])
        self.assertEqual(after["source_tree"], before["source_tree"])

    def test_source_edit_invalidates_fingerprint(self):
        before = source_identity(self.root)
        (self.root / "src/Proof.lean").write_text("theorem p : True := True.intro\n")
        self.commit()
        after = source_identity(self.root)
        self.assertNotEqual(before["input_fingerprint"], after["input_fingerprint"])
        self.assertNotEqual(before["source_tree"], after["source_tree"])

    def test_config_and_toolchain_changes_invalidate(self):
        before = source_identity(self.root)["input_fingerprint"]
        (self.root / "lake-manifest.json").write_text('{"version": 2}\n')
        self.commit()
        middle = source_identity(self.root)["input_fingerprint"]
        self.assertNotEqual(before, middle)
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
        self.commit()
        self.assertNotEqual(middle, source_identity(self.root)["input_fingerprint"])

    def test_uncommitted_and_untracked_source_refused(self):
        (self.root / "src/Proof.lean").write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "uncommitted"):
            source_identity(self.root)
        self.run_git("checkout", "--", "src/Proof.lean")
        (self.root / "src/Other.lean").write_text("theorem other : True := trivial\n")
        with self.assertRaisesRegex(ValueError, "uncommitted"):
            source_identity(self.root)

    def test_ignored_elaboration_input_refused(self):
        (self.root / ".gitignore").write_text("src/*.txt\n")
        self.commit()
        (self.root / "src/data.txt").write_text("could change elaboration")
        with self.assertRaisesRegex(ValueError, "ignored file"):
            source_identity(self.root)

    def test_dirty_manifest_and_wrong_repository_refused(self):
        (self.root / "lake-manifest.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "uncommitted"):
            source_identity(self.root)
        self.run_git("checkout", "--", "lake-manifest.json")
        with self.assertRaisesRegex(ValueError, "scoped"):
            source_identity(self.root, repository="leanprover-community/riemann-hypothesis")

    def test_missing_fingerprint_fields_refused(self):
        with self.assertRaisesRegex(ValueError, "precisely"):
            fingerprint({"source_tree": "example"})


if __name__ == "__main__":
    unittest.main()
