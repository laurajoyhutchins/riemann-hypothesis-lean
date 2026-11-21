"""No-network interruption and identity tests for persistent warm Lean workspace."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

from rh_ci_durable_build import (
    ensure_state, locked_file, make_plan, plan_key, run_build,
)


class DurableWarmBuildTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="rh-durable-")
        self.addCleanup(self.temporary.cleanup)
        self.outer = Path(self.temporary.name)
        self.workspace = self.outer / "persistent-checkout"
        self.workspace.mkdir()
        self.state = self.outer / "durable-state"
        self.state.mkdir()
        (self.workspace / "src").mkdir()
        (self.workspace / "src/Proof.lean").write_text("theorem p : True := trivial\n")
        (self.workspace / "lakefile.toml").write_text('name = "tree"\nsrcDir = "src"\n')
        (self.workspace / "lake-manifest.json").write_text('{"version": 1}\n')
        (self.workspace / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
        (self.workspace / "README.md").write_text("README\n")
        self.git("init", "-q")
        self.git("config", "user.name", "CI")
        self.git("config", "user.email", "ci@example.invalid")
        self.commit()
        self.fake_lake = self.outer / "fake-lake"
        self.fake_lake.write_text(
            "#!/usr/bin/env python3\n"
            "import pathlib, sys\n"
            "root = pathlib.Path('.lake/build/lib/lean')\n"
            "root.mkdir(parents=True, exist_ok=True)\n"
            "output = root/'Proof.olean'\n"
            "if not output.exists():\n"
            "    output.write_text('untrusted raw artifact')\n"
            "    sys.exit(7)\n"
            "pathlib.Path('reuse-observed.txt').write_text('second invocation saw retained bytes')\n"
            "sys.exit(0)\n"
        )
        self.fake_lake.chmod(0o700)

    def git(self, *args):
        return subprocess.check_output(
            ["git", "-C", str(self.workspace), *args],
            stderr=subprocess.STDOUT, text=True,
        ).strip()

    def commit(self):
        self.git("add", "-A")
        self.git("commit", "-qm", "fixture")

    def run_id(self):
        return self.state / "runs" / plan_key(make_plan(self.workspace, ["Proof"]))

    def record(self):
        return json.loads((self.run_id() / "checkpoint.json").read_text())

    def test_failed_build_retains_workspace_and_retries_actual_build(self):
        first = run_build(self.workspace, self.state, ["Proof"], lake=str(self.fake_lake))
        self.assertEqual(first, 7)
        self.assertEqual(self.record()["state"], "failed")
        self.assertFalse(self.record()["proof_verified"])
        artifact = self.workspace / ".lake/build/lib/lean/Proof.olean"
        self.assertEqual(artifact.read_text(), "untrusted raw artifact")
        self.assertEqual(run_build(
            self.workspace, self.state, ["Proof"], lake=str(self.fake_lake)), 0)
        self.assertEqual(self.record()["state"], "build_succeeded")
        self.assertEqual(self.record()["attempts"], 2)
        self.assertTrue((self.workspace / "reuse-observed.txt").is_file())
        self.assertIn(b"attempt=2", (self.run_id() / "build.log").read_bytes())

    def test_documentation_only_commit_reuses_provenance(self):
        first = make_plan(self.workspace, ["Proof"])
        (self.workspace / "README.md").write_text("Documentation revision\n")
        self.commit()
        self.assertEqual(first, make_plan(self.workspace, ["Proof"]))

    def test_source_changes_refused_in_same_retained_workspace(self):
        self.assertEqual(run_build(
            self.workspace, self.state, ["Proof"], lake=str(self.fake_lake)), 7)
        before = self.record()
        (self.workspace / "src/Proof.lean").write_text("theorem p : True := True.intro\n")
        self.commit()
        with self.assertRaisesRegex(ValueError, "different source/configuration"):
            run_build(self.workspace, self.state, ["Proof"], lake=str(self.fake_lake))
        self.assertEqual(before["state"], "failed")
        self.assertEqual(
            run_build(self.workspace, self.state, ["Proof"], lake=str(self.fake_lake),
                      cross_input=True), 0,
        )
        self.assertNotEqual(self.record()["plan"]["input_fingerprint"],
                            make_plan(self.workspace, ["Proof"])["input_fingerprint"])

    def test_dirty_source_refused_even_when_warm_reuse_requested(self):
        (self.workspace / "src/Proof.lean").write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "uncommitted"):
            run_build(self.workspace, self.state, ["Proof"],
                      lake=str(self.fake_lake), cross_input=True)

    def test_wrong_or_false_verification_receipt_is_rejected(self):
        plan = make_plan(self.workspace, ["Proof"])
        run_dir, _ = ensure_state(self.state, plan)
        checkpoint = run_dir / "checkpoint.json"
        record = json.loads(checkpoint.read_text())
        record["proof_verified"] = True
        checkpoint.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, "incorrectly claims"):
            ensure_state(self.state, plan)

    def test_unquiesced_run_refuses_automatic_adoption(self):
        plan = make_plan(self.workspace, ["Proof"])
        run_dir, _ = ensure_state(self.state, plan)
        checkpoint = run_dir / "checkpoint.json"
        record = json.loads(checkpoint.read_text())
        record["state"] = "building"
        checkpoint.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, "may still be executing"):
            ensure_state(self.state, plan)

    def test_workspace_lock_prevents_concurrent_controller(self):
        plan = make_plan(self.workspace, ["Proof"])
        key = __import__("hashlib").sha256(plan["workspace"].encode()).hexdigest()
        from rh_ci_durable_build import make_directory
        make_directory(self.state / "workspaces")
        with locked_file(self.state / "workspaces" / (key + ".lock")):
            with self.assertRaisesRegex(ValueError, "another build"):
                run_build(self.workspace, self.state, ["Proof"], lake=str(self.fake_lake))

    def test_checkpoint_symlink_is_not_followed(self):
        plan = make_plan(self.workspace, ["Proof"])
        run_dir, _ = ensure_state(self.state, plan)
        path = run_dir / "checkpoint.json"
        path.unlink()
        path.symlink_to(self.workspace / "README.md")
        with self.assertRaises((ValueError, OSError)):
            ensure_state(self.state, plan)
        self.assertEqual((self.workspace / "README.md").read_text(), "README\n")

    def test_sigterm_retains_partial_workspace_and_records_interrupt(self):
        slow = self.outer / "slow-lake"
        slow.write_text(
            "#!/usr/bin/env python3\n"
            "import pathlib, time\n"
            "p=pathlib.Path('.lake/build/lib/lean/Proof.olean')\n"
            "p.parent.mkdir(parents=True, exist_ok=True)\n"
            "if not p.exists():\n"
            "  p.write_text('raw partial bytes')\n"
            "  time.sleep(20)\n"
        )
        slow.chmod(0o700)
        script = Path(__file__).with_name("rh_ci_durable_build.py")
        command = [
            sys.executable, str(script), "--workspace", str(self.workspace),
            "--state-root", str(self.state), "--module", "Proof",
            "--lake", str(slow), "--acknowledge-isolated-runner",
        ]
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        artifact = self.workspace / ".lake/build/lib/lean/Proof.olean"
        deadline = time.monotonic() + 7
        try:
            while not artifact.exists() and time.monotonic() < deadline:
                time.sleep(0.05)
            self.assertTrue(artifact.exists(), "fixture subprocess did not start")
            process.send_signal(signal.SIGTERM)
            out, err = process.communicate(timeout=7)
            self.assertEqual(process.returncode, 143, (out, err))
            self.assertEqual(self.record()["state"], "interrupted")
            self.assertFalse(self.record()["proof_verified"])
            self.assertEqual(run_build(
                self.workspace, self.state, ["Proof"], lake=str(slow)), 0)
            self.assertEqual(self.record()["state"], "build_succeeded")
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate(timeout=7)


if __name__ == "__main__":
    unittest.main()
