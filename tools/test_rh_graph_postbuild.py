"""No Lean or RH checkout needed: retained-build admission tests."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from rh_graph_postbuild import inspect_retained_build, load_trusted_controller


def digest(data):
    return hashlib.sha256(data).hexdigest()


class RetainedBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.home = Path(self.temp.name)
        self.state = self.home / "state"
        self.work = self.state / "failed-work/run-abc"
        self.work.mkdir(parents=True)
        self.candidate = self.home / "candidate"
        self.candidate.mkdir()
        self.identity = {
            "candidate_head": "1" * 40,
            "source_tree": "2" * 40,
            "lakefile_sha256": digest(b"lean project"),
            "manifest_sha256": digest(b"manifest"),
            "toolchain": "leanprover/lean4:v4.33.1",
        }
        project = self.work / "project"
        (project / "src").mkdir(parents=True)
        (project / "src/Main.lean").write_text("import Statements\n")
        (project / "lakefile.toml").write_bytes(b"lean project")
        (project / "lake-manifest.json").write_bytes(b"manifest")
        (project / "lean-toolchain").write_text(self.identity["toolchain"] + "\n")
        modules = project / ".lake/build/lib/lean"
        modules.mkdir(parents=True)
        (modules / "Main.olean").write_bytes(b"opaque olean bytes")
        (modules / "Main.trace").write_text(json.dumps({"depHash": "a" * 16}))
        (self.work / "result").mkdir()
        (self.work / "result/outputs.jsonl").write_text(
            json.dumps("2026-03-17") + "\n" +
            json.dumps(["a" * 16, "b" * 16 + ".ltar"]) + "\n")
        (self.work / "cache/artifacts").mkdir(parents=True)
        (self.work / "cache/artifacts" / ("b" * 16 + ".ltar")).write_bytes(b"archive")
        self.checkpoint = self.work / "checkpoint.json"
        self.record = dict(schema=1, state="staged", build_exit_code=0,
                           identity=self.identity, work=str(self.work))
        self.save()

    def save(self):
        self.checkpoint.write_text(json.dumps(self.record))

    def inspect(self):
        with patch("rh_graph_postbuild.source_identity", return_value=self.identity):
            return inspect_retained_build(self.candidate, self.checkpoint, self.state)

    def test_matching_completed_build(self):
        result = self.inspect()
        self.assertEqual(result["source_tree"], "2" * 40)
        self.assertEqual(result["main_dep_hash"], "a" * 16)
        self.assertEqual(result["main_olean_sha256"], digest(b"opaque olean bytes"))

    def test_refuses_incomplete_build_and_input_drift(self):
        self.record["state"] = "failed"
        self.save()
        with self.assertRaisesRegex(ValueError, "not a successfully staged"):
            self.inspect()
        self.record["state"] = "staged"
        self.record["identity"] = dict(self.identity, source_tree="f" * 40)
        self.save()
        with self.assertRaisesRegex(ValueError, "does not match"):
            self.inspect()

    def test_refuses_escape_and_missing_main(self):
        with patch("rh_graph_postbuild.source_identity", return_value=self.identity):
            with self.assertRaises((ValueError, FileNotFoundError)):
                inspect_retained_build(self.candidate, self.home / "other/checkpoint.json", self.state)
        (self.work / "project/.lake/build/lib/lean/Main.olean").unlink()
        with self.assertRaisesRegex(ValueError, "Main.olean"):
            self.inspect()

    def test_refuses_unmapped_main(self):
        (self.work / "result/outputs.jsonl").write_text(json.dumps("2026-03-17") + "\n")
        with self.assertRaisesRegex(ValueError, "Main trace"):
            self.inspect()

    def test_refuses_unpinned_community_controller(self):
        with patch("rh_graph_postbuild.subprocess.check_output",
                   return_value="0" * 40 + "\\n"):
            with self.assertRaisesRegex(ValueError, "pinned clean revision"):
                load_trusted_controller(self.home / "community/scripts/ci-build.py")

    def test_refuses_missing_mapped_archive(self):
        (self.work / "cache/artifacts" / ("b" * 16 + ".ltar")).unlink()
        with self.assertRaisesRegex(ValueError, "archive"):
            self.inspect()


if __name__ == "__main__":
    unittest.main()
