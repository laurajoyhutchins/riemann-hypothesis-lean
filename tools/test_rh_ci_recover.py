"""No-network, fail-closed validation tests for stock Lake recovery receipts."""
import json
from pathlib import Path
import tempfile
import unittest

from rh_ci_recover import (
    candidates_from_traces, explicit_candidates, module_file,
    read_report, regular_file,
)


class StockRecoveryReceiptTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="rh-stock-recovery-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "src/Domain").mkdir(parents=True)
        (self.root / "src/Domain/Good.lean").write_text("def good : Nat := 1\n")
        (self.root / "src/Domain/Bad.lean").write_text("def bad : Nat := 1\n")
        (self.root / ".lake/build/lib/lean/Domain").mkdir(parents=True)

    def make_trace(self, name):
        trace = self.root / ".lake/build/lib/lean" / module_file(name, ".trace")
        trace.write_text("{}")
        return trace

    def make_report(self, *rows):
        p = self.root / "decisions.jsonl"
        p.write_text("".join(json.dumps(row) + "\n" for row in rows))
        return p

    def test_only_committed_root_module_names_are_candidates(self):
        self.make_trace("Domain.Good")
        self.make_trace("Domain.Bad")
        (self.root / ".lake/build/lib/lean/Mathlib.trace").write_text("{}")
        self.assertEqual(candidates_from_traces(self.root), ["Domain.Bad", "Domain.Good"])
        self.assertEqual(explicit_candidates(self.root, ["Domain.Good", "Domain.Good"]),
                         ["Domain.Good"])

    def test_unowned_or_invalid_module_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing artifact"):
            explicit_candidates(self.root, ["Mathlib.Data"])
        for name in ["../escape", "X; rm", "", "Foo/Bar", "a..b"]:
            with self.subTest(name=name):
                with self.assertRaises(ValueError):
                    module_file(name, ".lean")

    def test_symlinked_trace_is_rejected(self):
        trace = self.make_trace("Domain.Good")
        trace.unlink()
        trace.symlink_to(self.root / "src/Domain/Good.lean")
        with self.assertRaisesRegex(ValueError, "symlink"):
            candidates_from_traces(self.root)

    def test_symlinked_directory_is_rejected(self):
        (self.root / ".lake/build/lib/lean/Extra").symlink_to(
            self.root / "src/Domain", target_is_directory=True
        )
        with self.assertRaisesRegex(ValueError, "symlink"):
            candidates_from_traces(self.root)

    def test_symlinked_lake_parent_is_refused(self):
        external = self.root / "outside"
        external.mkdir()
        (self.root / ".lake/build/ir").mkdir(parents=True)
        (self.root / ".lake/build/ir").rmdir()
        (self.root / ".lake/build/ir").symlink_to(external, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlinked Lake build parent"):
            candidates_from_traces(self.root)

    def test_report_acceptance_and_explicit_rejection(self):
        p = self.make_report(
            {"module": "Domain.Bad", "accepted": False},
            {"module": "Domain.Good", "accepted": True,
             "input_hash": "c" * 16, "archive": "a" * 16 + ".ltar"}
        )
        successes, missing = read_report(p, ["Domain.Good", "Domain.Bad"])
        self.assertEqual([r["module"] for r in successes], ["Domain.Good"])
        self.assertEqual(missing, [])

    def test_missing_report_row_never_implies_acceptance(self):
        p = self.make_report({"module": "Domain.Bad", "accepted": False})
        accepted, missing = read_report(p, ["Domain.Bad", "Domain.Good"])
        self.assertEqual(accepted, [])
        self.assertEqual(missing, ["Domain.Good"])

    def test_duplicate_accepted_row_refused(self):
        row = {"module": "Domain.Good", "accepted": False}
        p = self.make_report(row, row)
        with self.assertRaisesRegex(ValueError, "repeated"):
            read_report(p, ["Domain.Good"])

    def test_unrequested_report_row_refused(self):
        p = self.make_report({"module": "Domain.Bad", "accepted": False})
        with self.assertRaisesRegex(ValueError, "unknown"):
            read_report(p, ["Domain.Good"])

    def test_malformed_success_identity_refused(self):
        for identity in [
            {"input_hash": "x", "archive": "a" * 16 + ".ltar"},
            {"input_hash": "b" * 16, "archive": "../a" + ".ltar"},
            {"input_hash": "b" * 16, "archive": "a" * 16 + ".txt"},
            {"input_hash": "b" * 16, "archive": "a" * 17 + ".ltar"},
        ]:
            p = self.make_report({"module": "Domain.Good", "accepted": True, **identity})
            with self.subTest(identity=identity):
                with self.assertRaisesRegex(ValueError, "valid Lake artifact"):
                    read_report(p, ["Domain.Good"])

    def test_nonboolean_verdict_refused(self):
        p = self.make_report({"module": "Domain.Good", "accepted": 1})
        with self.assertRaisesRegex(ValueError, "invalid stock Lake decision"):
            read_report(p, ["Domain.Good"])

    def test_report_symlink_refused(self):
        p = self.make_report({"module": "Domain.Good", "accepted": False})
        linked = self.root / "linked.jsonl"
        linked.symlink_to(p)
        with self.assertRaisesRegex(ValueError, "oversized stock Lake report"):
            read_report(linked, ["Domain.Good"])


if __name__ == "__main__":
    unittest.main()
