#!/usr/bin/env python3
"""Stock-Lean 4.33.1 recovery acceptance test on an isolated tiny Lake package.

This fixture intentionally never imports the 175,000-module RH corpus. It
checks that the pinned Lake no-build implementation accepts completed raw
artifacts, repacks a truncated LTAR, and rejects stale/corrupt outputs.
"""
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile

from rh_ci_recover import recovery_once


def cmd(cwd, *argv):
    proc = subprocess.run(argv, cwd=cwd, check=False, capture_output=True, text=True)
    if proc.returncode:
        raise AssertionError(
            f"command {argv} exited {proc.returncode}\n{proc.stdout}\n{proc.stderr}"
        )
    return proc.stdout


def main():
    here = Path(__file__).resolve().parent
    lean = Path(subprocess.check_output(["elan", "which", "lean"], text=True).strip())
    helper = here / "RHRecoverCompleted.lean"
    with tempfile.TemporaryDirectory(prefix="rh-lake-stock-") as temp:
        root = Path(temp) / "project"
        root.mkdir()
        (root / "src").mkdir()
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
        (root / "lakefile.toml").write_text(
            'name="recoveryFixture"\nsrcDir="src"\nplatformIndependent=true\n'
            'defaultTargets=["Proof"]\n[[lean_lib]]\nname="Proof"\n'
            'globs=["Fast", "Corrupt", "Stale"]\n'
        )
        (root / "lake-manifest.json").write_text(json.dumps({
            "version": "1.2.0", "packagesDir": ".lake/packages", "packages": []
        }) + "\n")
        (root / "src/Fast.lean").write_text("def fast : Nat := 42\n")
        (root / "src/Corrupt.lean").write_text("def corrupt : Nat := 1\n")
        (root / "src/Stale.lean").write_text("def stale : Nat := 1\n")
        cmd(root, "git", "init", "-q")
        cmd(root, "git", "config", "user.email", "fixture@example.invalid")
        cmd(root, "git", "config", "user.name", "Fixture")
        cmd(root, "git", "add", "src", "lakefile.toml", "lean-toolchain", "lake-manifest.json")
        cmd(root, "git", "commit", "-qm", "initial fixture")
        # Stock Lake builds genuine .olean/.ilean/C and archives the modules.
        print("fixture: compiling three real Lean 4.33.1 modules", flush=True)
        cmd(root, "lake", "build", "+Fast:ltar", "+Corrupt:ltar", "+Stale:ltar")
        fast_olean = root / ".lake/build/lib/lean/Fast.olean"
        fast_before = fast_olean.read_bytes()
        fast_pack = root / ".lake/build/ir/Fast.ltar"
        assert fast_pack.is_file()
        # Interrupted pack writes arbitrary partial bytes; stock Lake must
        # replace them, not accept their checksum as a valid packed archive.
        fast_pack.write_bytes(b"incomplete truncated LTAR from simulated interruption")
        # Corrupted completed output with a saved old trace must be rejected.
        corrupt_c = root / ".lake/build/ir/Corrupt.c"
        assert corrupt_c.is_file()
        with corrupt_c.open("ab") as stream:
            stream.write(b"\n/* mutated AFTER stock Lake saved the trace */\n")
        # Source is committed, but no new build of Stale has occurred.
        # Its previous trace must no longer match its current input.
        (root / "src/Stale.lean").write_text("def stale : Nat := 2\n")
        cmd(root, "git", "add", "src/Stale.lean")
        cmd(root, "git", "commit", "-qm", "invalidate Stale input")
        state = Path(temp) / "state"
        state.mkdir()
        print("fixture: stock Lake no-build pack and stale/corrupt rejection", flush=True)
        result = recovery_once(
            root, state, ["Fast", "Corrupt", "Stale"],
            lean=lean, helper=helper, workers=2,
        )
        if (result["accepted"], result["rejected"]) != (1, 2):
            raise AssertionError("incorrect acceptance: " + json.dumps(result, indent=2))
        if [x["module"] for x in result["artifacts"]] != ["Fast"]:
            raise AssertionError("only Fast may be recovered")
        if not fast_pack.is_file() or fast_pack.read_bytes().startswith(b"incomplete"):
            raise AssertionError("partial LTAR was not replaced")
        if fast_olean.read_bytes() != fast_before:
            raise AssertionError("recovery altered a finished proof object")
        if result["proof_verified"] is not False or result["artifact_published"] is not False:
            raise AssertionError("warm cache falsely claimed proof trust")
        print("PASS: completed Fast repacked, corrupt C rejected, stale source rejected", flush=True)


if __name__ == "__main__":
    main()
