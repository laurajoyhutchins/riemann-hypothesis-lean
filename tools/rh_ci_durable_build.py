#!/usr/bin/env python3
"""Experimental persistent *warm* Lean build runner (NOT proof verification).

Run this trusted controller only inside an independently configured sandbox on
persistent storage. It does NOT implement the community's sandbox, artifact
publisher, or stock-Lake raw-output recovery logic. It records honest state,
preserves the actual Lake workspace on interruption, and reruns stock Lake on
restart, leaving Lake itself to decide whether its outputs can be reused.

Reference: leanprover-community/riemann-hypothesis at 8ec38f92ac54b5c91bc07f4f6f88ea61691b7975,
scripts/ci-build.py and scripts/cache-bootstrap/RecoverCompleted.lean.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import time

from rh_ci_identity import canonical, source_identity

SCHEMA = 1
STATES = {"prepared", "building", "interrupted", "failed", "build_succeeded", "invalidated"}
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
MAX_JOURNAL = 1024 * 1024


def directory(path: Path) -> Path:
    """Reject unsafe or alien existing state directories."""
    if path.is_symlink() or not path.is_dir():
        raise ValueError(f"expected a nonsymlink directory: {path}")
    if path.stat().st_uid != os.getuid():
        raise ValueError(f"state directory must be owned by this runner: {path}")
    return path.resolve(strict=True)


def make_directory(path: Path) -> Path:
    if not path.exists() and not path.is_symlink():
        path.mkdir(mode=0o700, parents=True)
    return directory(path)


def regular_read(path: Path) -> bytes:
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        metadata = os.fstat(fd)
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_size > MAX_JOURNAL:
            raise ValueError(f"invalid checkpoint file: {path}")
        return os.read(fd, MAX_JOURNAL + 1)
    finally:
        os.close(fd)


def atomic_json(path: Path, record: dict) -> None:
    if path.exists() and path.is_symlink():
        raise ValueError(f"checkpoint symlink not allowed: {path}")
    data = canonical(record) + b"\n"
    if len(data) > MAX_JOURNAL:
        raise ValueError("oversized checkpoint")
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    fd = os.open(temporary, os.O_CREAT | os.O_EXCL | os.O_WRONLY | os.O_NOFOLLOW, 0o600)
    try:
        with os.fdopen(fd, "wb") as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
        dfd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(dfd)
        finally:
            os.close(dfd)
    finally:
        if temporary.exists():
            temporary.unlink()


@contextmanager
def locked_file(path: Path):
    fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        meta = os.fstat(fd)
        if not stat.S_ISREG(meta.st_mode) or meta.st_uid != os.getuid():
            raise ValueError("untrusted runner lock file")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError("another build is using this workspace or checkpoint") from exc
        yield
    finally:
        os.close(fd)


def decode_record(path: Path) -> dict:
    result = json.loads(regular_read(path))
    if not isinstance(result, dict) or result.get("schema") != SCHEMA:
        raise ValueError("invalid checkpoint schema")
    return result


def make_plan(workspace: Path, modules: list[str]) -> dict:
    if not modules or len(modules) > 256:
        raise ValueError("must supply 1..256 explicit Lean module roots")
    if any(MODULE.fullmatch(item) is None for item in modules):
        raise ValueError("invalid Lean module name")
    workspace = directory(workspace)
    identity = source_identity(workspace)
    roots = sorted(set(modules))
    return {
        "schema": SCHEMA,
        "workspace": str(workspace),
        "repository": identity["repository"],
        "input_fingerprint": identity["input_fingerprint"],
        "source_tree": identity["source_tree"],
        "toolchain": identity["toolchain"],
        "roots": roots,
    }


def plan_key(plan: dict) -> str:
    return hashlib.sha256(canonical(plan)).hexdigest()


def ensure_state(state_root: Path, plan: dict, *, cross_input: bool = False) -> tuple[Path, dict]:
    state_root = make_directory(state_root)
    runs = make_directory(state_root / "runs")
    workspaces = make_directory(state_root / "workspaces")
    workspace_key = hashlib.sha256(plan["workspace"].encode()).hexdigest()
    stamp_path = workspaces / (workspace_key + ".json")
    if stamp_path.exists() or stamp_path.is_symlink():
        previous = decode_record(stamp_path)
        if previous.get("workspace") != plan["workspace"]:
            raise ValueError("workspace stamp collision")
        if previous.get("input_fingerprint") != plan["input_fingerprint"] and not cross_input:
            raise ValueError(
                "different source/configuration in retained Lake workspace; "
                "use a fresh workspace, or explicitly opt in to untrusted Lake invalidation"
            )
    # This is a policy marker for warm-run isolation, not an artifact certificate.
    atomic_json(stamp_path, {
        "schema": SCHEMA, "workspace": plan["workspace"],
        "input_fingerprint": plan["input_fingerprint"],
        "proof_verified": False,
    })
    run_dir = make_directory(runs / plan_key(plan))
    journal_path = run_dir / "checkpoint.json"
    if journal_path.exists() or journal_path.is_symlink():
        record = decode_record(journal_path)
        if record.get("plan") != plan:
            raise ValueError("previous checkpoint is for different build inputs")
        if record.get("state") not in STATES:
            raise ValueError("unknown prior build state")
        if record["state"] in {"building", "invalidated"}:
            raise ValueError(
                "prior run may still be executing or its inputs changed; "
                "do not automatically adopt orphaned processes or outputs"
            )
        if record.get("proof_verified") is not False:
            raise ValueError("journal incorrectly claims proof verification")
    else:
        record = {
            "schema": SCHEMA, "plan": plan, "state": "prepared",
            "attempts": 0, "build_exit_code": None, "proof_verified": False,
        }
        atomic_json(journal_path, record)
    return run_dir, record


def write_state(run_dir: Path, record: dict, state: str, *, exit_code=None) -> None:
    if state not in STATES:
        raise ValueError("unrecognized state")
    record.update({
        "state": state, "build_exit_code": exit_code, "proof_verified": False,
        "controller_pid": os.getpid(), "updated_at_unix": int(time.time()),
    })
    atomic_json(run_dir / "checkpoint.json", record)


def run_build(
    workspace: Path, state_root: Path, modules: list[str],
    *, lake: str = "lake", cross_input: bool = False,
) -> int:
    """Use persistent original Lake outputs; never install our own cached proof bytes."""
    plan = make_plan(workspace, modules)
    state_root = make_directory(state_root)
    workspaces = make_directory(state_root / "workspaces")
    workspace_key = hashlib.sha256(plan["workspace"].encode()).hexdigest()
    # Serialize *every* build of one workspace, even with different roots.
    with locked_file(workspaces / (workspace_key + ".lock")):
        run_dir, record = ensure_state(state_root, plan, cross_input=cross_input)
        with locked_file(run_dir / "run.lock"):
            journal = run_dir / "checkpoint.json"
            # Recheck after acquiring the run lock.
            if decode_record(journal).get("state") in {"building", "invalidated"}:
                raise ValueError("cannot resume an unquiesced or invalidated run")
            record["attempts"] = record.get("attempts", 0) + 1
            write_state(run_dir, record, "building")
            interrupted = None
            child = None
            original_handlers = {}
            env = dict(os.environ)
            env["LEAN_ABORT_ON_PANIC"] = "1"
            env["LAKE_ARTIFACT_CACHE"] = "false"
            command = [lake, "build", *plan["roots"]]
            # No shell is used. A trusted external sandbox must contain Lean's
            # execution of untrusted source and generated initializers.
            try:
                with (run_dir / "build.log").open("ab") as log:
                    log.write((f"\n# attempt={record['attempts']} plan={plan_key(plan)}\n").encode())
                    log.flush()
                    os.fsync(log.fileno())
                    child = subprocess.Popen(
                        command, cwd=plan["workspace"], env=env, stdout=log,
                        stderr=subprocess.STDOUT, start_new_session=True,
                    )
                    def forward(signum, frame):
                        nonlocal interrupted
                        interrupted = signum
                        try:
                            os.killpg(child.pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                    for signum in (signal.SIGINT, signal.SIGTERM):
                        original_handlers[signum] = signal.signal(signum, forward)
                    try:
                        code = child.wait()
                    finally:
                        for signum, handler in original_handlers.items():
                            signal.signal(signum, handler)
                    if interrupted is not None:
                        # The process group should have exited after SIGTERM.
                        write_state(run_dir, record, "interrupted", exit_code=128 + interrupted)
                        return 128 + interrupted
                    # A successful exit is a build result, not an independent
                    # kernel replay nor a certificate about the RH theorem types.
                    newer = make_plan(Path(plan["workspace"]), plan["roots"])
                    if newer != plan:
                        write_state(run_dir, record, "invalidated", exit_code=code)
                        raise ValueError("build changed committed proof/config inputs")
                    write_state(
                        run_dir, record, "build_succeeded" if code == 0 else "failed",
                        exit_code=code,
                    )
                    return code
            except BaseException:
                if record["state"] == "building":
                    # SIGKILL cannot run this cleanup; its orphaned journal is
                    # intentionally not automatically resumable.
                    write_state(run_dir, record, "failed", exit_code=None)
                raise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True,
                        help="persistent committed candidate checkout; must survive job retries")
    parser.add_argument("--state-root", type=Path, required=True,
                        help="persistent state directory outside disposable CI workspace")
    parser.add_argument("--module", action="append", required=True)
    parser.add_argument("--lake", default="lake", help="trusted Lake executable; tests may inject a fixture")
    parser.add_argument("--allow-cross-input-reuse", action="store_true",
                        help="WARM LANE ONLY: delegate cross-revision output invalidation to stock Lake")
    parser.add_argument("--acknowledge-isolated-runner", action="store_true",
                        help="required: asserts the invoker configured process/network isolation")
    options = parser.parse_args()
    if not options.acknowledge_isolated_runner:
        parser.error("refusing to execute proof sources without acknowledged external isolation")
    try:
        code = run_build(
            options.workspace, options.state_root, options.module,
            lake=options.lake, cross_input=options.allow_cross_input_reuse,
        )
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"durable warm build refused: {exc}", file=sys.stderr)
        raise SystemExit(2) from exc
    raise SystemExit(code)


if __name__ == "__main__":
    main()
