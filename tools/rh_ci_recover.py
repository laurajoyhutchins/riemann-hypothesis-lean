#!/usr/bin/env python3
"""Recover stock-Lake-validated completed RH modules into local LTARs.

This is a manually invoked, externally sandboxed warm-build recovery step.
The trusted helper uses Lake's noBuild=true and trustHash=false and records
per-module acceptance. A returned LTAR is untrusted build output, NOT proof
verification or permission to publish. No network or artifact server is used.

The implementation follows the *mechanism* of the community RH recovery
without claiming to port its full trusted controller or publisher.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import time

from rh_ci_durable_build import atomic_json, directory, locked_file, make_directory
from rh_ci_identity import source_identity

MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
HASH16 = re.compile(r"[a-f0-9]{16}\.ltar\Z")
HASH = re.compile(r"[a-f0-9]{16}\Z")
MAX_CANDIDATES = 250000
MAX_REPORT_BYTES = 64 * 1024 * 1024


def regular_file(root: Path, relative: Path) -> Path:
    """Reject symlinks in any component, including traversed parents."""
    if relative.is_absolute() or any(p in (".", "..", "") for p in relative.parts):
        raise ValueError(f"unsafe artifact path {relative}")
    current = root
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(f"symlink in artifact path: {relative}")
    if not current.is_file():
        raise ValueError(f"missing artifact file: {relative}")
    if not stat.S_ISREG(current.stat().st_mode):
        raise ValueError(f"nonregular artifact: {relative}")
    return current


def module_file(name: str, extension: str) -> Path:
    if MODULE.fullmatch(name) is None:
        raise ValueError(f"invalid module name: {name!r}")
    return Path(*name.split(".")).with_suffix(extension)


def candidates_from_traces(workspace: Path) -> list[str]:
    base = workspace / ".lake/build/lib/lean"
    if base.is_symlink() or not base.is_dir():
        raise ValueError("no nonsymlink Lake output directory")
    found: set[str] = set()
    for parent, dirs, names in os.walk(base, followlinks=False):
        for name in dirs:
            if (Path(parent) / name).is_symlink():
                raise ValueError("symlink in Lake output tree")
        for name in names:
            if not name.endswith(".trace"):
                continue
            path = Path(parent) / name
            relative = path.relative_to(base)
            regular_file(base, relative)
            module = ".".join(relative.with_suffix("").parts)
            if MODULE.fullmatch(module) is None:
                raise ValueError(f"unexpected module trace path: {relative}")
            # Recover only root project's committed source, never Mathlib
            # or other externally supplied dependencies.
            source = module_file(module, ".lean")
            try:
                regular_file(workspace / "src", source)
            except ValueError:
                continue
            found.add(module)
            if len(found) > MAX_CANDIDATES:
                raise ValueError("unexpectedly large local module trace set")
    return sorted(found)


def explicit_candidates(workspace: Path, names: list[str]) -> list[str]:
    seen: set[str] = set()
    for name in names:
        if MODULE.fullmatch(name) is None:
            raise ValueError(f"invalid module name: {name}")
        regular_file(workspace / "src", module_file(name, ".lean"))
        seen.add(name)
    if not seen:
        raise ValueError("no modules requested for recovery")
    return sorted(seen)


def read_report(path: Path, requested: list[str]) -> tuple[list[dict], list[str]]:
    if path.is_symlink() or not path.is_file() or path.stat().st_size > MAX_REPORT_BYTES:
        raise ValueError("missing or oversized stock Lake report")
    accepted = []
    statuses: dict[str, bool] = {}
    expected = set(requested)
    for line in path.read_text().splitlines():
        row = json.loads(line)
        if not isinstance(row, dict):
            raise ValueError("invalid report row")
        name = row.get("module")
        verdict = row.get("accepted")
        if (name not in expected or name in statuses or type(verdict) is not bool):
            raise ValueError("unknown, repeated, or invalid stock Lake decision")
        statuses[name] = verdict
        if verdict:
            if (not isinstance(row.get("input_hash"), str)
                    or HASH.fullmatch(row["input_hash"]) is None
                    or not isinstance(row.get("archive"), str)
                    or HASH16.fullmatch(row["archive"]) is None):
                raise ValueError("accepted row lacks a valid Lake artifact identity")
            accepted.append(row)
    return accepted, sorted(expected - statuses.keys())


def hash_file(path: Path) -> str:
    stream = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            stream.update(block)
    return stream.hexdigest()


def recovery_once(
    workspace: Path, state_root: Path, names: list[str],
    *, lean: Path, helper: Path, workers: int = 4,
) -> dict:
    if workers < 1 or workers > 16:
        raise ValueError("worker count must be between 1 and 16")
    workspace = directory(workspace)
    state_root = make_directory(state_root)
    helper = helper.resolve(strict=True)
    if not helper.is_file():
        raise ValueError("missing trusted Lake helper")
    identity = source_identity(workspace)
    selected = explicit_candidates(workspace, names)
    # This is in addition to (not a replacement for) stock Lake traces:
    # the helper version is recorded with every local accepted-output report.
    helper_hash = hash_file(helper)
    prefix = hashlib.sha256(
        (str(workspace) + "\0" + identity["input_fingerprint"]).encode()
    ).hexdigest()
    output = make_directory(state_root / "stock-recovery")
    work = make_directory(output / prefix)
    lock = output / (hashlib.sha256(str(workspace).encode()).hexdigest() + ".lock")
    with locked_file(lock):
        req = work / "requested.json"
        report = work / "decisions.jsonl"
        if report.exists() and report.is_symlink():
            raise ValueError("unsafe previous report symlink")
        if req.exists() and req.is_symlink():
            raise ValueError("unsafe previous candidate symlink")
        # Previous outputs never imply this invocation succeeded.
        if report.exists():
            report.unlink()
        atomic_json(req, selected)
        lean = lean.resolve(strict=True)
        if not lean.is_file():
            raise ValueError("missing pinned Lean executable")
        lib = lean.parent.parent / "lib/lean/libLake_shared.so"
        if not lib.is_file():
            raise ValueError(f"missing same-toolchain Lake dynamic library: {lib}")
        cmd = [str(lean), "--load-dynlib=" + str(lib),
               "--run", str(helper), str(workspace), str(req),
               str(report), str(workers)]
        env = dict(os.environ)
        env["LAKE_ARTIFACT_CACHE"] = "false"
        env["LEAN_ABORT_ON_PANIC"] = "1"
        log = work / "lake-recover.log"
        if log.is_symlink():
            raise ValueError("unsafe recovery log")
        with log.open("ab") as stream:
            stream.write(("\n# stock no-build recovery: " + time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()) + "\n").encode())
            stream.flush()
            proc = subprocess.run(cmd, cwd=workspace, env=env,
                                  stdout=stream, stderr=subprocess.STDOUT)
        current = source_identity(workspace)
        if current["input_fingerprint"] != identity["input_fingerprint"]:
            raise ValueError("source/config inputs changed during recovery")
        # Lake's aggregate command may exit 3 when an individually reported
        # noBuild target is stale or corrupt. That is EXPECTED in a selective
        # recovery run; a successful per-module decision remains useful.
        # Every requested module must nevertheless have an explicit verdict.
        if proc.returncode not in (0, 3):
            tail = log.read_text(errors="replace")[-6000:]
            raise ValueError(
                f"stock Lake recovery exited {proc.returncode}; "
                f"report is NOT accepted. Diagnostic tail:\\n{tail}"
            )
        decisions, missing = read_report(report, selected)
        if missing:
            raise ValueError(f"stock Lake did not report {len(missing)} candidates")
        if proc.returncode != 0 and len(decisions) == len(selected):
            raise ValueError("stock Lake failed despite all modules reporting acceptance")
        receipts = []
        for item in decisions:
            module = item["module"]
            local = regular_file(
                workspace / ".lake/build/ir", module_file(module, ".ltar")
            )
            if local.stat().st_size == 0:
                raise ValueError(f"empty stock LTAR for {module}")
            trace = regular_file(
                workspace / ".lake/build/lib/lean", module_file(module, ".trace")
            )
            contents = json.loads(trace.read_text())
            if contents.get("depHash") != item["input_hash"]:
                raise ValueError(f"current trace identity differs for {module}")
            receipts.append({
                "module": module,
                "input_hash": item["input_hash"],
                "artifact": item["archive"],
                "local_ltar_sha256": hash_file(local),
            })
        # The result cannot claim proof validity. Output is retained in the
        # original Lake workspace, not exported to a public/shared cache.
        result = {
            "schema": 1,
            "repository": identity["repository"],
            "workspace": str(workspace),
            "source_tree": identity["source_tree"],
            "input_fingerprint": identity["input_fingerprint"],
            "helper_sha256": helper_hash,
            "requested": len(selected),
            "accepted": len(receipts),
            "rejected": len(selected) - len(receipts),
            "proof_verified": False,
            "artifact_published": False,
            "completed": True,
            "helper_exit_code": proc.returncode,
            "artifacts": receipts,
        }
        atomic_json(work / "receipt.json", result)
        return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--state-root", type=Path, required=True)
    parser.add_argument("--module", action="append", default=[])
    parser.add_argument("--scan-traces", action="store_true",
                        help="explicit opt-in: scan committed root modules with traces")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--lean", type=Path,
                        help="pinned toolchain lean binary (default: elan which lean)")
    parser.add_argument("--acknowledge-isolated-runner", action="store_true")
    args = parser.parse_args()
    if not args.acknowledge_isolated_runner:
        parser.error("must use an independently sandboxed runner; no isolation is installed by this script")
    if not args.scan_traces and not args.module:
        parser.error("provide --module or --scan-traces")
    try:
        workspace = directory(args.workspace)
        names = list(args.module)
        if args.scan_traces:
            names.extend(candidates_from_traces(workspace))
        lean = args.lean
        if lean is None:
            lean = Path(subprocess.check_output(
                ["elan", "which", "lean"], cwd=workspace, text=True
            ).strip())
        result = recovery_once(
            workspace, args.state_root, names, lean=lean,
            helper=Path(__file__).with_name("RHRecoverCompleted.lean"),
            workers=args.workers,
        )
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"stock Lake recovery refused: {exc}", file=sys.stderr)
        raise SystemExit(2) from exc
    print(json.dumps({key: value for key, value in result.items() if key != "artifacts"},
                     indent=2, sort_keys=True))
    if result["rejected"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
