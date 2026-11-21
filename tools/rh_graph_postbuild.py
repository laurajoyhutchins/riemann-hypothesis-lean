#!/usr/bin/env python3
"""Extract from retained community RH build work without rebuilding the corpus.

This invokes the pinned community controller's existing Bubblewrap sandbox.
It is graph research, not proof verification or an unfiltered kernel closure.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess

from rh_ci_identity import source_identity
from rh_lean_graph import RH_ROOTS, generate_driver, verify_extractor
from validate_rh_lean_graph import publish_graphs

TRUSTED_COMMUNITY_COMMIT = "79c751e0b0a5ea3bbfc20198c852fa85f28661e6"
DEP_HASH = re.compile(r"[0-9a-f]{16}\Z")
RESULT_NAMES = tuple(root + ".json" for root in RH_ROOTS) + ("RH-combined.json",)
FIELDS = ("source_tree", "lakefile_sha256", "manifest_sha256", "toolchain")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def inspect_retained_build(candidate: Path, checkpoint_path: Path, state: Path) -> dict:
    """Require a staged source-matching community build and mapped Main output."""
    parent = (state / "failed-work").resolve(strict=True)
    if checkpoint_path.name != "checkpoint.json" or checkpoint_path.is_symlink():
        raise ValueError("select a retained community checkpoint.json")
    work = checkpoint_path.parent.resolve(strict=True)
    if work.parent != parent or not work.name.startswith("run-"):
        raise ValueError("checkpoint must be in the community durable work directory")
    record = json.loads(checkpoint_path.read_text())
    if (record.get("schema") != 1 or record.get("state") != "staged"
            or record.get("build_exit_code") != 0 or record.get("work") != str(work)):
        raise ValueError("build checkpoint is not a successfully staged full build")
    evidence = source_identity(candidate)
    built = record.get("identity")
    if not isinstance(built, dict) or any(evidence[field] != built.get(field) for field in FIELDS):
        raise ValueError("retained build does not match this checkout's proof/config inputs")
    project = work / "project"
    if (project / "src").is_symlink() or not (project / "src/Main.lean").is_file():
        raise ValueError("retained source project or Main.lean missing")
    if (sha256(project / "lakefile.toml") != built["lakefile_sha256"] or
            sha256(project / "lake-manifest.json") != built["manifest_sha256"] or
            (project / "lean-toolchain").read_text().strip() != built["toolchain"]):
        raise ValueError("retained build configuration was modified")
    olean = project / ".lake/build/lib/lean/Main.olean"
    trace = project / ".lake/build/lib/lean/Main.trace"
    if any(p.is_symlink() or not p.is_file() for p in (olean, trace)):
        raise ValueError("Main.olean/Main.trace not present in completed build")
    dep_hash = json.loads(trace.read_text()).get("depHash")
    if not isinstance(dep_hash, str) or not DEP_HASH.fullmatch(dep_hash):
        raise ValueError("Main trace has no valid Lake input hash")
    outputs = (work / "result/outputs.jsonl").read_text().splitlines()
    if not outputs or json.loads(outputs[0]) != "2026-03-17":
        raise ValueError("unsupported completed Lake outputs map")
    mappings = [json.loads(line) for line in outputs[1:]]
    matches = [pair[1] for pair in mappings
               if isinstance(pair, list) and len(pair) == 2 and pair[0] == dep_hash]
    if len(matches) != 1 or not re.fullmatch(r"[0-9a-f]{16}\.ltar", matches[0]):
        raise ValueError("Main trace is not represented exactly once in completed output map")
    archive = work / "cache/artifacts" / matches[0]
    if archive.is_symlink() or not archive.is_file():
        raise ValueError("mapped Main artifact archive is absent")
    return {
        "work": work,
        "source_tree": built["source_tree"],
        "build_commit": built["candidate_head"],
        "toolchain": built["toolchain"],
        "main_olean_sha256": sha256(olean),
        "main_trace_sha256": sha256(trace),
        "main_ltar_sha256": sha256(archive),
        "main_dep_hash": dep_hash,
    }


def load_trusted_controller(path: Path):
    if path.is_symlink() or path.name != "ci-build.py" or path.parent.name != "scripts":
        raise ValueError("untrusted community CI controller path")
    checkout = path.parent.parent
    actual = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    if actual != TRUSTED_COMMUNITY_COMMIT:
        raise ValueError("community CI controller is not at the pinned revision")
    # Compare the actual bytes we are about to import, including staged edits.
    expected_blob = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD:scripts/ci-build.py"],
        text=True).strip()
    actual_blob = subprocess.check_output(
        ["git", "hash-object", str(path)], text=True).strip()
    if expected_blob != actual_blob:
        raise ValueError("community CI controller bytes differ from pinned Git blob")
    spec = importlib.util.spec_from_file_location("trusted_rh_ci_build", path)
    if spec is None or spec.loader is None:
        raise ValueError("missing upstream community ci-build.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verify_retained_source(candidate: Path, project: Path, controller) -> str:
    """Reuse upstream's exact Git-blob snapshot audit for *all* proof inputs."""
    head = subprocess.check_output(
        ["git", "-C", str(candidate), "rev-parse", "--verify", "HEAD"],
        text=True).strip()
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        raise ValueError("candidate Git HEAD is invalid")
    # The checkpoint may name an earlier tooling commit with identical src
    # and build inputs. Verify against the current committed bytes instead.
    controller.verify_snapshot(candidate, head, project)
    return head


def parse_time_receipt(path: Path) -> dict:
    """Parse exact per-invocation GNU time measurements, refusing gaps."""
    rows = {}
    for line in path.read_text().splitlines():
        key, sep, value = line.partition("=")
        if not sep or key in rows:
            raise ValueError("invalid GNU time receipt")
        rows[key] = value
    if set(rows) != {"wall_seconds", "peak_rss_kib", "exit_status"}:
        raise ValueError("incomplete GNU time receipt")
    wall = float(rows["wall_seconds"])
    rss = int(rows["peak_rss_kib"])
    status = int(rows["exit_status"])
    if not 0 <= wall < float("inf") or rss < 1 or status != 0:
        raise ValueError("invalid or failed extraction resource measurement")
    return {
        "wall_seconds": wall,
        "peak_rss_kib": rss,
        "measurement_scope": "GNU time enclosing sandbox, Lake, and Lean; not only extractor",
    }


def extract(evidence: dict, *, candidate: Path, community: Path, extractor: Path,
            state: Path, depth: int, output: Path, jobs: int) -> dict:
    if depth < 1 or jobs < 1:
        raise ValueError("depth and jobs must be positive")
    work = evidence["work"]
    project, cache, result, control = (work / s for s in ("project", "cache", "result", "control"))
    if any((result / n).exists() for n in RESULT_NAMES):
        raise ValueError("previous graph JSON exists in retained result; refuse stale/overwrite")
    if not (control / "packages.json").is_file():
        raise ValueError("community sandbox package overrides missing")
    driver = result / "RHLeanGraph.lean"
    timing = result / "rh-graph-time.txt"
    if driver.exists() or timing.exists():
        raise ValueError("previous graph extraction driver or receipt exists")
    community_build = load_trusted_controller(community / "scripts/ci-build.py")
    verified_head = verify_retained_source(candidate, project, community_build)
    source = generate_driver(verify_extractor(extractor.read_bytes()), RH_ROOTS, depth)
    driver.write_text(source)
    elan_env = {key: os.environ[key] for key in ("PATH", "HOME", "ELAN_HOME")
                if key in os.environ}
    elan_env["ELAN_TOOLCHAIN"] = evidence["toolchain"]
    toolchain = Path(subprocess.check_output(
        ["elan", "which", "lean"], text=True, env=elan_env).strip()).parent.parent
    if not subprocess.check_output([str(toolchain / "bin/lean"), "--version"],
                                   text=True).startswith("Lean (version 4.33.1,"):
        raise ValueError("wrong Lean executable version")
    packages = state / "dependencies/.lake/packages"
    private = work / "dependency-builds"
    if not packages.is_dir() or not private.is_dir():
        raise ValueError("prepared community dependency views missing")
    cmd = community_build.sandbox(toolchain, project, packages, cache, result,
                                   control, jobs, private)
    # Lake discovers the project first. Only its child shell changes to the
    # writable result directory so upstream's JSON files are not discarded.
    cmd += ["/opt/lean/bin/lake", "--packages", "/control/packages.json", "env",
            "/bin/sh", "-c", "cd /work/result && exec /opt/lean/bin/lean RHLeanGraph.lean"]
    # RUSAGE_CHILDREN.ru_maxrss accumulates a high-water mark from unrelated
    # children. GNU time records this exact sandbox invocation instead.
    time_cmd = ["/usr/bin/time", "--format",
                "wall_seconds=%e\\npeak_rss_kib=%M\\nexit_status=%x",
                "--output", str(timing), *cmd]
    with (result / "rh-graph-lean.log").open("w") as log:
        completed = subprocess.run(time_cmd, stdout=log, stderr=subprocess.STDOUT,
                                   check=False)
    if completed.returncode:
        raise RuntimeError(f"upstream Lean extraction failed, exit {completed.returncode}; "
                           f"see {result / 'rh-graph-lean.log'}")
    if any(not (result / n).is_file() for n in RESULT_NAMES):
        raise ValueError("upstream Lean did not produce all five root and combined graphs")
    measured = parse_time_receipt(timing)
    receipt = publish_graphs(result, output, RH_ROOTS, depth,
                             source_revision=verified_head)
    receipt["retained_build"] = {
        k: str(v) if isinstance(v, Path) else v
        for k, v in evidence.items() if k != "work"
    }
    receipt["extraction_resources"] = measured
    receipt["retained_build"]["graph_checkout_commit"] = verified_head
    (output / "extraction-time.txt").write_bytes(timing.read_bytes())
    (output / "manifest.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    (output / "extraction.log").write_bytes((result / "rh-graph-lean.log").read_bytes())
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--community", type=Path, required=True)
    parser.add_argument("--extractor", type=Path, required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--preflight-only", action="store_true")
    args = parser.parse_args()
    evidence = inspect_retained_build(args.candidate, args.checkpoint, args.state)
    if args.preflight_only:
        print(json.dumps({k: str(v) for k, v in evidence.items()}, sort_keys=True))
    else:
        receipt = extract(evidence, candidate=args.candidate,
                          community=args.community, extractor=args.extractor,
                          state=args.state, depth=args.depth, output=args.output,
                          jobs=args.jobs)
        print(json.dumps({"files": len(receipt["graphs"]),
                          "nodes": receipt["graphs"]["RH-combined.json"]["nodes"]}))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError, RuntimeError, KeyError, json.JSONDecodeError) as exc:
        raise SystemExit(f"RH retained-build extraction refused: {exc}")
