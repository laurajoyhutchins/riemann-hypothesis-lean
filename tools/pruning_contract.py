#!/usr/bin/env python3
"""Check the source-level invariants of a *proposed* six-file RH pruning.

This is a source and import DAG check, never a Lean kernel certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path

from import_closure import load_source, transitive_modules


def verify_proof_refactors(source: Path, entries: list[dict]) -> int:
    """Check every intended proof-sharing change at the exact Git blob identity.

    This witnesses physical source accounting only. It cannot certify Lean
    theorem types, proof elaboration, or independent kernel checking.
    """
    paths = [row["path"] for row in entries]
    if len(paths) != len(set(paths)):
        raise ValueError("duplicate proof refactor path")
    savings = 0
    for row in entries:
        relative = row["path"]
        if not relative.startswith("src/") or not relative.endswith(".lean"):
            raise ValueError(f"invalid proof refactor path: {relative}")
        current = source.parent / relative
        if not current.is_file():
            raise ValueError(f"proof refactor source missing: {relative}")
        raw = current.read_bytes()
        blob_sha = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if blob_sha != row["current_blob_sha"]:
            raise ValueError(f"proof refactor blob drift: {relative}")
        current_lines = raw.count(b"\n") + int(bool(raw) and not raw.endswith(b"\n"))
        if current_lines != row["current_lines"]:
            raise ValueError(f"proof refactor line drift: {relative}")
        original_lines = row["original_lines"]
        if original_lines < current_lines:
            raise ValueError(f"proof refactor expanded source: {relative}")
        if len(row["original_blob_sha"]) != 40 or not row.get("declaration"):
            raise ValueError(f"unreviewed proof refactor: {relative}")
        savings += original_lines - current_lines
    return savings


def verify(source: Path, manifest_path: Path) -> dict:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    names = manifest["modules"]
    removed = [r["path"] for r in names]
    if len(removed) != len(set(removed)):
        raise ValueError("duplicate removal path")
    if any(not path.startswith("src/") or not path.endswith(".lean") for path in removed):
        raise ValueError("invalid removal path")
    if sum(r["lines"] for r in names) != 286 or len(names) != 6:
        raise ValueError("unexpected removal batch; require fresh reviewed contract")
    for relative in removed:
        if (source.parent / relative).exists():
            raise ValueError(f"candidate not removed: {relative}")

    imports, sizes, warnings = load_source(source)
    if warnings:
        raise ValueError(f"unrecognized import syntax: {warnings[:5]}")
    project_prefixes = (
        "BuildAid", "CompanionTheory", "Development", "Formalism",
        "GroundTheory", "Lemmata", "PositivityTheory",
        "ReciprocityTheory", "Supplements", "Statements", "Main",
    )
    missing = sorted(
        {dep for dependencies in imports.values() for dep in dependencies
         if dep.split(".", 1)[0] in project_prefixes and dep not in imports}
    )
    if missing:
        raise ValueError(f"project imports without source modules: {missing[:10]}")
    reached = transitive_modules(imports, "Main")
    if reached != set(imports):
        raise ValueError(f"unreachable modules remain: {len(imports) - len(reached)}")
    refactors = manifest.get("proof_refactors", [])
    proof_sharing_savings = verify_proof_refactors(source, refactors)
    expected_count = manifest["baseline_files"] - len(names)
    expected_lines = manifest["baseline_lines"] - sum(row["lines"] for row in names) - proof_sharing_savings
    observed_lines = sum(sizes.values())
    if len(sizes) != expected_count or observed_lines != expected_lines:
        raise ValueError(
            f"source inventory mismatch: files {len(sizes)} != {expected_count}; "
            f"lines {observed_lines} != {expected_lines}"
        )
    return {
        "baseline_commit": manifest["baseline_commit"],
        "source_files": len(sizes),
        "source_lines": observed_lines,
        "reachable_import_modules": len(reached),
        "actual_removed_files": len(names),
        "actual_removed_physical_lines": sum(row["lines"] for row in names),
        "source_only_proof_sharing_reduction": proof_sharing_savings,
        "source_only_total_reduction_from_original_baseline": manifest["baseline_lines"] - observed_lines,
        "full_lean_build": "not checked",
        "kernel_verification": "not checked",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=Path("src"))
    parser.add_argument("--manifest", type=Path, default=Path("tools/pruning_contract.json"))
    parser.add_argument("--out", type=Path, default=Path("analysis/rh-pruned-tree.json"))
    args = parser.parse_args()
    report = verify(args.src, args.manifest)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
