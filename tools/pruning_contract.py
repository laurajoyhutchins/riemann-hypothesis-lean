#!/usr/bin/env python3
"""Check the source-level invariants of a *proposed* six-file RH pruning.

This is a source and import DAG check, never a Lean kernel certificate.
"""
import argparse
import json
from pathlib import Path

from import_closure import load_source, transitive_modules


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
    expected_count = manifest["baseline_files"] - len(names)
    expected_lines = manifest["baseline_lines"] - sum(row["lines"] for row in names)
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
