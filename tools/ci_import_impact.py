#!/usr/bin/env python3
"""Conservative reverse-import impact planner for RH source changes.

This is a *build planning* lower bound, NOT a proof certificate. The Lean
elaborator can depend on generated code, data, plugins, and non-import inputs;
every proof-source change still needs a successful Lean build and independent
kernel verification before it is considered proof-preserving.
"""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
import json
from pathlib import Path

from import_closure import load_source

GLOBAL_INPUTS = frozenset({"lakefile.toml", "lake-manifest.json", "lean-toolchain"})


def plan_impact(
    imports: dict[str, list[str]],
    sizes: dict[str, int],
    changed_paths: list[str],
) -> tuple[dict, list[str]]:
    """Return a conservative source-import *candidate* scope, not a verified closure."""
    if set(imports) != set(sizes):
        raise ValueError("imports and sizes must describe the same source modules")
    paths = sorted(set(changed_paths))
    changed_modules: set[str] = set()
    global_reasons: set[str] = set()
    for name in paths:
        if name in GLOBAL_INPUTS:
            global_reasons.add(name)
        if not name.startswith("src/"):
            continue
        relative = name.removeprefix("src/")
        if not relative or any(part in ("", ".", "..") for part in relative.split("/")):
            raise ValueError(f"invalid source path: {name!r}")
        if not name.endswith(".lean"):
            global_reasons.add(f"non-Lean source input: {name}")
            continue
        changed_modules.add(".".join(relative[:-5].split("/")))

    reverse: dict[str, set[str]] = defaultdict(set)
    local_roots = {name.partition(".")[0] for name in imports}
    unresolved: set[str] = set()
    for module, dependencies in imports.items():
        for dependency in dependencies:
            reverse[dependency].add(module)
            if dependency not in imports and (dependency.partition(".")[0] in local_roots or dependency in changed_modules):
                unresolved.add(dependency)

    # A missing internal import may be a deletion, but is *not* known to be
    # covered by the source graph. Treat it as a diagnostic, never an all-clear.
    if global_reasons:
        affected = set(imports)
    else:
        affected: set[str] = set()
        queue = deque(sorted(changed_modules))
        visited: set[str] = set()
        while queue:
            module = queue.popleft()
            if module in visited:
                continue
            visited.add(module)
            if module in imports:
                affected.add(module)
            queue.extend(sorted(reverse.get(module, ()) - visited))

    absent_changed = sorted(changed_modules - set(imports))
    report = {
        "classification": "source-import impact only; NOT a Lean build or kernel replay",
        "proof_verified": False,
        "changed_paths": paths,
        "changed_source_modules": sorted(changed_modules),
        "changed_modules_absent_from_head": absent_changed,
        "global_invalidation_reasons": sorted(global_reasons),
        "unresolved_local_imports": sorted(unresolved),
        "import_affected_modules": len(affected),
        "import_affected_physical_lines": sum(sizes[m] for m in affected),
        "total_source_modules": len(imports),
        "total_source_physical_lines": sum(sizes.values()),
        "interpretation": (
            "Candidates for incremental compilation, based only on explicit import "
            "edges. This does not certify completeness of elaboration dependencies, "
            "proof preservation, or equality of the five final theorem types."
        ),
    }
    return report, sorted(affected)


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--src", type=Path, required=True)
    p.add_argument("--changed-nul", type=Path, required=True,
                   help="NUL-delimited paths from git diff --name-only -z")
    p.add_argument("--out-dir", type=Path, required=True)
    args = p.parse_args()
    paths = [part.decode("utf-8") for part in args.changed_nul.read_bytes().split(b"\0") if part]
    imports, sizes, warnings = load_source(args.src)
    if warnings:
        raise ValueError("unrecognized Lean import syntax; cannot plan incrementally:\n"
                         + "\n".join(warnings[:20]))
    report, modules = plan_impact(imports, sizes, paths)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "rh-ci-import-impact.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / "rh-ci-import-affected-modules.txt").write_text(
        "".join(m + "\n" for m in modules), encoding="utf-8"
    )
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("changed_paths", "changed_source_modules",
                                     "unresolved_local_imports")}, indent=2))
    if report["unresolved_local_imports"]:
        raise SystemExit(
            "unresolved potentially local imports: no reliable incremental build scope "
            "(see report artifact)"
        )


if __name__ == "__main__":
    main()
