#!/usr/bin/env python3
"""Measure source import branches feeding an RH proof interface, without
pretending that import reachability implies semantic theorem dependence.

For each direct import of a chosen module, compute the source modules
reachable *through that import*. Exclusive modules are those reachable
through exactly one direct import of the chosen module. This is a DAG
fingerprint useful for locating mathematical bottlenecks, NOT a measure
of provably removable source lines.

External packages (such as Mathlib) are excluded from the source DAG.
Unknown *local* import names and import cycles are rejected.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import json
from pathlib import Path

from import_closure import load_source


def analyze(imports: dict[str, list[str]], sizes: dict[str, int],
            root: str) -> dict:
    if root not in imports:
        raise ValueError(f"root module not found: {root}")
    if set(imports) != set(sizes):
        raise ValueError("import and source-size inventories differ")
    internal_prefixes = {name.split(".", 1)[0] for name in imports}
    unknown_internal = sorted({
        dep for values in imports.values() for dep in values
        if dep not in imports and dep.split(".", 1)[0] in internal_prefixes
    })
    if unknown_internal:
        raise ValueError(f"unresolved internal import names: {unknown_internal[:12]}")
    direct = sorted({x for x in imports[root] if x in imports})
    if not direct:
        raise ValueError("root has no resolvable local imports")
    direct_id = {m: i for i, m in enumerate(direct)}
    # Dependencies point from importing module to imported module.
    local_edges = {
        module: sorted({dep for dep in deps if dep in imports})
        for module, deps in imports.items()
    }
    indegree = Counter({module: 0 for module in imports})
    for deps in local_edges.values():
        for dep in deps:
            indegree[dep] += 1
    todo = deque(sorted(m for m, n in indegree.items() if n == 0))
    masks = {name: 1 << i for name, i in direct_id.items()}
    visited = 0
    while todo:
        module = todo.popleft()
        visited += 1
        mask = masks.get(module, 0)
        for dependency in local_edges[module]:
            if mask:
                masks[dependency] = masks.get(dependency, 0) | mask
            indegree[dependency] -= 1
            if indegree[dependency] == 0:
                todo.append(dependency)
    if visited != len(imports):
        cyclic = sorted(m for m, degree in indegree.items() if degree > 0)
        raise ValueError(f"source import DAG contains a cycle: {cyclic[:12]}")
    total_modules = [0] * len(direct)
    total_lines = [0] * len(direct)
    exclusive_modules = [0] * len(direct)
    exclusive_lines = [0] * len(direct)
    shared_modules = shared_lines = 0
    examples = defaultdict(list)
    for module, mask in masks.items():
        if not mask:
            continue
        if mask.bit_count() > 1:
            shared_modules += 1
            shared_lines += sizes[module]
        else:
            i = mask.bit_length() - 1
            exclusive_modules[i] += 1
            exclusive_lines[i] += sizes[module]
            examples[i].append((sizes[module], module))
        pending = mask
        while pending:
            bit = pending & -pending
            i = bit.bit_length() - 1
            total_modules[i] += 1
            total_lines[i] += sizes[module]
            pending ^= bit
    rows = [
        {
            "direct_import": module,
            "exclusive_modules": exclusive_modules[i],
            "exclusive_source_lines": exclusive_lines[i],
            "all_reachable_modules_through_import": total_modules[i],
            "all_reachable_source_lines_through_import": total_lines[i],
            "largest_exclusive_modules": [
                {"module": n, "physical_source_lines": lines}
                for lines, n in sorted(examples[i], reverse=True)[:8]
            ],
        }
        for module, i in direct_id.items()
    ]
    rows.sort(key=lambda row: (
        -row["exclusive_source_lines"],
        -row["all_reachable_source_lines_through_import"],
        row["direct_import"]
    ))
    return {
        "root_module": root,
        "all_source_modules_scanned": len(imports),
        "direct_imports": len(imports[root]),
        "distinct_local_direct_imports": len(direct),
        "shared_by_multiple_direct_imports": {
            "source_modules": shared_modules, "physical_source_lines": shared_lines
        },
        "unique_source_footprint": {
            "source_modules": len(masks),
            "physical_source_lines": sum(sizes[n] for n in masks)
        },
        "direct_import_footprints": rows,
        "method": "Source module dependency reachability, not kernel proof dependency.",
        "proof_status": (
            "No declaration removal, proof term rewrite, or theorem implication verified. "
            "Exclusive modules could still be semantically required."
        )
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", type=Path, default=Path("src"))
    ap.add_argument("--root", default=(
        "Development.AutomorphicArithmetic.CharacterBoxes."
        "EveryCharacterOfLiteratureOfVWin"
    ))
    ap.add_argument("--out", type=Path, default=Path(
        "analysis/rh-common-spine-direct-import-footprints.json"
    ))
    args = ap.parse_args()
    imports, sizes, warnings = load_source(args.src)
    if warnings:
        raise ValueError("unparsed source import syntax: " + str(warnings[:12]))
    result = analyze(imports, sizes, args.root)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items()
                      if k != "direct_import_footprints"}, indent=2))
    print(json.dumps(result["direct_import_footprints"][:12], indent=2))


if __name__ == "__main__":
    main()
