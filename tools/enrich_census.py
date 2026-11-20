#!/usr/bin/env python3
"""Combine Lean declaration reachability with an exact physical source-line audit.

No module reported as unused here is proven safe to remove until the reduced
source rebuilds and its five theorems are independently kernel-checked.
"""
import argparse
import csv
import json
from pathlib import Path


def physical_lines(data: bytes) -> int:
    return data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))


def read_declarations(tsv: Path) -> dict[str, dict[str, int]]:
    result = {}
    columns = ("total", "expression_reachable", "block_reachable", "block_unreachable")
    with tsv.open(encoding="utf-8", newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            mod = row["module"]
            if mod in result:
                raise ValueError(f"duplicate module {mod}")
            counts = {k: int(row[k]) for k in columns}
            if not (0 <= counts["expression_reachable"] <= counts["block_reachable"] <= counts["total"]):
                raise ValueError(f"invalid reachability counts in {mod}")
            if counts["block_unreachable"] != counts["total"] - counts["block_reachable"]:
                raise ValueError(f"invalid unreachable count in {mod}")
            result[mod] = counts
    return result


def audit(src: Path, tsv: Path, output: Path) -> dict:
    decls = read_declarations(tsv)
    source = {}
    for path in sorted(src.rglob("*.lean")):
        mod = ".".join(path.relative_to(src).with_suffix("").parts)
        if mod in source:
            raise ValueError(f"duplicate module path: {mod}")
        source[mod] = physical_lines(path.read_bytes())
    missing = sorted(set(decls) - set(source))
    if missing:
        raise ValueError(f"declaration owners missing source files: {missing[:10]}")
    unknown = sorted(set(source) - set(decls))
    zero = sorted(n for n, s in decls.items()
                  if s["total"] > 0 and s["block_reachable"] == 0)
    report = {
        "source_files": len(source),
        "physical_source_lines": sum(source.values()),
        "declarations": sum(s["total"] for s in decls.values()),
        "expression_reachable": sum(s["expression_reachable"] for s in decls.values()),
        "block_reachable": sum(s["block_reachable"] for s in decls.values()),
        "block_unreachable": sum(s["block_unreachable"] for s in decls.values()),
        "zero_block_reachable_modules": len(zero),
        "candidate_whole_module_lines_upper_bound": sum(source[m] for m in zero),
        "unattributed_source_files": len(unknown),
        "unattributed_source_lines": sum(source[m] for m in unknown),
        "verified_prunable_lines": 0,
        "warning": "Reachability is necessary but not sufficient for source removal; "
                   "elaboration, instances, macros, imports and kernel rechecking remain."
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "rh-line-census.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    with (output / "rh-module-lines.tsv").open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f, delimiter="\t")
        w.writerow(("module", "source_lines", "total", "expression_reachable",
                    "block_reachable", "candidate_whole_module"))
        for mod, lines in sorted(source.items()):
            s = decls.get(mod)
            w.writerow((mod, lines, s["total"] if s else "",
                        s["expression_reachable"] if s else "",
                        s["block_reachable"] if s else "", int(mod in zero)))
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=Path("src"))
    parser.add_argument("--declarations", type=Path, default=Path("analysis/rh-declaration-modules.tsv"))
    parser.add_argument("--out", type=Path, default=Path("analysis"))
    args = parser.parse_args()
    print(json.dumps(audit(args.src, args.declarations, args.out), indent=2))


if __name__ == "__main__":
    main()
