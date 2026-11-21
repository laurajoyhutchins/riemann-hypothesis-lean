#!/usr/bin/env python3
"""Conservative source import-DAG census for the original and experimental Main.

This measures *module* reachability, not theorem-declaration reachability.
A file outside Main's import closure is a candidate for removal only after
source rebuilding and independent kernel checking. Dynamic source generation
and nonstandard import syntax are flagged, not silently interpreted.
"""
import argparse
import json
import re
from collections import deque
from pathlib import Path

MODULE_TOKEN = re.compile(r"^[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*$")
IMPORT_LINE = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+(.+)$")


def physical_lines(raw: bytes) -> int:
    return raw.count(b"\n") + int(bool(raw) and not raw.endswith(b"\n"))


def parse_imports(raw: bytes, source: str) -> tuple[list[str], list[str]]:
    dependencies = []
    warnings = []
    # Imports in Lean normally occur in a header. We scan all lines so
    # unexpected placement remains visible rather than being discarded.
    for number, line in enumerate(raw.decode("utf-8").splitlines(), 1):
        match = IMPORT_LINE.match(line)
        if not match:
            continue
        rest = match.group(1).split("--", 1)[0].strip()
        if rest.startswith("all "):
            rest = rest[4:].strip()
        if not rest:
            warnings.append(f"{source}:{number}: empty import declaration")
        for token in rest.split():
            if MODULE_TOKEN.fullmatch(token):
                dependencies.append(token)
            else:
                warnings.append(f"{source}:{number}: unexpected import token {token!r}")
    return dependencies, warnings


def load_source(src: Path):
    imports: dict[str, list[str]] = {}
    sizes: dict[str, int] = {}
    warnings: list[str] = []
    for path in src.rglob("*.lean"):
        module = ".".join(path.relative_to(src).with_suffix("").parts)
        if module in imports:
            raise ValueError(f"duplicate source module: {module}")
        raw = path.read_bytes()
        imports[module], issues = parse_imports(raw, str(path))
        warnings.extend(issues)
        sizes[module] = physical_lines(raw)
    if not imports:
        raise ValueError(f"empty source tree: {src}")
    return imports, sizes, warnings


def transitive_modules(imports: dict[str, list[str]], root: str,
                       override: dict[str, list[str]] | None = None) -> set[str]:
    work = deque([root])
    seen = set()
    while work:
        module = work.popleft()
        if module not in imports or module in seen:
            continue
        seen.add(module)
        work.extend((override or {}).get(module, imports[module]))
    return seen


def compare(src: Path, out: Path, original_main_imports: list[str],
            require_original_all: bool = False) -> dict:
    imports, sizes, warnings = load_source(src)
    if "Main" not in imports:
        raise ValueError("Main.lean missing from source tree")
    if "Supplements.Kernels.MainTheorems" not in imports:
        raise ValueError("MainTheorems.lean missing from source tree")
    if warnings:
        raise ValueError("unknown import syntax; do not use truncated graph:\n" +
                         "\n".join(warnings[:20]))
    baseline = transitive_modules(imports, "Main", {"Main": original_main_imports})
    reduced = transitive_modules(imports, "Main")
    lost = sorted(baseline - reduced)
    newly_reached = sorted(reduced - baseline)
    summary = {
        "source_modules": len(imports),
        "source_lines": sum(sizes.values()),
        "original_reachable_modules": len(baseline),
        "experimental_reachable_modules": len(reduced),
        "candidate_removed_import_modules": len(lost),
        "candidate_removed_import_lines": sum(sizes[m] for m in lost),
        "newly_reachable_modules": len(newly_reached),
        "original_unreachable_modules": len(imports) - len(baseline),
        "experimental_unreachable_modules": len(imports) - len(reduced),
        "verified_removed_modules": 0,
        "verified_removed_source_lines": 0,
        "note": "Import closure only. Declarations, elaborator support, and kernel proof rechecking not yet measured.",
    }
    out.mkdir(parents=True, exist_ok=True)
    (out / "rh-import-closure.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    (out / "rh-import-pruning-candidates.tsv").write_text(
        "module\tphysical_lines\n" +
        "".join(f"{m}\t{sizes[m]}\n" for m in sorted(lost, key=lambda n: (-sizes[n], n)))
    )
    if require_original_all and len(baseline) != len(imports):
        raise ValueError(
            f"original Main closure only has {len(baseline)} of {len(imports)} modules; "
            "verify import syntax and baseline before interpreting savings"
        )
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=Path("src"))
    parser.add_argument("--out", type=Path, default=Path("analysis"))
    parser.add_argument(
        "--original-main-import",
        action="append",
        default=None,
        help="Original Main imports, repeated once per imported module",
    )
    parser.add_argument("--require-original-all", action="store_true")
    a = parser.parse_args()
    old = a.original_main_import or ["Statements", "Supplements.Kernels.MainTheoremsAll"]
    print(json.dumps(compare(a.src, a.out, old, a.require_original_all), indent=2))


if __name__ == "__main__":
    main()
