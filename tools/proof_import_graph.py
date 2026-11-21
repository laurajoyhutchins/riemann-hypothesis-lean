#!/usr/bin/env python3
"""Conservative Lean module-import graph, NOT a theorem/constant dependency graph.

Run on a complete checkout:
  python3 tools/proof_import_graph.py src --root Main --root MainMinimal \
    --output docs/generated/import-summary.json

No third-party Python packages are needed. Exit nonzero on missing local roots,
ambiguous imports, duplicate modules, unreadable files, or unresolved modules.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys

MODULE_RE = re.compile(r"^[\w\u0080-\uffff'.]+$", flags=re.UNICODE)
IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(?:all\s+)?(.+)$")
DEFAULT_EXTERNAL_ROOTS = ("Mathlib", "Lean", "Std", "Init", "Lake", "Batteries", "Aesop", "Qq")


class GraphError(Exception):
    """Incomplete or ambiguous source inventory."""


@dataclass(frozen=True)
class Module:
    path: str
    lines: int
    imports: tuple[str, ...]


def uncomment_line(line: str, depth: int) -> tuple[str, int]:
    """Handle Lean's nested block comments and -- end-of-line comments.

    This scanner is only used while reading the pre-command import header; Lean
    syntax containing string literals after that header is outside its scope.
    """
    chars: list[str] = []
    i = 0
    while i < len(line):
        if line.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and line.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif line.startswith('--', i):
            break
        else:
            chars.append(line[i])
            i += 1
    return ''.join(chars).strip(), depth


def header_imports(source: str, module: str) -> tuple[str, ...]:
    imports: list[str] = []
    depth = 0
    for number, line in enumerate(source.splitlines(), 1):
        code, depth = uncomment_line(line, depth)
        if not code or code == 'prelude':
            continue
        match = IMPORT_RE.fullmatch(code)
        if match:
            target = match.group(1).strip()
            if not MODULE_RE.fullmatch(target):
                raise GraphError(f"{module}:{number}: unsupported import syntax: {code!r}")
            imports.append(target)
            continue
        # Lean imports occur in a header. Ignore declarations and proof bodies.
        break
    return tuple(dict.fromkeys(imports))


def inventory(source_root: Path) -> dict[str, Module]:
    if not source_root.is_dir():
        raise GraphError(f"source directory does not exist: {source_root}")
    modules: dict[str, Module] = {}
    paths = sorted(source_root.rglob('*.lean'))
    if not paths:
        raise GraphError(f"no Lean files found under {source_root}")
    for path in paths:
        name = '.'.join(path.relative_to(source_root).with_suffix('').parts)
        if name in modules:
            raise GraphError(f"duplicate Lean module {name}")
        try:
            data = path.read_bytes()
            source = data.decode('utf-8')
        except (OSError, UnicodeError) as exc:
            raise GraphError(f"cannot read {path}: {exc}") from exc
        lines = source.count('\n') + int(bool(source) and not source.endswith('\n'))
        modules[name] = Module(str(path.relative_to(source_root.parent)), lines,
                               header_imports(source, name))
    return modules


def closure(root: str, modules: dict[str, Module]) -> set[str]:
    if root not in modules:
        raise GraphError(f"root module {root!r} not found under src directory")
    seen: set[str] = set()
    work = [root]
    while work:
        name = work.pop()
        if name in seen:
            continue
        seen.add(name)
        work.extend(d for d in modules[name].imports if d in modules and d not in seen)
    return seen


def report(modules: dict[str, Module], roots: list[str], externals: set[str]) -> dict:
    unresolved: list[dict[str, str]] = []
    external_edges = 0
    local_edges = 0
    consumers: dict[str, int] = defaultdict(int)
    for name in sorted(modules):
        for dep in modules[name].imports:
            if dep in modules:
                local_edges += 1
                consumers[dep] += 1
            elif dep.partition('.')[0] in externals:
                external_edges += 1
            else:
                unresolved.append({'module': name, 'import': dep})
    if unresolved:
        example = ', '.join(f"{x['module']} -> {x['import']}" for x in unresolved[:6])
        raise GraphError(f"{len(unresolved)} unresolved imports; first: {example}; "
                         "add verified external roots with --external-root")
    root_sets = {root: closure(root, modules) for root in roots}
    total_lines = sum(m.lines for m in modules.values())
    closures = {}
    for root, names in root_sets.items():
        closures[root] = {
            'files': len(names),
            'lines': sum(modules[name].lines for name in names),
            'nonroot_files': len(names) - 1,
            'nonroot_lines': sum(modules[name].lines for name in names if name != root),
        }
    result: dict = {
        'graph_kind': 'Lean local module import graph; not elaborated declaration dependencies',
        'source_files': len(modules), 'source_lines': total_lines,
        'local_import_edges': local_edges, 'external_import_edges': external_edges,
        'external_roots': sorted(externals),
        'closures': closures,
        'top_direct_import_consumers': [
            {'module': name, 'direct_consumers': n}
            for name, n in sorted(consumers.items(), key=lambda kv: (-kv[1], kv[0]))[:20]
        ],
    }
    if len(root_sets) == 2:
        a, b = root_sets.keys()
        # Exclude the two entrypoint files when comparing imported dependencies.
        a_imports = root_sets[a] - {a}
        b_imports = root_sets[b] - {b}
        result['import_comparison'] = {
            'left': a, 'right': b,
            'only_left': sorted(a_imports - b_imports),
            'only_right': sorted(b_imports - a_imports),
            'only_left_lines': sum(modules[n].lines for n in a_imports - b_imports),
            'only_right_lines': sum(modules[n].lines for n in b_imports - a_imports),
        }
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('src', nargs='?', type=Path, default=Path('src'))
    parser.add_argument('--root', action='append', required=True,
                        help='Lean module name, e.g. Main (repeat to compare)')
    parser.add_argument('--external-root', action='append', default=[],
                        help='Verified nonlocal package prefix; repeat as needed')
    parser.add_argument('--output', type=Path, help='Write deterministic JSON summary')
    parser.add_argument('--graph-json', type=Path,
                        help='Also export every local module and its imports as JSON')
    args = parser.parse_args(argv)
    try:
        mods = inventory(args.src)
        data = report(mods, args.root, set(DEFAULT_EXTERNAL_ROOTS) | set(args.external_root))
    except GraphError as exc:
        print(f"graph incomplete: {exc}", file=sys.stderr)
        return 2
    output = json.dumps(data, ensure_ascii=False, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding='utf-8')
    else:
        print(output, end='')
    if args.graph_json:
        detail = {name: {'path': mod.path, 'lines': mod.lines,
                         'imports': list(mod.imports)} for name, mod in sorted(mods.items())}
        args.graph_json.parent.mkdir(parents=True, exist_ok=True)
        args.graph_json.write_text(json.dumps(detail, ensure_ascii=False, sort_keys=True,
                                              indent=2) + '\n', encoding='utf-8')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
