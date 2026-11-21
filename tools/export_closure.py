#!/usr/bin/env python3
"""Stream declaration names from a pinned lean4export NDJSON proof export.

Input may be the full NDJSON stream or only name and declaration records,
filtered with grep -E '"in":|"thm":|"def":|"opaque":|"inductive":|"quot":|"axiom":'.

The exporter recursively visits *kernel dependencies* of its chosen
roots. Thus these records constitute an independently published, prebuilt
kernel dependency census. They are NOT sufficient to delete Lean source:
elaboration dependencies and declaration-to-source attribution are absent.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import gzip
import json
from pathlib import Path
import sys

ROOTS = {
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
}
KINDS = ("axiom", "def", "thm", "opaque", "quot", "inductive")


def exact_type_families(rows, names):
    """Group theorem types whose *exported Expr IDs* and universe params agree.

    The pinned exporter globally interns expressions, so a shared type ID
    witnesses syntactic identity of its exported kernel expression. Including
    the ordered level parameter IDs avoids an unsound universe equivalence.
    No definitional equality, proof-value identity, or safe source rewrite
    is inferred from different IDs or from a group alone.
    """
    counts = Counter((expr, levels) for _, expr, levels in rows)
    repeated = {key: count for key, count in counts.items() if count > 1}
    members = defaultdict(list)
    for name_id, expr, levels in rows:
        key = (expr, levels)
        if key in repeated:
            members[key].append(names[name_id])
    keys = sorted(repeated, key=lambda key: (-repeated[key], key))
    return repeated, members, keys


def consume(stream, *, require_roots: bool = True):
    # Name indices are assigned sequentially by the pinned exporter.
    names = [""]
    name_count = 0
    counts = Counter()
    prefixes = Counter()
    axioms = []
    roots_found = set()
    found_names = set()
    declaration_rows = []
    theorem_type_rows = []
    metadata = None
    for raw in stream:
        if not raw.strip():
            continue
        # Support raw files in smoke checks, as well as grep-filtered
        # production streams. The latter avoids JSON decoding expressions.
        if b'"in":' not in raw and not any(
            ('"' + k + '":').encode() in raw for k in KINDS
        ) and b'"meta":' not in raw:
            continue
        obj = json.loads(raw)
        if "meta" in obj:
            metadata = obj["meta"]
            continue
        if "in" in obj:
            ix = obj["in"]
            if ix != len(names):
                raise ValueError(f"name index out of sequence: {ix} != {len(names)}")
            if "str" in obj:
                v = obj["str"]
                parent, segment = v["pre"], v["str"]
            elif "num" in obj:
                v = obj["num"]
                parent, segment = v["pre"], str(v["i"])
            else:
                raise ValueError("unknown name constructor")
            if not 0 <= parent < len(names):
                raise ValueError(f"invalid parent name index: {parent}")
            names.append(names[parent] + ("." if names[parent] else "") + segment)
            name_count += 1
            continue

        def emit(n, kind, entry):
            if not isinstance(n, int) or not 0 <= n < len(names):
                raise ValueError(f"declaration references missing name id {n!r}")
            if n in found_names:
                raise ValueError(f"duplicate exported declaration {names[n]}")
            found_names.add(n)
            name = names[n]
            counts[kind] += 1
            prefixes[name.split(".", 1)[0]] += 1
            declaration_rows.append((name, kind))
            if kind == "axiom":
                axioms.append(name)
            if kind == "thm":
                type_expr = entry.get("type")
                levels = entry.get("levelParams")
                if not isinstance(type_expr, int) or type_expr < 0:
                    raise ValueError(f"bad theorem type expression index for {name}")
                if not isinstance(levels, list) or any(
                    not isinstance(v, int) or not 0 <= v < len(names) for v in levels
                ):
                    raise ValueError(f"bad theorem universe parameters for {name}")
                theorem_type_rows.append((n, type_expr, tuple(levels)))
                if name in ROOTS:
                    roots_found.add(name)

        if "inductive" in obj:
            ind = obj["inductive"]
            for aliases, kind in ((("types", "inductiveVals"), "inductive_type"),
                                  (("ctors", "constructorVals"), "constructor"),
                                  (("recs", "recursorVals"), "recursor")):
                entries = next((ind[k] for k in aliases if k in ind), [])
                for entry in entries:
                    emit(entry["name"], kind, entry)
            counts["inductive_blocks"] += 1
            continue
        for kind in KINDS[:-1]:
            if kind in obj:
                entries = obj[kind]
                if isinstance(entries, dict):
                    entries = [entries]
                if not isinstance(entries, list):
                    raise ValueError(f"unexpected {kind} declaration layout")
                for entry in entries:
                    emit(entry["name"], kind, entry)
                break
    if not declaration_rows:
        raise ValueError("export contains no declarations")
    if require_roots and roots_found != ROOTS:
        raise ValueError(f"five theorem targets absent: {sorted(ROOTS - roots_found)}")
    repeated, members, keys = exact_type_families(theorem_type_rows, names)
    type_index_report = {
        "comparison": "identical exported expression ID AND ordered level parameter IDs",
        "repeated_family_count": len(keys),
        "theorems_in_repeated_families": sum(repeated.values()),
        "largest_family_size": repeated[keys[0]] if keys else 0,
        "top_families": [
            {
                "type_expr": key[0],
                "level_params": [names[v] for v in key[1]],
                "size": repeated[key],
                "sample_members": sorted(members[key])[:12],
            }
            for key in keys[:30]
        ],
        "scope_warning": "Exported target closure, not all source theorems; no source deletions certified",
    }
    return {
        "report": {
            "export_metadata": metadata,
            "distinct_exported_names": name_count,
            "exported_declarations": len(declaration_rows),
            "by_kind": dict(sorted(counts.items())),
            "exact_type_index": type_index_report,
            "top_name_prefixes": prefixes.most_common(40),
            "axiom_names": sorted(axioms),
            "five_roots_found": sorted(roots_found),
            "semantics": "Dependency-closed target export; not a source elaboration slice",
            "kernel_replay_of_modified_source": "not performed",
            "verified_removable_lines": 0,
        },
        "declarations": declaration_rows,
        "type_families": [
            (key[0], [names[v] for v in key[1]], sorted(members[key]))
            for key in keys
        ],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output-dir", type=Path, default=Path("analysis"))
    p.add_argument("--allow-partial", action="store_true",
                   help="only for small lean4export sample fixtures")
    p.add_argument("--compressed-sha256", default=None)
    a = p.parse_args()
    result = consume(sys.stdin.buffer, require_roots=not a.allow_partial)
    report = result["report"]
    report["compressed_input_sha256"] = a.compressed_sha256
    a.output_dir.mkdir(parents=True, exist_ok=True)
    (a.output_dir / "rh-export-dependency-counts.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    with gzip.open(a.output_dir / "rh-export-reachable-names.tsv.gz", "wt",
                   encoding="utf-8", compresslevel=5) as out:
        out.write("name\tkind\n")
        for name, kind in sorted(result["declarations"]):
            out.write(f"{name}\t{kind}\n")
    with gzip.open(a.output_dir / "rh-export-identical-theorem-types.tsv.gz",
                   "wt", encoding="utf-8", compresslevel=5) as out:
        out.write("type_expr\tlevel_params\tfamily_size\tname\n")
        for expr, levels, member_names in result["type_families"]:
            for name in member_names:
                out.write(f"{expr}\t{','.join(levels)}\t{len(member_names)}\t{name}\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
