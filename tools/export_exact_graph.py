#!/usr/bin/env python3
"""Exact *declaration reachability* from the official lean4export NDJSON stream.

Unlike export_closure.py (a declaration inventory), this tool consumes Expr
records and follows constant references in checked types AND proof values.

It builds a 16-byte/Expr disk-backed DAG. No 61GB text extraction or large
in-memory Expr dictionary is required. An exported declaration absent from
the five-root union is NOT automatically safe to delete from Lean source:
unexported elaboration dependencies and extra exporter roots still matter.

Run ONLY on a pinned official export whose hash has been checked separately:
    zstd -d --long=30 -c solution.ndjson.zst |
        python3 tools/export_exact_graph.py --output-dir analysis/exact
"""
from __future__ import annotations

import argparse
from collections import Counter
import gzip
import json
import mmap
from pathlib import Path
import struct
import sys
import tempfile

ROOTS = (
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
)

# (referenced Name ID, up to 3 child Expr IDs + 1). Zero means absent.
RECORD = struct.Struct("<IIII")
KINDS = ("axiom", "def", "thm", "opaque", "quot")


def expr_record(obj, index):
    """Return the direct name reference and expression DAG edges."""
    if obj.get("ie") != index:
        raise ValueError(f"nonconsecutive expression ID {obj.get('ie')}, expected {index}")
    n, ch = 0, ()
    if "const" in obj:
        n = obj["const"]["name"]
    elif "proj" in obj:
        n = obj["proj"]["typeName"]
        ch = (obj["proj"]["struct"],)
    elif "app" in obj:
        ch = (obj["app"]["fn"], obj["app"]["arg"])
    elif "lam" in obj or "forallE" in obj:
        b = obj.get("lam", obj.get("forallE"))
        ch = (b["type"], b["body"])
    elif "letE" in obj:
        b = obj["letE"]
        ch = (b["type"], b["value"], b["body"])
    elif "mdata" in obj:
        ch = (obj["mdata"]["expr"],)
    elif not any(k in obj for k in ("bvar", "sort", "natVal", "strVal")):
        raise ValueError(f"unknown expression constructor at {index}: {list(obj)}")
    if not isinstance(n, int) or not 0 <= n < 2**32:
        raise ValueError(f"invalid Name ID in Expr {index}")
    if len(ch) > 3 or any(
        not isinstance(x, int) or x < 0 or x >= index or x + 1 >= 2**32 for x in ch
    ):
        raise ValueError(f"invalid Expr children at {index}: {ch}")
    return RECORD.pack(n, *((x + 1 for x in ch)), *([0] * (3 - len(ch))))


def analyze(stream, roots=ROOTS, *, compressed_sha256=None):
    """Consume input and return a compact report plus reachable name rows.

    All expression data is kept in an anonymous on-disk temporary file,
    the five-root reachability markings use one byte per expression on disk.
    The Name and declaration indices occupy memory, not the Expr DAG.
    """
    rootset = set(roots)
    if len(rootset) != len(roots):
        raise ValueError("duplicate root names")
    names = [""]
    by_name = {}
    declared = {}
    metadata = None
    expr_count = 0
    expr_edges = 0
    const_exprs = 0
    extra_blocks = 0
    with tempfile.TemporaryFile() as graph:
        for raw in stream:
            if b'"ie":' in raw:
                obj = json.loads(raw)
                record = expr_record(obj, expr_count)
                graph.write(record)
                name, a, b, c = RECORD.unpack(record)
                expr_edges += bool(a) + bool(b) + bool(c)
                const_exprs += bool(name)
                expr_count += 1
                continue
            if b'"in":' not in raw and not any(
                ('"' + k + '":').encode() in raw for k in (*KINDS, "inductive", "meta")
            ):
                continue
            obj = json.loads(raw)
            if "meta" in obj:
                metadata = obj["meta"]
            elif "in" in obj:
                ix = obj["in"]
                if ix != len(names):
                    raise ValueError(f"nonconsecutive Name ID {ix}")
                value = obj.get("str", obj.get("num"))
                if value is None:
                    raise ValueError(f"unknown name constructor at {ix}")
                pre = value["pre"]
                if not 0 <= pre < ix:
                    raise ValueError(f"invalid Name parent {pre} at {ix}")
                segment = value.get("str", str(value.get("i")))
                name = names[pre] + ("." if names[pre] else "") + segment
                names.append(name)
                if name in rootset:
                    by_name[name] = ix
            else:
                if "inductive" in obj:
                    b = obj["inductive"]
                    entries = []
                    for keys, kind in (
                        (("types", "inductiveVals"), "inductive_type"),
                        (("ctors", "constructorVals"), "constructor"),
                        (("recs", "recursorVals"), "recursor"),
                    ):
                        for k in keys:
                            if k in b:
                                entries.extend((kind, x) for x in b[k])
                                break
                    group = tuple(e["name"] for _, e in entries)
                    extra_blocks += 1
                    for kind, entry in entries:
                        roots_exprs = [entry["type"]]
                        if kind == "recursor":
                            roots_exprs.extend(r["rhs"] for r in entry["rules"])
                        add_decl(declared, entry["name"], kind, roots_exprs, group,
                                 len(names), expr_count)
                else:
                    for kind in KINDS:
                        if kind not in obj:
                            continue
                        entries = obj[kind]
                        if isinstance(entries, dict):
                            entries = [entries]
                        group = tuple(e["name"] for e in entries) if kind == "quot" else ()
                        for entry in entries:
                            roots_exprs = [entry["type"]]
                            if kind in ("def", "opaque", "thm"):
                                roots_exprs.append(entry["value"])
                            siblings = tuple(entry.get("all", ())) + group
                            add_decl(declared, entry["name"], kind, roots_exprs, siblings,
                                     len(names), expr_count)
                        break
        if metadata is None:
            raise ValueError("no export metadata")
        if not declared or expr_count == 0:
            raise ValueError("empty export")
        absent = [r for r in roots if r not in by_name or by_name[r] not in declared]
        if absent:
            raise ValueError(f"theorem roots absent: {absent}")
        for r in roots:
            if declared[by_name[r]][0] != "thm":
                raise ValueError(f"root is not a theorem: {r}")
        graph.flush()
        with mmap.mmap(graph.fileno(), 0, access=mmap.ACCESS_READ) as dag:
            with tempfile.TemporaryFile() as seenfile:
                seenfile.truncate(expr_count)
                with mmap.mmap(seenfile.fileno(), expr_count, access=mmap.ACCESS_WRITE) as seen:
                    masks = {}
                    missing = set()
                    for i, root in enumerate(roots):
                        visit_root(by_name[root], 1 << i, declared, dag, seen, masks, missing)
        allmask = (1 << len(roots)) - 1
        union = sum(bool(mask) for mask in masks.values())
        by_root = {
            root: sum(bool(mask & (1 << i)) for mask in masks.values())
            for i, root in enumerate(roots)
        }
        exclusive = {
            root: sum(mask == (1 << i) for mask in masks.values())
            for i, root in enumerate(roots)
        }
        intersections = {
            roots[i] + " & " + roots[j]:
                sum((mask & (1 << i)) and (mask & (1 << j)) for mask in masks.values())
            for i in range(len(roots)) for j in range(i + 1, len(roots))
        }
        histogram = Counter(mask for mask in masks.values() if mask)
        kinds = Counter(declared[n][0] for n, mask in masks.items() if mask)
        report = {
            "export_metadata": metadata,
            "compressed_input_sha256": compressed_sha256,
            "roots": list(roots),
            "exported_declarations": len(declared),
            "exported_name_ids": len(names) - 1,
            "expression_nodes": expr_count,
            "expression_dag_edges": expr_edges,
            "expression_direct_name_refs": const_exprs,
            "inductive_blocks": extra_blocks,
            "per_root_declaration_count": by_root,
            "per_root_exclusive": exclusive,
            "pairwise_intersection_declarations": intersections,
            "all_five_intersection_declarations": histogram.get(allmask, 0),
            "union_of_five": union,
            "exported_declarations_outside_five_union": len(declared) - union,
            "union_by_kind": dict(sorted(kinds.items())),
            "membership_bitmask_counts": dict(sorted(histogram.items())),
            "unresolved_constant_ids": sorted(missing)[:100],
            "unresolved_constant_id_count": len(missing),
            "caveat": (
                "Exact expression-constant closure of five exported theorem types and values, "
                "with conservative mutual/inductive grouping. It is NOT a minimum Lean source "
                "slice and does NOT verify the modified fork or measure removable source lines."
            ),
        }
        members = [
            (names[n], declared[n][0], masks.get(n, 0))
            for n in declared
        ]
        members.sort()
        return report, members


def add_decl(declared, name_id, kind, exprs, group, name_count, expr_count):
    if not isinstance(name_id, int) or not 0 < name_id < name_count:
        raise ValueError(f"declaration name ID invalid: {name_id}")
    if name_id in declared:
        raise ValueError(f"duplicate declaration ID {name_id}")
    if any(not isinstance(e, int) or e < 0 or e >= expr_count for e in exprs):
        raise ValueError(f"out of range expression for declaration {name_id}")
    if any(not isinstance(n, int) or n < 0 or n >= name_count for n in group):
        raise ValueError(f"invalid mutual block name for declaration {name_id}")
    declared[name_id] = (kind, tuple(exprs), tuple(group))


def visit_root(root_id, bit, declared, dag, seen, masks, missing):
    # Tag 0 = declaration, tag 1 = Expr.
    stack = [(0, root_id)]
    while stack:
        kind, index = stack.pop()
        if kind == 0:
            old = masks.get(index, 0)
            if old & bit:
                continue
            info = declared.get(index)
            if info is None:
                missing.add(index)
                continue
            masks[index] = old | bit
            _, exprs, group = info
            stack.extend((1, e) for e in exprs)
            stack.extend((0, n) for n in group)
        else:
            old = seen[index]
            if old & bit:
                continue
            seen[index] = old | bit
            n, a, b, c = RECORD.unpack_from(dag, index * RECORD.size)
            if n:
                stack.append((0, n))
            if a:
                stack.append((1, a - 1))
            if b:
                stack.append((1, b - 1))
            if c:
                stack.append((1, c - 1))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--compressed-sha256")
    parser.add_argument("--root", action="append", help="override five roots for sample tests")
    args = parser.parse_args()
    report, members = analyze(
        sys.stdin.buffer, tuple(args.root) if args.root else ROOTS,
        compressed_sha256=args.compressed_sha256,
    )
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "rh-exact-root-closures.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    with gzip.open(args.output_dir / "rh-exact-root-membership.tsv.gz", "wt",
                   encoding="utf-8", compresslevel=5) as out:
        out.write("name\tkind\tmembership_bitmask\n")
        for name, kind, mask in members:
            out.write(f"{name}\t{kind}\t{mask}\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    if report["unresolved_constant_id_count"]:
        raise SystemExit("ERROR: export has references to declarations absent from export")


if __name__ == "__main__":
    main()
