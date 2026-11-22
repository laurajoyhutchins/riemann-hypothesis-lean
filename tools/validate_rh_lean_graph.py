#!/usr/bin/env python3
"""Validate and canonicalize upstream Lean Graph JSON, preserving explicit gaps.

Not a graph extractor or viewer. A closed emitted-edge graph is NOT a complete
Lean proof dependency graph because upstream filters types/instances by default.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

from rh_lean_graph import COMBINED_FILE, EXTRACTOR_BLOB_SHA, RH_ROOTS, UPSTREAM_COMMIT

CATEGORIES = {"Theorem", "Definition", "Axiom", "Other"}
FIELDS = {"name", "references", "constCategory", "constType"}


def inspect_graph(data: object, roots: tuple[str, ...]) -> tuple[list[dict], dict]:
    if not isinstance(data, list) or not data:
        raise ValueError("nonempty JSON node array required")
    nodes: dict[str, dict] = {}
    for node in data:
        if not isinstance(node, dict) or set(node) != FIELDS:
            raise ValueError("upstream node must have exactly four required fields")
        name = node["name"]
        refs = node["references"]
        if not isinstance(name, str) or not name or name in nodes:
            raise ValueError("empty or repeated node name")
        if (node["constCategory"] not in CATEGORIES
            or not isinstance(node["constType"], str)
            or not isinstance(refs, list)
            or any(not isinstance(r, str) or not r for r in refs)
            or len(refs) != len(set(refs))):
            raise ValueError(f"invalid category, type or references for {name}")
        nodes[name] = node
    for root in roots:
        if root not in nodes or nodes[root]["constCategory"] != "Theorem":
            raise ValueError(f"missing or non-theorem graph root: {root}")
    external = sorted({r for node in nodes.values()
                       for r in node["references"] if r not in nodes})
    canonical = [dict(name=name, references=sorted(nodes[name]["references"]),
                      constCategory=nodes[name]["constCategory"],
                      constType=nodes[name]["constType"])
                 for name in sorted(nodes)]
    return canonical, {
        "nodes": len(canonical),
        "edges_emitted": sum(len(n["references"]) for n in canonical),
        "external_reference_count": len(external),
        "external_references": external,
        "closed_under_emitted_edges": not external,
        "complete_lean_dependency_closure": False,
        "scope_warning": "Upstream regular extractor uses proof bodies, excludes instances by default, "
                         "and omits type-only references. Closure over emitted edges is weaker "
                         "than complete Lean declaration dependencies or proof AST coverage.",
    }


def read_validate(path: Path, roots: tuple[str, ...]) -> tuple[list[dict], dict]:
    return inspect_graph(json.loads(path.read_text(encoding="utf-8")), roots)


def publish_graphs(
    input_dir: Path, output_dir: Path, roots: tuple[str, ...],
    depth: int, require_closed: bool = False,
    source_revision: str = "unrecorded",
    combined: bool = True,
) -> dict:
    if depth < 1 or not roots or len(set(roots)) != len(roots):
        raise ValueError("invalid depth or roots")
    paths = [(root + ".json", (root,)) for root in roots]
    if combined:
        paths.append((COMBINED_FILE, roots))
    results = {}
    data_by_file = {}
    # Validate every input before writing anything, so malformed inputs don't
    # publish partly validated graph sets.
    for filename, expected in paths:
        canonical, stats = read_validate(input_dir / filename, expected)
        if require_closed and not stats["closed_under_emitted_edges"]:
            raise ValueError(f"{filename}: {stats['external_reference_count']} "
                             "external references remain; not a closed graph")
        data_by_file[filename] = canonical
        results[filename] = stats
    if combined:
        union = {n["name"]: n for n in data_by_file[COMBINED_FILE]}
        for root in roots:
            for node in data_by_file[root + ".json"]:
                if union.get(node["name"]) != node:
                    raise ValueError(f"combined graph does not contain identical {root} node "
                                     f"{node['name']}")
    output_dir.mkdir(parents=True, exist_ok=True)
    for filename, canonical in data_by_file.items():
        payload = (json.dumps(canonical, ensure_ascii=False, sort_keys=True,
                              separators=(",", ":")) + "\n").encode("utf-8")
        (output_dir / filename).write_bytes(payload)
        results[filename]["sha256"] = hashlib.sha256(payload).hexdigest()
        results[filename]["bytes"] = len(payload)
        # Huge graph frontiers should not dominate the receipt size.
        results[filename]["external_references_sample"] = results[filename].pop(
            "external_references")[:20]
    receipt = {
        "format": "patrik-cihal/lean-graph upstream node-array JSON",
        "extractor_commit": UPSTREAM_COMMIT,
        "extractor_blob_sha1": EXTRACTOR_BLOB_SHA,
        "extractor_theorem_value_patch": "constInfo.value? (allowOpaque := true)",
        "source_revision": source_revision,
        "roots": list(roots),
        "depth": depth,
        "strict_combined_node_recheck": combined,
        "coverage": "depth-bounded proof-body-only, instance-filtered",
        "full_proof_ast": False,
        "independent_kernel_verification": False,
        "graphs": results,
    }
    (output_dir / "manifest.json").write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=Path("."))
    parser.add_argument("--output-dir", type=Path, default=Path("analysis/lean-graph-json"))
    parser.add_argument("--root", action="append")
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--source-revision", default="unrecorded")
    parser.add_argument("--require-closed", action="store_true",
                        help="reject any dangling reference (NOT a full proof-closure assertion)")
    parser.add_argument("--no-combined", action="store_true")
    args = parser.parse_args()
    try:
        result = publish_graphs(args.input_dir, args.output_dir,
                                tuple(args.root) if args.root else RH_ROOTS,
                                args.depth, args.require_closed,
                                args.source_revision, not args.no_combined)
    except (ValueError, OSError, json.JSONDecodeError) as exc:
        parser.error(str(exc))
    for filename, stats in result["graphs"].items():
        print(f"{filename}: {stats['nodes']} nodes, {stats['edges_emitted']} edges, "
              f"{stats['external_reference_count']} external refs, "
              f"{stats['bytes']} bytes, sha256={stats['sha256']}")
    print("Note: emitted-edge closure does not establish complete Lean dependencies.")


if __name__ == "__main__":
    main()
