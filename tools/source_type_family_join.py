#!/usr/bin/env python3
"""Join source theorem ranges to exact checked-type groups in a pinned export.

The external export is from the original independently checked proof, not
necessarily the current edited source tree. Name attribution is conservative;
unresolved namespaces, private compiler names and ambiguous matches are not
guessed. Matching types do not prove that imports, proofs or source rewrites
can be changed safely. This is a discovery index only.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import gzip
import json
from pathlib import Path
import re

EXPECTED_EXPORT_SHA = "61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381"
BOUNDARY = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|"
    r"opaque|axiom|example|namespace|section|end|variable|open|"
    r"attribute|set_option)\b"
)
DECL = re.compile(
    r"^(?:(?:protected|noncomputable)\s+)*(theorem|lemma)\s+([^\s(:{]+)"
)
NAMESPACE = re.compile(r"^namespace\s+([^\s]+)")
SECTION = re.compile(r"^(?:noncomputable\s+)?section(?:\s+\S+)?\s*$")
END = re.compile(r"^end(?:\s+\S+)?\s*$")
GENERATED = re.compile(
    r"\._(?:simp|proof|match|eq|aux|uniq|inj|decr|sizeOf)[_.0-9]"
)


def load_export_types(type_tsv: Path, counts_json: Path) -> tuple[dict, dict]:
    if not type_tsv.is_file() or not counts_json.is_file():
        raise ValueError("required pinned export artifact files are absent")
    counts = json.loads(counts_json.read_text(encoding="utf-8"))
    if counts.get("compressed_input_sha256") != EXPECTED_EXPORT_SHA:
        raise ValueError("export artifact not bound to the pinned original export")
    by_name = {}
    ctr = Counter()
    with gzip.open(type_tsv, "rt", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f, delimiter="\t")
        if reader.fieldnames != ["type_expr", "level_params", "family_size", "name"]:
            raise ValueError(f"unknown type family TSV schema: {reader.fieldnames}")
        for row in reader:
            name = row["name"]
            ctr["exported_type_family_members"] += 1
            if name.startswith("_private.") or GENERATED.search(name):
                ctr["excluded_generated_or_private"] += 1
                continue
            if name in by_name:
                raise ValueError(f"duplicate exported theorem name: {name}")
            expr = int(row["type_expr"])
            size = int(row["family_size"])
            if expr < 0 or size < 2:
                raise ValueError(f"invalid family metadata for {name}")
            by_name[name] = (expr, row["level_params"], size)
    ctr["eligible_export_names"] = len(by_name)
    return by_name, dict(ctr)


def find_source_declarations(src: Path, root: str, type_index: dict) -> tuple[dict, dict]:
    base = src / root
    if not base.is_dir():
        raise ValueError(f"missing Lean source root: {base}")
    by_name = {}
    ambiguous = set()
    ctr = Counter()
    for file in sorted(base.rglob("*.lean")):
        ctr["scanned_modules"] += 1
        lines = file.read_text(encoding="utf-8").splitlines()
        ctr["scanned_source_lines"] += len(lines)
        starts = [i for i, line in enumerate(lines) if BOUNDARY.match(line)]
        starts.append(len(lines))
        namespace = []
        scopes = []
        for a, b in zip(starts, starts[1:]):
            line = lines[a]
            ns = NAMESPACE.match(line)
            if ns:
                previous = tuple(namespace)
                raw = ns.group(1)
                if raw.startswith("_root_."):
                    namespace[:] = raw.removeprefix("_root_.").split(".")
                else:
                    namespace.extend(raw.split("."))
                scopes.append(("namespace", previous))
                continue
            if SECTION.match(line):
                scopes.append(("section", tuple(namespace)))
                continue
            if END.match(line):
                if scopes:
                    _, previous = scopes.pop()
                    namespace[:] = previous
                else:
                    ctr["unmatched_end_commands"] += 1
                continue
            m = DECL.match(line)
            if not m:
                continue
            ctr["recognized_source_theorem_headers"] += 1
            name = m.group(2)
            if name.startswith("_root_."):
                candidates = [name.removeprefix("_root_.")]
            else:
                candidates = [".".join(namespace + [name]), name]
            hits = {candidate for candidate in candidates if candidate in type_index}
            if len(hits) != 1:
                if len(hits) > 1:
                    ctr["ambiguous_namespace_resolutions"] += 1
                continue
            full = next(iter(hits))
            segment = "\n".join(lines[a:b])
            marker = segment.find(":= by")
            if marker < 0:
                ctr["named_source_without_by_proof"] += 1
                continue
            proof_lines = len(segment[marker + len(":= by"):].splitlines()) + 1
            row = {
                "name": full,
                "path": "src/" + file.relative_to(src).as_posix(),
                "start_line": a + 1,
                "end_line": b,
                "proof_source_lines": proof_lines,
            }
            if full in by_name:
                ambiguous.add(full)
                ctr["ambiguous_duplicate_source_declarations"] += 1
            else:
                by_name[full] = row
    for name in ambiguous:
        by_name.pop(name, None)
    ctr["matched_export_names_to_unique_source_proofs"] = len(by_name)
    return by_name, dict(ctr)


def rank(source: dict, types: dict, *, min_lines: int, limit: int) -> dict:
    groups = defaultdict(list)
    for name, rec in source.items():
        key = types[name][:2]
        groups[key].append(rec)
    families = []
    for (expr, params), members in groups.items():
        if len(members) < 2:
            continue
        if len({r["path"] for r in members}) < 2:
            continue
        if max(r["proof_source_lines"] for r in members) < min_lines:
            continue
        donor = max(members, key=lambda r: r["proof_source_lines"])
        gross = sum(r["proof_source_lines"] for r in members) - donor["proof_source_lines"]
        families.append({
            "original_export_type_expr": expr,
            "original_export_level_params": params,
            "members_mapped_to_source": len(members),
            "source_modules": len({r["path"] for r in members}),
            "largest_proof_lines": donor["proof_source_lines"],
            "gross_body_text_upper_bound": gross,
            "representatives": sorted(
                members, key=lambda r: (-r["proof_source_lines"], r["path"])
            )[:16],
            "caveat": "Exact exported type, not validated reusable proof or source deletion",
        })
    families.sort(key=lambda r: (
        -r["gross_body_text_upper_bound"],
        -r["largest_proof_lines"],
        -r["members_mapped_to_source"],
    ))
    return {
        "qualified_families_before_limit": len(families),
        "gross_body_text_upper_bound_across_qualifying_families": sum(
            f["gross_body_text_upper_bound"] for f in families
        ),
        "families": families[:limit],
        "integrity": (
            "Exact checked-theorem type Expr ID + ordered universe parameters "
            "in the pinned original export; conservative source-name join to "
            "the current tree. Excludes private/generated names and ambiguous "
            "source attribution. No import compatibility, Lean elaboration, "
            "source reduction, kernel check, or certified savings implied."
        ),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", type=Path, default=Path("src"))
    ap.add_argument("--root", default="Development/AbelianVarietyTheory/Proofs")
    ap.add_argument("--types", type=Path, required=True)
    ap.add_argument("--counts", type=Path, required=True)
    ap.add_argument("--min-lines", type=int, default=40)
    ap.add_argument("--max-families", type=int, default=150)
    ap.add_argument("--out", type=Path, default=Path("analysis/rh-exact-type-source-families.json"))
    args = ap.parse_args()
    if args.min_lines < 1 or args.max_families < 1:
        ap.error("positive min-lines and max-families required")
    types, export_counts = load_export_types(args.types, args.counts)
    source, source_counts = find_source_declarations(args.src, args.root, types)
    output = rank(source, types, min_lines=args.min_lines, limit=args.max_families)
    output["export_census"] = export_counts
    output["source_census"] = source_counts
    output["source_scope"] = str(args.src / args.root)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in output.items() if k != "families"}, indent=2))
    print(json.dumps(output["families"][:8], indent=2))


if __name__ == "__main__":
    main()
