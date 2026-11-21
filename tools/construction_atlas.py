#!/usr/bin/env python3
"""Source-attributed candidates for shared mathematical constructions in Lean.

This is a discovery index, never a proof equivalence checker or a line-saving
certificate. Only elaboration and Lean kernel checking can justify edits.
The scanner is intentionally narrow: column-zero theorem/lemma boundaries and
an explicit ':= by' marker. Unsupported declarations are left unclassified.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re

START = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+([^\s(:{]+)")
BOUNDARY = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|"
    r"instance|structure|class|inductive|opaque|axiom|example|"
    r"namespace|section|end|variable|open|attribute|set_option|"
    r"noncomputable\s+section)\b"
)
ANCHOR = re.compile(
    r"\b(?:GlobalTheory|ReciprocityTheory|Formalism|GroundTheory|"
    r"UpperTheory|Development|CategoryTheory|AlgebraicGeometry)"
    r"(?:\.[A-Za-z_][A-Za-z_0-9']*){1,}\b"
)
GENERATED = re.compile(r"(?:^|\.)(?:_simp_|_proof_|_match_|_eq_)[A-Za-z_0-9]*")
WS = re.compile(r"\s+")
TACTIC = re.compile(
    r"^\s*(?:[·|]\s*)?(?:case\s+\S+\s*)?"
    r"(have|let|show|suffices|obtain|rcases|rintro|intro|intros|"
    r"refine|exact|apply|rw|simp|simp_all|simpa|change|constructor|"
    r"ext|funext|congr|calc|unfold|dsimp|aesop|omega|linarith|"
    r"norm_num|ring|rfl|first|all_goals|next)\b"
)


def digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()[:20]


def scan(src: Path, root: str, min_lines: int) -> tuple[list[dict], dict]:
    base = src / root
    if not base.is_dir():
        raise ValueError(f"missing analysis subtree: {base}")
    records: list[dict] = []
    counters = Counter()
    for file in sorted(base.rglob("*.lean")):
        rel = file.relative_to(src).as_posix()
        rows = file.read_text(encoding="utf-8").splitlines()
        counters["files"] += 1
        counters["source_lines_scanned"] += len(rows)
        starts = [i for i, s in enumerate(rows) if BOUNDARY.match(s)]
        starts.append(len(rows))
        for a, b in zip(starts, starts[1:]):
            m = START.match(rows[a])
            if not m:
                continue
            counters["source_theorem_headers"] += 1
            text = "\n".join(rows[a:b])
            marker = text.find(":= by")
            if marker < 0:
                counters["unclassified_no_by_marker"] += 1
                continue
            if GENERATED.search(m.group(2)):
                counters["excluded_generated_name"] += 1
                continue
            pre = text[:marker]
            body = text[marker + len(":= by"):]
            body_rows = body.splitlines()
            proof_lines = len(body_rows) + 1
            if proof_lines < min_lines:
                counters["excluded_short_proof"] += 1
                continue
            # This is candidate source attribution, not an AST source range.
            tactics = [t.group(1) for line in body_rows if (t := TACTIC.match(line))]
            anchors = sorted(set(ANCHOR.findall(body)))
            rec = {
                "name": m.group(2),
                "path": "src/" + rel,
                "start_line": a + 1,
                "end_line": b,
                "candidate_proof_lines": proof_lines,
                "statement_digest": digest(WS.sub(" ", pre).strip()),
                "proof_digest": digest(WS.sub(" ", body).strip()),
                "tactic_shape_digest": digest(" ".join(tactics)),
                "tactic_count": len(tactics),
                "anchors": anchors,
            }
            records.append(rec)
            counters["candidate_source_proofs"] += 1
    return records, dict(counters)


def rank(records: list[dict], *, max_groups: int, min_members: int) -> dict:
    """Every proposed gain is an explicitly speculative upper bound."""
    exact = defaultdict(list)
    shapes = defaultdict(list)
    by_anchor = defaultdict(list)
    for i, r in enumerate(records):
        exact[r["proof_digest"]].append(i)
        if r["tactic_count"] >= 12:
            shapes[r["tactic_shape_digest"]].append(i)
        for anchor in r["anchors"]:
            by_anchor[anchor].append(i)

    groups = []
    def add_group(kind: str, key: str, ids: list[int]) -> None:
        if len(ids) < min_members:
            return
        members = [records[i] for i in ids]
        modules = {r["path"] for r in members}
        if len(modules) < 2:
            return
        statements = {r["statement_digest"] for r in members}
        if kind != "identical_proof_text" and len(statements) < 2:
            return
        lines = sum(r["candidate_proof_lines"] for r in members)
        largest = max(r["candidate_proof_lines"] for r in members)
        anchor_common = set(members[0]["anchors"])
        for r in members[1:]:
            anchor_common.intersection_update(r["anchors"])
        if kind == "matching_tactic_shape" and not anchor_common:
            return
        groups.append({
            "class": kind,
            "key": key,
            "declarations": len(members),
            "modules": len(modules),
            "distinct_statement_digests": len(statements),
            "candidate_total_proof_lines": lines,
            "hypothetical_reusable_body_upper_bound": lines - largest,
            "common_qualified_anchors": sorted(anchor_common)[:20],
            "representatives": [
                {k: r[k] for k in ("name", "path", "start_line", "end_line", "candidate_proof_lines")}
                for r in sorted(members, key=lambda r: (-r["candidate_proof_lines"], r["path"]))[:12]
            ],
            "caveat": "No mathematical equivalence or removable source lines proved",
        })

    for signature, ids in exact.items():
        add_group("identical_proof_text", signature, ids)
    for signature, ids in shapes.items():
        if len(ids) > 100:  # A ubiquitous skeleton does not identify a construction.
            continue
        add_group("matching_tactic_shape", signature, ids)
    # Rare shared qualified dependencies discover related proofs even when
    # their theorem types and tactic sequences differ. They are weaker evidence.
    for anchor, ids in by_anchor.items():
        if len(ids) <= 1 or len(ids) > 80:
            continue
        add_group("shared_qualified_dependency", anchor, ids)

    classes = Counter(g["class"] for g in groups)
    groups.sort(key=lambda g: (
        -g["hypothetical_reusable_body_upper_bound"],
        -g["modules"], g["class"], g["key"]
    ))
    # Reserve slots for each evidence class: otherwise the weak shared-anchor
    # groups crowd all exact-text and shared-shape families out of the report.
    classes_order = ("identical_proof_text", "matching_tactic_shape",
                     "shared_qualified_dependency")
    quota, remainder = divmod(max_groups, len(classes_order))
    chosen = []
    for index, klass in enumerate(classes_order):
        allowance = quota + (index < remainder)
        chosen.extend([g for g in groups if g["class"] == klass][:allowance])
    return {
        "groups_before_output_limit": len(groups),
        "group_counts_by_class": dict(classes),
        "output_limit": max_groups,
        "groups": chosen,
        "integrity": (
            "This is a candidate index from source heuristics. Groups overlap. "
            "Upper bounds cannot be added, are not estimates of realizable savings, "
            "and do not constitute theorem equivalence, source-audited reduction, "
            "Lean elaboration, kernel checking, or full certification."
        ),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", type=Path, default=Path("src"))
    ap.add_argument("--root", default="Development/AbelianVarietyTheory/Proofs")
    ap.add_argument("--min-lines", type=int, default=40)
    ap.add_argument("--min-members", type=int, default=2)
    ap.add_argument("--max-groups", type=int, default=100)
    ap.add_argument("--out", type=Path, default=Path("analysis/rh-construction-family-atlas.json"))
    args = ap.parse_args()
    if args.min_lines < 10 or args.min_members < 2 or args.max_groups < 1:
        ap.error("min-lines >= 10, min-members >= 2, max-groups >= 1 required")
    records, census = scan(args.src, args.root, args.min_lines)
    ranking = rank(records, max_groups=args.max_groups, min_members=args.min_members)
    report = {
        "scope": str(args.src / args.root),
        "method": "heuristic source-level fingerprints and qualified construction references",
        "census": census, **ranking,
        "verified_removed_lines": 0,
        "locally_kernel_verified_lines": 0,
        "independently_certified_lines": 0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("Census:", json.dumps(census, sort_keys=True))
    print("Candidate groups:", json.dumps(ranking["group_counts_by_class"], sort_keys=True))
    for klass in ("identical_proof_text", "matching_tactic_shape",
                  "shared_qualified_dependency"):
        selected = [g for g in ranking["groups"] if g["class"] == klass][:10]
        for group in selected:
            print(json.dumps({
                "class": group["class"], "key": group["key"],
                "modules": group["modules"],
                "distinct_statements": group["distinct_statement_digests"],
                "common_anchors": group["common_qualified_anchors"][:4],
                "hypothetical_upper_bound": group["hypothetical_reusable_body_upper_bound"],
                "representatives": [r["path"] for r in group["representatives"][:3]]
            }, sort_keys=True))


if __name__ == "__main__":
    main()
