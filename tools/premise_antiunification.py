#!/usr/bin/env python3
"""Find exact conclusion templates with distinct source-level premises.

This scans source theorem headers, NOT elaborated Lean expressions. A candidate
(∀ binders, P → Q) / (∀ binders, P' → Q) needs a proof of P' → P to
reuse the first theorem. Without that proof it is *not* a valid refactor.
Do not count candidates as verified savings or even as a proven bound.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re

ROOT = "Development/AbelianVarietyTheory/Proofs"
START = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s(:{]+)")
BOUNDARY = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|"
    r"opaque|axiom|example|namespace|section|end|variable|open|"
    r"attribute|set_option)\b"
)
GENERATED = re.compile(r"(^_private\.|\._(?:simp|proof|match|aux|eq)[_.0-9])")
WS = re.compile(r"\s+")
OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSE = set(OPEN.values())


def top_level_positions(source: str) -> tuple[list[int], list[int]] | None:
    """Track Lean grouping in a statement; fail closed on malformed brackets.

    Does not parse all Lean syntax; its scope is a deliberately narrow
    source-level pattern, not a replacement for Lean's elaborator.
    """
    pending: list[str] = []
    commas: list[int] = []
    arrows: list[int] = []
    for i, ch in enumerate(source):
        if ch in OPEN:
            pending.append(OPEN[ch])
        elif ch in CLOSE:
            if not pending or ch != pending.pop():
                return None
        elif not pending and ch == ",":
            commas.append(i)
        elif not pending and ch == "→":
            arrows.append(i)
    if pending:
        return None
    return commas, arrows


def normal(s: str) -> str:
    return WS.sub(" ", s).strip()


def extract(header: str) -> tuple[str, str, str] | None:
    """Return (prefix, explicit premise, suffix) for one leading implication."""
    m = START.match(header)
    if not m:
        return None
    body = header[m.end():].strip()
    if not body.startswith(":"):
        return None
    body = body[1:].strip()
    pos = top_level_positions(body)
    if pos is None:
        return None
    commas, arrows = pos
    if not arrows or not commas:
        return None
    first_arrow = arrows[0]
    earlier_commas = [c for c in commas if c < first_arrow]
    if not earlier_commas:
        return None
    comma = earlier_commas[-1]
    prefix = normal(body[:comma+1])
    premise = normal(body[comma+1:first_arrow])
    suffix = normal(body[first_arrow+1:])
    if not prefix.startswith("∀ ") or not (3 <= len(premise) <= 500) or not suffix:
        return None
    # Nested arrows inside a grouped premise are allowed. Only the
    # top-level arrow, already isolated by top_level_positions, separates Q.
    return prefix, premise, suffix


def census(src: Path, *, root: str = ROOT) -> tuple[dict, dict]:
    base = src / root
    if not base.is_dir():
        raise ValueError(f"missing source subtree: {base}")
    groups = defaultdict(list)
    stats = Counter()
    for file in sorted(base.rglob("*.lean")):
        lines = file.read_text(encoding="utf-8").splitlines()
        stats["scanned_modules"] += 1
        stats["scanned_source_lines"] += len(lines)
        boundaries = [i for i, line in enumerate(lines) if BOUNDARY.match(line)]
        boundaries.append(len(lines))
        for a, b in zip(boundaries, boundaries[1:]):
            m = START.match(lines[a])
            if not m:
                continue
            stats["source_theorem_headers"] += 1
            if GENERATED.search(m.group(1)):
                stats["skipped_generated_names"] += 1
                continue
            declaration = "\n".join(lines[a:b])
            by = declaration.find(":= by")
            if by < 0:
                continue
            triple = extract(declaration[:by])
            if triple is None:
                continue
            prefix, premise, suffix = triple
            stats["qualified_implication_headers"] += 1
            key = hashlib.sha256((prefix + "\n→\n" + suffix).encode("utf-8")).hexdigest()
            groups[key].append({
                "name": m.group(1),
                "source_path": "src/" + file.relative_to(src).as_posix(),
                "source_line": a + 1,
                "end_line": b,
                "proof_source_lines": len(declaration[by + 5:].splitlines()) + 1,
                "premise": premise,
                "statement_prefix": prefix[:600],
                "statement_suffix": suffix[:600],
            })
    return groups, dict(stats)


def rank(groups: dict, *, limit: int = 150, min_proof: int = 40) -> dict:
    if limit < 1 or min_proof < 1:
        raise ValueError("positive family limit and minimum proof size required")
    families = []
    for digest, entries in groups.items():
        premises = {e["premise"] for e in entries}
        if len(premises) < 2 or len({e["source_path"] for e in entries}) < 2:
            continue
        if max(e["proof_source_lines"] for e in entries) < min_proof:
            continue
        members = sorted(entries, key=lambda e: (-e["proof_source_lines"],
                                                  e["source_path"], e["name"]))
        # Entire group may require new bridge proofs; this is a *gross*
        # source-length scale indicator, not an achievable upper bound.
        gross = sum(e["proof_source_lines"] for e in entries) - members[0]["proof_source_lines"]
        families.append({
            "template_sha256": digest,
            "members": len(entries),
            "distinct_premises": len(premises),
            "modules": len({e["source_path"] for e in entries}),
            "gross_body_text_scale_indicator": gross,
            "premises": sorted(premises)[:30],
            "source_witnesses": members[:18],
            "unproved_obligation": (
                "A theorem on one premise may replace another only if Lean "
                "checks the appropriate premise implication and the donor "
                "is available via an acyclic import."
            ),
        })
    families.sort(key=lambda f: (-f["gross_body_text_scale_indicator"],
                                 -f["members"], f["template_sha256"]))
    return {
        "qualifying_families_before_limit": len(families),
        "gross_body_text_scale_indicator_total": sum(
            f["gross_body_text_scale_indicator"] for f in families
        ),
        "families": families[:limit],
        "disclaimer": (
            "A source-level syntactic anti-unification search, NOT a Lean "
            "type equality or implication proof. The gross text number is "
            "not an upper bound on all source savings and not a claim that "
            "any candidate can be rewritten. No theorem changes are made."
        ),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", type=Path, default=Path("src"))
    ap.add_argument("--root", default=ROOT)
    ap.add_argument("--out", type=Path,
                    default=Path("analysis/rh-premise-antiunification.json"))
    ap.add_argument("--max-families", type=int, default=150)
    ap.add_argument("--min-proof-lines", type=int, default=40)
    args = ap.parse_args()
    groups, stats = census(args.src, root=args.root)
    report = rank(groups, limit=args.max_families,
                  min_proof=args.min_proof_lines)
    report["source_scan"] = stats
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items()
                      if k != "families"}, indent=2))
    print(json.dumps(report["families"][:8], indent=2))


if __name__ == "__main__":
    main()
