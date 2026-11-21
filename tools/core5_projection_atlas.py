#!/usr/bin/env python3
"""Find source theorem interfaces related by a proved Core5 projection.

This is a *candidate index*. Hypothesis replacement is supported by the
existing Core5.of_core/Core5.of_char theorems, but import acyclicity, actual
Lean applications, axioms and kernel checks are separate obligations.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re

ROOT = "Development/AbelianVarietyTheory/Proofs"
BOUNDARY = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|"
    r"opaque|axiom|example|namespace|section|end|variable|open|"
    r"attribute|set_option)\b"
)
START = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma)\s+([^\s(:{]+)"
)
HYPOTHESES = (
    ("core", "GlobalTheory.Hk3.Core R F"),
    ("core5", "GlobalTheory.Core5 R F"),
    # Independent Prop-valued record with five matching fields. The constructor
    # maps are a mathematical candidate in PR #14, NOT a checked equivalence yet.
    ("core_no_chain", "GlobalTheory.Hk3.CoreNoChain R F"),
    ("char", "R.Char F"),
)
WS = re.compile(r"\s+")


def collect(src: Path, root: str = ROOT) -> tuple[list[dict], dict]:
    base = src / root
    if not base.is_dir():
        raise ValueError(f"missing source root: {base}")
    records: list[dict] = []
    stats = Counter()
    for file in sorted(base.rglob("*.lean")):
        rows = file.read_text(encoding="utf-8").splitlines()
        stats["scanned_modules"] += 1
        stats["scanned_source_lines"] += len(rows)
        starts = [i for i, line in enumerate(rows) if BOUNDARY.match(line)]
        starts.append(len(rows))
        for a, b in zip(starts, starts[1:]):
            m = START.match(rows[a])
            if not m:
                continue
            stats["scanned_theorem_headers"] += 1
            text = "\n".join(rows[a:b])
            pos = text.find(":= by")
            if pos < 0:
                continue
            original_header = text[:pos]
            matched = [
                (label, token) for label, token in HYPOTHESES
                if token in original_header and
                original_header.split(token, 1)[1].lstrip().startswith("→")
            ]
            # Ambiguous interfaces are *not* merged into a projection family.
            if len(matched) != 1:
                if len(matched) > 1:
                    stats["ambiguous_multiple_hypotheses"] += 1
                continue
            label, token = matched[0]
            header = original_header.replace(token, "__core5_record__", 1)
            header = START.sub("theorem __member__", header, count=1)
            canonical = WS.sub(" ", header).strip()
            proof = text[pos + len(":= by"):]
            stats["record_tier_" + label] += 1
            records.append({
                "name": m.group(1),
                "path": "src/" + file.relative_to(src).as_posix(),
                "start_line": a + 1,
                "end_line": b,
                "proof_source_lines": len(proof.splitlines()) + 1,
                "tier": label,
                "canonical_statement_hash": hashlib.sha256(
                    canonical.encode("utf-8")
                ).hexdigest(),
            })
    return records, dict(stats)


def rank(records: list[dict], max_families: int = 100) -> dict:
    grouped = defaultdict(list)
    for record in records:
        grouped[record["canonical_statement_hash"]].append(record)
    families = []
    for key, members in grouped.items():
        tiers = {r["tier"] for r in members}
        if "core5" not in tiers or len(tiers) < 2:
            continue
        if len({r["path"] for r in members}) < 2:
            continue
        # Keep the largest existing Core5 proof as a *hypothetical* donor.
        donor = max((r for r in members if r["tier"] == "core5"),
                    key=lambda r: r["proof_source_lines"])
        gross = sum(r["proof_source_lines"] for r in members) - donor["proof_source_lines"]
        families.append({
            "canonical_statement_hash": key,
            "needs_unverified_bridge": "core_no_chain" in tiers,
            "bridge_obligation": (
                "Prove CoreNoChain to Core5 using exact record fields and compile imports"
                if "core_no_chain" in tiers else
                "Existing Core5.of_core / Core5.of_char still requires source elaboration"
            ),
            "members": len(members),
            "tiers": sorted(tiers),
            "modules": len({r["path"] for r in members}),
            "gross_source_body_reuse_candidate_lines": gross,
            "hypothetical_donor": donor,
            "representatives": sorted(members,
                key=lambda r: (-r["proof_source_lines"], r["path"]))[:20],
            "limitations": "No import cycle check, theorem elaboration, or source-line savings certified",
        })
    families.sort(key=lambda f: (
        -f["gross_source_body_reuse_candidate_lines"], -f["members"],
        f["canonical_statement_hash"]
    ))
    return {
        "families_before_output_limit": len(families),
        "gross_body_reuse_candidate_lines": sum(
            f["gross_source_body_reuse_candidate_lines"] for f in families
        ),
        "families": families[:max_families],
        "integrity": (
            "Exact source statement equality after one approved record "
            "hypothesis replacement, not definitional equality or a proof "
            "certificate. CoreNoChain-to-Core5 is a separate UNCHECKED bridge "
            "obligation (PR #14); do not describe it as already proved. "
            "Gross candidate lines are not valid claimed reductions; import "
            "cycles, bridges and wrappers cost source."
        ),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", type=Path, default=Path("src"))
    ap.add_argument("--root", default=ROOT)
    ap.add_argument("--max-families", type=int, default=100)
    ap.add_argument("--out", type=Path,
                    default=Path("analysis/rh-core5-projection-atlas.json"))
    args = ap.parse_args()
    if args.max_families < 1:
        ap.error("--max-families must be >= 1")
    records, stats = collect(args.src, args.root)
    result = rank(records, args.max_families)
    result["census"] = stats
    result["scope"] = str(args.src / args.root)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n",
                        encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items()
                      if k != "families"}, indent=2))
    print(json.dumps(result["families"][:6], indent=2))


if __name__ == "__main__":
    main()
