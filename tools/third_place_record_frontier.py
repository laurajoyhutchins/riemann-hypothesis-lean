#!/usr/bin/env python3
"""Evidence frontier of the actual 60-field third-place record.

This is a SOURCE-LEXICAL dependency witness, not Lean elaboration.
It distinguishes explicit field projections (P.field) from passing P
as a complete value to a theorem, because an opaque whole-record call
prevents inference that the other fields are irrelevant.

The public bridge and proof terms remain unchanged. Use the reported
whole-record edges to find the next theorem-interface refactoring.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

PREFIX = Path(
    "Development/AutomorphicArithmetic/ThetaCorrespondence/"
    "ThetaPairLifts/ThirdPlaceSeries"
)
SITES = (
    ("SiegelEisensteinSecondTermHypotheses.lean",
     "nonempty_hyps_definite_side_of_closed_bound"),
    ("HypothesesNonemptyOfUnramifiedExponents.lean",
     "hypotheses_nonempty_of_unramified_exponents_alt"),
    ("OpenOrbitOfUnramifiedExponents.lean",
     "open_orbit_of_unramified_exponents_alt"),
    ("SiegelEisensteinSecondTermHypotheses.lean",
     "every_character_of_theta_integrals_local_matching"),
)
RECORD_FILE = "EveryCharacterOfLiteratureOfVWin.lean"
RECORD_CONSTRUCTOR = "UpperTheory.LiteratureTheorems.published_results_eigen"
IDENT = r"[A-Za-z_][A-Za-z_0-9']*"


def theorem_slice(source: str, name: str) -> str:
    """Extract a source theorem through the next theorem or explicit end.

    Supports only the pinned source's conventional style. Refuse
    to silently treat a missing declaration as an empty proof.
    """
    anchor = re.compile(
        r"^theorem\s+" + re.escape(name) + r"\b", re.MULTILINE
    )
    matches = list(anchor.finditer(source))
    if len(matches) != 1:
        raise ValueError(f"exactly one source theorem required: {name}")
    start = matches[0].start()
    boundary = re.search(
        r"^(?:theorem|lemma|def|abbrev|namespace|section|end)\b",
        source[matches[0].end():], re.MULTILINE
    )
    stop = (matches[0].end() + boundary.start() if boundary
            else len(source))
    return source[start:stop]


def read_constructor_fields(source: str) -> list[str]:
    section = theorem_slice(source, RECORD_CONSTRUCTOR)
    if " where\n" not in section:
        raise ValueError("expected Lean record constructor with where")
    _, body = section.split(" where\n", 1)
    fields = re.findall(r"^  (" + IDENT + r")\s*:=", body, re.MULTILINE)
    if len(fields) != len(set(fields)):
        raise ValueError("duplicate field in source constructor")
    if len(fields) < 1:
        raise ValueError("no record fields found")
    return fields


def strip_line_comments(s: str) -> str:
    # Not a Lean parser: examined theorem bodies have no block comments
    # or string literals containing comment delimiters. This is a boundary.
    return "\n".join(line.split("--", 1)[0] for line in s.splitlines())


def direct_field_projection(theorem: str, binder: str = "P") -> Counter:
    proof = strip_line_comments(theorem)
    return Counter(re.findall(r"\b" + re.escape(binder) +
                              r"\.(" + IDENT + r")(?![A-Za-z_0-9\u0027])", proof))


def whole_record_contexts(theorem: str, binder: str = "P") -> list[str]:
    """Record non-projecting P uses, including nested theorem calls.

    Exclude binder introduction and the P.field projections. Leave each
    remaining occurrence for human inspection rather than auto-infer
    which constant P was passed to.
    """
    proof = strip_line_comments(theorem)
    if ":= by" in proof:
        proof = proof.split(":= by", 1)[1]
    elif " :=" in proof:
        proof = proof.split(" :=", 1)[1]
    else:
        raise ValueError("theorem has no source proof body")
    results = []
    pat = re.compile(r"\b" + re.escape(binder) + r"\b(?!\.)")
    for line in proof.splitlines():
        if re.match(r"^\s*intro(?:s)?\s", line):
            continue
        for match in pat.finditer(line):
            results.append(
                " ".join(line[max(0, match.start()-110):
                              match.end()+110].split())
            )
    return results


def analyze_sources(sources: dict[str, str], *, expect_fields: int | None = 60):
    source = sources.get(RECORD_FILE)
    if source is None:
        raise ValueError(f"missing record constructor module: {RECORD_FILE}")
    fields = read_constructor_fields(source)
    if expect_fields is not None and len(fields) != expect_fields:
        raise ValueError(f"record field-count drift: {len(fields)} vs {expect_fields}")
    known = set(fields)
    rows = []
    all_direct = set()
    for file, theorem in SITES:
        if file not in sources:
            raise ValueError(f"missing source module: {file}")
        src = theorem_slice(sources[file], theorem)
        proj = direct_field_projection(src)
        unknown = sorted(set(proj) - known)
        if unknown:
            raise ValueError(f"{theorem}: projections not fields of P: {unknown}")
        all_direct.update(proj)
        opaque = whole_record_contexts(src)
        rows.append({
            "theorem": theorem,
            "source_module": file,
            "source_sha256": hashlib.sha256(
                sources[file].encode("utf-8")
            ).hexdigest(),
            "directly_referenced_fields": sorted(proj),
            "direct_field_reference_counts": dict(sorted(proj.items())),
            "whole_record_occurrence_count": len(opaque),
            "whole_record_contexts": opaque,
            "directly_referenced_field_count": len(proj),
        })
    return {
        "record_constructor_theorem": RECORD_CONSTRUCTOR,
        "record_constructor_file": RECORD_FILE,
        "record_constructor_sha256": hashlib.sha256(
            source.encode("utf-8")
        ).hexdigest(),
        "record_field_count": len(fields),
        "record_fields": fields,
        "direct_fields_seen_across_slices": sorted(all_direct),
        "direct_field_union_count": len(all_direct),
        "other_fields_without_direct_projection_in_slices": sorted(
            known - all_direct
        ),
        "whole_record_occurrences_across_slices": sum(
            row["whole_record_occurrence_count"] for row in rows
        ),
        "proof_sites": rows,
        "interpretation": (
            "ONLY lexical direct field occurrences; whole-record calls "
            "require recursive theorem type/proof analysis. This is NOT a "
            "minimal record theorem, a proof of irrelevance, or a source "
            "compression certificate."
        ),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", type=Path, default=Path("src"))
    ap.add_argument("--output", type=Path, default=Path(
        "analysis/rh-third-place-record-field-frontier.json"
    ))
    args = ap.parse_args()
    paths = sorted({RECORD_FILE, *(f for f, _ in SITES)})
    sources = {
        f: (args.src / PREFIX / f).read_text(encoding="utf-8")
        for f in paths
    }
    report = analyze_sources(sources)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("record_fields", "proof_sites",
                                   "other_fields_without_direct_projection_in_slices")},
                     indent=2))
    for site in report["proof_sites"]:
        print(site["theorem"], "direct fields:",
              site["directly_referenced_field_count"],
              "whole-record occurrences:",
              site["whole_record_occurrence_count"])


if __name__ == "__main__":
    main()
