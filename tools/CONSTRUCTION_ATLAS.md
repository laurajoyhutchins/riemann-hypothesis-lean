# Construction-family candidate atlas

This index is a second-stage discovery tool after the exact exported
kernel-expression type census. It prioritizes long source-owned proof bodies
in Development/AbelianVarietyTheory/Proofs, where the original syntactic
profiler measured 7,436,698 physical lines across 95,418 files.
It is not an automatic proof compressor.

Run:

    python3 -m unittest discover -s tools -p 'test_construction_atlas.py' -v
    python3 tools/construction_atlas.py --src src --out analysis/rh-construction-family-atlas.json

Three intentionally distinct discovery signals are returned:

1. **Identical proof text.** Bodies have equal whitespace-normalized text but
   can elaborate against different statements and contexts. The theorem
   boundaries are still heuristic.
2. **Matching tactic shape.** Recognized tactic command sequences match, and
   at least one qualified mathematical dependency is shared. This is weaker
   than proof equivalence.
3. **Shared qualified dependency.** Several substantial proofs mention a
   less ubiquitous fully qualified construction. This detects mathematical
   neighborhoods, not necessarily duplicated proof arguments.

Candidates retain source paths and line spans so reviewers can inspect the
actual mathematical content. Source attribution and line ranges must be
revalidated by the Lean parser or direct file inspection before any edit.

For each candidate, ask:
- What general theorem or object could subsume these proofs?
- Are the differences reindexing, base change, equivalence, or genuinely
  different hypotheses?
- Is the donor accessible without an import cycle?
- Can original names and exact elaborated theorem types be retained?
- What is the net source-line delta after adding the generic construction
  and its bridge proofs?

The atlas upper-bound metric is **not a forecast**. Families overlap; lines
in one family can also appear in many others. A large group may be a common
tactic template applied to different mathematics with no reusable result.
Never add speculative savings from different groups.

## Acceptance tiers

- Candidate atlas scan and tests: discovery-only.
- Physical source inventory and diff: source-audited reduction.
- Pinned Lean source build, checked declarations and axiom audit: local proof
  evidence for the affected modules.
- New source-bound full export and independent kernel replay of five root
  theorems, with exact type/universe matching: independent certification.

A cancelled, skipped, or timed-out Lean gate is unresolved. Original export
receipts are not receipts for changed proof source.

Related: tools/README.md, tools/CI.md, and the Quartz studies
riemann-lean-proof-minimization and rh-ci-verification-tiers.
