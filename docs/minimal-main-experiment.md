# Minimal-import experiment: existing implementation and verification status

The first import-minimization experiment is implemented in **[draft PR #1](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/1)**, not duplicated in this documentation PR. This page is a navigation and evidence index, not another source rewrite.

## What PR #1 changed

The experiment replaced `Main.lean`'s import of `Supplements.Kernels.MainTheoremsAll` with a direct import of `Supplements.Kernels.MainTheorems`, retaining the same five theorem declarations and proof bodies. Its source import-closure census identified **six modules totaling 286 source lines** excluded from `Main`'s closure under the smaller import.

PR #1 then deleted the two supplement wrappers and four small-class-number files. The original source inventory reported in [PR #1's tooling README](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/blob/research/declaration-census-20261120/tools/README.md) was 175,187 Lean files and 17,374,215 physical source lines; the six-file deletion alone would leave 175,181 files and 17,373,929 lines.

A later [source-impact workflow run](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/actions/runs/44925050237) reported **175,181 modules and 17,373,625 physical lines** at its tested checkout. These are different revision snapshots; the 304-line difference relative to the earlier expected post-deletion total must be reconciled against exact commit diffs before asserting an additional saving.

All those figures describe **source text/import reachability**, not a successfully rechecked full RH proof.

## Where the actual tools live

[PR #1](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/1) already includes:

- `tools/import_closure.py`: module-level import census and original-vs-reduced comparison.
- `tools/source_inventory.py`: full source-inventory checks.
- `tools/pruning_contract.json` and `tools/pruning_contract.py`: removal contract and source checks.
- `tools/RHDeclarationCensus.lean`: proposed loaded-environment declaration census.
- `tools/export_exact_graph.py`: proposed exact constant-reference traversal over a pinned Lean export.
- Dedicated fixture tests and workflows, including source-impact and separate heavy graph checks.

Do not confuse a successful fixture or source-impact workflow with proof verification. PR #1 explicitly states that the modified full development has not successfully completed a full Lean rebuild, axiom audit, or independent kernel replay.

## How to use the result for navigation

1. Record the exact PR #1 commit and import-closure receipt being discussed.
2. Trace the final five theorem witnesses from `MainTheorems` using [proof navigation](proof-navigation.md).
3. Use the declaration census and export graph **only when** they have been run on the real Lean environment and their completeness/trust conditions are documented.
4. Prioritize the high-volume mathematical interfaces such as [the literature/theta-integral bridge](proof-atlas/literature-bridge.md), not further polishing the six-file deletion.
5. If a new compression candidate is found, measure net eliminated lines and require unchanged elaborated final statement types and independent kernel verification.

**Verification gate:** there is no verified proof-preserving reduction to claim yet. PR #1's 286-line source-level result is valuable as a test of the method but does not materially advance the 7.37-million-line reduction target.
