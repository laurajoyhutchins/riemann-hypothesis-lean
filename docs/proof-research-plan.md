# Research and navigation plan for the proposed RH/GRH formalization

**Status:** proposed execution plan, grounded in source inspection. No full Lean build, independent kernel replay, import-pruning experiment, or semantic compression has been completed under this plan. See [navigation](proof-navigation.md) and [the `everyCharacter` spine](every-character-spine.md).

## Goal and non-negotiable constraints

Make the mathematical argument navigable, then minimize the complete independently rebuildable development from approximately 17.37 million Lean source lines to fewer than 10 million **without modifying the elaborated types of the five final declarations in `src/Main.lean`**, relying on new axioms, or weakening the kernel-verification requirement.

Do not conflate:

- **Source/import reachability:** which modules might be needed to compile the final root;
- **Elaborated theorem dependency:** which constants, definitions, instances, and proof terms are actually needed;
- **Mathematical redundancy:** which results are genuinely special cases of a common theorem;
- **Cost:** source lines, compiled modules, elaboration time, peak memory, artifact size, and CI minutes.

Pruning an unreachable source file is a valid dependency reduction; factoring redundant mathematics is a different and harder proof-compression result. Measure both separately.

## Source-grounded starting points

1. `src/Main.lean` imports `Statements` and `Supplements.Kernels.MainTheoremsAll`. The five witnesses come from `MainTheorems.lean`.
2. `MainTheoremsAll.lean` adds `Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf`; its parent `MainTheoremsCritical.lean` adds three more small-class-number modules before importing `MainTheorems.lean`. The five theorem declarations do not explicitly reference these extra modules. **Hypothesis only:** a smaller main import closure may suffice.
3. `MainConclusion.lean` supplies `everyCharacter` by combining a Galois/theta-lift row input, an automorphic-window witness, and a literature bridge.
4. The bridge `EveryCharacterOfLiteratureOfVWin.lean` contains **815 lines, 208 direct imports, and 195 theorem declarations** as counted from the current source text. The imports include 79 `Development.AbelianVarietyTheory.Proofs` and 57 `Development.WeilBound.CoreStatements` modules. At line 215 it defines `OpenLiteratureStatements : Prop` with **three fields**. At line 666 `published_results_eigen` assembles a **60-field** `UnitaryGroupThirdPlaceHypotheses` value, and at line 810 `every_character_of_literature_of_vWin` applies `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` to several bundled inputs.
5. `Formalism.VW.rh_of_every` is defined in `src/Formalism/GammaFactorNonvanishing/CritLine.lean`; it reduces RH to the right-half-plane nonvanishing statement via `Formalism.VW.rh_of_right` in `RhOfRight.lean`.
6. The repository pins Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The checked default branch has no `.github/` directory: an automated GitHub Actions verification system should not be assumed to exist.

These counts are **source facts**, not evidence that an import or theorem is dispensable.

## Phase 0: Trustworthy baseline before destructive refactoring

**Deliverables:** `docs/verification-baseline.md`, reproducible logs/receipts for pinned commit and toolchain, exact statement-type manifests, and a CI-resource baseline.

- Pin repository commit, Lean/toolchain, Mathlib manifest, dependency cache, OS, and runner resources.
- Build `Statements`, then `Main`; measure wall time, peak RSS, per-module failures and cache effectiveness. Separately measure `lake build` default targets; do not assume building `Main` covers the full repository.
- Query all five final theorem types and their axioms from the loaded environment. Record full elaborated expressions with universes and constants, not just pretty-printed names; compare against the baseline after every transformation. Record any `sorryAx`, unexpected custom axioms, or non-kernel trust assumptions.
- Independently replay the compiled artifacts using an appropriate Lean kernel checker compatible with the pinned release. Until this passes, report only that source declarations were inspected or that a build succeeded.

**Gate:** No mathematical refactor is called verified without an exact-head build, axiom audit, and kernel-checking evidence. If baseline verification fails, stop compression claims and isolate the failure.

## Phase 1: Two graph layers, from the final five theorems

**Deliverables:** generated `docs/generated/module-graph.json`, `declaration-graph.json`, a browsable root-to-leaf index, and a manifest of graph completeness.

- **Cheap graph:** parse every `import` declaration across `src/` (including indirect imports) and compute reverse module reachability from `Main`; report source lines/files in and out of that closure, large fan-in/fan-out modules, strongly connected anomalies, and orphan modules. Fail closed if files cannot be read or parsed.
- **Semantic graph:** after loading the Lean environment, traverse the types and values/proofs of declarations reachable from the five final theorem names. Include implicit-argument/instance and definition dependencies, and annotate opaque boundaries. Distinguish direct references from transitively expanded dependencies. External Mathlib constants are separate nodes, not falsely attributed to this repository.
- Validate the semantic graph on several hand-audited declarations: `everyCharacter`, `everyCharacter_of_row`, `vwin_of_row`, `galoisLocalGlobalStrong_recParameter`, and `rh_of_every`. Verify that known direct edges appear.
- Generate links to exact commit, source path, declaration, and type; never build a graph solely by matching symbol strings.

**Gate:** Every root-to-leaf navigation result carries an evidence label (text match / imported module / elaborated constant dependency). The output is deterministic for the same source commit and pinned Lean version.

## Phase 2: Explain the actual mathematical cuts

**Deliverables:** short, evidence-annotated notes in `docs/proof-atlas/`, linked from `docs/proof-navigation.md`. Suggested first cuts:

| Cut | Anchor | Question answered |
| --- | --- | --- |
| Final analytic step | `Formalism.VW.rh_of_every` and `rh_of_right` | How does nonvanishing imply RH? |
| Character theorem | `UpperTheory.FinalTheorems.everyCharacter` | Which inputs establish all-character nonvanishing? |
| Local/global Galois input | `galoisLocalGlobalStrong_recParameter` | What is proved by `galoisRepresentations_of_thetaLift`? |
| Automorphic window | `vwin_of_row` | What hypotheses produce `VWin`? |
| Literature bridge | `every_character_of_literature_of_vWin` | Which bundled hypotheses are consumed by the final theta-integral theorem? |
| Deep theta-lift/multiplicity machinery | follow semantic dependencies from the bridge | Which Lean declarations, **if any**, implement the Stepanov-style iteration described by the author? |

For each cut record: exact theorem statement; assumptions and outputs; 5–10 lines of mathematical explanation; inputs and consumers; source links; evidence status; and unresolved questions. The author's remark is a **research hypothesis**, not a substitute for identifying actual Lean declarations.

**Gate:** A reader can traverse any final theorem to its major interfaces without scanning thousands of source files, and can tell which mathematical interpretations are still unverified.

## Phase 3: Two independent minimization experiments

### Experiment A: smaller final-theorem closure (low-risk, measurable)

Construct an isolated `MainMinimal` target that imports `Statements` and `Supplements.Kernels.MainTheorems` directly, instead of `MainTheoremsAll`; reproduce the same five propositions and witnesses under temporary names. Measure the module closure and successful build. If equivalent, test replacing only the import in `Main.lean` and repeat exact-type, axiom, and kernel gates.

This tests whether the extra `SmallClassNumbers` import fanout is needed. It may improve *main-target build cost* even if it removes zero lines from the complete repository. Do not claim line-count savings until modules are proven removable and actually removed.

### Experiment B: literature-bundle dependency minimization (high priority)

Starting at `every_character_of_literature_of_vWin`, track each input bundle's **fields actually used in its proof**. Test whether `published_results_eigen` (60 fields), `published_results_first`, and arithmetic/covolume bundles require all their source imports. Try one change at a time: narrow an interface, split a declaration into focused modules, or replace duplicative witness construction with a shared lemma. Rebuild the narrow target first, then all five final theorems.

A failed simplification is valuable evidence: record the precise counterdependency rather than silently restoring an enormous import list.

**Gate:** For every accepted change, store the before/after import closure, elaborated dependency comparison, source line delta, build time/RSS, and kernel verdict. No deletion based only on lexical reference scans.

## Phase 4: High-leverage semantic compression

Only after graph data identifies genuinely repeated theorem *families*, rank candidates by:

`expected safely removable lines × proof-family coverage ÷ verification cost`.

Start with repeated constructions in the Abelian variety region, not superficial shortening of 800-line bridge files. Seek parameterized definitions, universal lemmas, shared induction schemes, and canonical instances. Make the general statement explicit in Lean; prove the old instances as corollaries; mechanically switch consumers; then remove the redundant family.

An abstraction that merely moves code or changes formatting is not a counted compression result. Report **gross eliminated source lines, new shared lines, net lines, number of proof obligations discharged, and end-to-end build impact**. To meet the target, the current ~17.37M-line baseline requires more than ~7.37M net lines removed. Small successful edits are tools for finding scalable families, not the objective.

## Phase 5: CI designed around the dependency DAG

There is no inspected `.github/` CI setup on the repository's default branch. Build verification incrementally, without confusing a fast PR check with proof validation:

- **Fast PR checks:** docs links, source index consistency, import-graph changes, theorem-name inventory, formatting, and changed-file classification. Target sub-30-second feedback where feasible.
- **Affected closure checks:** compile changed modules and all affected reverse dependencies based on exact import graph; persist immutable toolchain/Mathlib and `.olean` caches keyed by source plus dependency fingerprints. Do not skip unknown or unparseable dependency edges.
- **Proof-changing merge gate:** all five `Main` theorem types, axiom inspection, and independent kernel replay on the exact candidate SHA. Run full repository/default-target builds on a separate controlled resource budget, additionally when changes may affect unrelated libraries.
- **Ratchet:** retain per-module elaboration time, RSS, cache hit rate, total proof lines, root reachability, kernel status, and baseline deltas; reject silent regressions or scope weakening.

No assumption about affordable full builds is justified until Phase 0 has measured them. If CI resources are unavailable, keep an explicit unverified status rather than treating skipped jobs as success.

## Recommended order of work

1. **First experiment:** test `MainMinimal` versus `MainTheoremsAll` while capturing the pinned baseline. This yields an early, falsifiable build-closure result.
2. **First large-scale measurement:** compute the module import closure from the five final theorems and count reachable versus unreachable source lines.
3. **First mathematical deep dive:** analyze the 60-field `published_results_eigen` interface and the exact arguments to `every_character_of_theta_integrals_local_matching`, then inspect their proof consumers.
4. **First scalable reduction:** select one repeated Abelian variety theorem family backed by normalized elaborated types; prove a general lemma and migrate a representative sample before multiplying the pattern across the tree.
5. Repeat the compression cycle only as long as each step produces real eliminated source or measurable simplification, with verification receipts.

## Tracking and definition of done

Maintain a compact `docs/proof-atlas/status.md` with one row per studied cut: source commit, exact declaration, explanation, dependency coverage, compression hypothesis, verification status, and link to evidence. Generated graphs are cacheable artifacts, not hand-written claims.

**Navigation done:** complete, reproducible theorem- and module-level routes to all five roots, with every explored cut documented and uncertainty explicit.

**Compression done:** fewer than 10,000,000 actual Lean lines in the complete independently rebuildable repository, unchanged elaborated types for all five results, and exact-head successful kernel verification with axioms/trust scope explicitly reported.

**Present state:** repository source was inspected, but none of these verification gates has yet been established.
