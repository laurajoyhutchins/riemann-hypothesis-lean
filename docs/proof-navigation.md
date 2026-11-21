# Navigating the proposed RH/GRH Lean development

This is a **source-navigation guide**, not a certification of the announced proof. Start with the actual checked statements and follow imports and theorem references inward. The author's [remark](https://alpo.ge/remark.pdf) provides mathematical motivation, but is not a verified map from its concepts to declarations.

## The five entry points

All five are in [`src/Main.lean`](../src/Main.lean), which imports `Statements` and `Supplements.Kernels.MainTheoremsAll`.

| Final declaration | Type | Immediate witness |
| --- | --- | --- |
| `riemannHypothesis` | Mathlib `RiemannHypothesis` | `rhOfAll` |
| `riemannZeta_eq_zero_re` | `RiemannZetaZerosOnLine` | `rhOfAll` |
| `LFunction_ne_zero_of_half_lt_re` | `DirichletLNonvanishingRightOfHalf` | `allChi` |
| `LFunction_eq_zero_re` | `DirichletLZerosOnLine` | `claimAll.2.1` |
| `LFunction_eq_zero_re_of_isPrimitive` | `PrimitiveDirichletLZerosOnLine` | `critAll` |

Four proposition definitions are in [`src/Statements.lean`](../src/Statements.lean). The fifth, `RiemannHypothesis`, comes from pinned Mathlib. **Preserve elaborated theorem types, not merely these names or textual renderings.**

## First dependency junction

[`src/Supplements/Kernels/MainTheorems.lean`](../src/Supplements/Kernels/MainTheorems.lean) contains:

```lean
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter
theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi
```

It also derives `critAll` using `Formalism.VW.critLine allChi`, and `claimAll` from `allChi`, `Claim.strip allChi`, and `Claim.zeta allChi`.

Thus the first major question is **how `UpperTheory.FinalTheorems.everyCharacter` is established**. A second question is how `Formalism.VW.rh_of_every` converts that hypothesis into RH. Follow both separately; they represent different proof obligations.

The junction imports:

- `Formalism.GammaFactorNonvanishing.CritLine`
- `Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip`
- `Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion`

These are *verified source references*, not an assertion that they constitute the complete transitive dependency closure.

## Source regions

| Region | Navigation role / caution |
| --- | --- |
| `src/Development/` | Largest source region; investigate dependencies of `UpperTheory.FinalTheorems.everyCharacter` here |
| `src/Formalism/` | Contains the visible `Formalism.VW` conversion and critical-line references |
| `src/GroundTheory/` | Foundational region; identify its actual consumers rather than assuming mathematical purpose from the name |
| `src/ReciprocityTheory/` | Trace imports and declarations before assigning a role |
| `src/CompanionTheory/` | Trace imports and declarations before assigning a role |
| `src/PositivityTheory/` | Trace imports and declarations before assigning a role |
| `src/Lemmata/` | Shared lemmas, candidate for deduplication only after type-level comparison |
| `src/Supplements/` | Thin bridge from internal theorems to final results |
| `src/BuildAid/` | Build support, not a mathematical proof stage |

Do not infer theorem dependencies from folder names alone.

## Mathematical roadmap from the announcement

The [four-page remark](https://alpo.ge/remark.pdf) describes a Stepanov-inspired multiplicity strategy, using chains of theta lifts of length on the order of `sqrt X` for a von Mangoldt sum of length `X`. Its timeline mentions determinant positivity, theta-lift periods, seesaw/Rallis identities, divisibility, Iwasawa towers, slope inequalities, integral structures, relative trace formulas, and arithmetic cohomology.

**Unverified correspondence:** no declaration-by-declaration mapping from those phrases to the Lean tree has yet been established. Treat them as search hypotheses. For each candidate, record the exact declaration, its type, imports, and a proof-term or elaborated-dependency witness before asserting a correspondence.

## A repeatable investigation

1. Select one of the five declarations in `Main.lean`; copy its *exact* elaborated type and pinned toolchain/Mathlib commit.
2. Follow its immediate witness into `MainTheorems.lean`; then locate the referenced declaration with `rg -n 'everyCharacter|rh_of_every|critLine' src`.
3. Record the declaration's hypotheses and conclusion. Separate **direct textual references**, **transitive module imports**, and **kernel-level constant dependencies**; these graphs are not interchangeable.
4. Explain the mathematical mechanism in a paragraph, and mark any interpretation not justified by the source as a hypothesis.
5. Identify the next unresolved dependency and repeat. When comparing similar proofs, normalize and compare theorem types before proposing a common abstraction.
6. Rebuild the affected Lean targets and check axioms. Do not infer independent kernel verification from successful text scans or documentation.

For a local clone, useful starting commands:

```bash
rg -n 'theorem (everyCharacter|rh_of_every)|def (EveryCharacter|RiemannHypothesis)' src
rg -n 'theta|Theta|Rallis|seesaw|Iwasawa|Bost' src/Development src/Formalism
lake build Statements
lake build Main
```

The second search is *exploratory*: a missing text match does not prove a mathematical construction is absent.

## Record findings consistently

For each substantive subsystem, add a short note with:

- **Entry theorem and exact type**
- **Source path and commit**
- **What is proved**, including hypotheses
- **How it works**, in mathematical language
- **Upstream prerequisites and downstream consumers**, each with evidence
- **Repetition or compression opportunities**, with a proposed general theorem and expected proof obligations
- **Verification status**: inspected / elaborated / built / axioms checked / independently kernel-replayed
- **Unknowns and counterexamples**

Do not call a reduction proof-preserving until the final theorem types and kernel checks have been compared. The target of fewer than ten million lines is a research objective, not evidence of a successful reduction.

## First executable investigation

The [minimal Main experiment](minimal-main-experiment.md) has already been performed at the *source/import* level in separate [draft PR #1](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/1), which also has more advanced dependency tooling. Those source results do not constitute a kernel dependency certificate. For the mathematics behind the final theorem witnesses, read the [analytic reduction](proof-atlas/analytic-reduction.md), [character-box interface](proof-atlas/character-box.md), and [literature/theta bridge](proof-atlas/literature-bridge.md).

The [covolume assembly study](proof-atlas/covolume-assembly.md) identifies a candidate shared proof parameterized by the point-admissibility guard, while keeping the two realization models distinct.

## Next maps to build

1. Exact transitive declaration-dependency graph for `everyCharacter` and `rh_of_every`.
2. A theorem-level map of theta lifts, including which declarations encode iteration, periods, and divisibility.
3. A repeated-proof-family inventory based on normalized theorem statements, with examples and independently verified candidate abstractions.

Keep the canonical conceptual explanations in the [technical notebook](https://github.com/laurajoyhutchins/technical-notebook); keep repo-specific theorem paths, proof maps, and verification recipes here.
