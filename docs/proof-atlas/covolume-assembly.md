# Covolume assembly: a reusable theorem hidden behind two realization guards

**Evidence level:** source inspection and a mathematical conditional derivation. **Not** a Lean-kernel-checked refactor. This page studies the two routes feeding the [literature/theta-integral bridge](literature-bridge.md). See [the investigation plan](../proof-research-plan.md).

## Two source-level proof families

| Stage | Hodge-bundle route | Third-place/theta route |
| --- | --- | --- |
| Row admissibility | `GlobalTheory.CovTop.RowsT p := p.Rows ∧ RecTied D L` | `GlobalTheory.CovTop.RowsTAlt p := p.PointConditions' ∧ RecTied D L` |
| Eventual bound | `EvTied Fm Q` | `EventuallyAtAllPoints Fm Q` |
| Universal lifting hypotheses | `Lifts Q`, `Covers Q` | `LiftsCondition Q`, `CoversCondition Q` |
| Eight bounds | `Gram, Rec, Cut, Bad, abelian₂, Size, CoreLe, Low` | `GramCondition, LiftRecursive, LiftTruncation, LiftBadSet, LiftLambdaBound, SizeCondition, CoreBound', LiftLowBound` |
| Core assembly | `GlobalTheory.CovTop.Assembly.covolX_of_steps` | `GlobalTheory.CovTop.Assembly.covolX_of_lift_bounds_and_coreLe` |
| Final proposition | `CovolX` | `CovolumeBoundOfX` |
| Top-level wrapper | `SelfIntersectionVolumeEstimates.topCovolG_alt` | `SelfIntersectionVolumeEstimates.topCovolG_alt_alt` |
| Arithmetic input | `PositivityTheory.HtPt.Ah.deep_slim_use` | **The same** `deep_slim_use` |

Source paths (relative to `src/`):

- Original definitions and `CovolX`: `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`.
- Original core proof: `Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFromGramAndBounds.lean`.
- New definitions and `CovolumeBoundOfX`: `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LiftLambdaBound.lean`.
- New core proof: `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/CovolXOfSteps.lean`.
- Original wrapper: `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/TopCovolG.lean`.
- New wrapper: `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolG.lean`.
- Shared arithmetic input: `Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/HilbertSamuelApplications/AhSlimU.lean`.

The *local* premises (`GramAt`, `RecAt`, `CutAt`, `BadAt`, `LamAt`, `SizeAt`, `CoreAt`, `LowAt`) are reused directly in the new definitions. Both core proofs invoke `exists_loss_le` and `lcv_le` from the original `CovolumeFromGramAndBounds.lean`. The repeated work is principally in combining eventual universal bounds.

## Why they are not automatically the same theorem

The original `PtAt.Rows` (defined in `.../Divisors/TupleReadBaseTupleEqFamily.lean`) and the new `PtAt.PointConditions'` (in `.../ThirdPlaceSeries/Realised.lean`) contain the same *named* row conditions except for their final field:

```text
Rows.ties                 : p.Ties
PointConditions'.ties     : p.CompatibilityConditions

Ties.real                 : p.Realised
CompatibilityConditions.real : p.RealisedCondition
```

The remaining fields of `Ties` and `CompatibilityConditions` have the same displayed names/types in the inspected files. But the realization witnesses themselves are different:

- `p.Realised` packages `RecT`, `STiesR`, `RealTB`, `RealPins`, `RealRec`, `RealRecPins`, and the equality `ofReal ... = p`.
- `p.RealisedCondition` packages `RecTAlt`, `STiesRAlt`, `RealTBAlt`, `IndefiniteRealisationNormalisation`, `IndefiniteRealisationRecursion`, `IndefiniteRealisationCompatible`, and `ofReal_alt ... = p`.
- The original `RealRecPins.rowLoc` refers to `RowLocPin`; its later counterpart refers to `RowLocPinAlt`.

These facts rule out *asserting* definitional identity merely from matching field names. No implication between the realization predicates has been established.

## Route A: transport old results to the new guard (conditional)

If a theorem supplies, for all relevant points,

\[
  p.\mathrm{PointConditions'}\ \Rightarrow\ p.\mathrm{Rows},
\]

then `RowsTAlt p → RowsT p`. Consequently, any eventual bound established under `RowsT` is also valid under `RowsTAlt`: retain the same cutoff and apply the old bound after converting its guard.

The same proof gives the **conditional mathematical implication**

\[
  \left(\forall p,\ \mathrm{RowsTAlt}(p)\Rightarrow\mathrm{RowsT}(p)\right)
  \Rightarrow
  \left(\mathrm{CovolX}\Rightarrow\mathrm{CovolumeBoundOfX}\right).
\]

Here the quantifier over `p` includes the relevant dependent family/index parameters. Both target definitions use the same closed-family covolume predicate and differ in the eventual point guard. The proof preserves their uniform `C₀` and cutoff `x₀` without weakening either numerical bound.

An adequate *sufficient*, but unproved, local obligation is `p.RealisedCondition → p.Realised`: copy the remaining fields to obtain `p.CompatibilityConditions → p.Ties`, then `p.PointConditions' → p.Rows`. **This may fail** if the alternative realization is genuinely more general; no bridge or equivalence is claimed.

Under that bridge, the old `topCovolG_alt` has the same displayed seven premise types as `topCovolG_alt_alt`, so the latter should be derivable by applying `CovolX → CovolumeBoundOfX` to the former. This is a proposed Lean experiment, **not** an elaborated type comparison.

## Route B: share the assembly proof without equating realizations (preferred first)

There is a stronger architecture that avoids Route A's potentially difficult hypothesis.

Parameterize the *eventual-point guard* by a family-dependent predicate `A`. Define, schematically,

\[
\begin{aligned}
\mathrm{Eventually}_A(F,Q) &:= \exists x_0,\ \forall x\ge x_0,\ \forall \iota,p,\ A(p)\Rightarrow Q(p),\\
\mathrm{Lift}_A(Q) &:= \mathrm{Closed}\left(F\mapsto \exists C\ge0,\ \mathrm{Eventually}_A(F,\forall i,\ Q_i(C))\right).
\end{aligned}
\]

(The real definitions also carry `eps`, `Fm`, `hx`, `CH`, implicit parameters, and indices. This is a mathematical schema, **not copy-paste Lean syntax**.)

**Candidate general theorem:**

\[
\begin{split}
&\mathrm{Gram}_A \to \mathrm{Rec}_A \to \mathrm{Cut}_A \to \mathrm{Bad}_A\\
&\qquad\to \mathrm{Lambda}_A\to \mathrm{Size}_A\to\mathrm{Core}_A\to\mathrm{Low}_A\\
&\qquad\qquad\to \mathrm{Covolume}_A.
\end{split}
\]

**Proof:** conjoin eight eventual hypotheses, choosing the maximum of their cutoff points. Obtain their constants `A, B, C₁, C₂`. The already-proved `exists_loss_le` supplies a further asymptotic cutoff. At each admissible point invoke the already-proved local `lcv_le` with the eight local estimates. Choose the resulting uniform constant `C₁+C₂+1`, and use `unitE ≥ 0` to extend the inequality to larger `C`. At no stage does the numerical proof inspect the *definition* of the admissibility guard; it only uses the eight local hypotheses obtained **under** that guard.

Specialize once with `A := RowsT` and once with `A := RowsTAlt`. These specializations reproduce their respective target predicates without assuming either guard implies the other. This is **shared proof abstraction**, not automatic logical equivalence between the resulting theorems.

**Lean verification work needed:** define a suitably dependent guard, prove a generic eventual-conjunction lemma, express the eight lifting predicates in terms of it, prove the common assembly lemma, and check each specialization elaborates to the exact original proposition. Keep both old theorems available as public corollaries while switching downstream consumers. Do not introduce axioms or replace any original final type.

## How far might it scale?

Using Git tree objects for the two directories in the inspected repository snapshot:

- `HodgeBundleWeights/`: **188** Lean files.
- `ThirdPlaceSeries/`: **2,251** Lean files.
- **60** identical *filenames* occur in both directories.

Three sampled pairs have matching construction roles with renamed result interfaces: `CoveringGramMatrixOfLocalTraces`, `CoveringDegreeMultiplicative`, and `HeightLowerBoundGeneral`. All require elaborated-type and proof-level investigation; **60 is not a count of redundant files**.

The thesis to test is whether an admissibility-parameterized theorem family can replace parallel chains of proofs, not merely abbreviate their names. In particular, the full `topCovolG` wrappers have different intermediate lemma names and are not automatically instances of a single theorem even after sharing the eight-bound assembly.

## Reproducible decision procedure

1. In the pinned Lean 4.33.1 environment, record `#check` and `#print axioms` for `covolX_of_steps`, `covolX_of_lift_bounds_and_coreLe`, `topCovolG_alt`, and `topCovolG_alt_alt`.
2. Implement **Route B** in a new non-default experiment module. Check the generic theorem and its two specializations without deleting either original.
3. If either specialization fails, record the exact mismatch: dependent guard, `Closed` API, type elaboration, or a genuinely different local mathematical statement. No `sorry`/axiom substitutions.
4. Independently investigate **Route A** only if the realization refinement is provable. Compare `RecTAlt` to `RecT`, `RealTBAlt` to `RealTB`, and `RowLocPinAlt` to `RowLocPin` with explicit projections or counterexamples.
5. If both specializations compile, migrate one downstream consumer and capture before/after import/declaration closures; compare elaborated types, axiom sets and kernel verdicts. Count **net physical source lines actually deleted**, not hypothetical import savings.
6. Sample the 60 matched filenames and expand only when genuine reusable proofs, rather than equivalent labels, are demonstrated.

**Current verdict:** the numerical covolume assembly is a strong **candidate for guard-parametric sharing**, with a mathematical proof argument grounded in the two existing source scripts. No general Lean theorem or realization conversion has been kernel-checked in this investigation.
