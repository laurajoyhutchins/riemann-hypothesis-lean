# The literature and theta-integral bridge

**Evidence:** inspected Lean source in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean` and direct consumers. This note records declarations and their visible mathematical interfaces, **not** an independently checked proof.

## First find the real inputs

The bridge file defines a proposition-valued structure at approximately line 215:

```lean
structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where
  caraianiLocalGlobalDual : UpperTheory.One.M.Row
  localLanglandsExists : UpperTheory.Zero.LLC.RecTExists
  galoisRepOfPolarizedPairLit : UpperTheory.One.M.Row
```

This structure has **three fields**. It is not a proof of them, and it does not mean the rest of the mathematics is reducible to three lines. The file imports 208 modules, declares 195 theorems, and constructs large bundled inputs using earlier mathematical results. Its first three-field structure is a *hypothesis interface*, not a magical replacement for the substantial proofs required to inhabit it.

The top-level consumer in [`CharacterBoxes/MainConclusion.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean) constructs the interface from the row hypothesis and `recTExists`:

```lean
theorem UpperTheory.FinalTheorems.everyCharacter_of_row
    (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩
    (UpperTheory.One.vwin_of_row h)
```

**Question to resolve via elaboration:** how do the two uses of `h` elaborate to the first and third declared fields, and are they logically interchangeable or simply definitionally compatible?

## The actual final theorem application

At lines 810–813, the file declares

```lean
theorem UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    (O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements)
    (hV : UpperTheory.Top.VWin) : UpperTheory.EveryCharacter := ...
```

The proof term applies `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` to the following seven *visible* argument groups:

| Input | Where supplied | Navigation question |
| --- | --- | --- |
| Automorphic eigen/third-place hypotheses | `published_results_eigen O` | Which fields are used by the next theorem? |
| Theta-local hypotheses | `published_results_first O` | Which pieces of local theta representation theory are essential? |
| Global theta-integral agreement | first projection of `theta_integrals_agree_and_local_matching_of_literature O` | What is the exact equality/compatibility statement? |
| Local matching | second projection of the same conjunction | How does it interact with the global integral? |
| Arithmetic covolume/positivity input | `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt ...` | Which arithmetic-geometric lemmas establish its bound? |
| Local Langlands existence | `local_langlands_gl_recT_exists_of_literature O` | Is this derived from `O.localLanglandsExists`, or does it require further constructions? |
| Automorphic window | `hV : UpperTheory.Top.VWin` | How is it obtained from the row theorem? |

This is a **useful mathematical cut**: the ultimate nonvanishing theorem consumes a joint collection of spectral, local theta, matching, arithmetic positivity, Langlands, and automorphic-window inputs. The exact *statement* of `every_character_of_theta_integrals_local_matching` still needs to be located and inspected. Do not substitute the author's narrative for that statement.

## Why the bridge is large

The bridge file contains **815 physical source lines, 208 direct import declarations, and 195 theorem declarations**. Its imports include **79** from `Development.AbelianVarietyTheory.Proofs` and **57** from `Development.WeilBound.CoreStatements`. In particular:

- `published_results_eigen O` (line 666) constructs a `GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses` value with **60 named fields** (counted from the source).
- `published_results_first O` (line 727) builds `GlobalTheory.FunPr.ThetaLocalInputs`.
- `published_results_arithmetic O` (line 781) builds `GlobalTheory.CovTop.PublishedHodgeBundleTheorems`.
- The final theorem passes `published_results_arithmetic O` and many other results to the self-intersection/covolume argument.

These bundles make good navigation landmarks. Their sizes tell us little about whether the proofs behind their fields can be compressed. A field might be crucial to a downstream theorem even if it looks ceremonial here.

## Follow the two upstream constructions

The automorphic-window witness is in [`VwinOfRow.lean`](../../src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean):

```lean
UpperTheory.One.vwin_of_row h :=
  UpperTheory.One.Join.automorphic_window_of_inputs
    (UpperTheory.LiteratureTheorems.OpenImageCondition.mk h)
    (UpperTheory.BaseChangeIdentities.baseChangeN h)
```

The Galois row witness is in [`RowSrc.lean`](../../src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean):

```lean
UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter :=
  galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK
```

Both are distinct from the final literature bridge. They should be documented independently once the exact types of their input theorems and transitive dependencies have been obtained.

## Next precise investigation

1. Locate the defining declaration of `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` in an **exact elaborated declaration inventory** and inspect its type and proof; do not guess its source file from the name.
2. Extract which of `published_results_eigen`'s 60 fields actually occur in the elaborated proof dependency graph. Record a field-to-consumer map rather than dropping apparently unused fields.
3. Record the full theorem type of `topCovolSlim2_use_alt_alt` and trace the self-intersection/height input back to its source. This is an especially promising mathematical subsystem for high-leverage abstractions, but no redundancy has been demonstrated yet.
4. Distinguish three potential reductions: unused *imports*, unused *bundle fields*, and mathematically redundant *proof families*. A reduction in one does not establish the others.
5. Use the existing dependency tools in [research PR #1](https://github.com/laurajoyhutchins/riemann-hypothesis-lean/pull/1), which already includes source closure, Lean census, and export-graph work. Do not create a second, competing graph implementation.

Related: [analytic reduction](analytic-reduction.md), [source-level spine](../every-character-spine.md), [research plan](../proof-research-plan.md).


## Verified source location: the arithmetic covolume input

The fifth argument of `every_character_of_literature_of_vWin` is defined in [`ThirdPlaceSeries/TopCovolSlim2Use.lean`](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolSlim2Use.lean). The file is 26 lines and the theorem has this precise *source signature* (here names are retained verbatim):

```lean
theorem SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt :
    GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero →
    GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero →
    GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv →
    PositivityTheory.MbHsUse.HSUse →
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement →
    HT.FarguesExact →
    GR.ZarhinStatement →
    Pub.NefRR →
    GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative →
    GlobalTheory.Published.PointSeparationPair →
    GlobalTheory.Published.ArDegree →
    GlobalTheory.CovTop.PublishedHodgeBundleTheorems →
    GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.CovTop.CovolumeBoundOfX := ...
```

Its proof constructs `GlobalTheory.CovTop.HypothesesX` from the toroidal-fan input, seminegativity, Green regularity, point separation and the Hodge-bundle Chow-height formula; constructs `GlobalTheory.CovHt.HypothesesH` from Siegel/toroidal inputs and arithmetic degree; and invokes `SelfIntersectionVolumeEstimates.topCovolG_alt_alt` with an arithmetic height/positivity input from `PositivityTheory.HtPt.Ah.deep_slim_use`.

This is an **explicit compositional proof interface**, not evidence that the 15 hypotheses are independent, minimal, or redundant. A useful next refactoring experiment is to compare the source and elaborated types of `topCovolG_alt_alt`, `deep_slim_use`, and the associated hypothesis structures; test whether a general theorem over an abstract package can subsume multiple concrete wrappers. Record actual consumers before deleting any module.

The original open question remains: the defining file/type of `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` has **not yet been located**. GitHub code search returned no indexed matches for the fully qualified identifier, so the direct proof-term reference above is the current evidence.

The next level of the arithmetic branch is now documented in [covolume assembly and realization refinement](covolume-assembly.md). It explains the shared local estimate, two distinct row admissibility predicates, and why a guard-parametric assembly theorem may share proofs without first proving a realization equivalence.
