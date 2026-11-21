# The `everyCharacter` dependency spine

**Scope:** a source-verified *direct theorem-reference spine*, not a complete transitive dependency graph or a kernel dependency certificate. Read alongside [proof navigation](proof-navigation.md). All paths below are relative to `src/`.

## Root

`Main.lean` uses `allChi` for the right-half-plane nonvanishing result and indirectly for the other final results. In `Supplements/Kernels/MainTheorems.lean`:

```lean
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter
```

In `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`:

```lean
theorem UpperTheory.FinalTheorems.everyCharacter_of_row
    (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩
    (UpperTheory.One.vwin_of_row h)

theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter_of_row
    UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
```

This exposes three conceptually distinct obligations: (1) construct a `Row0b` input, (2) derive `VWin` from that input, and (3) turn the resulting literature/automorphic hypotheses into `EveryCharacter`.

## Confirmed direct edges

| Parent theorem | Immediate proof reference | Source |
| --- | --- | --- |
| `allChi` | `UpperTheory.FinalTheorems.everyCharacter` | `Supplements/Kernels/MainTheorems.lean` |
| `everyCharacter` | `everyCharacter_of_row` and `galoisLocalGlobalStrong_recParameter` | `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean` |
| `everyCharacter_of_row` | `every_character_of_literature_of_vWin`, `recTExists`, `vwin_of_row` | same |
| `vwin_of_row` | `automorphic_window_of_inputs`, `OpenImageCondition.mk`, `baseChangeN` | `Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean` |
| `galoisLocalGlobalStrong_recParameter` | `galoisRepresentations_of_thetaLift`, `tLiftK` | `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean` |

These are *syntactic proof-term references* inspected from the repository, not a claim about every elaborated constant dependency. Implicit arguments, instances, and imported theorem proofs can add dependencies.

## Read in this order

1. **Root statement:** `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`.
2. **Galois input:** `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean`. Its short proof explicitly uses `galoisRepresentations_of_thetaLift` and `tLiftK`.
3. **Automorphic window:** `Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean`. Its proof invokes `automorphic_window_of_inputs` and `baseChangeN`.
4. **Literature-to-character bridge:** `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`. This is imported by the root and needs a focused theorem-level examination; it has a very large direct import list, including numerous `Development.AbelianVarietyTheory` modules.
5. **Conversion to RH:** `Formalism.VW.rh_of_every` is defined in `Formalism/GammaFactorNonvanishing/CritLine.lean` and invokes `Formalism.VW.rh_of_right` from `Formalism/GammaFactorNonvanishing/RhOfRight.lean`. The elaborated dependencies have **not yet been enumerated**.

## Why this matters for compression

The shortest visible route to `everyCharacter` already separates a Galois/theta-lift input from an automorphic-window input, joined by a literature theorem. The fact that a bridge imports many modules does **not** prove all imports are necessary for the five final theorems. Likewise, similarly named lemmas do not imply redundant proof terms.

A useful next experiment is to compute the exact import closure and the elaborated constant dependencies for these bridge declarations, then compare the two graphs. A proof-preserving reduction must keep required constants and instances, not merely the imports that appear in source text.

**Evidence level:** source inspection only; no full Lean build, kernel replay, or proof compression has been performed for this map.

## Large bridge: measured source structure

`EveryCharacterOfLiteratureOfVWin.lean` contains 815 source lines, 208 direct imports, and 195 theorem declarations. Of these imports, 79 are `Development.AbelianVarietyTheory.Proofs` and 57 are `Development.WeilBound.CoreStatements`. The `OpenLiteratureStatements : Prop` structure has three fields (line 215), whereas the `published_results_eigen` theorem constructs a 60-field `UnitaryGroupThirdPlaceHypotheses` bundle (line 666); `every_character_of_literature_of_vWin` consumes that and other bundles (line 810). These are **measured structural clues**, not evidence that any theorem or module is unused. See [the research plan](proof-research-plan.md) for tests and verification gates.
