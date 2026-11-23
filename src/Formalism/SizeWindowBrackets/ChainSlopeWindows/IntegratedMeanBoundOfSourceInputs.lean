import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SlopeInequalityOfFamilyIntegrated
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruenceIntegrated

/-!
# Integrated level-of-congruence error from unchanged arithmetic source inputs

The source `Inputs2` predicate includes all of the old geometric,
arithmetic, and loss premises. Previously these witnesses only yielded
the logarithmic local `SlopeIneq`. This module reuses the source
`ranks_of_places` theorem and the new family-level integrated bridge
to obtain `SlopeIneqIntegrated`, then applies the independently
kernel-checked sharp weighted-mean calculation.

The result is conditional on the original `Inputs2`; it is not a new
proof of their satisfiability or of the eventual RH/GRH conclusion.
-/

open Module NumberField Matrix

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData
open Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  {W : H → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {m : ℕ}

/-- The same `Inputs2` as in the published source chain now gives an
actual rational-integrated mean error, without a new slope premise. -/
theorem weighted_mean_bound_of_source_inputs_integrated
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ)
    (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ)
    (hInput : Inputs2 D ell G C cT N TT T2 a w Fm η θ eK K CL) :
    umean (mkData G C.cHH D ell N TT T2 a w Fm).ASK ≤
      umean (mkData G C.cHH D ell N TT T2 a w Fm).Main +
        errorTermWithIntegrated
          (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G) := by
  classical
  obtain ⟨hB, hLoss⟩ := hInput
  obtain ⟨hSet, hQuot, _, hHH, hFP⟩ :=
    sizeConditions_of_split D ell G C cT N TT T2 a w Fm
      η θ eK K CL hB
  obtain ⟨hLat, hPl, _, _, hd, _, hDIV, hE, hHC,
    hCnt, hSl, _, _, hWin, _, _, _⟩ := hB
  have hx1 : (1 : ℝ) ≤ G.x := hWin.1.1
  have hε : 0 < G.ε := hWin.1.2.1
  have hb2 : 2 ≤ bTx G.x G.ε ^ 2 := by
    have h1 : 1 ≤ G.x ^ G.ε := Real.one_le_rpow hx1 hε.le
    have h2 : 2 ≤ bTx G.x G.ε := by
      have := Real.add_one_le_exp (G.x ^ G.ε)
      unfold bTx
      linarith
    nlinarith
  have hRanks :
      ∀ u0 u,
        3 / 4 * (Fm u0).dM u ≤ (Fm u0).du u ∧
        (Fm u0).du u ≤ (Fm u0).dM u := by
    intro u0 u
    exact ranks_of_places _ (Fm u0) _ _
      (phi_card_pos (H := H)) hb2 (hd u0) (hPl u0) u
  have hSharp :
      (mkData G C.cHH D ell N TT T2 a w Fm).SlopeIneqIntegrated :=
    slope_inequality_of_family_integrated G C.cHH D ell N TT T2 a w Fm
      hLat hRanks
  exact weighted_mean_bound_integrated
    (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G)
    ⟨(0 : H)⟩ hSet hDIV hE hHC hCnt hSl hQuot
    hLoss hSharp hHH hFP

#print axioms Formalism.LFunctionChainParameters.LChain2.weighted_mean_bound_of_source_inputs_integrated

end Formalism.LFunctionChainParameters.LChain2
