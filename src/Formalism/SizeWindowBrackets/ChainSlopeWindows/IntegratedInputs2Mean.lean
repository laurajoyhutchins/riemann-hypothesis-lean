import Formalism.SizeWindowBrackets.ChainSlopeWindows.IntegratedFamSlope
import Formalism.SizeWindowBrackets.ChainSlopeWindows.IntegratedLatticeFamilyBridge

/-!
# Production-family harmonic mean bound from the original Inputs2 record

The existing \`InputsB\` and \`Inputs2\` data encode all concrete family
and arithmetic hypotheses. The source's \`sizeConditions_of_split\` proves
the old arithmetic conditions from them, and \`ranks_of_places\` establishes
the same dimension bounds required by \`slope_inequality_of_family\`.

The new production-family theorem reuses those proofs verbatim and
substitutes the kernel-checked integrated slope version. In particular it
takes neither an abstract \`LatForS\` witness nor a new
\`Data.SlopeIneqIntegrated\` assumption.
-/

open Module NumberField Matrix
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData
open Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
  [∀ u0, Nonempty (W u0)]

/-- The original InputsB fields already force the sharpened slope
inequality for the concrete mkData family. -/
theorem integrated_slope_of_inputsB
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ)
    (hB : InputsB D ell G C cT N TT T2 a w Fm η θ eK K CL) :
    (mkData G C.cHH D ell N TT T2 a w Fm).SlopeIneqIntegrated := by
  obtain ⟨hLat, hPl, _, _, hd, _, _, _, _, _, _, _, _, hWin, _, _, _⟩ := hB
  have hx1 : (1 : ℝ) ≤ G.x := hWin.1.1
  have hε : 0 < G.ε := hWin.1.2.1
  have hb : 0 < bTx G.x G.ε := Real.exp_pos _
  have hb2 : (2 : ℝ) ≤ bTx G.x G.ε ^ 2 := by
    have h1 : 1 ≤ G.x ^ G.ε := Real.one_le_rpow hx1 hε.le
    have h2 : 2 ≤ bTx G.x G.ε := by
      have := Real.add_one_le_exp (G.x ^ G.ε)
      unfold bTx
      linarith
    nlinarith
  exact slope_inequality_of_family_integrated G C.cHH D ell N TT T2 a w Fm hLat
    (fun u0 u => ranks_of_places _ (Fm u0) _ _ phi_card_pos hb2
      (hd u0) (hPl u0) u)

/-- Actual production-family improvement: the original Inputs2
assumptions imply a weighted mean bound with the rational harmonic
rank-loss term. This does not merely restate a stronger slope premise. -/
theorem weighted_mean_of_inputs2_integrated
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ)
    (h : Inputs2 D ell G C cT N TT T2 a w Fm η θ eK K CL) :
    umean (mkData G C.cHH D ell N TT T2 a w Fm).ASK ≤
      umean (mkData G C.cHH D ell N TT T2 a w Fm).Main +
        errorTermWithIntegrated (mkData G C.cHH D ell N TT T2 a w Fm)
          C (XppH H G) := by
  obtain ⟨hB, hLoss⟩ := h
  have hSI := integrated_slope_of_inputsB D ell G C cT N TT T2 a w Fm
    η θ eK K CL hB
  obtain ⟨hSet, hSN, _, hHHB, hFPar⟩ :=
    sizeConditions_of_split D ell G C cT N TT T2 a w Fm η θ eK K CL hB
  obtain ⟨_, _, _, _, _, _, hDIV, hE, hHC, hCnt, hSl, _, _, _, _, _, _⟩ := hB
  have hne : Nonempty H := ⟨0⟩
  exact weighted_mean_bound_integrated
    (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G)
    hne hSet hDIV hE hHC hCnt hSl hSN hLoss hSI hHHB hFPar

#print axioms Formalism.LFunctionChainParameters.LChain2.integrated_slope_of_inputsB
#print axioms Formalism.LFunctionChainParameters.LChain2.weighted_mean_of_inputs2_integrated

end Formalism.LFunctionChainParameters.LChain2


/-!
## Pointwise sharp error, for the actual downstream arithmetic contract

The original \`CoreTopEach\`/\`TopOfInputs2\` statements use a bound at
*each* unit, which cannot be deduced from the mean bound alone.
We instead specialize the already-checked \`Ga_bound5_integrated\`
pointwise and reuse the original local loss and Lo5-cap arguments.
-/

namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds

open Formalism.RankGapBounds.WeightedMeanData

variable {U0 : Type} [Fintype U0] {W : U0 → Type}
  [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)

/-- The exact original \`ErrX5at\` baseline, with only the uniform
logarithmic slope-loss term replaced by its harmonic refinement. -/
def ErrX5atIntegrated (u0 : U0) : ℝ :=
  K0v5 D C + Real.log (Fintype.card (W u0) : ℝ) + D.LoP C
    + MLo5 D C Xpp
    + (1 - D.delBar)⁻¹ *
      (4 * (UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
        (UBar5 D C Xpp + D.x ^ C.cHH * D.b)) +
        (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

/-- The harmonic per-unit error is bounded by the old error,
using the already-proved comparison of the corresponding mean terms. -/
theorem ErrX5atIntegrated_le_ErrX5at
    (hS : D.HidaSetting C) (hU : 0 ≤ UBar5 D C Xpp)
    (u0 : U0) :
    ErrX5atIntegrated D C Xpp u0 ≤ ErrX5at D C Xpp u0 := by
  have h := errorTermWithIntegrated_le_errorTermWith D C Xpp hS hU
  unfold errorTermWithIntegrated errorTermWith at h
  unfold ErrX5atIntegrated ErrX5at K0v5 Data.EDiv
  linarith

/-- Genuine per-unit harmonic upper bound, from the same old
Hida, exponent, count, slope and local loss hypotheses. -/
theorem each_unit_bound_integrated
    (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C)
    (hH : D.HComp C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : LossBounds D C) (hSI : D.SlopeIneqIntegrated)
    (hHH : D.HHBound C) (hFP : D.FParams) (u0 : U0) :
    D.ASK u0 ≤ D.Main u0 + ErrX5atIntegrated D C Xpp u0 := by
  have h1 := Ga_bound5_integrated D C Xpp
    hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP u0
  have hML : wmean (D.d u0) (Lo5 D C Xpp u0) ≤
      MLo5 D C Xpp := by
    have h2 := weighted_mean_lower_bound_le D C Xpp hS hCount u0
    have hcSl1 : 0 ≤ C.cSl1 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, _, _, _, _⟩ := hS
      exact hc
    have hIO := mul_le_mul_of_nonneg_left (hLoss u0).2 hcSl1
    dsimp only [MLo5, K7v5] at h2 ⊢
    linarith
  have h4 := (hLoss u0).1
  unfold ErrX5atIntegrated
  linarith

#print axioms Formalism.LFunctionChainParameters.WeightedSlopeBounds.each_unit_bound_integrated

end Formalism.LFunctionChainParameters.WeightedSlopeBounds

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData
open Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.characterSumData

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
  {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
  [∀ u0, Nonempty (W u0)]

/-- Production \`Inputs2\` yields an improved bound for every character
sum separately, not merely for their arithmetic average. -/
theorem pointwise_of_inputs2_integrated
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ)
    (h : Inputs2 D ell G C cT N TT T2 a w Fm η θ eK K CL) :
    ∀ u0, (∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)) ≤
      (mkData G C.cHH D ell N TT T2 a w Fm).Main u0 +
        ErrX5atIntegrated (mkData G C.cHH D ell N TT T2 a w Fm)
          C (XppH H G) u0 := by
  obtain ⟨hB, hLoss⟩ := h
  have hSI := integrated_slope_of_inputsB D ell G C cT N TT T2 a w Fm
    η θ eK K CL hB
  obtain ⟨hSet, hSN, _, hHHB, hFPar⟩ :=
    sizeConditions_of_split D ell G C cT N TT T2 a w Fm η θ eK K CL hB
  obtain ⟨_, _, _, _, _, _, hDIV, hE, hHC, hCnt, hSl, _, _, _, _, _, _⟩ := hB
  intro u0
  change (mkData G C.cHH D ell N TT T2 a w Fm).ASK u0 ≤
    (mkData G C.cHH D ell N TT T2 a w Fm).Main u0 +
      ErrX5atIntegrated (mkData G C.cHH D ell N TT T2 a w Fm)
        C (XppH H G) u0
  exact each_unit_bound_integrated
    (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G)
    hSet hDIV hE hHC hCnt hSl hSN hLoss hSI hHHB hFPar u0

#print axioms Formalism.LFunctionChainParameters.LChain2.pointwise_of_inputs2_integrated

end Formalism.LFunctionChainParameters.LChain2
