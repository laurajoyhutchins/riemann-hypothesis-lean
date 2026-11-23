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
