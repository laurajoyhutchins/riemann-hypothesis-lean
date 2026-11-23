import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually
import Formalism.SizeWindowBrackets.ChainSlopeWindows.IntegratedLatticeFamilyBridge

/-!
# Sharp slope inequality for the actual arithmetic Fam/mkData family

This theorem follows the existing `slope_inequality_of_family` proof,
reusing precisely its `Fam.LatHyp` and rank-compression hypotheses.
The only changed mathematical conclusion is the harmonic integrated
rank-loss in `Data.SlopeIneqIntegrated`.

No new independent lattice witnesses are assumed.
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

/-- Exact production-family hypotheses of the original `SlopeIneqOfFam`,
with the stronger integrated result as the only altered conclusion. -/
def SlopeIneqOfFamIntegrated : Prop :=
  ∀ (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m),
    (∀ u0, (Fm u0).LatHyp (sgX G cHH)) →
    (∀ u0 u, 3 / 4 * (Fm u0).dM u ≤ (Fm u0).du u ∧ (Fm u0).du u ≤ (Fm u0).dM u) →
    (mkData G cHH D ell N TT T2 a w Fm).SlopeIneqIntegrated

/-- Production-family strengthening of `slope_inequality_of_family`.
All rank-compression and matrix hypotheses are discharged from the
same original source `LatHyp` and `du/dM` estimates. -/
theorem slope_inequality_of_family_integrated : SlopeIneqOfFamIntegrated (H := H) (W := W) (m := m) := by
  intro G cHH D ell N TT T2 a w Fm hL hdu
  intro u0 hδ0 hδ1 hη0 he0 he4 hHHbound hHHpos
  have hSide : LatticeToWeightTransfer.SideF
      (mkData G cHH D ell N TT T2 a w Fm) u0 :=
    ⟨hδ0, hδ1, hη0, he0, he4, hHHbound, hHHpos⟩
  obtain ⟨hG, hγ, hBV, hV, hD, hsg, hsg20, hR, h0, h0', h1, he0, hse, hS⟩ := hL u0
  have hRpos : 0 < MatrixLatticeEstimates.RsG (Fm u0).ιf := lt_of_lt_of_le (div_pos hD hsg) hR
  have hRle : MatrixLatticeEstimates.RsG (Fm u0).ι ≤ MatrixLatticeEstimates.RsG (Fm u0).ιf := Finset.sum_le_sum fun u _ => (hdu u0 u).2
  have hRge : 3 / 4 * MatrixLatticeEstimates.RsG (Fm u0).ιf ≤ MatrixLatticeEstimates.RsG (Fm u0).ι := by
    unfold MatrixLatticeEstimates.RsG
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u _ => (hdu u0 u).1
  have hde4 : (Fm u0).deF ≤ 1 / 4 := by
    unfold Fam.deF
    have : 3 / 4 ≤ MatrixLatticeEstimates.RsG (Fm u0).ι / MatrixLatticeEstimates.RsG (Fm u0).ιf := by
      rw [le_div_iff₀ hRpos]; exact hRge
    linarith
  have hde0 : 0 ≤ (Fm u0).deF := by
    unfold Fam.deF
    rw [sub_nonneg, div_le_one hRpos]
    exact hRle
  have hcor : ∑ i, ((Fintype.card ((Fm u0).ιf i) : ℝ) - (Fintype.card ((Fm u0).ι i) : ℝ))
      ≤ (Fm u0).deF * MatrixLatticeEstimates.RsG (Fm u0).ιf := by
    unfold Fam.deF
    rw [Finset.sum_sub_distrib, sub_mul, one_mul, div_mul_cancel₀ _ hRpos.ne']
    exact le_refl _
  exact LatticeToWeightTransfer.function_slope_integrated _ u0 (Fm u0).K (Fm u0).Wd (Fm u0).κ (Fm u0).κ₁ (Fm u0).V (Fm u0).ι (Fm u0).b'
    (Fm u0).X' (Fm u0).cc (Fm u0).b (Fm u0).X (Fm u0).N' (Fm u0).B (Fm u0).v (Fm u0).Y (Fm u0).Y'
    (Fm u0).Ball (Fm u0).γ (Fm u0).ιf (Fm u0).Bf (Fm u0).Vr (Fm u0).Dstar (sgX G cHH) (Fm u0).η0
    (Fm u0).η1 (Fm u0).e0 (Fm u0).deF
    ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩, hG, hγ, hBV, hV, hD, hsg, hsg20, hR, h0, h0',
      h1, he0, hse, hde0, hde4, hcor, hS, rfl, rfl⟩ hSide

#print axioms Formalism.LFunctionChainParameters.LChain2.slope_inequality_of_family_integrated

end Formalism.LFunctionChainParameters.LChain2
