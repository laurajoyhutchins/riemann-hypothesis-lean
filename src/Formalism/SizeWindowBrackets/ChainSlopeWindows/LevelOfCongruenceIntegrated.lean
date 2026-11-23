import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.RankGapBounds.RankGapProofs.IntegratedSlopeError

/-!
# Sharper level-of-congruence error propagation

The old mean-bound proof bounds the logarithmic loss with \`phi_bound\`.
Here we establish the actual uniform spread cap from exactly the
hypotheses already used by that proof. Monotonicity of the harmonic
loss then supplies a rational error term that has no extra logarithm.

This module does not yet replace the final \`MeanBoundWith\` proof;
it verifies the crucial source-specific cap and its improved error.
-/

namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds

open Formalism.RankGapBounds.WeightedMeanData

noncomputable section

variable {U0 : Type} [Fintype U0]
  {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}

variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)

/-- The original local spread estimate and the original loss bound
combine into the uniform cap UBar5. No new arithmetic hypothesis
is introduced. -/
theorem sourceSpread_le_UBar5
    (hS : D.HidaSetting C)
    (hE : EComp5 D C) (hH : D.HComp C)
    (hCount : Count5 D C)
    (hSl : D.Slopes C)
    (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : LossBounds D C) (u0 : U0) :
    D.uF u0 ≤ UBar5 D C Xpp := by
  have hlocal := u_function_le_mean D C Xpp hS hE hH hCount hSl hSN u0
  have hweighted := weighted_mean_lower_bound_le D C Xpp hS hCount u0
  have hcSl1 : 0 ≤ C.cSl1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, _, _, _, _⟩ := hS
    exact hc
  have hIO := mul_le_mul_of_nonneg_left (hLoss u0).2 hcSl1
  dsimp only [UBar5, Data.K3, MLo5, K7v5] at hlocal hweighted ⊢
  linarith

/-- The old arithmetic assumptions provide exactly the source cap
needed by the harmonic-loss bound. -/
theorem sourceHarmonicLoss_le_uniform
    (hS : D.HidaSetting C)
    (hE : EComp5 D C) (hH : D.HComp C)
    (hCount : Count5 D C)
    (hSl : D.Slopes C)
    (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : LossBounds D C)
    (hHH : D.HHBound C) (u0 : U0) :
    D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0) ≤
      UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
        (UBar5 D C Xpp + D.x ^ C.cHH * D.b) := by
  exact harmonicLoss_uniform (D.uF_nonneg C hS u0)
    (hHH u0).2.1.le
    (sourceSpread_le_UBar5 D C Xpp hS hE hH hCount hSl hSN hLoss u0)
    (hHH u0).2.2

/-- The arithmetic source's uniform cap is nonnegative whenever the
original domain is nonempty and the standard hypotheses hold. -/
theorem UBar5_nonneg [Nonempty U0]
    (hS : D.HidaSetting C)
    (hE : EComp5 D C) (hH : D.HComp C)
    (hCount : Count5 D C)
    (hSl : D.Slopes C)
    (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : LossBounds D C) :
    0 ≤ UBar5 D C Xpp := by
  let u0 : U0 := Classical.choice ‹Nonempty U0›
  exact (D.uF_nonneg C hS u0).trans
    (sourceSpread_le_UBar5 D C Xpp hS hE hH hCount hSl hSN hLoss u0)

/-- A uniformly smaller arithmetic error than \`errorTermWith\`,
obtained by replacing only the slope-tail contribution. -/
def errorTermWithIntegrated : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + (C.cDiv * D.nT * D.a * D.La +
        C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + MLo5 D C Xpp
    + (1 - D.delBar)⁻¹ *
      (4 * (UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
          (UBar5 D C Xpp + D.x ^ C.cHH * D.b))
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

/-- The new error really improves the old published logarithmic error,
provided the source spread cap is nonnegative. -/
theorem errorTermWithIntegrated_le_errorTermWith
    (hS : D.HidaSetting C)
    (hUBar : 0 ≤ UBar5 D C Xpp) :
    errorTermWithIntegrated D C Xpp ≤ errorTermWith D C Xpp := by
  have hx : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hS.1 _
  have hb : 0 < D.b := hS.2.1
  have hHbar : 0 ≤ D.x ^ C.cHH * D.b := (mul_pos hx hb).le
  have hsharp := harmonicLoss_le_log (UBar5 D C Xpp)
    (D.x ^ C.cHH * D.b) hUBar hHbar
  have hlog := phi_bound (u := UBar5 D C Xpp)
    (H := D.x ^ C.cHH * D.b)
    (X := D.x ^ C.cHH) (b := D.b) (U := UBar5 D C Xpp)
    hUBar (mul_pos hx hb) le_rfl hb hx le_rfl
  have hcompare :
      4 * (UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
          (UBar5 D C Xpp + D.x ^ C.cHH * D.b)) ≤
        4 * Real.log (1 + D.x ^ C.cHH) * (UBar5 D C Xpp + D.b) := by
    nlinarith [hsharp, hlog]
  have hinv : 0 ≤ (1 - D.delBar)⁻¹ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hd, _, _, _⟩ := hS
    exact inv_nonneg.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hcompare hinv
  unfold errorTermWithIntegrated errorTermWith
  linarith

end

end Formalism.LFunctionChainParameters.WeightedSlopeBounds
