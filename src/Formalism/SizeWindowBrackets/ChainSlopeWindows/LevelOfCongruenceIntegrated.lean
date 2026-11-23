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


/-- The actual level-of-congruence Ga bound with harmonic, rather than
logarithmic, uniform error. The nonnegative spread cap and the upper
height cap are proved from the same existing source assumptions. -/
theorem Ga_bound5_integrated
    (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C)
    (hH : D.HComp C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hLoss : LossBounds D C) (hSI : D.SlopeIneqIntegrated)
    (hHH : D.HHBound C) (hFP : D.FParams) (u0 : U0) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ)
      + K0v5 D C + wmean (D.d u0) (Lo5 D C Xpp u0)
      + (1 - D.delBar)⁻¹ *
          (4 * (UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
            (UBar5 D C Xpp + D.x ^ C.cHH * D.b))
          + (D.etaBar + 4 * Real.sqrt D.eBar) *
            (D.x ^ C.cHH * D.b)) := by
  have hsl := s_lower5 D C Xpp hS hDIV hE hCount hSl hSN u0
  have huF0 := D.uF_nonneg C hS u0
  have hratio := sourceHarmonicLoss_le_uniform D C Xpp
    hS hE hH hCount hSl hSN hLoss hHH u0
  obtain ⟨hx, hb, -, -, -, hv, hf, -, hw, -, -, -, -, hdelBar, hetaBar,
      heBar0, heBar⟩ := hS
  have hid := key_identity5 D C hv hf u0 (hw u0)
  obtain ⟨hdel0, hdelle, heta0, hetale, he0, hele⟩ := hFP u0
  obtain ⟨hHH1, hHH2, hHH3⟩ := hHH u0
  have hSI' := hSI u0 hdel0 (by linarith) heta0 he0 (by linarith) hHH1 hHH2
  have hratio0 :
      0 ≤ D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0) :=
    div_nonneg (mul_nonneg huF0 hHH2.le) (add_nonneg huF0 hHH2.le)
  have hsq : Real.sqrt (D.e u0) ≤ Real.sqrt D.eBar :=
    Real.sqrt_le_sqrt hele
  have hc0 : 0 ≤ D.η u0 + 4 * Real.sqrt (D.e u0) :=
    add_nonneg heta0 (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hc1 : 0 ≤ D.etaBar + 4 * Real.sqrt D.eBar :=
    add_nonneg hetaBar (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hB :
      (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 ≤
        (D.etaBar + 4 * Real.sqrt D.eBar) *
          (D.x ^ C.cHH * D.b) :=
    calc
      _ ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * D.HH u0 :=
        mul_le_mul_of_nonneg_right (by linarith) hHH2.le
      _ ≤ (D.etaBar + 4 * Real.sqrt D.eBar) *
          (D.x ^ C.cHH * D.b) :=
        mul_le_mul_of_nonneg_left hHH3 hc1
  have hB0 :
      0 ≤ (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 :=
    mul_nonneg hc0 hHH2.le
  have hinv : (1 - D.del u0)⁻¹ ≤ (1 - D.delBar)⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ :=
    inv_nonneg.mpr (by linarith)
  have hPhi :
      (1 - D.del u0)⁻¹ *
        (4 * (D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0))
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤
      (1 - D.delBar)⁻¹ *
        (4 * (UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
          (UBar5 D C Xpp + D.x ^ C.cHH * D.b))
          + (D.etaBar + 4 * Real.sqrt D.eBar) *
            (D.x ^ C.cHH * D.b)) :=
    calc
      _ ≤ (1 - D.delBar)⁻¹ *
          (4 * (D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0))
            + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) :=
        mul_le_mul_of_nonneg_right hinv (by nlinarith [hratio0, hB0])
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left (by nlinarith [hratio, hB]) hinv0
  unfold K0v5
  unfold K5v5 at hsl
  linarith


/-- Stronger arithmetic mean-bound interface using the same original
hypotheses, except for the sharpened local integrated-slope inequality.
It leaves the old \`MeanBoundWith\` unchanged. -/
def MeanBoundWithIntegrated : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → EComp5 D C →
    D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C →
    D.SlopeIneqIntegrated → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + errorTermWithIntegrated D C Xpp

/-- The original weighted-mean calculation with the now-checked sharp
source-level bound, rather than a comparison against the old logarithmic
error. -/
theorem weighted_mean_bound_integrated : MeanBoundWithIntegrated D C Xpp := by
  intro hne hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
  letI : Nonempty U0 := hne
  have hcSl1 : 0 ≤ C.cSl1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, _, _, _, _⟩ := hS
    exact hc
  have hGa : ∀ u0, D.Ga u0 ≤
      D.Main u0 + Real.log (Fintype.card (W u0) : ℝ)
        + C.cSl1 * D.IO u0 + 0 * D.IO u0
        + (K0v5 D C + K7v5 D C Xpp
          + (1 - D.delBar)⁻¹ *
            (4 * (UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
              (UBar5 D C Xpp + D.x ^ C.cHH * D.b))
             + (D.etaBar + 4 * Real.sqrt D.eBar) *
               (D.x ^ C.cHH * D.b))) := by
    intro u0
    have h1 := Ga_bound5_integrated D C Xpp
      hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP u0
    have h2 := weighted_mean_lower_bound_le D C Xpp hS hCount u0
    linarith
  have h1 := umean_le_comb (X := D.Ga) (A := D.Main)
    (B := fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    (P := D.IO) (E := D.IO)
    (C.cSl1) 0
    (K0v5 D C + K7v5 D C Xpp
      + (1 - D.delBar)⁻¹ *
        (4 * (UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
          (UBar5 D C Xpp + D.x ^ C.cHH * D.b))
         + (D.etaBar + 4 * Real.sqrt D.eBar) *
           (D.x ^ C.cHH * D.b))) hGa
  have h2 := umean_le_comb (X := D.ASK)
    (A := fun u0 => D.ASK u0 - D.Ga u0) (B := D.Ga)
    (P := D.Ga) (E := D.Ga) 0 0 0 (fun i => by
      show D.ASK i ≤
        (D.ASK i - D.Ga i) + D.Ga i +
          0 * D.Ga i + 0 * D.Ga i + 0
      linarith)
  have hLoss' := losses_of_losses5 D C hLoss
  have h3 := mul_le_mul_of_nonneg_left hLoss'.2 hcSl1
  have h4 := hLoss'.1
  dsimp only [K0v5, K7v5, Data.EDiv] at h1
  unfold errorTermWithIntegrated MLo5
  linarith


/-- The harmonic tail contribution is bounded by its input spread,
including the zero-denominator case of Lean's totalized division. -/
theorem harmonicLoss_le_spread (u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H) :
    u * H / (u + H) ≤ u := by
  rcases (add_nonneg hu hH).eq_or_lt with hzero | hpos
  · have hu0 : u = 0 := by linarith
    simp [hu0]
  · apply (div_le_iff₀ hpos).2
    nlinarith [sq_nonneg u]

/-- A simpler arithmetic budget with no logarithm and no denominator
in the *rank-tail* contribution. Other independently occurring
logarithms in the arithmetic argument are deliberately unchanged. -/
def errorTermWithSpreadCap : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + (C.cDiv * D.nT * D.a * D.La +
        C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + MLo5 D C Xpp
    + (1 - D.delBar)⁻¹ *
        (4 * UBar5 D C Xpp +
          (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

/-- The full harmonic budget implies the pure-spread budget under
the existing positivity assumptions. No asymptotic approximation
or new geometric hypothesis is used. -/
theorem errorTermWithIntegrated_le_spreadCap
    (hS : D.HidaSetting C) (hU : 0 ≤ UBar5 D C Xpp) :
    errorTermWithIntegrated D C Xpp ≤
      errorTermWithSpreadCap D C Xpp := by
  have hx : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hS.1 _
  have hb : 0 < D.b := hS.2.1
  have hH : 0 ≤ D.x ^ C.cHH * D.b := (mul_pos hx hb).le
  have htail := harmonicLoss_le_spread
    (UBar5 D C Xpp) (D.x ^ C.cHH * D.b) hU hH
  have hinv : 0 ≤ (1 - D.delBar)⁻¹ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hd, _, _, _⟩ := hS
    exact inv_nonneg.mpr (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left
    (show
      4 * (UBar5 D C Xpp * (D.x ^ C.cHH * D.b) /
          (UBar5 D C Xpp + D.x ^ C.cHH * D.b)) +
        (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) ≤
      4 * UBar5 D C Xpp +
        (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) by
        nlinarith [htail]) hinv
  unfold errorTermWithIntegrated errorTermWithSpreadCap
  linarith

/-- The actual sharpened arithmetic mean bound also yields a uniform
spread-only rank-tail budget. All other original hypotheses are kept;
in particular the source realization of SlopeIneqIntegrated remains
a separate, explicit proof obligation. -/
def MeanBoundWithSpreadCap : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → EComp5 D C →
    D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C →
    D.SlopeIneqIntegrated → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + errorTermWithSpreadCap D C Xpp

theorem weighted_mean_bound_spread_cap : MeanBoundWithSpreadCap D C Xpp := by
  intro hne hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
  letI : Nonempty U0 := hne
  have hU := UBar5_nonneg D C Xpp hS hE hH hCount hSl hSN hLoss
  have hmean := weighted_mean_bound_integrated D C Xpp
    hne hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
  have herr := errorTermWithIntegrated_le_spreadCap D C Xpp hS hU
  linarith

end

end Formalism.LFunctionChainParameters.WeightedSlopeBounds

#print axioms Formalism.LFunctionChainParameters.WeightedSlopeBounds.Ga_bound5_integrated
#print axioms Formalism.LFunctionChainParameters.WeightedSlopeBounds.weighted_mean_bound_integrated

#print axioms Formalism.LFunctionChainParameters.WeightedSlopeBounds.errorTermWithIntegrated_le_spreadCap
#print axioms Formalism.LFunctionChainParameters.WeightedSlopeBounds.weighted_mean_bound_spread_cap
