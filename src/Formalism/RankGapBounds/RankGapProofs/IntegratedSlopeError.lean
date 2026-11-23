import Formalism.RankGapBounds.RankGapProofs.WeightedMeanData
import Formalism.RankGapBounds.RankGapProofs.SharpLossBound

/-!
# Arithmetic interface for the logarithm-free slope loss

The original \`Data.SlopeIneq\` must retain its published mathematical
contract. We introduce a separate stronger hypothesis with precisely the
rational rank-loss term and show it implies the old logarithmic hypothesis
under the existing positivity conditions.

The uniform harmonic-error bound will be used when replacing the old
\`phi_bound\` step in the second-form mean-bound proof.
-/

namespace Formalism.RankGapBounds.WeightedMeanData

noncomputable section

variable {U0 : Type} [Fintype U0] [Nonempty U0]
  {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}

namespace Data

variable (D : Data U0 W Top m f) (C : Consts)

/-- Sharper arithmetic slope interface, keeping all of the old
parameter assumptions but replacing the logarithmic loss by the
uniformly sharper harmonic loss. -/
def SlopeIneqIntegrated : Prop :=
  ∀ u0, 0 ≤ D.del u0 → D.del u0 < 1 →
    0 ≤ D.η u0 → 0 ≤ D.e u0 → D.e u0 ≤ 1 / 4 →
    D.s u0 - D.muMinCC u0 ≤ D.HH u0 → 0 < D.HH u0 →
    D.s u0 - Real.log (Fintype.card (W u0) : ℝ)
      - (1 - D.del u0)⁻¹ *
        (4 * (D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0)) +
          (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤ D.muCC u0

/-- The integrated geometric theorem supplies the old arithmetic
slope hypothesis without changing any existing consumers. -/
theorem slopeIneq_of_integrated
    (hS : D.HidaSetting C) (hSI : D.SlopeIneqIntegrated) :
    D.SlopeIneq := by
  intro u0 hdel0 hdel1 heta he0 he1 hHH hHHpos
  have hu : 0 ≤ D.uF u0 := D.uF_nonneg C hS u0
  have hharmonic := harmonicLoss_le_log (D.uF u0) (D.HH u0) hu hHHpos.le
  have hmul :
      4 * (D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0)) +
        (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 ≤
      4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) +
        (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 := by
    nlinarith
  have hinv : 0 ≤ (1 - D.del u0)⁻¹ :=
    inv_nonneg.mpr (by linarith)
  have hloss := mul_le_mul_of_nonneg_left hmul hinv
  have hsharp := hSI u0 hdel0 hdel1 heta he0 he1 hHH hHHpos
  linarith

/-- The uniform height cap in \`HHBound\` and any established spread cap
can be inserted directly into the rational error term. -/
theorem harmonicLoss_of_HHBound
    (hS : D.HidaSetting C) (hHH : D.HHBound C)
    (u0 : U0) (U : ℝ) (huU : D.uF u0 ≤ U) :
    D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0) ≤
      U * (D.x ^ C.cHH * D.b) / (U + D.x ^ C.cHH * D.b) :=
  harmonicLoss_uniform (D.uF_nonneg C hS u0)
    (hHH u0).2.1.le huU (hHH u0).2.2

/-- Fully uniform arithmetic error with a harmonic rank-loss term. The
remaining additive terms are unchanged from \`ErrX\`. -/
def ErrXIntegrated : ℝ :=
  D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) +
      2 * D.logGam / ((f : ℝ) * D.k))
    + (C.cDiv * D.nT * D.a * D.La +
       C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + D.MLo C
    + (1 - D.delBar)⁻¹ *
        (4 * (D.UBar C * (D.x ^ C.cHH * D.b) /
           (D.UBar C + D.x ^ C.cHH * D.b))
          + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

/-- Under the natural nonnegative uniform-spread hypothesis, the new
arithmetic error does not exceed the older logarithmic bound. -/
theorem errXIntegrated_le_errX
    (hS : D.HidaSetting C) (hUBar : 0 ≤ D.UBar C) :
    D.ErrXIntegrated C ≤ D.ErrX C := by
  have hx : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hS.1 _
  have hb : 0 < D.b := hS.2.1
  have hcap : 0 ≤ D.x ^ C.cHH * D.b := (mul_pos hx hb).le
  have hsharp := harmonicLoss_le_log (D.UBar C)
    (D.x ^ C.cHH * D.b) hUBar hcap
  have hlog := phi_bound (u := D.UBar C)
    (H := D.x ^ C.cHH * D.b) (X := D.x ^ C.cHH)
    (b := D.b) (U := D.UBar C) hUBar (mul_pos hx hb) le_rfl hb hx le_rfl
  have hcompare :
      4 * (D.UBar C * (D.x ^ C.cHH * D.b) /
          (D.UBar C + D.x ^ C.cHH * D.b)) ≤
        4 * Real.log (1 + D.x ^ C.cHH) * (D.UBar C + D.b) := by
    nlinarith [hsharp, hlog]
  have hinv : 0 ≤ (1 - D.delBar)⁻¹ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdelBar, _, _, _⟩ := hS
    exact inv_nonneg.mpr (by linarith)
  have hcompare' := mul_le_mul_of_nonneg_left hcompare hinv
  unfold ErrXIntegrated Data.ErrX
  linarith

end Data

end

end Formalism.RankGapBounds.WeightedMeanData
