import Formalism.HarderNarasimhan.HarderNarasimhanProofs.IntegratedRankLossTargetTransfer

/-!
# Recovering the published logarithmic allowance from sharp integrated loss

A strengthened geometric estimate must imply (not replace by fiat) the
unchanged \`TheoremFSharp\` conclusion. The elementary inequality
  u*H/(u+H) ≤ u*log(1+H/u)
for u,H≥0 is the missing analytic dominance needed for that implication.
For u=0 the expression follows Lean's totalized division conventions.
-/

namespace Formalism.HN

/-- The sharp input allowance is at most the logarithmic allowance when
the upper-variation parameter is strictly positive. -/
theorem sharpIntegratedLoss_le_log_pos
    (u H : ℝ) (hu : 0 < u) (hH : 0 ≤ H) :
    u * H / (u + H) ≤ u * Real.log (1 + H / u) := by
  have hq : 0 < 1 + H / u := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hq
  have hden : u + H ≠ 0 := ne_of_gt (by linarith)
  have hu0 : u ≠ 0 := hu.ne'
  have heq : u * H / (u + H) = u * (1 - (1 + H / u)⁻¹) := by
    have hsum : 1 + H / u = (u + H) / u := by
      field_simp <;> ring
    rw [hsum]
    have hnonzero : (u + H) / u ≠ 0 := div_ne_zero hden hu0
    field_simp <;> ring
  calc
    _ = u * (1 - (1 + H / u)⁻¹) := heq
    _ ≤ u * Real.log (1 + H / u) := mul_le_mul_of_nonneg_left hlog hu.le

/-- The conclusion of the sharp integrated slope theorem implies the
published logarithmic allowance for all nonnegative parameters. -/
theorem sharpIntegratedLoss_le_log
    (u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H) :
    u * H / (u + H) ≤ u * Real.log (1 + H / u) := by
  rcases eq_or_lt_of_le hu with hzero | hpos
  · rw [← hzero]
    simp
  · exact sharpIntegratedLoss_le_log_pos u H hpos hH

/-- Multiply the sharp-vs-log inequality by the nonnegative rank deficit
normalization, retaining the frame term unchanged. -/
theorem sharpFrameAllowance_le_log
    (u H A δ : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H) (hδ : δ < 1) :
    (1 - δ)⁻¹ * (A * H + 4 * (u * H / (u + H))) ≤
      (1 - δ)⁻¹ * (A * H + 4 * u * Real.log (1 + H / u)) := by
  have h1 := sharpIntegratedLoss_le_log u H hu hH
  have h2 : 0 ≤ (1 - δ)⁻¹ :=
    le_of_lt (inv_pos.mpr (by linarith : (0 : ℝ) < 1 - δ))
  have hbase :
      A * H + 4 * (u * H / (u + H)) ≤
        A * H + 4 * u * Real.log (1 + H / u) := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hbase h2

end Formalism.HN
