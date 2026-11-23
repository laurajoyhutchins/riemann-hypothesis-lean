import Mathlib

/-!
# Uniform harmonic-mean rank-loss bounds

When the improved geometric estimate supplies the loss \`u*H/(u+H)\`,
the arithmetic reduction must bound both the input spread \`u\` and the
height window \`H\`. The ratio is monotone in *both* nonnegative inputs,
even at the zero endpoints, so one can bound it by one fixed pair of
uniform caps without returning to the older logarithmic envelope.
-/

namespace Formalism.RankGapBounds.WeightedMeanData

/-- Monotonicity of the harmonic rank-loss expression in both variables,
including Lean's totalized 0/0 endpoint. -/
theorem harmonicLoss_mono {u U H T : ℝ}
    (hu : 0 ≤ u) (hH : 0 ≤ H)
    (huU : u ≤ U) (hHT : H ≤ T) :
    u * H / (u + H) ≤ U * T / (U + T) := by
  have hU : 0 ≤ U := hu.trans huU
  have hT : 0 ≤ T := hH.trans hHT
  rcases eq_or_lt_of_le hu with hu0 | huPos
  · subst u
    simpa using (div_nonneg (mul_nonneg hU hT) (add_nonneg hU hT))
  rcases eq_or_lt_of_le hH with hH0 | hHPos
  · subst H
    simpa using (div_nonneg (mul_nonneg hU hT) (add_nonneg hU hT))
  have hUPos : 0 < U := huPos.trans_le huU
  have hTPos : 0 < T := hHPos.trans_le hHT
  have hfirst : u * H / (u + H) ≤ U * H / (U + H) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr huU) (sq_nonneg H)]
  have hsecond : U * H / (U + H) ≤ U * T / (U + T) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (sq_nonneg U) (sub_nonneg.mpr hHT)]
  exact hfirst.trans hsecond

/-- With a height cap X*b and a spread cap U, the improved loss has the
uniform bound U*(X*b)/(U+X*b). No extra logarithmic factor is needed. -/
theorem harmonicLoss_uniform {u H X b U : ℝ}
    (hu : 0 ≤ u) (hH : 0 ≤ H)
    (huU : u ≤ U) (hHX : H ≤ X * b) :
    u * H / (u + H) ≤ U * (X * b) / (U + X * b) :=
  harmonicLoss_mono hu hH huU hHX

/-- The sharp harmonic loss never exceeds the old logarithmic allowance.
The statement includes u=0 (both sides vanish by totalized division). -/
theorem harmonicLoss_le_log (u H : ℝ)
    (hu : 0 ≤ u) (hH : 0 ≤ H) :
    u * H / (u + H) ≤ u * Real.log (1 + H / u) := by
  rcases eq_or_lt_of_le hu with hu0 | huPos
  · subst u
    simp
  have hq : 0 < 1 + H / u := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hq
  have hden : u + H ≠ 0 := ne_of_gt (by linarith)
  have heq : u * H / (u + H) = u * (1 - (1 + H / u)⁻¹) := by
    field_simp
    ring
  calc
    _ = u * (1 - (1 + H / u)⁻¹) := heq
    _ ≤ u * Real.log (1 + H / u) :=
      mul_le_mul_of_nonneg_left hlog huPos.le

end Formalism.RankGapBounds.WeightedMeanData
