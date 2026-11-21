import Mathlib

/-!
# A finite integrated shortfall inequality

This elementary result is independent of the theta-lift and Hermitian-lattice
constructions. It is the algebraic core of the integrated low-slope estimate
in Proposition 2.1 of *Three simplifications in the Alpöge–Claude argument
for Dirichlet GRH* (twinheterodox, 21 November 2026).

This module proves only the finite slope inequality. A separate source-level
bridge is needed to use it in `Formalism.HN.theoremFSharp_of`.
-/

namespace Formalism.HN

private theorem clippedShortfall_majorant (z u H : ℝ)
    (hu : 0 ≤ u) (hH : 0 ≤ H) (hz : -u ≤ z) :
    (u + H) * min H (max z 0) ≤ H * (z + u) := by
  rcases le_total z 0 with hz0 | hz0
  · rw [max_eq_right hz0, min_eq_right hH]
    have hzu : 0 ≤ z + u := by linarith
    nlinarith [mul_nonneg hH hzu]
  · rw [max_eq_left hz0]
    rcases le_total z H with hle | hle
    · rw [min_eq_right hle]
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hle)]
    · rw [min_eq_left hle]
      nlinarith [mul_nonneg hH (sub_nonneg.mpr hle)]

/-- The integrated low-slope loss in denominator-free form. The mean and
upper-bound assumptions apply to the *same* finite list of slopes; they cannot
be replaced by independent pointwise tail-probability estimates. This form
includes the degenerate case `u = H = 0` without division by zero. -/
theorem finiteClippedShortfallBound {α : Type*} (S : Finset α) (a : α → ℝ)
    (s u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H)
    (hmean : (S.card : ℝ) * s ≤ S.sum a)
    (hupper : ∀ i ∈ S, a i ≤ s + u) :
    (u + H) * S.sum (fun i => min H (max (s - a i) 0)) ≤
      (S.card : ℝ) * u * H := by
  have hpoint (i : α) (hi : i ∈ S) :
      (u + H) * min H (max (s - a i) 0) + H * a i ≤ H * (s + u) := by
    have h := clippedShortfall_majorant (s - a i) u H hu hH (by linarith [hupper i hi])
    nlinarith [h]
  have hsum :
      S.sum (fun i => (u + H) * min H (max (s - a i) 0) + H * a i) ≤
        S.sum (fun _ => H * (s + u)) :=
    Finset.sum_le_sum (fun i hi => hpoint i hi)
  have htotal :
      (u + H) * S.sum (fun i => min H (max (s - a i) 0)) + H * S.sum a ≤
        (S.card : ℝ) * (H * (s + u)) := by
    simpa only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      using hsum
  have hmean' : 0 ≤ H * (S.sum a - (S.card : ℝ) * s) :=
    mul_nonneg hH (sub_nonneg.mpr hmean)
  nlinarith [htotal, hmean']

/-- The positive-denominator version, normalized by the number of input
slopes only when needed. -/
theorem finiteClippedShortfallBound_div {α : Type*} (S : Finset α) (a : α → ℝ)
    (s u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H) (hpos : 0 < u + H)
    (hmean : (S.card : ℝ) * s ≤ S.sum a)
    (hupper : ∀ i ∈ S, a i ≤ s + u) :
    S.sum (fun i => min H (max (s - a i) 0)) ≤
      (S.card : ℝ) * (u * H / (u + H)) := by
  have h := finiteClippedShortfallBound S a s u H hu hH hmean hupper
  have h' : S.sum (fun i => min H (max (s - a i) 0)) ≤
      ((S.card : ℝ) * u * H) / (u + H) := by
    apply (le_div_iff₀ hpos).2
    nlinarith [h]
  calc
    _ ≤ ((S.card : ℝ) * u * H) / (u + H) := h'
    _ = (S.card : ℝ) * (u * H / (u + H)) := by ring

end Formalism.HN
