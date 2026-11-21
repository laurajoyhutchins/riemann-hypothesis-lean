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

/-! ## From a fixed finite slope family to its threshold integral -/

/-- A threshold indicator is antitone as the threshold grows. -/
private theorem indicatorAntitone (c : ℝ) :
    Antitone (fun t : ℝ => if t < c then (1 : ℝ) else 0) := by
  intro a b hab
  by_cases hb : b < c
  · have ha : a < c := lt_of_le_of_lt hab hb
    simp [ha, hb]
  · by_cases ha : a < c <;> simp [ha, hb]

/-- The integral of a strict threshold indicator is at most the capped positive
part. Unlike the log-envelope estimate, this uses the actual shared threshold. -/
private theorem indicatorIntegral_le_clipped (c H : ℝ) (hH : 0 ≤ H) :
    (∫ t in (0 : ℝ)..H, if t < c then (1 : ℝ) else 0) ≤ min H (max c 0) := by
  rcases le_total c 0 with hc0 | hc0
  · have hbound :
        (∫ t in (0 : ℝ)..H, if t < c then (1 : ℝ) else 0) ≤
          ∫ _t in (0 : ℝ)..H, (0 : ℝ) := by
      apply intervalIntegral.integral_mono_on hH
        (indicatorAntitone c).intervalIntegrable intervalIntegrable_const
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) H := by
        simpa [Set.uIcc_of_le hH] using ht
      have hnot : ¬ t < c := not_lt.mpr (le_trans hc0 ht'.1)
      simp [hnot]
    simpa [max_eq_right hc0, min_eq_right hH] using hbound
  · rcases le_total c H with hcH | hcH
    · have hi1 : IntervalIntegrable
          (fun t : ℝ => if t < c then (1 : ℝ) else 0) MeasureTheory.volume 0 c :=
        (indicatorAntitone c).intervalIntegrable
      have hi2 : IntervalIntegrable
          (fun t : ℝ => if t < c then (1 : ℝ) else 0) MeasureTheory.volume c H :=
        (indicatorAntitone c).intervalIntegrable
      have hfirst :
          (∫ t in (0 : ℝ)..c, if t < c then (1 : ℝ) else 0) ≤ c := by
        have h := intervalIntegral.integral_mono_on hc0 hi1 intervalIntegrable_const
          (fun t _ => by split_ifs <;> norm_num)
        simpa using h
      have hsecond :
          (∫ t in c..H, if t < c then (1 : ℝ) else 0) ≤ 0 := by
        have h := intervalIntegral.integral_mono_on hcH hi2 intervalIntegrable_const
          (fun t ht => by
            have ht' : t ∈ Set.Icc c H := by simpa [Set.uIcc_of_le hcH] using ht
            simp [not_lt.mpr ht'.1])
        simpa using h
      have hbound :
          (∫ t in (0 : ℝ)..H, if t < c then (1 : ℝ) else 0) ≤ c := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
        linarith
      simpa [max_eq_left hc0, min_eq_right hcH] using hbound
    · have hbound :
          (∫ t in (0 : ℝ)..H, if t < c then (1 : ℝ) else 0) ≤
            ∫ _t in (0 : ℝ)..H, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hH
          (indicatorAntitone c).intervalIntegrable intervalIntegrable_const
        intro t ht
        split_ifs <;> norm_num
      simpa [max_eq_left hc0, min_eq_left hcH] using hbound

/-- Integrate the *actual finite threshold counts* rather than their
pointwise envelope. The full geometric theorem must preserve this function
through its rank comparison to use this improvement. -/
theorem finiteThresholdIntegralBound (N : ℕ) (a : Fin N → ℝ)
    (s u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H) (hpos : 0 < u + H)
    (hmean : (N : ℝ) * s ≤ ∑ i, a i)
    (hupper : ∀ i, a i ≤ s + u) :
    (∫ t in (0 : ℝ)..H,
      ((Finset.univ.filter (fun i : Fin N => a i < s - t)).card : ℝ)) ≤
        (N : ℝ) * (u * H / (u + H)) := by
  have hcount (t : ℝ) :
      ((Finset.univ.filter (fun i : Fin N => a i < s - t)).card : ℝ) =
        ∑ i : Fin N, if t < s - a i then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
    congr 1
    apply Finset.filter_congr
    intro i _
    constructor <;> intro h <;> linarith
  have heq :
      (fun t : ℝ => ((Finset.univ.filter (fun i : Fin N => a i < s - t)).card : ℝ)) =
        (fun t : ℝ => ∑ i : Fin N, if t < s - a i then (1 : ℝ) else 0) := by
    funext t
    exact hcount t
  rw [show (∫ t in (0 : ℝ)..H,
      ((Finset.univ.filter (fun i : Fin N => a i < s - t)).card : ℝ)) =
      ∫ t in (0 : ℝ)..H, ∑ i : Fin N, if t < s - a i then (1 : ℝ) else 0 from by
        exact congrArg (fun f : ℝ → ℝ => ∫ t in (0 : ℝ)..H, f t) heq]
  rw [intervalIntegral.integral_finset_sum
    (fun i _ => (indicatorAntitone (s - a i)).intervalIntegrable)]
  have hstep :
      (∑ i : Fin N, ∫ t in (0 : ℝ)..H, if t < s - a i then (1 : ℝ) else 0) ≤
        ∑ i : Fin N, min H (max (s - a i) 0) :=
    Finset.sum_le_sum (fun i _ => indicatorIntegral_le_clipped (s - a i) H hH)
  have hclip :
      (∑ i : Fin N, min H (max (s - a i) 0)) ≤
        (N : ℝ) * (u * H / (u + H)) := by
    have h := finiteClippedShortfallBound_div (Finset.univ : Finset (Fin N))
      a s u H hu hH hpos (by simpa using hmean) (by intro i _; exact hupper i)
    simpa using h
  exact le_trans hstep hclip


end Formalism.HN
