import Formalism.HarderNarasimhan.HarderNarasimhanProofs.IntegratedRankLossCoupling

/-!
# Source-compatible normalization of geometric rank loss

The placement estimate is naturally phrased over the coefficient field.
The slope distribution is counted with real-rank multiplicity. This theorem
checks the exact degree factor required to pass between them.

The geometric pointwise estimate and the rank-count identity are explicit
premises. Discharging them from `thmF_place` and `frameB_count_lt` in
`TheoremFSharp.lean` remains a separate source-integration obligation.
-/

namespace Formalism.HN

open Finset

/--
If a low-slope real-rank count is exactly the field-degree multiple of the
coefficient-field corank, and total real rank has the same normalization,
then a pointwise *actual-corank* geometric estimate gives the sharp
integrated target-slope bound. This retains the same corank function at
every threshold; a free pointwise envelope does not suffice.
-/
theorem realRankNormalizedCoupledSlopeBound {α : Type*}
    (S : Finset α) (M : ℕ) (a : α → ℝ) (b : Fin M → ℝ)
    (fieldDegree inputRank : ℝ) (corank : ℝ → ℝ)
    (s u H δ A : ℝ)
    (hu : 0 ≤ u) (hH : 0 ≤ H) (hpos : 0 < u + H)
    (hM : 0 < M) (hδ : δ < 1)
    (hdegree : 0 < fieldDegree) (hrank : 0 < inputRank)
    (hcard : (S.card : ℝ) = fieldDegree * inputRank)
    (hmean : (S.card : ℝ) * s ≤ S.sum a)
    (hupper : ∀ i ∈ S, a i ≤ s + u)
    (hlower : ∀ j, s - H ≤ b j)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) H,
      fieldDegree * corank t =
        ((S.filter (fun i => a i < s - t)).card : ℝ))
    (hgeometric : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((univ.filter (fun j : Fin M => b j < s - t)).card : ℝ) ≤
        (M : ℝ) * ((1 - δ)⁻¹ * (A + 4 * (corank t / inputRank)))) :
    s - (∑ j, b j) / (M : ℝ) ≤
      (1 - δ)⁻¹ * (A * H + 4 * (u * H / (u + H))) := by
  classical
  have hN : (0 : ℝ) < (S.card : ℝ) := by
    rw [hcard]
    exact mul_pos hdegree hrank
  have hscale : 0 ≤ (1 - δ)⁻¹ := by
    exact le_of_lt (inv_pos.mpr (by linarith : (0 : ℝ) < 1 - δ))
  have hC1 : 0 ≤ (1 - δ)⁻¹ * 4 / (S.card : ℝ) := by
    exact div_nonneg (mul_nonneg hscale (by norm_num)) hN.le
  have hratio (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) H) :
      corank t / inputRank =
        ((S.filter (fun i => a i < s - t)).card : ℝ) / (S.card : ℝ) := by
    apply (div_eq_div_iff hrank.ne' hN.ne').2
    calc
      corank t * (S.card : ℝ) =
          corank t * (fieldDegree * inputRank) := by rw [hcard]
      _ = (fieldDegree * corank t) * inputRank := by ring
      _ = ((S.filter (fun i => a i < s - t)).card : ℝ) * inputRank := by
        rw [hreal t ht]
  have htarget : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((univ.filter (fun j : Fin M => b j < s - t)).card : ℝ) ≤
        ((1 - δ)⁻¹ * A +
          ((1 - δ)⁻¹ * 4 / (S.card : ℝ)) *
            ((S.filter (fun i => a i < s - t)).card : ℝ)) * (M : ℝ) := by
    intro t ht
    calc
      _ ≤ (M : ℝ) * ((1 - δ)⁻¹ * (A + 4 * (corank t / inputRank))) :=
        hgeometric t ht
      _ = ((1 - δ)⁻¹ * A +
        ((1 - δ)⁻¹ * 4 / (S.card : ℝ)) *
          ((S.filter (fun i => a i < s - t)).card : ℝ)) * (M : ℝ) := by
        rw [hratio t ht]
        ring
  have hbound :=
    coupledFinsetSlopeBound S M a b s u H
      ((1 - δ)⁻¹ * A) ((1 - δ)⁻¹ * 4 / (S.card : ℝ))
      hu hH hpos hM hC1 hmean hupper hlower htarget
  have hcancel :
      ((1 - δ)⁻¹ * 4 / (S.card : ℝ)) * (S.card : ℝ) =
        (1 - δ)⁻¹ * 4 := by
    field_simp
  calc
    _ ≤ (1 - δ)⁻¹ * A * H +
      ((1 - δ)⁻¹ * 4 / (S.card : ℝ)) *
        ((S.card : ℝ) * (u * H / (u + H))) := hbound
    _ = (1 - δ)⁻¹ * (A * H + 4 * (u * H / (u + H))) := by
      rw [← mul_assoc, hcancel]
      ring

end Formalism.HN
