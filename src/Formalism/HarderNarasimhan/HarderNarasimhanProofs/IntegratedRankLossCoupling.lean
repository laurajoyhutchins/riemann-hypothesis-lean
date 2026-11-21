import Formalism.HarderNarasimhan.HarderNarasimhanProofs.IntegratedRankLoss
import Formalism.CorankShare.CorankShareProofs.LayerCakeFormula

/-!
# Coupled finite input and target slopes

The abstract input shortfall inequality is useful for the original RH
formalization only if the same input slope distribution controls the
geometric target rank loss at every threshold. This theorem isolates
precisely that interface.

The layer-cake argument is reused from the original source, not reimplemented.
-/

namespace Formalism.HN

open Finset MeasureTheory
open Formalism.CorankShareLayerCake.FR

/-- Finite layer-cake comparison with a coupled, rather than pointwise-enveloped,
input corank. The target loss bound follows from the actual input distribution.
No input rank divisor appears; a caller may put it into C1 explicitly. -/
theorem coupledFiniteSlopeBound (N M : ℕ) (a : Fin N → ℝ) (b : Fin M → ℝ)
    (s u H C0 C1 : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H) (hpos : 0 < u + H)
    (hM : 0 < M) (hC1 : 0 ≤ C1)
    (hmean : (N : ℝ) * s ≤ ∑ i, a i)
    (hupper : ∀ i, a i ≤ s + u)
    (hlower : ∀ j, s - H ≤ b j)
    (hcount : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((univ.filter (fun j : Fin M => b j < s - t)).card : ℝ) ≤
        (C0 + C1 * ((univ.filter (fun i : Fin N => a i < s - t)).card : ℝ)) *
          (M : ℝ)) :
    s - (∑ j, b j) / (M : ℝ) ≤
      C0 * H + C1 * ((N : ℝ) * (u * H / (u + H))) := by
  let r : ℝ → ℝ := fun t =>
    ((univ.filter (fun i : Fin N => a i < s - t)).card : ℝ)
  let w : ℝ → ℝ := fun t => C0 + C1 * r t
  have hranti : Antitone r := by
    intro t₁ t₂ hle
    have hs : (univ.filter (fun i : Fin N => a i < s - t₂)) ⊆
        (univ.filter (fun i : Fin N => a i < s - t₁)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      linarith
    exact_mod_cast Finset.card_le_card hs
  have hwanti : Antitone w := by
    intro t₁ t₂ ht
    have hc := hranti ht
    dsimp [w]
    nlinarith [mul_nonneg hC1 (sub_nonneg.mpr hc)]
  have hri : IntervalIntegrable r MeasureTheory.volume 0 H :=
    hranti.intervalIntegrable
  have hwi : IntervalIntegrable w MeasureTheory.volume 0 H :=
    hwanti.intervalIntegrable
  have hminanti : Antitone (fun t : ℝ => min 1 (w t)) := by
    intro t₁ t₂ ht
    exact min_le_min_left (1 : ℝ) (hwanti ht)
  have hmini : IntervalIntegrable (fun t : ℝ => min 1 (w t))
      MeasureTheory.volume 0 H := hminanti.intervalIntegrable
  have hcount' : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((univ.filter (fun j : Fin M => b j < s - t)).card : ℝ) ≤
        w t * (M : ℝ) := by
    intro t ht
    exact hcount t ht
  have hLC : s - (∫ t in (0 : ℝ)..H, min 1 (w t)) ≤
      (∑ j, b j) / (M : ℝ) :=
    layer_cake_formula M b s H w hM hH hlower hmini hcount'
  have hint :
      (∫ t in (0 : ℝ)..H, w t) =
        C0 * H + C1 * (∫ t in (0 : ℝ)..H, r t) := by
    dsimp [w]
    rw [intervalIntegral.integral_add intervalIntegrable_const (hri.const_mul C1),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  have hmono :
      (∫ t in (0 : ℝ)..H, min 1 (w t)) ≤
        ∫ t in (0 : ℝ)..H, w t := by
    apply intervalIntegral.integral_mono_on hH hmini hwi
    intro t _
    exact min_le_right 1 (w t)
  have hinput :
      (∫ t in (0 : ℝ)..H, r t) ≤
        (N : ℝ) * (u * H / (u + H)) := by
    simpa only [r] using finiteThresholdIntegralBound N a s u H
      hu hH hpos hmean hupper
  have hscaled := mul_le_mul_of_nonneg_left hinput hC1
  rw [hint] at hmono
  linarith

end Formalism.HN
