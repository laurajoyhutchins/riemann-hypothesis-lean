module

public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.BasicNotions

open NumberField

variable {R : Ranks}

theorem Host.sqrtMinusD_sq (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem Host.conj_sqrtMinusD (H : Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h1 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := H.conjE_apply H.φ₀ H.sqrtMinusD
  rw [h1, map_neg]
  set z := H.φ₀ H.sqrtMinusD
  have hz : z ^ 2 = -(H.d : ℂ) := by rw [← map_pow, H.sqrtMinusD_sq]; simp
  have hre : z.re = 0 := by
    have h2 := congrArg Complex.im hz
    have h3 := congrArg Complex.re hz
    simp [pow_two] at h2 h3
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    rcases mul_eq_zero.mp (show z.re * z.im * 2 = 0 by linarith) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · rw [h] at h3; nlinarith [sq_nonneg z.re]
    · norm_num at h
  apply Complex.ext <;> simp [hre]

theorem Host.exists_trace_one (H : Host R) : ∃ c : 𝓞 H.E, (c : H.E) + H.conj c = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.hyp.2.2.2.1; omega⟩
  set c : H.E := (1 + H.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : H.E) = 0 := by
    have e : ((H.d : ℕ) : H.E) + 1 = 4 * (m : H.E) := by exact_mod_cast hm
    have hs := H.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : H.E) * hs - (1 / 4 : H.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, ?_⟩
  show c + H.conj c = 1
  simp only [c, map_div₀, map_add (f := _), map_one, H.conj_sqrtMinusD, map_ofNat]
  ring

end Formalism.BasicNotions
