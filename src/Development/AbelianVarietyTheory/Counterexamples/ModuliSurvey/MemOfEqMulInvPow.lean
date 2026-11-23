module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.JointModelGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_of_eq_mul_inv_pow (W : ValuationSubring ℂ) {x a : ℂ} (ha : a ∈ W) (n : ℕ) (h : x = a * x⁻¹ ^ n) :
    x ∈ W := by
  rcases W.mem_or_inv_mem x with hx | hx
  · exact hx
  · rw [h]; exact mul_mem ha (pow_mem hx n)

theorem exists_root_and_zeta (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by simpa using this)
  have hrW : H.rt0 ∈ W := mem_of_eq_mul_inv_pow W (a := -(H.d : ℂ)) (neg_mem (natCast_mem W _)) 1 (by
    rw [← H.sqrt_neg_disc_sq]; field_simp)
  have hp : IsPrimitiveRoot (zeta l.A) l.A := Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
  have hz0 : zeta l.A ≠ 0 := hp.ne_zero l.A_pos.ne'
  have hzW : zeta l.A ∈ W := mem_of_eq_mul_inv_pow W (a := 1) (one_mem W) (l.A - 1) (by
    have h1 : zeta l.A * zeta l.A ^ (l.A - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel l.A_pos]; exact hp.pow_eq_one
    rw [one_mul, inv_pow]
    exact eq_inv_of_mul_eq_one_left h1)
  exact ⟨⟨⟨_, hr⟩, hrW⟩, ⟨⟨_, hz⟩, hzW⟩, rfl, rfl⟩

end GlobalTheory.JointModelGuards
