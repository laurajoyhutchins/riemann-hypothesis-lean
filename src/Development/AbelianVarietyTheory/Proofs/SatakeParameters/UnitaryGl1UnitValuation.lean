module

public import Formalism.SatakeDualWeyl.StatementF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

noncomputable section
namespace GlobalTheory.Hk3.LatModel
open Classical

section Abstract
variable {W G : Type} [AddCommGroup W] [Group G]

end Abstract

section Concrete
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  by_contra hne
  have hle : Valued.v (2 : L) ≤ 1 := by
    have := (Valued.v (R := L)).integer.add_mem (one_mem _) (one_mem _)
    rw [one_add_one_eq_two] at this; exact this
  have hlt := lt_of_le_of_ne hle hne
  set R := (Valued.v (R := L)).valuationSubring
  change Nat.card (R ⧸ IsLocalRing.maximalIdeal R) = q ^ 2 at hc
  have hm : (2 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h20 : (2 : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rwa [map_ofNat] at this
  have hodd : Odd (Nat.card (R ⧸ IsLocalRing.maximalIdeal R)) := by rw [hc]; exact hq.pow
  obtain ⟨k, hk⟩ := hodd
  have h3 : ((Nat.card (R ⧸ IsLocalRing.maximalIdeal R) : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    rw [← nsmul_one]; exact card_nsmul_eq_zero'
  rw [hk] at h3
  push_cast at h3
  rw [h20] at h3
  simp at h3

end Concrete

end GlobalTheory.Hk3.LatModel
end
