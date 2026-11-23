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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism.UG Matrix

namespace GlobalTheory.Hk3.Inh

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc' : Nat.card (IsLocalRing.ResidueField O) = q ^ 2 := hc
  haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by rw [hc']; positivity)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  have h0 : ((q ^ 2 : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← hc', Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  have hle : Valued.v (2 : L) ≤ 1 := (2 : O).2
  by_contra hne
  have hlt : Valued.v (2 : L) < 1 := lt_of_le_of_ne hle hne
  have hm : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h2' : (2 : IsLocalRing.ResidueField O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (2 : O)).2 hm
    rwa [map_ofNat] at this
  obtain ⟨k, hk⟩ : Odd (q ^ 2) := hq.pow
  rw [hk] at h0
  push_cast at h0
  rw [h2'] at h0
  simp at h0




section Main

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ}







end Main

section Laurent

end Laurent

end GlobalTheory.Hk3.Inh

end
