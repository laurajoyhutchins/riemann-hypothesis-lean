module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Bl.general_b_fact_upper_bis_form

theorem goal1 :
  ∀ {n : Nat} (f : Fin n → Rat),
  (∀ (i i' : Fin n), LT.lt.{0} i i' → LT.lt.{0} 0 (f i') → LT.lt.{0} 0 (f i)) →
    ∀ (i : Fin n), Iff (LT.lt.{0} 0 (f i)) (LT.lt.{0} i.val (PI.FJM.nP f))  := by
  intro n f hmono i
  unfold PI.FJM.nP
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.filter (fun j => 0 < f j) Finset.univ := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases lt_or_eq_of_le hj with h | h
      · exact hmono j i h hi
      · rw [h]; exact hi
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro hi
    by_contra hneg
    have hsub : Finset.filter (fun j => 0 < f j) Finset.univ ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hji
      rw [not_lt] at hji
      rcases lt_or_eq_of_le hji with h | h
      · exact hneg (hmono i j h hj)
      · exact hneg (by rw [h]; exact hj)
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    omega

end Bl.general_b_fact_upper_bis_form
