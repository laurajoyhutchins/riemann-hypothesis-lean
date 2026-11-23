module

public import Formalism.LocalRingCardinality.DataSpaces
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

@[expose] public section

open NumberField

namespace GlobalTheory.NonzeroIntegerSmulMem

theorem exists_ne_zero_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : Formalism.BasicNotions.HSpace E} (L : Submodule (RingOfIntegers E) (Formalism.BasicNotions.HSpace.V S))
    (hL : Submodule.IsFullLattice E L) (x : Formalism.BasicNotions.HSpace.V S) :
    ∃ r : RingOfIntegers E, r ≠ (0 : RingOfIntegers E) ∧ r • x ∈ L := by

  have hx : x ∈ Submodule.span E (L : Set (Formalism.BasicNotions.HSpace.V S)) := by
    rw [hL.span_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hrL⟩ := hy
    obtain ⟨t, ht, htL⟩ := hz
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have e : (r * t) • (y + z) = t • (r • y) + r • (t • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm r t y]
    rw [e]
    exact L.add_mem (L.smul_mem t hrL) (L.smul_mem r htL)
  | smul a y _ hy =>
    obtain ⟨r, hr, hrL⟩ := hy

    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    refine ⟨r * (d : RingOfIntegers E), mul_ne_zero hr (nonZeroDivisors.coe_ne_zero d), ?_⟩
    have e1 : (d : RingOfIntegers E) • a = algebraMap (RingOfIntegers E) E n := by
      rw [Algebra.smul_def, mul_comm]
      exact hnd
    have e : (r * (d : RingOfIntegers E)) • (a • y) = n • (r • y) := by
      rw [mul_smul, ← smul_assoc (d : RingOfIntegers E) a y, e1, algebraMap_smul E n y,
        smul_comm r n y]
    rw [e]
    exact L.smul_mem n hrL

end GlobalTheory.NonzeroIntegerSmulMem
