module

public import Mathlib.NumberTheory.NumberField.Basic
import Formalism.LocalRingCardinality.DataHost
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem denom_bound_mul : ∀ (E κ ι : Type) [Field E] [NumberField E] [Fintype κ] [Fintype ι] (T : Matrix κ ι E), ∃ M : ℕ, 0 < M ∧ ∀ (L : ℕ) (x : ι → E), (∀ i, IsIntegral ℤ ((L : E) * x i)) → ∀ k, IsIntegral ℤ (((M * L : ℕ) : E) * ∑ i, T k i * x i) := by
  intro E κ ι _ _ _ _ T
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image (fun p : κ × ι => T p.1 p.2))
  refine ⟨y.natAbs ^ 2, by positivity, ?_⟩
  intro L x hx k
  have hT : ∀ i, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * T k i) := by
    intro i
    have h1 := hint (T k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
    have hy' : IsIntegral ℤ ((y : E)) := by
      have := (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E y)); simpa using this
    have : ((y.natAbs ^ 2 : ℕ) : E) * T k i = (y : E) * (y • T k i) := by
      rw [zsmul_eq_mul]
      have : ((y.natAbs ^ 2 : ℕ) : E) = ((y ^ 2 : ℤ) : E) := by
        have hz : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
        rw [← hz, Int.cast_natCast]
      rw [this]; push_cast; ring
    rw [this]
    exact hy'.mul h1
  have heq : (((y.natAbs ^ 2 * L : ℕ) : E) * ∑ i, T k i * x i)
      = ∑ i, (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [heq]
  have := Subalgebra.sum_mem (integralClosure ℤ E) (t := Finset.univ)
    (f := fun i => (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i))
    (fun i _ => Subalgebra.mul_mem _ (hT i) (hx i))
  exact this

end GlobalTheory
