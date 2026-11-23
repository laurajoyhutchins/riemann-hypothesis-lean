module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFinPartInCompactBoundedDenominatorStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaConv

theorem exists_den_of_inBox : ∀ (D : D7) (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ (x : Mx D m n) (ξ : Matrix (Fin m) (Fin n) D.host.E), x.map (finPart D) = (ξ.map (incA D) : Mx D m n).map (finPart D) → GlobalTheory.Unf.InBox K x → ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j) := by
  intro D m n K hK
  have hK1 : IsCompact (⋃ p : Fin m × Fin n, (fun x : Mx D m n => x p.1 p.2) '' K) :=
    isCompact_iUnion fun p => hK.image (continuous_id.matrix_elem p.1 p.2)
  obtain ⟨L, hL, h⟩ := GlobalTheory.T.rational_finPart_in_compact_bounded_denominator D _ hK1
  refine ⟨L, hL, fun x ξ hx ⟨k, hk, hxk⟩ i j => ?_⟩
  refine h (k i j) (Set.mem_iUnion.2 ⟨(i, j), k, hk, rfl⟩) (ξ i j) ?_
  have h1 : finPart D (x i j) = finPart D (incA D (ξ i j)) := congrFun (congrFun hx i) j
  have h2 : finPart D (x i j - k i j) = 0 := congrFun (congrFun hxk i) j
  have h3 : finPart D (x i j) - finPart D (k i j) = 0 :=
    ((finPart D).map_sub (x i j) (k i j)).symm.trans h2
  exact h1.symm.trans (sub_eq_zero.1 h3)

end GlobalTheory.ThetaConv
