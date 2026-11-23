module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem shuffle_cup1_degree_zero {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (u : Cn (box F) 1) (w : Cn (box F) 0) :
    Sh F 0 (cup1 (box F) 0 u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst 0 1) OrderHom.id w := by
  have hsum : GlobalTheory.CompanionTheory.HopfC.Sh F 0 = AlgHom.toLinearMap
      (GlobalTheory.CompanionTheory.HopfC.bv F (N := 0 + 1) (p := 1) (q := 0)
        (GlobalTheory.CompanionTheory.HopfC.sI 0) (Fin.predAboveOrderHom 0)) := by
    rw [GlobalTheory.CompanionTheory.HopfC.Sh]
    first
    | (rw [Fin.sum_univ_one]; simp)
    | simp
    | (ext; simp)
  rw [hsum, AlgHom.toLinearMap_apply, GlobalTheory.CompanionTheory.HopfC.cup1_apply, map_mul,
    GlobalTheory.CompanionTheory.HopfC.bv_pr, GlobalTheory.CompanionTheory.HopfC.bv_pr]
  congr 1
  all_goals
    first
    | rfl
    | (refine GlobalTheory.CompanionTheory.HopfC.bv_congr (fun i => ?_) (fun i => ?_) _ <;>
        fin_cases i <;> first | rfl | decide | exact Subsingleton.elim (α := Fin 1) _ _)

end GlobalTheory.CompanionTheory.HopfC
