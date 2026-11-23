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

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem pr_eq_zero_of_degenerate :
    ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {m : ℕ} (x : Cn F 1)
      (_ : dn F 1 x = 0) (e : Fin (1 + 1) →o Fin (m + 1)) (_ : e 0 = e 1), pr F e x = 0 := by
  intro R _ C _ F m x hx e h01
  have key : ∀ i : Fin (1 + 1 + 1),
      GlobalTheory.CompanionTheory.HopfC.pr F ((GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0)).comp (GlobalTheory.CompanionTheory.HopfC.dl i)) x =
        GlobalTheory.CompanionTheory.HopfC.pr F e x := by
    intro i
    refine GlobalTheory.CompanionTheory.HopfC.pr_congr (fun j => ?_) x
    show e 0 = e j
    fin_cases j
    · rfl
    · exact h01
  have h := congrArg (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0))) hx

  rw [map_zero (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0))),
  GlobalTheory.CompanionTheory.HopfC.dn_eq, map_sum] at h
  simp only [map_smul, map_zsmul, GlobalTheory.CompanionTheory.HopfC.pr_pr] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, key] at h
  norm_num at h
  exact h

end GlobalTheory.CompanionTheory.HopfC
