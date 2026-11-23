module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx


open TopologicalSpace in
theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{0}} (Z : Closeds X)
    (h : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have hr : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  haveI : IrreducibleSpace (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    Subtype.irreducibleSpace (by rw [hr]; exact h)
  let f := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Function.Surjective.irreducibleSpace f.symm.continuous f.symm.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced _


open TopologicalSpace in
theorem exists_integral_closed_cover :
    ∀ (X : Scheme.{0}) [IsNoetherian X], ∃ (n : ℕ) (Z : Fin n → Scheme.{0}) (j : ∀ i, Z i ⟶ X),
      (∀ i, IsIntegral (Z i) ∧ IsClosedImmersion (j i)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (j i) := by
  intro X _
  haveI : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents X)
  let C : Fin n → Closeds X := fun i =>
    ⟨(e.symm i).1, isClosed_of_mem_irreducibleComponents _ (e.symm i).2⟩
  refine ⟨n, fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subscheme,
    fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subschemeι,
    fun i => ⟨GlobalTheory.CompanionTheory.Ar.Approx.isIntegral_subscheme_vanishingIdeal (C i) (e.symm i).2.1, inferInstance⟩,
    fun x => ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  show x ∈ (e.symm (e _)).1
  rw [Equiv.symm_apply_apply]
  exact mem_irreducibleComponent

end GlobalTheory.CompanionTheory.Ar.Approx
