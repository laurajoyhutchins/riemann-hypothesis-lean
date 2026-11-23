module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfGenericFiberSmoothProperStatement
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

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem geometricallyConnected_snd_snd_iff {X S S' S'' : Scheme.{0}} (g : X ⟶ S) (f : S' ⟶ S)
    (b : S'' ⟶ S') :
    GeometricallyConnected (pullback.snd (pullback.snd g f) b) ↔
      GeometricallyConnected (pullback.snd g (b ≫ f)) := by
  haveI : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← pullbackLeftPullbackSndIso_hom_snd g f b]
  exact MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem stableUnderSpecialization_geometricallyConnected :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → IsProper G.hom →
      StableUnderSpecialization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ G _ _ hsm hpr x y hxy hx
  haveI := hsm
  haveI := hpr
  have hle : x.asIdeal ≤ y.asIdeal := (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hs' : Smooth ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom := by
    show Smooth (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
    infer_instance
  have hp' : IsProper ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom := by
    show IsProper (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
    infer_instance
  have hgen : GeometricallyConnected (pullback.snd
      ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom
      (spMap (algebraMap (k ⧸ x.asIdeal) x.asIdeal.ResidueField))) := by
    show GeometricallyConnected (pullback.snd (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
      (spMap (algebraMap (k ⧸ x.asIdeal) x.asIdeal.ResidueField)))
    rw [geometricallyConnected_snd_snd_iff, spMap_comp_moduli_spaces, ← IsScalarTower.algebraMap_eq]
    exact hx
  have hG' : GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal)))) :=
    GlobalTheory.T.geometricallyConnected_of_generic_fiber_smooth_proper (k ⧸ x.asIdeal) x.asIdeal.ResidueField
      ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G) hs' hp' hgen
  have hker : ∀ a ∈ x.asIdeal, algebraMap k y.asIdeal.ResidueField a = 0 := fun a ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hle ha)
  have hφ : (Ideal.Quotient.lift x.asIdeal (algebraMap k y.asIdeal.ResidueField) hker).comp
      (algebraMap k (k ⧸ x.asIdeal)) = algebraMap k y.asIdeal.ResidueField := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.lift_comp_mk _ _ _
  show GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k y.asIdeal.ResidueField)))
  rw [← hφ, ← spMap_comp_moduli_spaces, ← geometricallyConnected_snd_snd_iff]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
