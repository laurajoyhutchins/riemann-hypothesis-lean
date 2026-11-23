module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChowLemmaQuasiProjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NoetherianIntegralClosedCoverStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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

theorem exists_proper_qproj_cover : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), (∀ i, IsProper (π i) ∧ IsQProjOver (π i ≫ p)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (π i) := by
  intro k _ _ X p hs hl hq
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hC : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hN : IsNoetherian X := { }
  obtain ⟨n, Z, j, hj, hcov⟩ := GlobalTheory.T.noetherian_integral_closed_cover X
  have key : ∀ i, ∃ (X' : Scheme.{0}) (π : X' ⟶ Z i), IsProper π ∧ Surjective π ∧
      IsQProjOver (π ≫ j i ≫ p) := by
    intro i
    have := (hj i).1
    have := (hj i).2
    exact GlobalTheory.T.chow_lemma_quasi_projective k (Z i) (j i ≫ p) inferInstance inferInstance inferInstance
  choose Y π hp hsurj hqp using key
  refine ⟨n, Y, fun i => π i ≫ j i, fun i => ?_, fun x => ?_⟩
  · have := (hj i).2
    have := hp i
    refine ⟨inferInstance, ?_⟩
    rw [Category.assoc]
    exact hqp i
  · obtain ⟨i, z, rfl⟩ := hcov x
    obtain ⟨y, rfl⟩ := (hsurj i).surj z
    exact ⟨i, y, by simp⟩

end GlobalTheory.CompanionTheory.Ar.Approx
