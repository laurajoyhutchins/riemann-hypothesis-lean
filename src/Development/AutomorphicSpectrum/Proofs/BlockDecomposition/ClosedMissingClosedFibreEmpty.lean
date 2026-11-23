module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.RingTheory.AdicCompletion.Basic
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.ClosedFibre

theorem closed_missing_closedFibre_empty : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R →
  ∀ (X : Over (Spec (CommRingCat.of R))), UniversallyClosed X.hom →
  ∀ Z : Set X.left, IsClosed Z → (∀ x ∈ Z, ¬ (I ≤ (X.hom.base x).asIdeal)) → Z = ∅ := by
  intro R _ I hI X hX Z hZ h
  haveI := hI
  haveI := hX
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hcl : IsClosed (X.hom.base '' Z) := X.hom.isClosedMap _ hZ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (X.hom.base x).asIdeal (X.hom.base x).isPrime.ne_top
  let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hsp : (X.hom.base x) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have hq : q ∈ X.hom.base '' Z := hsp.mem_closed hcl ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyq⟩ := hq
  apply h y hy
  rw [hyq]
  exact (IsAdicComplete.le_jacobson_bot (I := I)).trans (sInf_le ⟨bot_le, hm⟩)

end GlobalTheory.CompanionTheory.ClosedFibre
