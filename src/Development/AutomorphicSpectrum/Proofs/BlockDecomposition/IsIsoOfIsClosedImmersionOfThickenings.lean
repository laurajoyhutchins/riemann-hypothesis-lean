module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.FormalClosed

open GlobalTheory.ThickeningClosed

theorem mem_of_forall_mem_over_closedFibre {R : Type} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {W : Set X} (hW : IsOpen W)
    (h : ∀ x, I ≤ (f x).asIdeal → x ∈ W) (x : X) : x ∈ W := by
  by_contra hx
  have hZ : IsClosed (f '' Wᶜ) := f.isClosedMap _ hW.isClosed_compl
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (f x).asIdeal (f x).isPrime.ne_top
  let p : PrimeSpectrum (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have h1 : p ∈ closure ({f x} : Set (PrimeSpectrum (CommRingCat.of R))) :=
    (PrimeSpectrum.le_iff_mem_closure (f x) p).1 hle
  have hfx : f x ∈ f '' Wᶜ := ⟨x, hx, rfl⟩
  have hp : p ∈ f '' Wᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 hfx) hZ h1
  obtain ⟨z, hz, hzp⟩ := hp
  apply hz
  apply h z
  rw [hzp]
  show I ≤ m
  refine hI.trans ?_
  unfold Ideal.jacobson
  exact sInf_le ⟨bot_le, hm⟩

theorem eq_bot_of_forall_mem_zeroLocusOpen {X : Scheme.{0}} (K : X.IdealSheafData)
    (h : ∀ x, x ∈ zeroLocusOpen K) : K = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_bot]
  apply le_antisymm _ bot_le
  intro a ha
  rw [Ideal.mem_bot]
  by_contra ha0
  let J : Ideal Γ(X, U) := LinearMap.ker (LinearMap.toSpanSingleton Γ(X, U) Γ(X, U) a)
  have hJ : J ≠ ⊤ := by
    intro hJ
    apply ha0
    have h1 : (1 : Γ(X, U)) ∈ J := by rw [hJ]; exact Submodule.mem_top
    simpa [J] using h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem K U ⟨m, hm.isPrime⟩ (h _) ha
  apply hs
  apply hJm
  simpa [J] using hsa

theorem isIso_of_isClosedImmersion_of_thickenings :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
    ∀ (E : Scheme.{0}) (j : E ⟶ X.left), IsClosedImmersion j →
      (∀ e, ∃ h : (thickObj R I e X).left ⟶ E, h ≫ j = pullback.fst X.hom (thick R I e)) →
        IsIso j := by
  intro R _ _ I hI X hX E j hj hth
  haveI := hX
  haveI := hj
  haveI := hI
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  apply eq_bot_of_forall_mem_zeroLocusOpen
  intro x
  refine mem_of_forall_mem_over_closedFibre (IsAdicComplete.le_jacobson_bot I) X.hom
    (isOpen_zeroLocusOpen _) ?_ x
  intro y hy
  refine mem_of_thickenings I X.hom j ?_ y hy
  intro n
  obtain ⟨l, hl⟩ := hth n
  exact ⟨l, hl⟩

end GlobalTheory.CompanionTheory.FormalClosed
