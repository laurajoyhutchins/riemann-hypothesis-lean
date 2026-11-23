module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem triv_of_isEmpty {Y : Scheme.{0}} [IsEmpty Y] (L : LB Y) : Triv L := by
  have hs : ∀ U : Y.Opens, Subsingleton Γ(Y, U) := fun U => by
    have hU : U = ⊥ := by
      ext y
      exact (IsEmpty.false y).elim
    subst hU
    infer_instance
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have := hs (L.U i ⊓ L.U j)
  exact Subsingleton.elim _ _

theorem exists_ideal_near : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB →
    Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → Surjective f →
    (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
      IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) →
    ∀ p : PrimeSpectrum R, ∃ (r : R) (I : Ideal R), r ∉ p.asIdeal ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) →
        (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  intro R _ X f M hM hP hQ hprop hgi hsurj hbij p
  have hW := GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hprop hgi
  by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)}
  · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, hpb, ht⟩ := hp
    obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance hsurj K g₀ X₀ π₀ f₀ hpb
      (hbij K g₀ X₀ π₀ f₀ hpb) ht
    refine ⟨r, I, fun hrp => hr ?_, H⟩
    rw [← hk] at hrp
    exact hrp
  · obtain ⟨_, ⟨r, rfl⟩, hpr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ _ from hp) hW.isOpen_compl
    refine ⟨r, ⊤, hpr, fun R' _ g X' π f' h hu => ?_⟩
    rcases subsingleton_or_nontrivial R' with hR' | hR'
    · have hE : IsEmpty (Spec (CommRingCat.of R')) := inferInstanceAs (IsEmpty (PrimeSpectrum R'))
      have hX' : IsEmpty X' := ⟨fun x => hE.false (f' x)⟩
      exact ⟨fun _ x _ => Subsingleton.elim _ _, fun _ => triv_of_isEmpty _⟩
    · refine ⟨fun ht => ?_, fun hle => ?_⟩
      · exfalso
        obtain ⟨m, hm⟩ := Ideal.exists_maximal R'
        let _ : Field (R' ⧸ m) := Ideal.Quotient.field m
        let q : R' →+* R' ⧸ m := Ideal.Quotient.mk m
        have hpb : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom q)) ≫ π)
            (pullback.snd f' (Spec.map (CommRingCat.ofHom q))) f
            (Spec.map (CommRingCat.ofHom (q.comp g))) := by
          have e : Spec.map (CommRingCat.ofHom (q.comp g)) =
              Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom g) := by
            rw [← Spec.map_comp, CommRingCat.ofHom_comp]
          rw [e]
          exact (IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom q))).paste_horiz h
        have hprime : (RingHom.ker (q.comp g)).IsPrime := RingHom.ker_isPrime _
        refine hsub (show (⟨RingHom.ker (q.comp g), hprime⟩ : PrimeSpectrum R) ∈ _ from ?_)
          ⟨R' ⧸ m, inferInstance, q.comp g, _, _, _, rfl, hpb, GlobalTheory.Biadditive.triv_pull_comp ht _⟩
        intro hr
        exact (hu.map q).ne_zero hr
      · have h1 : g 1 = 0 := hle (Submodule.mem_top (x := (1 : R)))
        rw [map_one] at h1
        exact absurd h1 one_ne_zero

end GlobalTheory.CompanionTheory.TrivLoc
