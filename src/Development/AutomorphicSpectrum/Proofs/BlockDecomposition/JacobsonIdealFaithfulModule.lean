module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeCriterionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorNoetherianAffineOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPrimeLocalizationCriterionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPrimeOverIdealCompletionStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Krull

theorem fPow_torsion_of_chartIn : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (I : Ideal Γ(X, V)) {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R] {M : Type} [AddCommGroup M] [Module R M] [Module Γ(X, V) M] [IsScalarTower Γ(X, V) R M] [Module.Finite R M], I.map (algebraMap Γ(X, V) R) ≤ Ideal.jacobson ⊥ → (∀ a ∈ J.ideal ⟨V, hV⟩, ∀ m : M, a • m = 0) → ∀ f : Γ(X, V), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ y : M, (∀ n, ChartIn (ψ ≫ J.subschemeι) V (I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) y) → ∃ k : ℕ, f ^ k • y = 0 := by
  intro X J Z ψ hψ V hV _ I R _ _ _ M _ _ _ _ _ hIR hJM f hiso y hy
  by_contra hne
  push_neg at hne
  let A : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M y)
  have hA : ∀ a : R, a ∈ A ↔ a • y = 0 := fun a => by
    simp [A, LinearMap.toSpanSingleton_apply]
  have hdisj : Disjoint (A : Set R) (Submonoid.powers (algebraMap Γ(X, V) R f) : Set R) := by
    refine Set.disjoint_left.2 fun x hxA hxS => ?_
    obtain ⟨k, rfl⟩ := hxS
    apply hne k
    have h1 := (hA _).1 hxA
    simp only at h1
    rwa [← map_pow, algebraMap_smul] at h1
  obtain ⟨p, hp, hAp, hpS⟩ := Ideal.exists_le_prime_disjoint A _ hdisj
  have hfp : algebraMap Γ(X, V) R f ∉ p := fun h =>
    Set.disjoint_left.1 hpS h (Submonoid.mem_powers _)
  have hJp : (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => hAp ((hA _).2 ?_)
    rw [algebraMap_smul]
    exact hJM a ha y
  obtain ⟨U, hU, h, Q₀, Q₁, hQ₀, hQ₁, hle, hQ₀p, hQ₁m⟩ := GlobalTheory.T.proper_birational_prime_exists J ψ hψ V hV f hiso p hp hJp hfp
  letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra
  haveI : IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := GlobalTheory.T.tensor_noetherian_affine_open J ψ hψ V hV U hU h R
  have hy' : ∀ n : ℕ, y ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range
      ((I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M).subtype.rTensor Γ(Z, U)) := fun n => hy n U hU h
  have hIQ : I.map (algebraMap Γ(X, V) R) ≤
      Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) :=
    hIR.trans (sInf_le ⟨bot_le, hQ₁m⟩)
  obtain ⟨w, hw, hwy⟩ := GlobalTheory.T.tensor_prime_over_ideal_completion I y hy' Q₁ hQ₁ hIQ
  have hw0 : w ∉ Q₀ := fun h' => hw (hle h')
  have hfq : f ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : Γ(Z, U) →ₐ[Γ(X, V)] R ⊗[Γ(X, V)] Γ(Z, U))).comap
      (algebraMap Γ(X, V) Γ(Z, U)) := by
    intro hf
    apply hfp
    rw [← hQ₀p]
    simp only [Ideal.mem_comap] at hf ⊢
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply] at hf
    simpa [Algebra.TensorProduct.includeLeftRingHom_apply] using hf
  obtain ⟨hloc1, hloc2⟩ := GlobalTheory.T.proper_birational_prime_criterion J ψ V hV f hiso U hU h _ (Ideal.comap_isPrime _ _) hfq
  obtain ⟨u, hu, huy⟩ := GlobalTheory.T.tensor_prime_localization_criterion (J.ideal ⟨V, hV⟩) hJM Q₀ hQ₀ hloc1 hloc2 y w hw0 hwy
  rw [hQ₀p] at hu
  exact hu (hAp ((hA u).2 huy))

end GlobalTheory.CompanionTheory.GE.Krull
