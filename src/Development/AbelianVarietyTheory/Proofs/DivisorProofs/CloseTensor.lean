module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CloseTen

theorem baseChange_tensor_holomorphic_closeness {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀)
    (hρ : ∀ (a : Fin g) (h : Hol W),
      ρ (dw (W := W) a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h))
    (ψ₂ : R ⊗[ℂ] Hol W₀ →+* C) (ρ₁ : Hol W₀ →+* C)
    (hc : Close J ρ₁ (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)) :
    ∀ φ : R ⊗[ℂ] Hol W₀ →+* C,
      (∀ h : Hol W₀, φ ((1 : R) ⊗ₜ[ℂ] h) = ρ₁ h) →
      (∀ d : R, φ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (φ.comp ρ) (ψ₂.comp ρ) := by
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro φ hφ hφd
    have e : φ = ψ₂ := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul d h =>
        have e1 : d ⊗ₜ[ℂ] h = (d ⊗ₜ[ℂ] (1 : Hol W₀)) * ((1 : R) ⊗ₜ[ℂ] h) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
        rw [e1, map_mul, map_mul, hφd, hφ]
        rfl
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    subst e
    exact Relation.ReflTransGen.refl
  | head hs _ ih =>
    intro φ hφ hφd
    obtain ⟨n, hnJ, hn2, hn⟩ := hs
    have hMove : ∃ φ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x,
        φ' x = φ x + ∑ a, φ (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap x) * n a :=
      GlobalTheory.SqZeroMove.gen_hom φ
        (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
        (fun a => GlobalTheory.SqZeroMove.lTensor_one (R := R) (dw (W := W₀) a))
        (fun a x y => GlobalTheory.SqZeroMove.lTensor_leibniz (dw (W := W₀) a) x y) n hn2
    obtain ⟨φ', hφ'⟩ := hMove
    refine Relation.ReflTransGen.head ⟨n, hnJ, hn2, fun h => ?_⟩ (ih φ' (fun h => ?_) (fun d => ?_))
    · rw [RingHom.comp_apply, hφ']
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [RingHom.comp_apply, hρ]
    · rw [hφ', hn h, hφ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, hφ]
    · rw [hφ', ← hφd]
      conv_rhs => rw [← add_zero (φ (d ⊗ₜ[ℂ] 1))]
      congr 1
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
        TensorProduct.tmul_zero, map_zero, zero_mul]

theorem close_tensor :
    ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
      {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
      (ρ : Hol W →+* R ⊗[ℂ] Hol W₀),
      (∀ (a : Fin g) (h : Hol W),
        ρ (dw (W := W) a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h)) →
      ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C,
        (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) →
        Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)
          (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) →
        Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  intro I _ g W W₀ R _ _ C _ J ρ hρ ψ₁ ψ₂ hd hc
  exact baseChange_tensor_holomorphic_closeness J ρ hρ ψ₂ _ hc ψ₁ (fun h => rfl) hd

end GlobalTheory.CloseTen
