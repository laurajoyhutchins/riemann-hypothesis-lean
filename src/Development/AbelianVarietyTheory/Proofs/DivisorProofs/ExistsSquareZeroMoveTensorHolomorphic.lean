module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLeibniz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
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

namespace GlobalTheory.SqZeroMove

theorem gen_hom {A C : Type} [CommRing A] [CommRing C] {g : ℕ} (ψ : A →+* C) (D : Fin g → A →+ A)
    (h1 : ∀ a, D a 1 = 0) (hL : ∀ a x y, D a (x * y) = x * D a y + y * D a x)
    (n : Fin g → C) (hn : ∀ a b, n a * n b = 0) :
    ∃ ψ' : A →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (D a x) * n a := by
  have hsq : ∀ (u v : Fin g → C), (∑ a, u a * n a) * (∑ b, v b * n b) = 0 := by
    intro u v
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    calc u a * n a * (v b * n b) = u a * v b * (n a * n b) := by ring
      _ = 0 := by rw [hn a b, mul_zero]
  refine ⟨{ toFun := fun x => ψ x + ∑ a, ψ (D a x) * n a,
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun x => rfl⟩
  · simp [h1]
  · intro x y
    have e := hsq (fun a => ψ (D a x)) (fun a => ψ (D a y))
    simp only [hL, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib]
    have ex : ∑ a, ψ x * ψ (D a y) * n a = ψ x * ∑ a, ψ (D a y) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    have ey : ∑ a, ψ y * ψ (D a x) * n a = ψ y * ∑ a, ψ (D a x) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [ex, ey]
    linear_combination (-1 : C) * e
  · simp
  · intro x y
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
    ring

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : R ⊗[ℂ] S) :
    LinearMap.lTensor R d.toLinearMap (x * y) =
      x * LinearMap.lTensor R d.toLinearMap y + y * LinearMap.lTensor R d.toLinearMap x := by
  first
  | exact @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | (apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz ..)

theorem lTensor_one {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) : LinearMap.lTensor R d.toLinearMap (1 : R ⊗[ℂ] S) = 0 := by
  rw [Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
    TensorProduct.tmul_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem sqZeroMove : ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C), (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw a).toLinearMap x) * n a := by
  intro g W₀ R _ _ C _ ψ n hn
  exact gen_hom ψ (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
    (fun a => lTensor_one _) (fun a x y => lTensor_leibniz _ x y) n hn

end GlobalTheory.SqZeroMove
