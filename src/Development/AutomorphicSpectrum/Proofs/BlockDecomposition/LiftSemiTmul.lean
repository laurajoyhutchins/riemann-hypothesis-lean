module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
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

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfVB

abbrev Hc {S A B C : Type} [CommRing S] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C] (f : A →ₗ[S] B) (g : B →ₗ[S] C) : Type :=
  LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype

def Lift {A Q N : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (b : Q →ₗ[A] N) : Prop :=
  ∀ (J : Ideal A) (t : A), J ≠ ⊤ → (∀ x ∈ IsLocalRing.maximalIdeal A, x * t ∈ J) → ∀ z : Q,
    b z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A N) →
    ∃ x : Q, b x ∈ J • (⊤ : Submodule A N) ∧
      x - z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A Q)

def SmallLift {R P₀ P₁ P₂ : Type} [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁)
    (a₁ : P₁ →ₗ[R] P₂) : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (t : B), (∀ x, ¬ IsUnit x → x * t = 0) →
    ∀ z : (B ⧸ Ideal.span {t}) ⊗[R] P₁, a₁.lTensor _ z = 0 →
    ∃ (x : B ⊗[R] P₁) (y : (B ⧸ Ideal.span {t}) ⊗[R] P₀), a₁.lTensor B x = 0 ∧
      (Ideal.Quotient.mkₐ R (Ideal.span {t})).toLinearMap.rTensor P₁ x - z = a₀.lTensor _ y

section Semi

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

def liftSemi {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[algebraMap R S] N) : S ⊗[R] M →ₗ[S] N :=
  letI : Module R N := Module.compHom N (algebraMap R S)
  haveI : IsScalarTower R S N := ⟨fun r s n ↦ by
    change (r • s) • n = algebraMap R S r • s • n
    rw [Algebra.smul_def, mul_smul]⟩
  LinearMap.liftBaseChange S
    { toFun := f, map_add' := f.map_add, map_smul' := fun r x ↦ f.map_smulₛₗ r x }

theorem liftSemi_tmul {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[algebraMap R S] N) (s : S) (x : M) : liftSemi f (s ⊗ₜ x) = s • f x := by
  simp [liftSemi]

end Semi

section Cochains

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

def c0 (m : BC F F') : C0 F →ₛₗ[algebraMap R S] C0 F' where
  toFun f T := m.α T (f T)
  map_add' f g := funext fun T ↦ map_add (m.α T) _ _
  map_smul' r f := funext fun T ↦ m.smul T r (f T)

def c1 (m : BC F F') : C1 F →ₛₗ[algebraMap R S] C1 F' where
  toFun f T T' φ := m.α T' (f T T' φ)
  map_add' f g := funext fun T ↦ funext fun T' ↦ funext fun φ ↦ map_add (m.α T') _ _
  map_smul' r f := funext fun T ↦ funext fun T' ↦ funext fun φ ↦ m.smul T' r (f T T' φ)

def c2 (m : BC F F') : C2 F →ₛₗ[algebraMap R S] C2 F' where
  toFun f T T' T'' φ ψ := m.α T'' (f T T' T'' φ ψ)
  map_add' f g := funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦
    map_add (m.α T'') _ _
  map_smul' r f := funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦
    m.smul T'' r (f T T' T'' φ ψ)

def th0 (m : BC F F') : S ⊗[R] C0 F →ₗ[S] C0 F' := liftSemi (c0 m)

def th1 (m : BC F F') : S ⊗[R] C1 F →ₗ[S] C1 F' := liftSemi (c1 m)

def th2 (m : BC F F') : S ⊗[R] C2 F →ₗ[S] C2 F' := liftSemi (c2 m)

end Cochains

def IsModel {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {P₀ P₁ P₂ : Type} [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀]
    [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F)
    (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) : Prop :=
  a₁ ∘ₗ a₀ = 0 ∧ ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀ ∧ ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁ ∧
    ∀ M : ModuleCat.{0} R,
      QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] C0 F) ((d0 F).lTensor M)
        (ψ₀.lTensor M) ∧
      QIsoAt (a₀.lTensor M) (a₁.lTensor M) ((d0 F).lTensor M) ((d1 F).lTensor M) (ψ₁.lTensor M)

end GlobalTheory.CompanionTheory.PerfVB
