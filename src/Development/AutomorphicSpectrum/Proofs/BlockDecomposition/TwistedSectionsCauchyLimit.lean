module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LimitOfFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

theorem exists_limit_of_finite {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L, ∀ m, f m - L ∈ (I ^ m • ⊤ : Submodule A M) :=
  _root_.UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite I hI f hf

theorem finite_twisted_sections {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) {P : X.Modules} (hP : IsCoherent P) (n : ℤ)
    [Module A Γ(GlobalTheory.twistZ P H n, ⊤)]
    (hs : ∀ (a : A) (x : Γ(GlobalTheory.twistZ P H n, ⊤)), a • x = algebraMap A Γ(X, ⊤) a • x) :
    Module.Finite A Γ(GlobalTheory.twistZ P H n, ⊤) := by
  haveI : GlobalTheory.QCoh.IsFiniteQC P := ⟨hP.1, hP.2⟩
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.twistZ P H n) :=
    GlobalTheory.Twist.isFiniteQC_twist (F := P) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n)
  have h0 : Module.Finite A (GlobalTheory.coh (GlobalTheory.twistZ P H n) 0) :=
    GlobalTheory.IsAmpleLB.finite_coh (R := A) (f := X ↘ Spec (.of A)) (fun _ => rfl) _ hH 0
  exact Module.Finite.equiv ((GlobalTheory.cohOn.zeroEquiv A (GlobalTheory.twistZ P H n) ⊤).trans
    (GlobalTheory.sectionsOn.equivOfSMul A (GlobalTheory.twistZ P H n) ⊤ fun a x => by
      rw [hs, GlobalTheory.restrictGlobal_top]))

theorem exists_limit_twPow : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := by
  intro A _ _ I hI X _ _ H hH P hP n f hf
  letI : Module A Γ(GlobalTheory.twistZ P H n, ⊤) := Module.compHom _ (algebraMap A Γ(X, ⊤))
  haveI : IsScalarTower A Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) :=
    ⟨fun a r x => by
      change (a • r) • x = algebraMap A Γ(X, ⊤) a • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI := finite_twisted_sections (A := A) H hH hP n (fun _ _ => rfl)
  have hmem : ∀ (m : ℕ) (y : Γ(GlobalTheory.twistZ P H n, ⊤)),
      y ∈ twPow I H n P m ↔ y ∈ (I ^ m • ⊤ : Submodule A Γ(GlobalTheory.twistZ P H n, ⊤)) := by
    intro m y
    have hfun : toFunctions (X := X) (A := A) ⊤ = algebraMap A Γ(X, ⊤) := by
      ext a
      simp [toFunctions, restrictTop]
    have h := Ideal.smul_restrictScalars (R := A) (S := Γ(X, ⊤))
      (M := Γ(GlobalTheory.twistZ P H n, ⊤)) (I ^ m) ⊤
    rw [Submodule.restrictScalars_top] at h
    rw [← h]
    simp only [twPow, hfun]
    rfl
  obtain ⟨L, hL⟩ := exists_limit_of_finite I hI.toIsPrecomplete f fun m => (hmem m _).1 (hf m)
  exact ⟨L, fun m => (hmem m _).2 (hL m)⟩

end GlobalTheory.CompanionTheory.GE
