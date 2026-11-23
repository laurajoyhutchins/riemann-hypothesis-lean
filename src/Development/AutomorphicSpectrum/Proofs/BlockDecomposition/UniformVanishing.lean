module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

def twSecs {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules} (S : Subobject P) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤)

def twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  ((Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤))

structure OpSeq {X : Scheme.{0}} (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (d : ℕ) : Prop where
  coherent : ∀ e, IsCoherent (M e)
  comm : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)
  gen : ∀ e, d ≤ e → ∀ U : X.affineOpens,
    Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤

def GradedNoeth : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (k : ℕ) (M : ℕ → Type)
    [∀ e, AddCommGroup (M e)] [∀ e, Module R (M e)] [∀ e, Module.Finite R (M e)]
    (T : Fin k → ∀ e, M e →ₗ[R] M (e + 1)),
    (∀ i j e x, T j (e + 1) (T i e x) = T i (e + 1) (T j e x)) →
    ∀ d : ℕ, (∀ e, d ≤ e → ⨆ i, LinearMap.range (T i e) = ⊤) →
    ∀ L : ∀ e, Submodule R (M e), (∀ i e, (L e).map (T i e) ≤ L (e + 1)) →
    ∃ d' : ℕ, ∀ e, d' ≤ e → ⨆ i, (L e).map (T i e) = L (e + 1)

def UniformVanishing : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q)

def UniformGen : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, d ≤ e →
      Submodule.span Γ(X, ⊤)
        (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (T i e)).app ⊤)) = ⊤

end GlobalTheory.CompanionTheory.GE
