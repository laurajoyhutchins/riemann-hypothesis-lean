module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct

namespace GlobalTheory.CompanionTheory.GE

variable {X Z : Scheme.{0}}

def secsSub {E : X.Modules} (S : Subobject E) (V : X.Opens) : Submodule Γ(X, V) Γ(E, V) where
  carrier := secs S V
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨a, rfl⟩
    exact ⟨r • a, Scheme.Modules.Hom.app_smul _ _ _⟩

def pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [Z.Over (Spec (.of A))]
    (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E) (e : ℕ) :
    Subobject ((Scheme.Modules.pullback φ).obj E) :=
  imageSubobject ((Scheme.Modules.pullback φ).map (S e).arrow) ⊔ powSub I _ (e + 1)

def adjMap (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    E ⟶ (Scheme.Modules.pushforward φ).obj (cokernel B.arrow) :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E (cokernel B.arrow) (cokernel.π B.arrow)

def adjKer (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    Subobject E :=
  kernelSubobject (adjMap φ B)

def ChartIn (φ : Z ⟶ X) (V : X.Opens) {N : Type} [AddCommGroup N] [Module Γ(X, V) N]
    (T : Submodule Γ(X, V) N) (x : N) : Prop :=
  ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range (T.subtype.rTensor Γ(Z, U))

def powIdeal (J₀ : X.IdealSheafData) (m : ℕ) : X.IdealSheafData where
  ideal U := J₀.ideal U ^ m
  map_ideal_basicOpen U f := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl

end GlobalTheory.CompanionTheory.GE
