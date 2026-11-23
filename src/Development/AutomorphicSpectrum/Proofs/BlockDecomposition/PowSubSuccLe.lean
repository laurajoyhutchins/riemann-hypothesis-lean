module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Support
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Mathlib.Tactic.Lemma
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

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}

def secs {E : X.Modules} (S : Subobject E) (V : X.Opens) : Set Γ(E, V) :=
  Set.range (S.arrow.app V)

def Killed (J : X.IdealSheafData) {E : X.Modules} (S : Subobject E) : Prop :=
  ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x : Γ(E, U), a • x ∈ secs S U

variable [X.Over (Spec (.of A))]

def powSub (E : X.Modules) (n : ℕ) : Subobject E := Subobject.mk (idealPowι I E n)

def PropSupp (A : Type) [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules}
    (S : Subobject E) : Prop :=
  ∃ T : X.IdealSheafData, IsProper (T.subschemeι ≫ (X ↘ Spec (.of A))) ∧
    Scheme.Modules.SupportedIn (cokernel S.arrow) (T.support : Set X)

structure ClosedSys (E : X.Modules) (S : ℕ → Subobject E) : Prop where
  qcoh : ∀ e, (S e : X.Modules).IsQuasicoherent
  pow_le : ∀ e, powSub I E (e + 1) ≤ S e
  succ : ∀ e, S e = S (e + 1) ⊔ powSub I E (e + 1)

def Alg (E : X.Modules) (S : ℕ → Subobject E) : Prop :=
  ∃ B : Subobject E, (B : X.Modules).IsQuasicoherent ∧ PropSupp A B ∧
    ∀ e, B ⊔ powSub I E (e + 1) = S e

def Statement (J : X.IdealSheafData) : Prop :=
  ∀ (E : X.Modules), IsCoherent E → ∀ S : ℕ → Subobject E, ClosedSys I E S →
    (∀ e, Killed J (S e)) → PropSupp A (S 0) → Alg I E S

def restrictSys {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (c e : ℕ) :
    Subobject (D : X.Modules) :=
  (Subobject.pullback D.arrow).obj (S (e + c)) ⊔ powSub I (D : X.Modules) (e + 1)

lemma powSub_succ_le (E : X.Modules) (n : ℕ) : powSub I E (n + 1) ≤ powSub I E n :=
  Subobject.mk_le_mk_of_comm (idealPowSucc I E n) (idealPowSucc_ι I E n)

theorem closedSys_pow (E : X.Modules) [E.IsQuasicoherent] :
    ClosedSys I E (fun e => powSub I E (e + 1)) := by
  refine { qcoh := ?_, pow_le := fun _ => le_rfl, succ := ?_ }
  · intro e
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (idealPowι I E (e + 1))).symm inferInstance
  · intro e
    exact (sup_eq_right.2 (powSub_succ_le I E (e + 1))).symm

end GlobalTheory.CompanionTheory.GE
