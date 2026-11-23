module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.ExtSpan

theorem extOrder_eq_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  intro R _ T _ R' _ φ A g
  set S : Set (T → R') := {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} with hS
  have hmul : ∀ {x y : T → R'}, x ∈ S → y ∈ S → x * y ∈ S := by
    rintro _ _ ⟨f1, hf1, rfl⟩ ⟨f2, hf2, rfl⟩
    exact ⟨f1 * f2, A.mul_mem hf1 hf2, by funext t; simp [map_mul]⟩
  have hone : (1 : T → R') ∈ S := ⟨1, A.one_mem, by funext t; simp⟩
  let M : Submonoid (T → R') := { carrier := S, mul_mem' := hmul, one_mem' := hone }
  have hcl : ((Submonoid.closure S : Submonoid (T → R')) : Set (T → R')) = S :=
    congrArg (fun N : Submonoid (T → R') => (N : Set (T → R'))) (Submonoid.closure_eq M)
  have hspan : Subalgebra.toSubmodule (Algebra.adjoin R' S) = Submodule.span R' S := by
    rw [Algebra.adjoin_eq_span, hcl]
  have hdef : extOrder φ A = Algebra.adjoin R' S := by
    first
    | rfl
    | (unfold extOrder; congr 1)
    | (unfold extOrder; congr 1; ext x; simp only [hS, Set.mem_setOf_eq, Set.mem_range, Set.mem_image, Subtype.exists, exists_prop, SetLike.mem_coe]; constructor <;> rintro ⟨f, hf, h⟩ <;> exact ⟨f, hf, h.symm⟩)
  rw [hdef, ← Subalgebra.mem_toSubmodule, hspan]

end GlobalTheory.CompanionTheory.Ar.BT.ExtSpan
