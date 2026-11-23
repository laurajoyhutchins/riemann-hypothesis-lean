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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

lemma range_app_iso_comp {X : Scheme.{0}} {P Q E : X.Modules} (e : P ≅ Q) (f : Q ⟶ E)
    (V : X.Opens) : Set.range ((e.hom ≫ f).app V) = Set.range (f.app V) := by
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.app V x, by rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.app V y, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_assoc]

theorem secs_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (E : X.Modules) (hE : E.IsQuasicoherent) (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) :
    secs (powSub I E n) V =
      ((Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(E, V)) :
        Set Γ(E, V)) := by
  rw [← range_idealPowι_app I E hV n, ← range_app_iso_comp
    (Subobject.underlyingIso (idealPowι I E n)) (idealPowι I E n) V]
  unfold secs powSub
  rw [Subobject.underlyingIso_hom_comp_eq_mk]

end GlobalTheory.CompanionTheory.GE
