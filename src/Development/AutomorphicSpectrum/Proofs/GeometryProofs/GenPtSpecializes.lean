module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
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
import Mathlib.RingTheory.SimpleRing.Principal
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptInh

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem dom (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) := by
  exact Function.Injective.isDomain (genMap ξ p) (h.inj p)

theorem nogen (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hy
  obtain ⟨q, hq⟩ := hy'
  obtain ⟨f, hf⟩ : ∃ f : X.presheaf.stalk (genPt ξ) →+* Ω, Function.Bijective f :=
    ⟨(Scheme.stalkClosedPointTo ξ).hom, h.bij⟩
  have hmax : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (genPt ξ)), x = 0 := by
    intro x hx
    by_contra hne
    have h1 : f x ≠ 0 := by
      intro h0
      apply hne
      apply hf.1
      rw [h0, map_zero]
    obtain ⟨v, hv⟩ := hf.2 (f x)⁻¹
    have hxv : x * v = 1 := hf.1 (by rw [map_mul, hv, mul_inv_cancel₀ h1, map_one])
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsUnit.of_mul_eq_one v hxv)
  have hq' : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime q).ne_top
    · intro x hx
      rw [hmax x hx]
      exact zero_mem _
  rw [← hq, hq']
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.CompanionTheory.Ar.CptInh
