module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.SpecialisationPts

open GlobalTheory.AffinePoints GlobalTheory.CxPts

theorem nonempty_point (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem specializes_iff_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x z : X}
    (hz : z ∈ U) : x ⤳ z ↔ ∀ f : Γ(X, U), z ∈ X.basicOpen f → x ∈ X.basicOpen f := by
  refine ⟨fun h f hf => h.mem_open (X.basicOpen f).2 hf, fun h => ?_⟩
  rw [specializes_iff_forall_open]
  intro s hs hzs
  obtain ⟨g, hg, hzg⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨z, hzs⟩ hz
  exact hg (h g hzg)

theorem mem_basicOpen_iff_notMem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (f : Γ(X, U)) :
    x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f := by
    change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _
    rw [hU.fromSpec_primeIdealOf]
  rw [← h, hU.fromSpec_preimage_basicOpen]
  rfl

theorem specializes_iff_ev {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) {y : GlobalTheory.CxPts p (RingHom.id ℂ)} (hy : y ∈ ptsIn p (RingHom.id ℂ) U) :
    x ⤳ y.1 (IsLocalRing.closedPoint ℂ) ↔
      ∀ f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal, ev p (RingHom.id ℂ) U f y = 0 := by
  rw [specializes_iff_basicOpen hU (mem_ptsIn.1 hy)]
  refine forall_congr' fun f => ?_
  rw [mem_basicOpen_iff_notMem hU hx, ← mem_ptsIn, mem_ptsIn_basicOpen hy]
  exact not_imp_not

theorem nonempty_and_isPreconnected : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), LocallyOfFiniteType p →
    ∀ (U : X.Opens), IsAffineOpen U → ∀ x ∈ U,
    (∃ y : GlobalTheory.CxPts p (RingHom.id ℂ), y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧
      x ⤳ y.1 (IsLocalRing.closedPoint ℂ)) ∧
    _root_.IsPreconnected {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
  intro X p hp U hU x hx
  let : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType ℂ Γ(X, U) := hft
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have : P.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let Φ (φ : (Γ(X, U) ⧸ P) →ₐ[ℂ] ℂ) : GlobalTheory.CxPts p (RingHom.id ℂ) :=
    ofHom hU (φ.comp (Ideal.Quotient.mkₐ ℂ P)).toRingHom
      fun a => (φ.comp (Ideal.Quotient.mkₐ ℂ P)).commutes a
  have hmem (φ) : Φ φ ∈ ptsIn p (RingHom.id ℂ) U := ofHom_mem _ _ _
  have hev (φ) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (Φ φ) = φ (Ideal.Quotient.mk P f) :=
    ev_ofHom _ _ _ f
  have hc : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun φ => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hmem φ) (Filter.Eventually.of_forall hmem)
        fun f => ?_)
    have h := (continuous_eval (R := ℂ) (C := ℂ) (Ideal.Quotient.mk P f)).tendsto φ
    simp only [← hev] at h
    exact h
  have hr : Set.range Φ = {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
    ext y
    constructor
    · rintro ⟨φ, rfl⟩
      refine ⟨mem_ptsIn.1 (hmem φ), (specializes_iff_ev hU hx (hmem φ)).2 fun f hf => ?_⟩
      rw [hev, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    · rintro ⟨hy, hxy⟩
      have hy' := mem_ptsIn.2 hy
      let ψ : Γ(X, U) →ₐ[ℂ] ℂ :=
        { evHom hy' with commutes' := fun a => (ev_eq hy' _).symm.trans (ev_algX hy' a) }
      refine ⟨Ideal.Quotient.liftₐ P ψ fun f hf =>
        (ev_eq hy' f).symm.trans ((specializes_iff_ev hU hx hy').1 hxy f hf), ?_⟩
      refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hmem _) hy' fun f => ?_)
      exact (hev _ f).trans (ev_eq hy' f).symm
  constructor
  · obtain ⟨φ⟩ := nonempty_point (Γ(X, U) ⧸ P)
    have h := Set.mem_range_self (f := Φ) φ
    rw [hr] at h
    exact ⟨_, h⟩
  · have := GlobalTheory.RootConst.preconnectedSpace_algHom (Γ(X, U) ⧸ P)
    rw [← hr]
    exact isPreconnected_range hc

end GlobalTheory.SpecialisationPts
