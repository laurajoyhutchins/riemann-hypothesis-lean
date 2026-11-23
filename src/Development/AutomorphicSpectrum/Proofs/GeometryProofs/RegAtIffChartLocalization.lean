module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordLoc

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hξ : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hξ).hom f) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have h2 := congrArg (fun g => g.hom f) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes q.2).hom
    ((X.presheaf.germ U q.1 hq).hom f)) = _
  rw [h2]

end GlobalTheory.CompanionTheory.Ar.CoordLoc

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_iff_exists_chart_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  intro X Ω _ ξ o _ _ κ x hT c p hp a
  have hc : x c ≠ 0 := hp.1
  constructor
  · intro ha
    obtain ⟨U, hU, hUmem⟩ := hT.affine c hc
    have hpU : p.1 ∈ U := (hUmem p.1).2 ⟨p.2, hp⟩
    have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
    let φ : Γ(X, U) → Ω := fun f =>
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hgU).hom f)
    have hφA : ∀ f, φ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
      intro f
      rw [hT.ring c hc]
      intro q hq
      have hqU : q.1 ∈ U := (hUmem q.1).2 ⟨q.2, hq⟩
      exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom f, CoordLoc.genMap_germ ξ U hgU q hqU f⟩
    have hφp : ∀ f, φ f = genMap ξ p ((X.presheaf.germ U p.1 hpU).hom f) := fun f =>
      (CoordLoc.genMap_germ ξ U hgU p hpU f).symm
    have ha' : a ∈ (genMap ξ p).range := ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha'
    let xU : U := ⟨p.1, hpU⟩
    have := hU.isLocalization_stalk xU
    have hgerm : ∀ f, algebraMap Γ(X, U) (X.presheaf.stalk xU.1) f = (X.presheaf.germ U p.1 hpU).hom f :=
      fun f => rfl
    obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf xU).asIdeal.primeCompl
      (S := X.presheaf.stalk xU.1) g
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk xU.1) t s
    simp only at hts
    rw [hts, hgerm, hgerm] at hspec
    have hunit := IsLocalization.map_units (X.presheaf.stalk xU.1) s
    rw [hgerm] at hunit
    obtain ⟨u, hu⟩ := hunit
    refine ⟨φ s, hφA s, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hφp, ← hu]
      exact (u.isUnit.map (genMap ξ p)).ne_zero
    · exact ⟨(X.presheaf.germ U p.1 hpU).hom s, (hφp s).symm⟩
    · refine RingHom.mem_range.mpr ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩
      rw [hφp, ← hu]
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    · have hmul : φ s * genMap ξ p g = φ t := by
        rw [hφp, hφp, ← map_mul, mul_comm, hspec]
      rw [hmul]
      exact hφA t
  · rintro ⟨s, _, ⟨hs0, _, hsinv⟩, hsa⟩
    have hsa' : s * a ∈ regAt ξ p := (hT.ring c hc (s * a)).mp hsa p hp
    have heq : a = s⁻¹ * (s * a) := by
      rw [← _root_.mul_assoc, inv_mul_cancel₀ hs0, _root_.one_mul]
    rw [heq]
    exact Subring.mul_mem _ hsinv hsa'

end GlobalTheory.CompanionTheory.Ar
