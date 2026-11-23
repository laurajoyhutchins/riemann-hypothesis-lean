module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer.SliceZero

theorem prod_sumElim_zero {I : Type} {g : ℕ} {R : Type} [CommRing R] (N : ℕ) (t : I → R)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (s : Fin (N + 1) → I ⊕ Fin g) :
    ∏ a, (Sum.elim t (0 : Fin g → R)) (s a) = 0 := by
  by_cases h : ∀ a, ∃ i, s a = Sum.inl i
  · choose f hf using h
    rw [Finset.prod_congr rfl fun a _ ↦ by rw [hf a]]
    simpa using ht f
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ : ∃ b, s a = Sum.inr b := by
      rcases hs : s a with i | b
      · exact absurd hs (ha i)
      · exact ⟨b, rfl⟩
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hb]; rfl)

end GlobalTheory.AnPer.SliceZero


open GlobalTheory.AnPer.SliceZero in
theorem GlobalTheory.AnPer.exists_sliceZero_isTay : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∃ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ := by
  intro I _ _ g R _ _ N t ht W W₀ hW
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AnPer.exists_sliceTaylor_algHom N (Sum.elim t (0 : Fin g → R))
    (prod_sumElim_zero N t ht) (E := Tot Empty g) W W₀ Prod.snd
    (fun p _ ↦ analyticAt_snd) hW
  refine ⟨ρ.toRingHom, fun h p hp ↦ ?_⟩
  refine (hρ h p hp).trans ?_
  have hh : AnalyticAt ℂ h.fn (0, p.2 + (fun _ : I → ℂ ↦ (0 : Fin g → ℂ)) 0) := by
    rw [add_zero]; exact h.analytic _ (hW p hp)
  have hs := taylor_shear N t ht h.fn (fun _ ↦ (0 : Fin g → ℂ)) p.2 analyticAt_const hh
  simp only [add_zero, Pi.zero_apply, taylor_const_fun, map_zero, sub_zero] at hs
  rw [hs]
  rfl
