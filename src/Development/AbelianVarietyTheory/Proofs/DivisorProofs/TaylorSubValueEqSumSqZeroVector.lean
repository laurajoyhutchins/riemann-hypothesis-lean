module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem taylor_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  intro I _ _ g R _ _ J N hJ r
  induction r with
  | zero =>
    intro m _ _ τ _
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun a => ?_⟩
    have h := (taylor_formal_properties N (fun i ↦ ∑ j : Fin 0, m j i)).2.2.2.2.2 (fun z ↦ τ z a)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    have : Set.range (fun _ : I => (0 : R)) ⊆ {0} := by
      rintro _ ⟨_, rfl⟩; rfl
    have hb : Ideal.span (Set.range (fun _ : I => (0 : R))) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨_, rfl⟩; rfl
    rw [hb, Ideal.mem_bot] at h
    exact h
  | succ r ih =>
    intro m hmJ hm τ hτ
    obtain ⟨n', hn'J, hn', hn'eq⟩ := ih (fun j => m (Fin.castSucc j)) (fun j i => hmJ _ i)
      (fun j i i' => hm _ i i') τ hτ
    set t : I → R := fun i => ∑ j : Fin r, m (Fin.castSucc j) i with ht
    set l : I → R := fun i => m (Fin.last r) i with hl
    let v : Fin g → R := fun a => ∑ i, taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i 1)) * l i
    have htJ : ∀ i, t i ∈ J := fun i => J.sum_mem fun j _ => hmJ _ i
    have hlJ : ∀ i, l i ∈ J := fun i => hmJ _ i
    have hspan : Ideal.span (Set.range t ∪ Set.range l) ≤ J := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact htJ i
      · exact hlJ i
    have hvJ : ∀ a, v a ∈ J := fun a => J.sum_mem fun i _ => J.mul_mem_left _ (hlJ i)
    have hv : ∀ a b, v a * v b = 0 := by
      intro a b
      simp only [v, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
      have := hm (Fin.last r) i' i
      calc _ = (taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z b) z (Pi.single i 1)) *
              taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i' 1))) * (l i' * l i) := by ring
        _ = 0 := by simp only [hl, this, mul_zero]
    refine ⟨Fin.snoc (α := fun _ => Fin g → R) n' v, ?_, ?_, ?_⟩
    · intro j a
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hvJ a
      · simpa using hn'J j a
    · intro j a b
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hv a b
      · simpa using hn' j a b
    · intro a
      have hfa : AnalyticAt ℂ (fun z ↦ τ z a) 0 :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) a).analyticAt (τ 0)).comp hτ
      have hsum : (fun i ↦ ∑ j : Fin (r + 1), m j i) = fun i => t i + l i := by
        funext i; simp only [ht, hl, Fin.sum_univ_castSucc]
      have hstep := taylor_add_of_mul_eq_zero N t l
        (fun s hs => hJ s fun a => hspan (hs a)) (fun i j => hm (Fin.last r) i j) _ hfa
      rw [hsum, hstep, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hn'eq a]
      simp only [v, t]
      ring

end GlobalTheory.PeriodFamily
