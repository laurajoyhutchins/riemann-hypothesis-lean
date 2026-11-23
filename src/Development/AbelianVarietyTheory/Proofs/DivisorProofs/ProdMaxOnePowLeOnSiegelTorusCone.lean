module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConeMax

theorem prod_max_le_prod (r m e : ℕ) (c : ℝ) (hc : 0 < c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c,
    ∏ k : Fin r ⊕ Fin r ⊕ Fin m, max 1 (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ))) k) ^ e ≤
      C * ∏ i, t i ^ e := by
  set c0 : ℝ := min c 1 ^ r with hc0
  have hm0 : 0 < min c 1 := lt_min hc one_pos
  have hc0pos : 0 < c0 := pow_pos hm0 r
  have hc0le : c0 ≤ 1 := pow_le_one₀ hm0.le (min_le_right _ _)
  refine ⟨(c0⁻¹ ^ e) ^ r * (c0⁻¹ ^ e) ^ r, by positivity, ?_⟩
  intro t ht
  have hlow : ∀ i, c0 ≤ t i := fun i => GlobalTheory.LatCount.cone_pow_le hc ht i
  have htpos : ∀ i, 0 < t i := fun i => hc0pos.trans_le (hlow i)
  have h1 : ∀ i, max 1 (t i) ≤ t i * c0⁻¹ := by
    intro i
    have hi : 1 ≤ c0⁻¹ := one_le_inv₀ hc0pos |>.2 hc0le
    refine max_le ?_ ?_
    · rw [← mul_inv_cancel₀ hc0pos.ne']
      exact mul_le_mul_of_nonneg_right (hlow i) (inv_nonneg.2 hc0pos.le)
    · exact le_mul_of_one_le_right (htpos i).le hi
  have h2 : ∀ i, max 1 (t i)⁻¹ ≤ c0⁻¹ := by
    intro i
    refine max_le (one_le_inv₀ hc0pos |>.2 hc0le) ?_
    exact inv_anti₀ hc0pos (hlow i)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, max_self, one_pow, Finset.prod_const_one, mul_one]
  have A : ∏ i : Fin r, max 1 (t i) ^ e ≤ ∏ i : Fin r, (t i ^ e * c0⁻¹ ^ e) := by
    refine Finset.prod_le_prod₀ (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (le_max_left _ _ |>.trans' zero_le_one) (h1 i) e
  have B : ∏ i : Fin r, max 1 (t i)⁻¹ ^ e ≤ ∏ _i : Fin r, c0⁻¹ ^ e :=
    Finset.prod_le_prod₀ (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun i _ =>
      pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (h2 i) e
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at A
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at B
  have hA0 : 0 ≤ ∏ i : Fin r, max 1 (t i)⁻¹ ^ e := Finset.prod_nonneg fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  calc (∏ i : Fin r, max 1 (t i) ^ e) * ∏ i : Fin r, max 1 (t i)⁻¹ ^ e
      ≤ ((∏ i : Fin r, t i ^ e) * (c0⁻¹ ^ e) ^ r) * (c0⁻¹ ^ e) ^ r :=
        mul_le_mul A B hA0
          (mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (htpos i).le _) (by positivity))
    _ = (c0⁻¹ ^ e) ^ r * (c0⁻¹ ^ e) ^ r * ∏ i, t i ^ e := by ring

end GlobalTheory.ConeMax
