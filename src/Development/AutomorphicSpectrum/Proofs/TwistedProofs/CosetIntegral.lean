module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

theorem cosetIntegral : CosetIntegral := by
  intro G _ _ _ _ _ μ _ K hK hμK F Z hF hZ
  set f : G ⧸ K → ℂ := fun x => F x.out with hf_def
  have hFf : ∀ g, F g = f (QuotientGroup.mk g) := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [hf_def, hh, hF g h h.2]
  set C : G ⧸ K → Set G := fun x => (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {x} with hC_def
  have hC_eq : ∀ x, C x = (fun h => x.out⁻¹ * h) ⁻¹' (K : Set G) := by
    intro x
    ext g
    simp only [hC_def, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq]
  have hC_open : ∀ x, IsOpen (C x) := fun x => by
    rw [hC_eq]
    exact hK.preimage (continuous_const_mul _)
  have hC_meas : ∀ x, MeasurableSet (C x) := fun x => (hC_open x).measurableSet
  have hC_one : ∀ x, μ (C x) = 1 := fun x => by
    rw [hC_eq, measure_preimage_mul, hμK]
  have hF_on : ∀ x, Set.EqOn F (fun _ => f x) (C x) := by
    intro x g hg
    simp only [hC_def, Set.mem_preimage, Set.mem_singleton_iff] at hg
    rw [hFf g, hg]
  have hcount : (Function.support f).Countable := hZ.summable.countable_support
  have : Countable (Function.support f) := hcount.to_subtype
  set s : Function.support f → Set G := fun i => C i with hs_def
  have hs_meas : ∀ i, MeasurableSet (s i) := fun i => hC_meas _
  have hs_disj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    refine Disjoint.preimage _ (Set.disjoint_singleton.2 fun h => hij (Subtype.ext h))
  have hs_int : ∀ i, IntegrableOn F (s i) μ := by
    intro i
    refine (integrableOn_const (by rw [hC_one]; exact ENNReal.one_ne_top)).congr_fun
      (fun g hg => (hF_on i hg).symm) (hs_meas i)
  have hs_val : ∀ i, ∫ g in s i, F g ∂μ = f i := by
    intro i
    rw [setIntegral_congr_fun (hs_meas i) (hF_on i), setIntegral_const]
    simp [Measure.real, hs_def, hC_one]
  have hs_norm : ∀ i, ∫ g in s i, ‖F g‖ ∂μ = ‖f i‖ := by
    intro i
    rw [setIntegral_congr_fun (hs_meas i) (fun g hg => congrArg norm (hF_on i hg)), setIntegral_const]
    simp [Measure.real, hs_def, hC_one]
  have hU : IntegrableOn F (⋃ i, s i) μ := by
    refine integrableOn_iUnion_of_summable_integral_norm hs_int ?_
    simp only [hs_norm]
    exact hZ.summable.norm.subtype _
  have hout : ∀ g, g ∉ ⋃ i, s i → F g = 0 := by
    intro g hg
    by_contra hne
    apply hg
    have hmem : QuotientGroup.mk g ∈ Function.support f := by
      rw [Function.mem_support, ← hFf g]
      exact hne
    exact Set.mem_iUnion.2 ⟨⟨_, hmem⟩, rfl⟩
  have hint : Integrable F μ := hU.integrable_of_forall_notMem_eq_zero hout
  refine ⟨hint, ?_⟩
  have hsum := hasSum_integral_iUnion hs_meas hs_disj hU
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at hsum
  simp only [hs_val] at hsum
  exact (hasSum_subtype_support.1 hsum).unique hZ

end GlobalTheory.CompanionTheory.InertZeta
