module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.CompanionTheory.FSCrofton.HessFrame

private lemma contDiffOn_norm_sq_of_differentiableOn {d : ℕ} {U : Set (V d)} (hU : IsOpen U) {f : V d → ℂ}
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℝ ∞ (fun v => ‖f v‖ ^ 2) U :=
  (contDiff_norm_sq ℝ).comp_contDiffOn
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn d f U hU hf).restrict_scalars ℝ)

theorem cHess_log_sum_normSq_eq (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α)
    (U : Set (V d)) (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (h0 : ∀ z ∈ U, b j₀ z ≠ 0) : ∀ z ∈ U,
    cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z =
      cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ))
        z := by
  intro z hz
  obtain ⟨R, hRdef⟩ : ∃ R : V d → ℝ,
      R = fun v => 1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2 := ⟨_, rfl⟩
  have hpos : ∀ v ∈ U, 0 < ‖b j₀ v‖ ^ 2 := fun v hv => pow_pos (norm_pos_iff.2 (h0 v hv)) 2
  have hRpos : ∀ v, 0 < R v := fun v => by rw [hRdef]; positivity
  have hp : ContDiffOn ℝ ∞ (fun v => Real.log (‖b j₀ v‖ ^ 2)) U :=
    (contDiffOn_norm_sq_of_differentiableOn hU (hb j₀)).log fun v hv => (hpos v hv).ne'
  have hq : ContDiffOn ℝ ∞ (fun v => Real.log (R v)) U := by
    refine ContDiffOn.log ?_ fun v _ => (hRpos v).ne'
    rw [hRdef]
    exact contDiffOn_const.add
      (ContDiffOn.sum fun j _ => contDiffOn_norm_sq_of_differentiableOn hU (by
        simpa only [div_eq_mul_inv] using (hb j.1).fun_mul ((hb j₀).fun_inv h0)))
  have hsplit : ∀ v ∈ U, ∑ j, ‖b j v‖ ^ 2 = ‖b j₀ v‖ ^ 2 * R v := by
    intro v hv
    have hn : ‖b j₀ v‖ ^ 2 ≠ 0 := (hpos v hv).ne'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      Finset.sum_subtype (F := inferInstance) (Finset.univ.erase j₀) (p := fun j => j ≠ j₀) (by simp),
      hRdef]
    simp only [mul_add, mul_one, Finset.mul_sum, norm_div, div_pow, mul_div_cancel₀ _ hn]
  have hev : (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun v => ((Real.log (‖b j₀ v‖ ^ 2) + 1 * Real.log (R v) : ℝ) : ℂ) := by
    refine Filter.eventually_of_mem (hU.mem_nhds hz) fun v hv => ?_
    simp only
    rw [hsplit v hv, Real.log_mul (hpos v hv).ne' (hRpos v).ne', one_mul]
  have hzero : cHess d (fun w => ((Real.log (‖b j₀ w‖ ^ 2) : ℝ) : ℂ)) z = 0 := by
    ext j k
    simp only [cHess, Matrix.of_apply, Matrix.zero_apply]
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log hU hz (hb j₀) h0 j k
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr hev,
    ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hU hp hq 1 hz, hzero, zero_add, Complex.ofReal_one,
    one_smul, hRdef]

end GlobalTheory.CompanionTheory.FSCrofton.HessFrame
