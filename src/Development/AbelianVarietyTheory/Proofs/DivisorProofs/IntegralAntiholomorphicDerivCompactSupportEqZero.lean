module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
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
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop

theorem integral_dbar_eq_zero_of_hasCompactSupport {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem setIntegral_dbar_eq_zero {n : ℕ} (U K : Set (V n)) (g : V n → ℂ) (ξ : V n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hg : ContDiffOn ℝ 1 g U)
    (h0 : ∀ v ∈ U, v ∉ K → g v = 0) :
    IntegrableOn (fun v => dbar g v ξ) U ∧ ∫ v in U, dbar g v ξ = 0 := by
  classical
  set G : V n → ℂ := U.indicator g with hGdef
  have hin : ∀ v ∈ U, G =ᶠ[𝓝 v] g := fun v hv => by
    filter_upwards [hU.mem_nhds hv] with x hx
    exact Set.indicator_of_mem hx g
  have hz : ∀ x, x ∉ K → G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [hGdef, Set.indicator_of_mem hxU, h0 x hxU hx]
    · rw [hGdef, Set.indicator_of_notMem hxU]
  have hout : ∀ v, v ∉ K → G =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hv] with x hx
    exact hz x hx
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ U
    · exact (hg.contDiffAt (hU.mem_nhds hv)).congr_of_eventuallyEq (hin v hv)
    · exact contDiffAt_const.congr_of_eventuallyEq (hout v fun h => hv (hKU h))
  have hc : HasCompactSupport G := HasCompactSupport.intro hK hz
  obtain ⟨hI, hE⟩ := integral_dbar_eq_zero_of_hasCompactSupport hG hc ξ
  have heq : Set.EqOn (fun v => dbar G v ξ) (fun v => dbar g v ξ) U := fun v hv => by
    simp only [dbar_congr (hin v hv)]
  refine ⟨hI.integrableOn.congr_fun heq hU.measurableSet, ?_⟩
  rw [← setIntegral_congr_fun hU.measurableSet heq,
    setIntegral_eq_integral_of_forall_compl_eq_zero, hE]
  intro v hv
  rw [dbar_congr (hout v fun h => hv (hKU h))]
  simp [dbar_apply]

end GlobalTheory.GoodTop
