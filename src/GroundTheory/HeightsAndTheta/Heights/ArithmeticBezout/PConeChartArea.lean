module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)

theorem integral_indicator_ball_norm_pow (e : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t : ℂ, (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) t =
      Real.pi * R ^ (2 * (e + 1)) / (e + 1) := by
  have hfun : (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) =
      fun t => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) ‖t‖ := by
    ext t
    simp [Set.indicator]
  rw [hfun, integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun r : ℝ => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) r)]
  have hvol : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real]
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y = R ^ (2 * e + 2) / (2 * e + 2) := by
    have hpt : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
        (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y) =
        (Iio R).indicator (fun y : ℝ => y ^ (2 * e + 1)) := by
      ext y
      by_cases hy : y < R
      · simp [Set.indicator, hy, Complex.finrank_real_complex, pow_succ]
        ring
      · simp [Set.indicator, hy]
    rw [hpt, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR, integral_pow]
    push_cast
    ring_nf
  rw [hint, hvol, Complex.finrank_real_complex]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

end GroundTheory.Heights₂.Heights
