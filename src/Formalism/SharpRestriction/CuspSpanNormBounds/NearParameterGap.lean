module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.NearParameterGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.OnePlaceEstimates

theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set N : ℝ := 2 * (r : ℝ) + k + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN2 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2 := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith
  have hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith
  have hnk : ((2 * r + k : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2) :=
      mul_le_mul hnk hdN hdN0 (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have e1 : ((k : ℝ) + r) ≤ N := by rw [hN]; linarith
    have e2 : ((r : ℝ) + 1) ≤ N := by rw [hN]; linarith
    have e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity

end Formalism.MainNotions.NearParameterGap
