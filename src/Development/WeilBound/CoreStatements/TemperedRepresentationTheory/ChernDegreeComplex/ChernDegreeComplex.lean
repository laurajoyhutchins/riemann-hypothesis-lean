module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralEqIntersectionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPolynomialGrowthStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPresentationIndepStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneTwistGloballyGeneratedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomialStatement
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace PositivityTheory.Tls2.Chern2

theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex := by
  intro Y Δ L r hr φ hφ
  refine ⟨GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ, ?_⟩
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart ℂ Y.N (Y.ι (genericPoint ↥Y.X))
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (GlobalTheory.T.hyperplane_twist_globally_generated Y i hi 0)
  obtain ⟨L₀, r₀, n₀, b₀, hL₀, hp₀, hb₀⟩ := hM₀ (M₀ + 1) (by omega)
  have hφ₀ := Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL₀ b₀ hb₀ 1 (by simp)
  obtain ⟨P, -, hP⟩ := GlobalTheory.T.chern_integral_polynomial_growth Y Δ _ L L₀ r r₀ hr hp₀ φ _ hφ hφ₀
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.intersection_number_polynomial Y Δ (0 + (M₀ + 1) • Y.hyp hi)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (GlobalTheory.T.hyperplane_twist_globally_generated Y i hi Δ)
  have key : ∀ m : ℕ, M ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨L', r', ψ, hp', hψ, hψeq⟩ := hP m
    have hmm : M ≤ m * (M₀ + 1) := le_trans hm (Nat.le_mul_of_pos_right m (Nat.succ_pos M₀))
    obtain ⟨L₁, r₁, n₁, b₁, hL₁, hp₁, hb₁⟩ := hM (m * (M₀ + 1)) hmm
    have hΔ : Δ + (m * (M₀ + 1)) • Y.hyp hi = Δ + m • (0 + (M₀ + 1) • Y.hyp hi) := by
      rw [zero_add, mul_smul]
    rw [hΔ] at hp₁
    rw [← hψeq, ← hQ m, ← GlobalTheory.T.chern_integral_eq_intersection Y _ L₁ r₁ hL₁ n₁ b₁ hb₁ hp₁]
    exact GlobalTheory.T.chern_integral_presentation_indep Y _ L' L₁ r' r₁ hp' hp₁ ψ _ hψ
      (Weight.isCInf_fsBasis _ _ _ _ _)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite M).image Nat.cast_injective.injOn)
    rintro x ⟨m, hm, rfl⟩
    exact key m hm
  obtain ⟨L', r', ψ, hp', hψ, hψeq⟩ := hP 0
  have h0 : Δ + (0 : ℕ) • (0 + (M₀ + 1) • Y.hyp hi) = Δ := by simp
  rw [h0] at hp'
  have hQ0 := hQ 0
  rw [h0] at hQ0
  rw [hQ0, ← hPQ, ← hψeq]
  exact GlobalTheory.T.chern_integral_presentation_indep Y Δ L L' r r' hr hp' φ ψ hφ hψ

end PositivityTheory.Tls2.Chern2
