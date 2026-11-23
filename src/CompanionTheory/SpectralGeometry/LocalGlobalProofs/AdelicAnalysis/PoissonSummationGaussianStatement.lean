module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PoissonSummationGaussian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory.CompanionTheory.SW.Core.PoiLat in

theorem _root_.GlobalTheory.T.poisson_summation_gaussian :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ),
    Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ,
    let f : (κ → ℝ) → ℂ := fun x => Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ))));
    let fh : (κ → ℝ) → ℂ := fun y =>
      ∫ x, f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ));
    Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧
      Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧
      (∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ))) = ((|g.det|⁻¹ : ℝ) : ℂ) *
        ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
            ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  intro κ _ _ Z hs hp g hg a f fh
  have hZ : GlobalTheory.IsSiegel Z := ⟨hs, hp⟩
  have hσ := hZ.transpose_mul_mul hg
  have hf : ∀ n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) =
      GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
        ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n :=
    fun n => gaussian_lattice_term Z hg a n
  have hfh : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) =
      GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 0
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
    intro n
    rw [← fourier_lattice_term hZ hg n]
    exact gaussian_fourier hZ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [hf]
    exact hσ.summable_norm_riemannThetaTerm _ _ _
  · simp only [hfh, norm_mul]
    exact (hσ.neg_inv.summable_norm_riemannThetaTerm _ _ _).mul_left _
  · have hterm : ∀ n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) =
      GlobalTheory.siegelGaussIntegral Z *
        GlobalTheory.riemannThetaTerm 0 (-(g⁻¹ *ᵥ a))
          (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
      intro n
      rw [hfh, phase_lattice, mul_assoc]
      congr 1
      rw [GlobalTheory.riemannThetaTerm_zero_zero, GlobalTheory.riemannThetaTerm_def,
        ← Complex.exp_add]
      congr 1
      simp [dotProduct]
      ring
    simp only [hf, hterm]
    rw [tsum_mul_left, ← mul_assoc, ← siegelGaussIntegral_congr Z hg]
    have h0 := hσ.riemannTheta_eq_neg_inv (g⁻¹ *ᵥ a) 0
    have h1 := GlobalTheory.riemannTheta_neg 0 (g⁻¹ *ᵥ a)
      (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0
    simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h0 h1
    rw [h1] at h0
    exact h0
