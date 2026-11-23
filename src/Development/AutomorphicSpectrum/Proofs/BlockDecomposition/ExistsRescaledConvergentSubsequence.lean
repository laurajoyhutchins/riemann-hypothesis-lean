module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimVec

theorem normalised_subseq_limit : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (g : ℕ → M), (∀ k, g k ≠ 0) → ∃ (c : ℕ → ℂ) (φ : ℕ → ℕ) (G : M), StrictMono φ ∧ G ≠ 0 ∧ ∀ ℓ : Module.Dual ℂ M, Tendsto (fun k => c k * ℓ (g (φ k))) atTop (𝓝 (ℓ G)) := by
  intro M _ _ _ g hg
  let e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ) := (Module.finBasis ℂ M).equivFun
  let s : ℕ → ℂ := fun k => ((‖e (g k)‖⁻¹ : ℝ) : ℂ)
  have hv : ∀ k, e (g k) ≠ 0 := fun k h => hg k (by simpa using h)
  have hmem : ∀ k, s k • e (g k) ∈ Metric.sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1 := by
    intro k
    have hn : ‖e (g k)‖ ≠ 0 := norm_ne_zero_iff.mpr (hv k)
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp only [s, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn
  obtain ⟨v, hvs, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1).tendsto_subseq hmem
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hvs
    simp at hvs
  refine ⟨fun k => s (φ k), φ, e.symm v, hφ, by simpa using hv0, fun ℓ => ?_⟩
  let L : (Fin (Module.finrank ℂ M) → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ e.symm.toLinearMap
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h := (hL.tendsto v).comp hlim
  have hfun : (L ∘ ((fun k => s k • e (g k)) ∘ φ)) = fun k => s (φ k) * ℓ (g (φ k)) := by
    funext k
    simp [L]
  rw [hfun] at h
  simpa [L] using h

end GlobalTheory.CompanionTheory.LimVec
