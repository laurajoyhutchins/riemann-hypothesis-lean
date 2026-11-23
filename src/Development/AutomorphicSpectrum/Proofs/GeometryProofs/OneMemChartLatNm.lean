module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.Diag

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L}
    (hz : z ∈ ptsOver L (mCoordIdeal y)) {w w' : L} (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h₁, hg, hh, hd, hy, hz0, hzw⟩ := h
  obtain ⟨dg', dh', g', h₁', hg', hh', hd', hy', hz0', hzw'⟩ := h'
  have e : dg + dh' = dg' + dh := by
    funext k
    simp only [Pi.add_apply]
    have h1 := hd k
    have h2 := hd' k
    omega
  have hh2 : IsMultiHomog (g' * h₁) (dg + dh') := by
    rw [e]
    exact GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_mul hg' hh
  have hF : g * h₁' - g' * h₁ ∈ mCoordIdeal y := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.mem_of_aeval_eq_zero
      (GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_sub (GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_mul hg hh') hh2) ?_
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have h0 := hz.2 _ hF
  rw [map_sub, map_mul, map_mul, hzw, hzw'] at h0
  have h2 : (w - w') * ((MvPolynomial.aeval z) h₁ * (MvPolynomial.aeval z) h₁') = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 (mul_ne_zero hz0 hz0')

end General

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

end GlobalTheory.CompanionTheory.Ar.Ht.Diag
