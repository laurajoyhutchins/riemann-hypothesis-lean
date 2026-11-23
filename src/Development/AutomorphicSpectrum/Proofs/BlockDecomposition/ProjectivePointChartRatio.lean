module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem ptP_mem_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c) :=
  CxPts.ofHom_mem _ _ _

theorem ev_ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w) = chartHom N c w a :=
  CxPts.ev_ofHom _ _ _ a

theorem ev_ptP_ratio (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) (ratio ℤ N c i) (ptP N c w) = w i / w c := by
  rw [ev_ptP]
  by_cases h : i = c
  · subst h
    rw [ratio, ratioOn_self, map_one, div_self hc]
  · have e : (chartAlgEquiv ℤ N c).symm (ratio ℤ N c i) = X ⟨i, h⟩ := by
      rw [← chartAlgEquiv_X ℤ N c ⟨i, h⟩]
      exact AlgEquiv.symm_apply_apply _ _
    simp [chartHom, e]

theorem ptP_mem_chart_iff (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0 := by
  have e := CxPts.mem_ptsIn_basicOpen (ptP_mem_chart N c w) (ratio ℤ N c i)
  rw [ratio, basicOpen_ratioOn, CxPts.mem_ptsIn_inf] at e
  rw [← ratio, ev_ptP_ratio N c w hc i] at e
  constructor
  · intro h
    have := e.1 ⟨ptP_mem_chart N c w, h⟩
    exact fun h0 => this (by rw [h0, zero_div])
  · intro h
    exact (e.2 (div_ne_zero h hc)).2

theorem ptP_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0) :
    (∀ i, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0) ∧
    ∀ i j, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) →
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (GlobalTheory.CompanionTheory.MPSmooth.ptP N c w) =
        w j / w i := by
  refine ⟨ptP_mem_chart_iff N c w hc, fun i j hi => ?_⟩
  have hwi : w i ≠ 0 := (ptP_mem_chart_iff N c w hc i).1 hi
  have hW : ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i) :=
    CxPts.mem_ptsIn_inf.2 ⟨ptP_mem_chart N c w, hi⟩
  have h₁ : ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left i *
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j =
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left j :=
    ratioOn_mul_ratioOn
  have h₂ := congrArg (fun f => CxPts.ev (PSpace.str ℤ N) σ₀ _ f (ptP N c w)) h₁
  simp only [CxPts.ev_mul] at h₂
  have ea : ∀ k, CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left k) (ptP N c w) = w k / w c := fun k =>
    (CxPts.ev_res inf_le_left hW (ratio ℤ N c k)).trans (ev_ptP_ratio N c w hc k)
  have eb : CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j) (ptP N c w) =
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (ptP N c w) :=
    CxPts.ev_res inf_le_right hW (ratio ℤ N i j)
  rw [ea, ea, eb] at h₂
  field_simp at h₂ ⊢
  exact h₂

end GlobalTheory.CompanionTheory.MPSmooth
