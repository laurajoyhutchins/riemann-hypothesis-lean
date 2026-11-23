module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
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
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.CxSmooth

private theorem analyticAt_of_differentiableOn_open {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h U) {c : Fin n → ℂ} (hc : c ∈ U) :
    AnalyticAt ℂ h c := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hc)
  have hd : ∀ ζ ∈ Metric.closedBall c r, DifferentiableAt ℂ h ζ :=
    fun ζ hζ => hh.differentiableAt (hU.mem_nhds (hrU hζ))
  have hA : AnalyticAt ℂ (fun w => ((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ *
      ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd (ReciprocityTheory.AnForm.Osgood.kern c r w)) c :=
    analyticAt_const.mul
      (((ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd).analyticAt _).comp
        (ReciprocityTheory.AnForm.Osgood.kern_analyticAt c hr))
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero)
  refine hA.congr ?_
  filter_upwards [Metric.ball_mem_nhds c hr] with w hw
  rw [ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hr hd hw]
  exact inv_mul_cancel_left₀ h2 (h w)

theorem analyticAt_of_differentiableOn {ι : Type} [Fintype ι] {U : Set (ι → ℂ)} (hU : IsOpen U)
    {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {z : ι → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z := by
  classical
  let e := Fintype.equivFin ι
  let φ : (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e)
  let ψ : (ι → ℂ) →L[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e.symm)
  have hφψ : ∀ w, φ (ψ w) = w := fun w => funext fun i => by simp [φ, ψ]
  have hmem : ψ z ∈ φ ⁻¹' U := by
    rw [Set.mem_preimage, hφψ]
    exact hz
  have hA := analyticAt_of_differentiableOn_open (hU.preimage φ.continuous)
    (hf.comp φ.differentiableOn (Set.mapsTo_preimage φ U)) hmem
  have hB := hA.comp (ψ.analyticAt z)
  have heq : (f ∘ ⇑φ) ∘ ⇑ψ = f := funext fun w => by simp only [Function.comp_apply, hφψ]
  rwa [heq] at hB

theorem contDiffAt_comp_of_cInfAt : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {ι : Type} [Fintype ι]
  {T : Set (ι → ℂ)} {s : (ι → ℂ) → CxPts p σ} {f : CxPts p σ → ℝ} {z₀ : ι → ℂ}, IsOpen T → ContinuousOn s T →
  (∀ (W : Y.Opens) (g : Γ(Y, W)), DifferentiableOn ℂ (CxPts.ev p σ W g ∘ s) (T ∩ s ⁻¹' ptsIn p σ W)) →
  z₀ ∈ T → CInfAt f (s z₀) → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ s) z₀ := by
  intro k _ Y p σ ι _ T s f z₀ hT hs hd hz h
  obtain ⟨W, ι', _, g, F, O, hyW, hO, hmem, hF, hev⟩ := h
  have hN : IsOpen (T ∩ s ⁻¹' ptsIn p σ W) := hs.isOpen_inter_preimage hT (isOpen_ptsIn W)
  have hzN : z₀ ∈ T ∩ s ⁻¹' ptsIn p σ W := ⟨hz, hyW⟩
  have hG : AnalyticAt ℂ (fun z a => ev p σ W (g a) (s z)) z₀ :=
    analyticAt_pi_iff.2 fun a => analyticAt_of_differentiableOn hN (hd W (g a)) hzN
  have hcont : ContinuousAt s z₀ := hs.continuousAt (hT.mem_nhds hz)
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ fun z a => ev p σ W (g a) (s z)) z₀ :=
    (hF.contDiffAt (hO.mem_nhds hmem)).comp z₀ (hG.contDiffAt.restrict_scalars ℝ)
  exact h1.congr_of_eventuallyEq (hev.comp_tendsto hcont)

end GlobalTheory.CompanionTheory.CxSmooth
