module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpBridge
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

noncomputable section

namespace PI.GalTorsConj.W

open PI.GalTorsConj Filter Topology

theorem wp_onto (L : PeriodPair) (x : ℂ) : ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = x := by
  classical
  by_contra hne
  push Not at hne
  set f : ℂ → ℂ := fun z => (L.weierstrassP z - x)⁻¹ with hf
  have hmer : ∀ z, MeromorphicAt f z := by
    intro z
    have h := L.meromorphic_weierstrassP z
    fun_prop
  have hper : Formalism.L2.Th1.F.IsPeriodic L f := by
    intro ω hω z
    show (L.weierstrassP (z + ω) - x)⁻¹ = (L.weierstrassP z - x)⁻¹
    rw [show L.weierstrassP (z + ω) = L.weierstrassP z from L.weierstrassP_add_coe z ⟨ω, hω⟩]
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ f z := by
    intro z hz
    have h1 : AnalyticAt ℂ L.weierstrassP z := L.analyticOnNhd_weierstrassP z hz
    have h2 : L.weierstrassP z - x ≠ 0 := sub_ne_zero.mpr (hne z hz)
    exact (h1.sub analyticAt_const).inv h2
  have hord : ∀ z, 0 ≤ meromorphicOrderAt f z := by
    intro z
    by_cases hz : z ∈ L.lattice
    · have h1 : meromorphicOrderAt (fun w => L.weierstrassP w - x) z = -2 := by
        have e : (fun w => L.weierstrassP w - x) = L.weierstrassP + (fun _ => -x) := by
          ext w
          simp [sub_eq_add_neg]
        rw [e, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-x) z)]
        · exact L.order_weierstrassP z hz
        · rw [L.order_weierstrassP z hz, meromorphicOrderAt_const]
          split_ifs
          · exact WithTop.coe_lt_top _
          · decide
      have e2 : f = (fun w => L.weierstrassP w - x)⁻¹ := rfl
      rw [e2, meromorphicOrderAt_inv, h1]
      decide
    · exact (han z hz).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := Formalism.L2.Th1.F.ellipticNoPole L f hmer hper hord
  have hev : L.weierstrassP =ᶠ[𝓝[≠] 0] fun _ => x + c⁻¹ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz0 hz
    have hzl : z ∉ L.lattice := fun h => hz ⟨h, hz0⟩
    have h1 : f z = c := hc z (han z hzl).continuousAt
    have h1' : (L.weierstrassP z - x)⁻¹ = c := h1
    rw [← h1', inv_inv]
    ring
  have h3 := meromorphicOrderAt_congr hev
  rw [L.order_weierstrassP 0 L.lattice.zero_mem, meromorphicOrderAt_const] at h3
  split_ifs at h3
  · exact absurd h3 (WithTop.coe_ne_top)
  · exact absurd h3 (by decide)

theorem pOnto : POnto := by
  intro L x y hxy
  obtain ⟨z, hz, hzx⟩ := wp_onto L x
  have hsq := L.derivWeierstrassP_sq z hz
  rw [hzx, ← hxy] at hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact ⟨z, hz, hzx, h⟩
  · refine ⟨-z, ?_, by rw [L.weierstrassP_neg, hzx], by rw [L.derivWeierstrassP_neg, h, neg_neg]⟩
    intro hm
    exact hz (by simpa using L.lattice.neg_mem hm)

end PI.GalTorsConj.W

end
