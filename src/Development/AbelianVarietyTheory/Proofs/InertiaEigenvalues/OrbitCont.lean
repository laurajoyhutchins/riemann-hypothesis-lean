module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst

namespace GlobalTheory.LTChar

variable {l : ℕ} [Fact l.Prime]

theorem orbit_cont (y : ℂ_[l]) : Continuous fun g : GQ l => Formalism.Per.σC g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨z, hz⟩ : ∃ z : Om l, dist y (z : ℂ_[l]) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  let F := adjExt (z : Om l)
  haveI := F.2
  have hH : IsOpen ((F.1.fixingSubgroup : Subgroup (GQ l)) : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isOpen F.1
  have hU : IsOpen {g : GQ l | g₀⁻¹ * g ∈ F.1.fixingSubgroup} :=
    hH.preimage (continuous_const.mul continuous_id)
  have hg₀ : g₀ ∈ {g : GQ l | g₀⁻¹ * g ∈ F.1.fixingSubgroup} := by
    simp only [Set.mem_setOf_eq, inv_mul_cancel]
    exact Subgroup.one_mem _
  filter_upwards [hU.mem_nhds hg₀] with g hg
  have hgz : g z = g₀ z := by
    have h := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg z (mem_adjExt z)
    rw [AlgEquiv.mul_apply] at h
    have h' := congrArg g₀ h
    rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
  have e : Formalism.Per.σC g y - Formalism.Per.σC g₀ y =
      Formalism.Per.σC g (y - z) + Formalism.Per.σC g₀ ((z : ℂ_[l]) - y) := by
    rw [map_sub, map_sub, GlobalTheory.RingBasics.σC_coe, GlobalTheory.RingBasics.σC_coe, hgz]
    ring
  rw [dist_eq_norm, e]
  calc _ ≤ ‖Formalism.Per.σC g (y - z)‖ + ‖Formalism.Per.σC g₀ ((z : ℂ_[l]) - y)‖ := norm_add_le _ _
    _ = ‖y - z‖ + ‖y - z‖ := by rw [GlobalTheory.RingBasics.norm_σC, GlobalTheory.RingBasics.norm_σC, norm_sub_rev (z : ℂ_[l]) y]
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.LTChar
