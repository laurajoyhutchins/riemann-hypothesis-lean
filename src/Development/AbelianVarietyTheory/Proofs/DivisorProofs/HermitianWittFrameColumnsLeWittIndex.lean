module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittIdxBound

theorem witt_frame_le_wittIdx : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  intro D V r X Y h
  obtain ⟨ev, hev⟩ := GlobalTheory.BesselCompare.eMat_surj V X
  obtain ⟨ev', hev'⟩ := GlobalTheory.BesselCompare.eMat_surj V Y
  have hiso : ∀ a b, V.hT (ev a) (ev b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev]
    exact congrFun (congrFun h.xx a) b
  have hpair : ∀ i j, V.hT (ev i) (ev' j) = if i = j then 1 else 0 := fun i j => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev, hev', h.xy]
    simp [Matrix.one_apply]
  have hli : LinearIndependent D.host.E ev := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (fun v => V.hT v (ev' j)) hc

    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hpair, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, LinearMap.zero_apply] at h1
    simpa using h1
  have hmem : ∀ x ∈ Submodule.span D.host.E (Set.range ev), ∃ c : Fin r → D.host.E, ∑ i, c i • ev i = x :=
    fun x hx => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx
  apply le_csSup
  · refine ⟨Module.finrank D.host.E V.V, ?_⟩
    rintro k ⟨W, rfl, -⟩
    exact Submodule.finrank_le W
  · refine ⟨Submodule.span D.host.E (Set.range ev), ?_, ?_⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
    · intro x hx y hy
      obtain ⟨c, rfl⟩ := hmem x hx
      obtain ⟨d, rfl⟩ := hmem y hy

      simp [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hiso]

end GlobalTheory.WittIdxBound
