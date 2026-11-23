module

public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem hspace_gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) :
    W.gram.det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hb : ∀ i, W.hT (W.frame i) (∑ j, v j • W.frame j) = 0 := by
    intro i
    have := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this

    rw [map_sum, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hz : (∑ j, v j • W.frame j) = 0 := by
    refine W.nondeg.2 _ fun x => ?_

    rw [← W.frame.sum_repr x, map_sum W.hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hb, smul_zero]
  apply hv
  funext j
  exact Fintype.linearIndependent_iff.mp W.frame.linearIndependent v hz j

theorem cmData_isCMExt_and_gram_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), IsCMExt F E cm.sig ∧ ∀ W : HSpace E, IsHermND cm.sig W.gram := by
  intro F E _ _ _ _ _ _ cm
  refine ⟨⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩, fun W => ⟨fun i j => ?_, hspace_gram_det_ne_zero W⟩⟩
  exact W.herm.eq (W.frame j) (W.frame i)

end GlobalTheory.Mem.Vol
