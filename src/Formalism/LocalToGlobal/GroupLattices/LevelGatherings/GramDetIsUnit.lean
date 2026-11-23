module

public import Formalism.LocalRingCardinality.DataLevel
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField Formalism.UG

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isUnit_det_gram0 (sp : Spaces R F E) : IsUnit sp.gram0.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  rw [Spaces.gram0, Matrix.det_reindex_self] at hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hi : ∀ i, (sp.X 0).hT ((sp.X 0).frame i) (∑ j, v j • (sp.X 0).frame j) = 0 := by
    intro i
    have h := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at h

    simp only [map_sum, map_smul, smul_eq_mul]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hy : ∀ x, (sp.X 0).hT x (∑ j, v j • (sp.X 0).frame j) = 0 := by
    intro x

    rw [← (sp.X 0).frame.sum_repr x, map_sum (sp.X 0).hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  have h0 := (sp.X 0).nondeg.2 _ hy
  have hv' := Fintype.linearIndependent_iff.mp (sp.X 0).frame.linearIndependent v h0
  exact hv0 (funext hv')

end Formalism.L2.G
