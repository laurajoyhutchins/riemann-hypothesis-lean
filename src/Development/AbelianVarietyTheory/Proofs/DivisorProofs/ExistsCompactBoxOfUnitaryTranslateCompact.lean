module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BoxMove

theorem inBox_image_mul : ∀ (D : D7) (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.InBox K (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) → GlobalTheory.Unf.InBox K' x := by
  intro D V n Q hQ K hK
  have hmt : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n) :=
    (hmt.comp continuous_fst).matrix_mul continuous_snd
  refine ⟨(fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n)) '' (Q ×ˢ K), (hQ.prod hK).image hf, ?_⟩
  rintro y hy x ⟨k, hk, h0⟩
  refine ⟨(HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n), ⟨(y, k), ⟨hy, hk⟩, rfl⟩, ?_⟩
  have hyy : Formalism.L2.Theta.mt V y * Formalism.L2.Theta.mt V y⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hx : x - (HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n) = (HMul.hMul (Formalism.L2.Theta.mt V y) ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) - k) : Mx D V.rank n) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  rw [hx, Matrix.map_mul, h0, Matrix.mul_zero]

end GlobalTheory.BoxMove
