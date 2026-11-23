module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNatMulMemRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormNatCastAdicCompletionLeOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormNatCastLe
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothForms

theorem denom_norm_natCast_le_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one
  | exact _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one
  | (apply _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one ..)

theorem denom_global {F : Type} [Field F] [NumberField F] (H : HeightOneSpectrum (𝓞 F) → NNReal)
    (hH : ∀ v, 1 ≤ H v) (hf : (Function.mulSupport H).Finite) :
    ∃ d : ℕ, 0 < d ∧ (d : NNReal) ≤ ∏ᶠ v, H v ∧
      ∀ v, ∀ y : v.adicCompletion F, ‖y‖₊ ≤ H v → ‖(d : v.adicCompletion F) * y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator
  | exact _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator
  | (apply _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator ..)

theorem denom_exists_int {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ r : 𝓞 E, (r : E) = k * e := by
  first
  | exact @_root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers
  | exact _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers
  | (apply _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers ..)


open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies Formalism.L2.Pj in
theorem denomBound : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    DenomBound θ V := by
  first
  | exact @_root_.GlobalTheory.AdeleDenominators.denomBound
  | exact _root_.GlobalTheory.AdeleDenominators.denomBound
  | (apply _root_.GlobalTheory.AdeleDenominators.denomBound <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdeleDenominators.denomBound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdeleDenominators.denomBound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdeleDenominators.denomBound ..)

end GlobalTheory.SmoothForms
