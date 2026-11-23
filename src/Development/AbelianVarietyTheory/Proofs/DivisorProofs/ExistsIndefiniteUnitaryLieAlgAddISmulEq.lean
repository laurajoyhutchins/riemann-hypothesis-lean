module

public import Formalism.LocalRingCardinality.DataTheta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem jm_conjTranspose (p q : ℕ) : (Formalism.BasicNotions.TH.Jm p q)ᴴ = Formalism.BasicNotions.TH.Jm p q := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp

theorem jm_mul_self (p q : ℕ) : Formalism.BasicNotions.TH.Jm p q * Formalism.BasicNotions.TH.Jm p q = 1 := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem upq_span (p q : ℕ) (Z : Mat p q) : ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  obtain ⟨J, hJ⟩ : ∃ J, J = Formalism.BasicNotions.TH.Jm p q := ⟨_, rfl⟩
  have hJh : Jᴴ = J := hJ ▸ jm_conjTranspose p q
  have hJJ : J * J = 1 := hJ ▸ jm_mul_self p q
  refine ⟨(1/2 : ℂ) • (Z - J * Zᴴ * J), ?_, (-(Complex.I / 2)) • (Z + J * Zᴴ * J), ?_, ?_⟩
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp [star_div₀]
    rw [this]
    module
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [star_div₀]; ring
    rw [this]
    module
  · rw [smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; ring
    rw [this]
    module

end GlobalTheory.HoweD
