module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation Topology Filter

variable {l : ℕ} [hl : Fact l.Prime]

theorem zetaQ_pow (P : LocPrime l) (j k : ℕ) : P.ζQ (j + k) ^ (l ^ k) = P.ζQ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]

theorem chiQ_norm (P : LocPrime l) (h : GQ l) : ‖(P.χQ h : ℚ_[l])‖ = 1 := by
  have hroot : P.ζQ 1 ^ l = 1 := by
    have h0 := zetaQ_pow P 0 1
    rwa [zero_add, P.ζQ_zero, pow_one] at h0
  have hle : ∀ g : GQ l, ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
    intro g
    obtain ⟨a, ha, -⟩ := P.χQ_cyc g 1 (P.ζQ 1) (by rwa [pow_one])
    have hA : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have h2 : ‖((a : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
        first
          | exact (Padic.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
          | exact (padicNormE.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
      simpa using h2
    have hl1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) ≤ 1 := by
      have h3 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
      simp only [Nat.cast_one, zpow_neg, zpow_one]
      first
        | exact inv_le_one_of_one_le₀ h3
        | exact inv_le_one h3
    calc ‖(P.χQ g : ℚ_[l])‖ = ‖((P.χQ g : ℚ_[l]) - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖(P.χQ g : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := by
        first
          | exact Padic.nonarchimedean _ _
          | exact padicNormE.nonarchimedean _ _
          | exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (ha.trans hl1) hA
  have h1 := hle h
  have h2 := hle h⁻¹
  have hmul : ‖(P.χQ h : ℚ_[l])‖ * ‖(P.χQ h⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]
    simp
  exact le_antisymm h1 (by nlinarith [norm_nonneg (P.χQ h : ℚ_[l]), norm_nonneg (P.χQ h⁻¹ : ℚ_[l])])

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
