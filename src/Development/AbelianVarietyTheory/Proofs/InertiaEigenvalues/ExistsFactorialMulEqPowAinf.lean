module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_factorial_mul_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : ℤ_[l], ((n.factorial : ℕ) : ℤ_[l]) * c = ((l : ℕ) : ℤ_[l]) ^ n := by
  have hp : l.Prime := Fact.out
  obtain ⟨k, m, hm, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) l hp.ne_one
  have hk : k ≤ n := by
    have h1 : k ≤ padicValNat l n.factorial :=
      ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (Nat.factorial_ne_zero n)).1 ⟨m, h⟩
    have h2 : (l - 1) * padicValNat l n.factorial = n - (l.digits n).sum := by
      simpa only [Nat.padicValNat_def] using hp.sub_one_mul_multiplicity_factorial (n := n)
    have h3 : 1 ≤ l - 1 := by have := hp.two_le; omega
    have h4 : padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial :=
      Nat.le_mul_of_pos_left _ h3
    omega
  have hu : IsUnit ((m : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨u * (l : ℤ_[l]) ^ j, ?_⟩
  rw [h]
  push_cast
  linear_combination ((l : ℤ_[l]) ^ (k + j)) * hu

theorem exists_factorial_mul_eq_pow_ainf (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : Ainf l, ((n.factorial : ℕ) : Ainf l) * c = ((l : ℕ) : Ainf l) ^ n := by
  obtain ⟨c, hc⟩ := exists_factorial_mul_eq_pow l n
  refine ⟨algebraMap ℤ_[l] (Ainf l) c, ?_⟩
  simpa only [map_mul, map_pow, map_natCast] using congrArg (algebraMap ℤ_[l] (Ainf l)) hc

end GlobalTheory.Per
