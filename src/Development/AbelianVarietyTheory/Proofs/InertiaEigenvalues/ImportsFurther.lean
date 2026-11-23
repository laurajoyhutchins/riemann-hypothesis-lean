module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory.ScalarMultipleMembership

theorem exists_smul_mem {Ks WL : Type} [Field Ks] [NumberField Ks] [AddCommGroup WL] [Module Ks WL]
    [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL]
    (M : Submodule (NumberField.RingOfIntegers Ks) WL) (x : WL)
    (hx : x ∈ Submodule.span Ks (M : Set WL)) :
    ∃ a : NumberField.RingOfIntegers Ks, a ≠ 0 ∧ a • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem b hay
    · rw [mul_smul]; exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, hc⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (NumberField.RingOfIntegers Ks) Ks d ≠ 0 := by
      intro h
      exact hd0 (IsFractionRing.injective (NumberField.RingOfIntegers Ks) Ks (by simpa using h))
    refine ⟨a * d, mul_ne_zero ha hd0, ?_⟩
    have key : (a * d) • c • y = n • a • y := by
      rw [← algebraMap_smul Ks (a * d), ← algebraMap_smul Ks n, ← algebraMap_smul Ks a,
        smul_smul, smul_smul, ← hc, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem n hay

theorem main {LL Ks WL G : Type} [inst : Field LL] [NumberField LL] [inst_2 : Field Ks] [inst_3 : NumberField Ks] [inst_4 : Algebra Ks LL] [inst_5 : AddCommGroup WL] [inst_6 : Module LL WL] [inst_7 : Module Ks WL] [IsScalarTower Ks LL WL] [inst_9 : Module (NumberField.RingOfIntegers Ks) WL] [inst_10 : IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {W : (LL →+* ℂ) → Type} [inst_11 : (σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [inst_12 : (σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [inst_13 : Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (h : Submodule.span Ks (↑(Formalism.IndefR.Arith.FormsL.MK Φ) : Set WL) = Formalism.IndefR.Arith.FormsL.WK Φ) :
    ∀ x ∈ Formalism.IndefR.Arith.FormsL.WK Φ, ∃ (a : NumberField.RingOfIntegers Ks), a ≠ (0 : NumberField.RingOfIntegers Ks) ∧ a • x ∈ Formalism.IndefR.Arith.FormsL.MK Φ := by
  intro x hx
  rw [← h] at hx
  exact exists_smul_mem _ x hx

end GlobalTheory.ScalarMultipleMembership
