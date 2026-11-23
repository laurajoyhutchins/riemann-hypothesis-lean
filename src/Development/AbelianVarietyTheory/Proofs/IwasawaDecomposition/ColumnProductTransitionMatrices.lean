module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylDualData

open Formalism.BasicNotions Formalism.L2.DIV

theorem fockQ_sum_zsmul {σ κ : Type} [Fintype κ] (c : κ → ℤ) (f : κ → MvPolynomial σ ℚ)
    (g : MvPolynomial σ ℚ) :
    Formalism.GradedWeylDivisibility.fockQ (∑ i, c i • f i) g = ∑ i, (c i : ℚ) * Formalism.GradedWeylDivisibility.fockQ (f i) g := by

  rw [← ps_fockL_rat, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℚ, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ps_fockL_rat, smul_eq_mul]
  simp

theorem dual_data : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N),
    (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∃ (ι : Type) (_ : Fintype ι) (b d : ι → MvPolynomial (Fin N × Fin N) ℤ)
      (B : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ι → ℤ)
      (Cm : ι → (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ),
      (∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = ∑ i, B J i • b i) ∧
      (∀ i, b i = ∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) ∧
      (∀ i, ∑ J, B J i • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = d i) ∧
      (∀ i, d i ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r)) := by
  classical
  intro N Y hY H
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  letI : Fintype (Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r)) :=
    (Formalism.GradedWeylDivisibility.sSIdxFinite N N _).fintype
  obtain ⟨b, d, hb, hd, hbd⟩ := GlobalTheory.StdDual.exists_dual_bases N (fun r : Fin N => Y.rowLen r) hanti
  have hN0 : Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
      (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) ≠ 0 :=
    ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have hcol : ∀ J, Formalism.GradedWeylDivisibility.intQ N N (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) =
      GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J := fun J => fk_map_bidet (Int.castRingHom ℚ) _ _ _
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.intQ N N) :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hspan : Submodule.span ℤ (Set.range b) =
      Submodule.span ℤ (Set.range (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY)) := by
    rw [hb, ← GlobalTheory.StdDual.dualWeyl_intQ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY,
      Submodule.map_span, ← Set.range_comp]
    congr 2
    funext J
    exact hcol J
  have hBex : ∀ J, ∃ c : Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r) → ℤ,
      ∑ i, c i • b i = GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J := fun J =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan ▸ Submodule.subset_span ⟨J, rfl⟩)
  choose B hB using hBex
  have hCex : ∀ i, ∃ c : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      ∑ J, c J • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose Cm hCm using hCex
  have hdW : ∀ k, d k ∈ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
    intro k
    rw [GlobalTheory.StdDual.weyl_intQ, ← hd]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hdD : ∀ k, d k ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) := by
    intro k
    have h := hdW k
    rw [GlobalTheory.StdDual.weylEqDualNabla N N le_rfl _ hanti] at h
    exact h.1
  have hkey : ∀ k, ∑ J, B J k • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = d k := by
    intro k
    have h := H (d k) (hdD k)
    have e : ∀ J, Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) (d k) =
        (B J k : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) := by
      intro J
      rw [← hB J, fockQ_sum_zsmul]
      simp only [hbd, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [e] at h
    apply smul_right_injective _ hN0
    simp only
    rw [← h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm]
  refine ⟨Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r), inferInstance,
    fun i => ∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J,
    fun k => ∑ J, B J k • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J, B, Cm, ?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · have hbZ : ∀ i, Formalism.GradedWeylDivisibility.intQ N N (∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) = b i := by
      intro i

      rw [map_sum, ← hCm i]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [map_zsmul, hcol]
    intro J
    apply hinj

    rw [hcol, map_sum, ← hB J]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hbZ]
  · intro k
    obtain ⟨w, hw, hwe⟩ := hdW k
    have : (∑ J, B J k • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) = w := by
      apply hinj

      rw [hwe, ← hkey k, map_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [map_zsmul, hcol]
    show (∑ J, B J k • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) ∈ _
    rw [this]
    exact hw

end GlobalTheory.WeylDualData
