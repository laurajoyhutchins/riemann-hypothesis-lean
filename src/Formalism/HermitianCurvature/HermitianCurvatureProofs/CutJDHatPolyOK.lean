module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZinvBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

open scoped ContDiff

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jdh_ckOn_of_contDiff {k r : ℕ} {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {f : B.Mat k r → E'}
    (hf : ContDiff ℝ ∞ f) (UU : Set (B.Mat k r)) : B.CkOn ⊤ UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, trivial, hf.contDiffOn, fun _ _ _ => rfl⟩

theorem jdh_opOrder_le {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o : ℕ) (Θ : B.DiffOp k r Wp Wq)
    (h : ∀ Tm ∈ Θ, Tm.word.length ≤ o) : B.opOrder Θ ≤ o := by
  unfold B.opOrder
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h T (List.mem_cons_self ..)) (ih fun Tm hTm => h Tm (List.mem_cons_of_mem _ hTm))

theorem jdh_pd_star {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) :
    U.IsPolyDeg κ (fun g => star (P g)) := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · refine (MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)
    exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  · show star (P g) = _
    rw [he g, MvPolynomial.eval_rename, MvPolynomial.eval_map]
    show (starRingEnd ℂ) (MvPolynomial.eval₂ (RingHom.id ℂ) _ q) = _
    rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem polynomial_decay_admissible : JDPolyOK := by
  intro k r Wp Wq _ _ _ _ _ o κ Θ hΘ
  let Lm : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
  have hLm : ∀ c : ℂ, Lm c = c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun c => by
    simp [Lm]

  have key : ∀ Tm ∈ Θ, ∃ P : B.Mat k r → ℂ, U.IsPolyDeg κ P ∧ ContDiff ℝ ∞ P ∧
      Tm.coef = (fun g => Lm (P g)) ∧ Tm.coefAdj = (fun g => Lm (star (P g))) := by
    intro Tm hTm
    obtain ⟨-, P, hP, hc, ha⟩ := hΘ Tm hTm
    exact ⟨P, hP, (poly_adm (n := 0) hP).1, funext fun g => by rw [hc g, hLm],
      funext fun g => by rw [ha g, hLm]⟩
  have smooth : ∀ Tm ∈ Θ, ContDiff ℝ ∞ Tm.coef ∧ ContDiff ℝ ∞ Tm.coefAdj := by
    intro Tm hTm
    obtain ⟨P, -, hc, e1, e2⟩ := key Tm hTm
    refine ⟨?_, ?_⟩
    · rw [e1]; exact (Lm.restrictScalars ℝ).contDiff.comp hc
    · rw [e2]
      have hs : ContDiff ℝ ∞ (fun g => star (P g)) := by
        have := (Complex.conjCLE.contDiff (n := ∞)).comp hc
        simpa [Function.comp_def, Complex.conjCLE_apply] using this
      exact (Lm.restrictScalars ℝ).contDiff.comp hs
  refine ⟨fun UU Tm hTm => ⟨jdh_ckOn_of_contDiff (smooth Tm hTm).1 UU, jdh_ckOn_of_contDiff (smooth Tm hTm).2 UU⟩,
    fun d hd Tm hTm => ⟨jdh_ckOn_of_contDiff (smooth Tm hTm).1 _, jdh_ckOn_of_contDiff (smooth Tm hTm).2 _,
      fun m => ?_⟩, jdh_opOrder_le o Θ fun Tm hTm => (hΘ Tm hTm).1⟩
  obtain ⟨P, hP, -, e1, e2⟩ := key Tm hTm
  obtain ⟨⟨C, hC0, hUB⟩, -⟩ :=
    ubl_clm (Lm.restrictScalars ℝ) (subset_refl (GV k r)) (ubl_poly hP (GV k r) (subset_refl _) m 0)
  obtain ⟨⟨C', hC0', hUB'⟩, -⟩ :=
    ubl_clm (Lm.restrictScalars ℝ) (subset_refl (GV k r)) (ubl_poly (jdh_pd_star hP) (GV k r) (subset_refl _) m 0)
  refine ⟨max C C', fun u w hu hw hl g hg => ?_⟩
  have hg1 : 1 ≤ gN g := gN_ge_one hg
  have hpow : gN g ^ κ ≤ gN g ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hd0 : 0 ≤ gN g ^ d := Real.rpow_nonneg (by linarith) _
  constructor
  · rw [e1, dLR_eq]
    have hb := hUB (wL u ++ wR w) ⟨u, w, hu, hw, hl, rfl⟩ g hg
    simp only [zero_mul, add_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd0))
  · rw [e2, dLR_eq]
    have hb := hUB' (wL u ++ wR w) ⟨u, w, hu, hw, hl, rfl⟩ g hg
    simp only [zero_mul, add_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC0').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd0))

end

end Formalism.FourierDecayAlt.P.CutMP
