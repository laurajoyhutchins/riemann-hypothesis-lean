module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private noncomputable abbrev sι {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) :
    Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))

private lemma sι_eq {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) :
    sι C i = Sigma.ι (fun i => Spec (CommRingCat.of (C i))) i ≫ sigmaSpec (fun i => CommRingCat.of (C i)) :=
  (ι_sigmaSpec (fun i => CommRingCat.of (C i)) i).symm

private theorem bijective_sheaf_sigma_restrict {P : Scheme.{0}ᵒᵖ ⥤ Type 1}
    (hP : Presieve.IsSheaf Scheme.zariskiTopology P) {n : ℕ} (X : Fin n → Scheme.{0}) :
    Function.Bijective (fun (s : P.obj (op (∐ X))) (i : Fin n) => P.map (Sigma.ι X i).op s) := by
  have hcov := hP.isSheafFor _ (sigmaOpenCover X).mem_grothendieckTopology
  rw [Presieve.isSheafFor_arrows_iff] at hcov
  have hcomp : ∀ x : ∀ i, P.obj (op (X i)), Presieve.Arrows.Compatible P (Sigma.ι X) x := by
    intro x i j Z gi gj h
    by_cases hij : i = j
    · subst hij
      rw [cancel_mono] at h
      rw [h]
    · haveI := isEmpty_of_commSq_sigmaι_of_ne ⟨h⟩ hij
      exact (hP (⊥ : Sieve Z) (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext
        (fun _ _ hf => hf.elim)
  constructor
  · intro s t hst
    exact (hcov (fun i => P.map (Sigma.ι X i).op s) (hcomp _)).unique (fun i => rfl)
      (fun i => (congr_fun hst i).symm)
  · intro y
    obtain ⟨t, ht, -⟩ := hcov y (hcomp y)
    exact ⟨t, funext ht⟩

theorem UpperTheory.sections_specPi_bijective_prod_sections :
    ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℕ) (C : Fin n → Type) [∀ i, CommRing (C i)],
        Function.Bijective (fun (s : Sec F (Spec (CommRingCat.of (∀ i, C i)))) (i : Fin n) =>
          (Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))) s : Sec F (Spec (CommRingCat.of (C i))))) := by
  intro R _ F n C _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology
      (F.obj ⋙ CategoryTheory.forget (ModuleCat (ULift.{1, 0} R))) := by
    apply Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_etaleTopology
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)).mp F.property
  have key := bijective_sheaf_sigma_restrict hG (fun i => Spec (CommRingCat.of (C i)))
  have hiso : Function.Bijective ((F.obj ⋙ CategoryTheory.forget _).map
      (sigmaSpec (fun i => CommRingCat.of (C i))).op) :=
    (isIso_iff_bijective _).mp inferInstance
  convert key.comp hiso using 1
  funext s i
  rw [show Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) = _ from sι_eq C i]
  simp only [Sec.res, Function.comp_apply, op_comp, Functor.map_comp]
  rfl
