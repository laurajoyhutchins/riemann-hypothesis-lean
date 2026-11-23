module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedMissingClosedFibreEmpty
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE.PSupp

def badSet {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) : Set X :=
  {x | ∀ V : X.affineOpens, secs S (V : X.Opens) = Set.univ → x ∉ (V : X.Opens)}

lemma badSet_compl_eq {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) :
    (badSet S)ᶜ = ⋃ V ∈ {V : X.affineOpens | secs S (V : X.Opens) = Set.univ}, ((V : X.Opens) : Set X) := by
  ext x
  simp only [badSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, exists_prop, Set.mem_iUnion]
  constructor
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hV, not_not.mp hx⟩
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hV, not_not.mpr hx⟩

lemma isClosed_badSet {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) : IsClosed (badSet S) := by
  rw [← isOpen_compl_iff, badSet_compl_eq]
  exact isOpen_biUnion fun V _ => (V : X.Opens).isOpen

theorem subset_of_closedFibre {A : Type} [CommRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens) (C : Set X)
    (hC : IsClosed C) (h : ∀ x ∈ C, I ≤ ((X ↘ Spec (.of A)).base x).asIdeal → x ∈ (O : Set X)) :
    C ⊆ O := by

  have hZ := GlobalTheory.CompanionTheory.ClosedFibre.closed_missing_closedFibre_empty A I hI
    (Over.mk (X ↘ Spec (.of A))) (inferInstanceAs (UniversallyClosed (X ↘ Spec (.of A))))
    (C ∩ (O : Set X)ᶜ) (hC.inter O.isOpen.isClosed_compl) (by
      rintro x ⟨hxC, hxO⟩ hIx
      exact hxO (h x hxC hIx))
  intro x hx
  by_contra hxO
  have hx' : x ∈ C ∩ (O : Set X)ᶜ := ⟨hx, hxO⟩
  rw [hZ] at hx'
  exact hx'

end GlobalTheory.CompanionTheory.GE.PSupp
