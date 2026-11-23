module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoOfIsClosedImmersionOfThickenings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.FormalUniq

theorem eq_of_comp_thickenings_eq :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
    ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  intro R _ _ I hI X Z hX hZ Y b hpb g g' hb
  have hw : g.left ≫ Z.hom = g'.left ≫ Z.hom := by rw [Over.w g, Over.w g']
  obtain ⟨L, hL1, hL2⟩ : ∃ L : X.left ⟶ pullback Z.hom Z.hom,
      L ≫ pullback.fst _ _ = g.left ∧ L ≫ pullback.snd _ _ = g'.left :=
    ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hfac : ∀ e : ℕ, ∃ h, h ≫ pullback.snd (pullback.diagonal Z.hom) L =
      pullback.fst X.hom (thick R I e) := by
    intro e
    have hfe : pullback.fst X.hom (thick R I e) ≫ g.left =
        pullback.fst X.hom (thick R I e) ≫ g'.left := by
      rw [← (hpb e).isoPullback_inv_fst, Category.assoc, Category.assoc, hb e]
    refine ⟨pullback.lift (pullback.fst X.hom (thick R I e) ≫ g.left)
      (pullback.fst X.hom (thick R I e)) ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, hL1]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, hL2, hfe]
  haveI : IsIso (pullback.snd (pullback.diagonal Z.hom) L) :=
    GlobalTheory.CompanionTheory.FormalClosed.isIso_of_isClosedImmersion_of_thickenings R I hI X hX _ _ inferInstance hfac
  have hc := pullback.condition (f := pullback.diagonal Z.hom) (g := L)
  have e1 := congrArg (· ≫ pullback.fst Z.hom Z.hom) hc
  have e2 := congrArg (· ≫ pullback.snd Z.hom Z.hom) hc
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    hL1, hL2] at e1 e2
  exact Over.OverMorphism.ext
    ((cancel_epi (pullback.snd (pullback.diagonal Z.hom) L)).mp (e1.symm.trans e2))

end GlobalTheory.CompanionTheory.FormalUniq
