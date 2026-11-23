module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.DictCup

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem mp_val_congr (x : Cn F 1) {c c' : Fin (1 + 1) ⥤ C} (hc : c = c') {T : C}
    (g : c.obj (Fin.last 1) ⟶ T) (g' : c'.obj (Fin.last 1) ⟶ T) (hg : HEq g g') :
    mp F g (x c) = mp F g' (x c') := by
  subst hc
  obtain rfl := eq_of_heq hg
  rfl

theorem blockDecomposition_mk₂_fact {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : (0 : Fin 3) ⟶ 1) :
    (ComposableArrows.mk₂ φ ψ).map h = φ := by
  rw [show h = homOfLE (by decide) from Subsingleton.elim _ _]
  rfl

theorem composableArrows_mk₂_map_one_two {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : (1 : Fin 3) ⟶ 2) :
    (ComposableArrows.mk₂ φ ψ).map h = ψ := by
  rw [show h = homOfLE (by decide) from Subsingleton.elim _ _]
  rfl

theorem front_chain {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (fr 1).monotone.functor ⋙ ComposableArrows.mk₂ φ ψ = ComposableArrows.mk₁ φ := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  show _ = 𝟙 _ ≫ φ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact blockDecomposition_mk₂_fact φ ψ (homOfLE (by decide))

theorem face_chain {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (dl (0 : Fin (1 + 1 + 1))).monotone.functor ⋙ ComposableArrows.mk₂ φ ψ = ComposableArrows.mk₁ ψ := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  show _ = 𝟙 _ ≫ ψ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact composableArrows_mk₂_map_one_two φ ψ (homOfLE (by decide))

theorem cup1_mk₂_eq_mp_mul (x x' : Cn F 1) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')
    (y : F.obj T') (y' : F.obj T'') (hy : x (ComposableArrows.mk₁ φ) = y)
    (hy' : x' (ComposableArrows.mk₁ ψ) = y') :
    cup1 F 1 x x' (ComposableArrows.mk₂ φ ψ) = mp F ψ y * y' := by
  have e₁ : pr F (fr 1) x (ComposableArrows.mk₂ φ ψ) = mp F ψ y := by
    rw [pr_apply, ← hy]
    refine mp_val_congr x (front_chain φ ψ) _ ψ (heq_of_eq (composableArrows_mk₂_map_one_two φ ψ _))
  have e₂ : pr F (dl 0) x' (ComposableArrows.mk₂ φ ψ) = y' := by
    rw [pr_apply, ← hy']
    refine (mp_val_congr x' (face_chain φ ψ) _ (𝟙 T'') (heq_of_eq ?_)).trans (mp_id F _ _)
    exact (ComposableArrows.mk₂ φ ψ).map_id _
  rw [cup1_apply]
  exact congrArg₂ (· * ·) e₁ e₂

end GlobalTheory.CompanionTheory.HopfC.DictCup

namespace GlobalTheory.CompanionTheory.HopfC

theorem dict_cup : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (u₁ : H1 F →ₗ[R] HH F 1) (u₂ : H2 F →ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁ → IsDegreeTwoComparison F u₂ → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → ∀ a b, u₂ (cup F a b) = Lc F 1 (u₁ a) (u₁ b) := by
  intro R _ C _ F u₁ u₂ h₁ h₂ hx a b
  obtain ⟨f, rfl⟩ := H1.mk_surjective F a
  obtain ⟨f', rfl⟩ := H1.mk_surjective F b
  obtain ⟨x, hf⟩ := hx f
  obtain ⟨x', hf'⟩ := hx f'
  rw [h₁ f x hf, h₁ f' x' hf', Lc_mk, cup_mk]
  refine h₂ (cupZ F f f') (cz F 1 x x') fun T T' T'' φ ψ ↦ ?_
  rw [cz_val, cupZ_apply]
  exact DictCup.cup1_mk₂_eq_mp_mul x.1 x'.1 φ ψ _ _ (hf T T' φ) (hf' T' T'' ψ)

end GlobalTheory.CompanionTheory.HopfC
