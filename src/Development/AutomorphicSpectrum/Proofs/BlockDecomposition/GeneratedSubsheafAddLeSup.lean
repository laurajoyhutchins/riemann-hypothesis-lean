module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalLimit

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem imageSubobject_add_le {C : Type*} [Category C] [Preadditive C] [HasImages C]
    [HasBinaryCoproducts C] {A B : C} (f g : A ⟶ B) :
    imageSubobject (f + g) ≤ imageSubobject f ⊔ imageSubobject g := by
  have key : ∀ h : A ⟶ B, (imageSubobject h).Factors h := fun h => by
    have := Subobject.factors_comp_arrow (P := imageSubobject h) (factorThruImageSubobject h)
    rwa [imageSubobject_arrow_comp] at this
  have h := Subobject.factors_add f g
    (Subobject.factors_of_le f le_sup_left (key f)) (Subobject.factors_of_le g le_sup_right (key g))
  exact imageSubobject_le (f + g) _ (Subobject.factorThru_arrow _ _ h)

theorem sectionHom_add {X : Scheme.{0}} {F : X.Modules} (b c : Γ(F, ⊤)) :
    GlobalTheory.QCoh.sectionHom (b + c) = GlobalTheory.QCoh.sectionHom b + GlobalTheory.QCoh.sectionHom c := by
  ext V a
  change GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) (b + c) =
    GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) b +
      GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) c
  rw [map_add (f := _), smul_add]

theorem genHom_add {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    genHom hH n (b + c) = genHom hH n b + genHom hH n c := by
  have h : GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom (b + c)) =
      GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b) +
        GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom c) := by
    rw [sectionHom_add]
    exact (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))).map_add
  simp only [genHom, h, Preadditive.add_comp]

theorem genSub_add_le {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    genSub hH n (b + c) ≤ genSub hH n b ⊔ genSub hH n c := by
  unfold genSub
  simp only [genHom_add]
  exact imageSubobject_add_le _ _

end GlobalTheory.CompanionTheory.GE.TwGen
