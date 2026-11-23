module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out

namespace PositivityTheory.FormalThickening

def GEClosed : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (P : Over (Spec (CommRingCat.of R))), IsSeparated P.hom → LocallyOfFiniteType P.hom →
      QuasiCompact P.hom →
    ∀ (C : ℕ → Scheme.{0}) (i : ∀ e, C e ⟶ (thickObj R I e P).left) (β : ∀ e, C e ⟶ C (e + 1)),
      (∀ e, IsClosedImmersion (i e)) →
      (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P)) →
      IsProper (i 0 ≫ (thickObj R I 0 P).hom) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ P.left) (b : ∀ e, C e ⟶ C'),
      IsClosedImmersion j ∧ IsProper (j ≫ P.hom) ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst P.hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e

def GEClosedProj : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ N : ℕ,
    let P : Over (Spec (CommRingCat.of R)) :=
      Over.mk (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)
    ∀ (C : ℕ → Scheme.{0}) (i : ∀ e, C e ⟶ (thickObj R I e P).left) (β : ∀ e, C e ⟶ C (e + 1)),
      (∀ e, IsClosedImmersion (i e)) →
      (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ P.left) (b : ∀ e, C e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst P.hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e

def IsoOfThick : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X), IsProper X.hom → IsProper p.left →
      (∀ e, IsIso ((Over.pullback (thick R I e)).map p).left) → IsIso p

end PositivityTheory.FormalThickening
