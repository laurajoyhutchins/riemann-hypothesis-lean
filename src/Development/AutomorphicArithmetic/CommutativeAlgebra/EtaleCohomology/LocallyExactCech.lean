module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Et

abbrev PMod (R : Type) [CommRing R] : Type 2 := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

variable {R : Type} [CommRing R]

abbrev sec (M : PMod R) (U : Scheme.{0}) : Type 1 := M.obj (op U)

abbrev rs (M : PMod R) {V U : Scheme.{0}} (g : V ⟶ U) (x : sec M U) : sec M V := (M.map g.op).hom x

abbrev ap {M N : PMod R} (α : M ⟶ N) {U : Scheme.{0}} (x : sec M U) : sec N U := (α.app (op U)).hom x

def LocT (τ : GrothendieckTopology Scheme.{0}) (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ τ U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

def Inv (q : ℕ) (U : Scheme.{0}) : Prop := IsUnit (q : Γ(U, ⊤))

def Gen (τ : GrothendieckTopology Scheme.{0}) (q : ℕ) (M : PMod R) {U : Scheme.{0}} (g : sec M U) : Prop :=
  q • g = 0 ∧ (∀ (V : Scheme.{0}) (k : V ⟶ U) (c : ℕ), Nonempty V → c • rs M k g = 0 → q ∣ c) ∧
  ∀ (V : Scheme.{0}) (k : V ⟶ U) (y : sec M V), LocT τ V fun _ h => ∃ c : ℕ, rs M h y = c • rs M (h ≫ k) g

section Cech
variable {Y X : Scheme.{0}} (f : Y ⟶ X)




variable {f}

variable (f)


end Cech

end UpperTheory.Et

end
