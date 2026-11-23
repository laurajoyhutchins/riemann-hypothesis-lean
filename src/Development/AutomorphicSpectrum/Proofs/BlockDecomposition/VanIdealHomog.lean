module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE

abbrev PO (R : Type) [CommRing R] (N : ℕ) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)

abbrev thickι (R : Type) [CommRing R] (I : Ideal R) (N e : ℕ) :
    (thickObj R I e (PO R N)).left ⟶ PSpace R N :=
  pullback.fst (PO R N).hom (thick R I e)

variable {R : Type} [CommRing R] {N : ℕ}

def HomogIdeal {B : Type} [CommRing B] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) B)) : Prop :=
  ∀ (d : ℕ) (f : MvPolynomial (Fin n) B), f ∈ P → homogeneousComponent d f ∈ P

def KillsForm {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R)
    (hf : f.IsHomogeneous n) : Prop :=
  ∀ k, (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
    (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0

def vanIdeal {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) : Ideal (MvPolynomial (Fin (N + 1)) R) :=
  Ideal.span {f | ∃ n, ∃ hf : f.IsHomogeneous n, KillsForm φ n f hf}


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem vanIdeal_homog {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) : HomogIdeal (vanIdeal φ) := by
  intro d f hf
  have hI : (vanIdeal φ).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) R) := by
    apply Ideal.homogeneous_span
    rintro x ⟨n, hx, -⟩
    exact ⟨n, (mem_homogeneousSubmodule n x).mpr hx⟩
  exact homogeneousComponent_mem_of_mem hI hf d

end GlobalTheory.CompanionTheory.GE
