module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Regular.RegularSequence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing

namespace GlobalTheory.CompanionTheory.KoszulCount

def germSec {X : Scheme.{0}} {L : LB X} (s : L.Sec) {i : L.ι} {x : X} (hx : x ∈ L.U i) :
    X.presheaf.stalk x :=
  X.presheaf.germ (L.U i) x hx (s.f i)

def CotIndep {X : Scheme.{0}} {L : LB X} {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    LinearIndependent (ResidueField (X.presheaf.stalk x))
      (fun j : {j : Fin d // germSec (t j) hx ∈ maximalIdeal (X.presheaf.stalk x)} =>
        ((maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
          CotangentSpace (X.presheaf.stalk x)))

def GoodStalks {X : Scheme.{0}} {L : LB X} (F : X.Modules) {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    RingTheory.Sequence.IsWeaklyRegular (F.presheaf.stalk x :)
        (List.ofFn fun j => germSec (t j) hx) ∧
      Module.length (X.presheaf.stalk x)
        ((F.presheaf.stalk x :) ⧸ (Ideal.span (Set.range fun j => germSec (t j) hx) •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)))) ≤ 1

end GlobalTheory.CompanionTheory.KoszulCount
