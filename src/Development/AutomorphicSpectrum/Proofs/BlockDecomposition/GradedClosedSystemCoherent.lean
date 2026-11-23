module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreAffine
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

lemma isCoherent_lvl {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules} (hP : IsCoherent P)
    {S : ℕ → Subobject P} (hS : ClosedSys I P S) (e : ℕ) :
    IsCoherent (lvl S e : X.Modules) := by
  cases e with
  | zero =>
    have : IsIso (lvl S 0).arrow := by
      exact (Subobject.isIso_arrow_iff_eq_top _).2 rfl
    exact IsCoherent.of_iso (asIso (lvl S 0).arrow).symm hP
  | succ e => exact GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)

theorem isCoherent_gr : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules}, IsCoherent P →
    ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) (e : ℕ), IsCoherent (gr (anti hS) e) := by
  intro A _ _ I X _ _ P hP S hS e
  have := (isCoherent_lvl hP hS (e + 1)).1
  exact isCoherent_cokernel (incl (anti hS) e) (isCoherent_lvl hP hS e)

end GlobalTheory.CompanionTheory.GE.Step
