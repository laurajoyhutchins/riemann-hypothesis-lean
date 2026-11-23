module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Step

theorem shortExact_lvl_zero {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) :
    (ShortComplex.mk (incl (anti hS) 0) (grπ (anti hS) 0) (incl_grπ (anti hS) 0)).ShortExact := by
  have : Mono (incl (anti hS) 0) := by
    unfold incl
    infer_instance
  have : Epi (grπ (anti hS) 0) := by
    exact coequalizer.π_epi
  exact { exact := ShortComplex.exact_cokernel (incl (anti hS) 0) }

theorem lifts_zero : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ),
    Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (S 0 : X.Modules) H n) 1) → Lifts I H hS n 0 := by
  intro A _ _ I X _ H hH P S hS n hv y
  have hsurj : Function.Surjective
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) 0)).app ⊤) :=
    GlobalTheory.cohOn.app_surjective
      (GlobalTheory.Twist.shortExact_map (GlobalTheory.Twist.isLB_lbZPow hH n) (shortExact_lvl_zero hS)) ⊤ hv
  obtain ⟨c, hc⟩ := hsurj y
  refine ⟨c, hc, ?_⟩
  have htop : Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ 0) = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
  simp only [twPow, htop, Submodule.top_smul]
  trivial

end GlobalTheory.CompanionTheory.GE.Step
