module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem step_of_lifts {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB) {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ) (e : ℕ) (hL : Lifts I H hS n (e + 1)) :
    ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  rintro x ⟨c0, rfl⟩
  have hLB : (GlobalTheory.lbZPow H n).IsLB := GlobalTheory.Twist.isLB_lbZPow hH n
  let S0 : ShortComplex X.Modules :=
    ShortComplex.mk (incl (anti hS) (e + 1)) (grπ (anti hS) (e + 1)) (incl_grπ (anti hS) (e + 1))
  have hex0 : S0.Exact := S0.exact_of_g_is_cokernel (cokernelIsCokernel _)
  have hex1 : (S0.map (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n))).Exact :=
    (GlobalTheory.Twist.exact_map_iff hLB S0).mpr hex0
  have hmono0 : Mono (incl (anti hS) (e + 1)) := mono_of_mono_fac (incl_arrow (anti hS) (e + 1))
  have hmono1 : Mono (S0.map (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n))).f :=
    (GlobalTheory.Twist.mono_map_iff hLB (incl (anti hS) (e + 1))).mpr hmono0
  have hexΓ := GlobalTheory.QCoh.exact_app_of_exact_of_mono hex1 ⊤
  let c1 : Γ(GlobalTheory.twistZ (lvl S (e + 1) : X.Modules) H n, ⊤) := c0
  obtain ⟨c, hc1, hc2⟩ := hL ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) (e + 1))).app ⊤ c1)
  have hker : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) (e + 1))).app ⊤ (c1 - c) = 0 := by
    rw [map_sub, hc1, sub_self]
  obtain ⟨d, hd⟩ := (hexΓ (c1 - c)).mp hker
  let d1 : Γ(GlobalTheory.twistZ (S (e + 1) : X.Modules) H n, ⊤) := d
  have hd' : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (incl (anti hS) (e + 1))).app ⊤ d1 = c1 - c := hd
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1, ⟨d1, rfl⟩, ?_⟩
  have harr0 : incl (anti hS) (e + 1) ≫ (S e).arrow = (S (e + 1)).arrow :=
    incl_arrow (anti hS) (e + 1)
  have harr : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1 =
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ (c1 - c) :=
    (congrArg (fun φ => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) φ).app ⊤ d1) harr0.symm).trans
      ((congrArg (fun f => f.app ⊤ d1)
          (GlobalTheory.Twist.map_comp (GlobalTheory.lbZPow H n) (incl (anti hS) (e + 1)) (S e).arrow)).trans
        ((GlobalTheory.QCoh.app_app _ _ ⊤ d1).symm.trans
          (congrArg (fun s => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ s) hd')))
  have hfin : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1 =
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c := by
    calc _ = (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
          (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ (c1 - c) := by rw [harr]
      _ = (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
          ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c1 -
            (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c) :=
          congrArg (fun t => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 - t)
            (map_sub (ConcreteCategory.hom ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤)) c1 c)
      _ = _ := sub_sub_cancel _ _
  rw [hfin]
  exact hc2

end GlobalTheory.CompanionTheory.GE.Step
