module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem pullLE_oneOn_eq_congr {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y}
    (v : LB.Iso N (N'.pull β)) (hL : (pw N 0).IsLB) (hM : ((pw N' 0).pull β).IsLB)
    (hw : (pullPow v 0).IsGen) (V : Y.Opens) (V' : X.Opens) (e : V' ≤ β ⁻¹ᵁ V) :
    SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V) =
      SecOn.congr hL hM (pullPow v 0) hw V' (oneOn N rfl V') := by
  refine GlobalTheory.LB.sec_ext_of_cover hL.cover fun p q => ?_
  have h := SecOn.coord_congr hL hM (pullPow v 0) hw (oneOn N rfl V') p q
    (O := V' ⊓ ((pw N' 0).pull β).U p ⊓ (pw N 0).U q) inf_le_left
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right)
  have c1 : GlobalTheory.LB.coord (SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V)) p = 1 := by
    rw [SecOn.coord_pullLE]
    exact map_one _
  have c2 : GlobalTheory.LB.coord (oneOn N (rfl : (0 : ℤ) = 0) V') q = 1 := rfl
  have c3 : (show Γ(X, ((pw N' 0).pull β).U p ⊓ (pw N 0).U q)ˣ from (pullPow v 0).s (p, q)) = 1 :=
    zpow_zero _
  rw [c2, c3] at h
  rw [c1]
  refine Eq.trans ?_ h.symm
  simp

theorem red_oneOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (h : a = 0) (e : ℕ) (S : Finset ι), red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ (oneOn (N (e + 1)) h (D (e + 1) S))) = SecOnR.of _ _ _ (oneOn (N e) h (D e S)) := by
  intro R _ I Y β hβ N v hN ι D hDβ a h e S
  subst h
  simp only [red, redL, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq, SecOnR.pull_of, SecOnR.linEquiv_of]
  exact congrArg (SecOnR.of _ _ _) (pullLE_oneOn_eq_congr (v e) _ _ _ _ _ _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
