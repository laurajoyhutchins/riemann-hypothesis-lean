module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
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
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem lbIso_pull_quot_of_consecutive_pw : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  intro X Y b A C N n hA hC hN h1 h2
  have hAb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hA b
  have hCb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hC b
  have hT := GlobalTheory.AbLaw.isLB_tw hC hA (-1)
  have hTb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hT b
  rw [← GlobalTheory.CechPic.cls_eq_iff hN hTb, GlobalTheory.CechPic.cls_pull hT b hTb]
  have e1 := (GlobalTheory.CechPic.cls_eq_iff hAb (GlobalTheory.AbLaw.isLB_pw hN n)).2 h1
  have e2 := (GlobalTheory.CechPic.cls_eq_iff hCb (GlobalTheory.AbLaw.isLB_pw hN (n + 1))).2 h2
  rw [GlobalTheory.CechPic.cls_pull hA b hAb, GlobalTheory.EffBound.cls_pw hN n] at e1
  rw [GlobalTheory.CechPic.cls_pull hC b hCb, GlobalTheory.EffBound.cls_pw hN (n + 1)] at e2
  have hT' : GlobalTheory.CechPic.cls (GlobalTheory.AbLaw.tw C A (-1)) hT
      = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
    show GlobalTheory.CechPic.cls (C.div (GlobalTheory.AbLaw.pw A (-(-1)))) hT = _
    rw [GlobalTheory.CechPic.cls_div hC (GlobalTheory.AbLaw.isLB_pw hA _) hT, GlobalTheory.EffBound.cls_pw hA]
    simp
  rw [hT', map_sub, e1, e2, add_smul, one_smul, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.FormalAlg
