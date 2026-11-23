module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PerfectRing
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.Pull2ChernClassEqZero
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
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem duality_of_surjAll (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange)
    (hS : SurjAll) : AbelianDeRham.Duality := by
  intro R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have iso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0 :=
    orth_of_surj hF hB hA hg (fun C _ _ A' _ φ h ↦ hS C A' g (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h)
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg))
      (LB.isLB_linComb hL _ _) (isCorrForm_lam hψ)
  exact ⟨iso, perfect_ring hF hH hB hA hg hL hψ iso⟩

end CrystallinePoints.Pd
