module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem stalk_isRegularLocalRing_and_ringKrullDim_le :
    ∀ (Y : Var ℂ) (x : Y.X), IsRegularLocalRing (Y.X.presheaf.stalk x) ∧
      ringKrullDim (Y.X.presheaf.stalk x) ≤ Y.dim := by
  intro Y x
  have hsm : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim Y.str
  haveI hAr : IsRegularRing (Y.X.presheaf.stalk x) :=
    ExtendRig.isRegularRing_stalk isRegularRing_of_smooth ℂ Y.str x
  refine ⟨IsRegularLocalRing.of_isRegularRing_of_isLocalRing _, ?_⟩
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens (Opens.mem_top x)
  have hdim : ringKrullDim Γ(Y.X, U) = Y.dim :=
    SmoothDim.ringKrullDim_affineOpen ℂ _ Y.str _ inferInstance U hU ⟨x, hx⟩
  letI : Algebra Γ(Y.X, U) (Y.X.presheaf.stalk x) := (Y.X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← hdim, IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (Y.X.presheaf.stalk x)]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

end GlobalTheory.CompanionTheory.KoszulCount
