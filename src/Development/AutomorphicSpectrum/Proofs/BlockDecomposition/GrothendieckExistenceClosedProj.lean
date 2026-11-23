module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealFiltrationSaturatedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickeningStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousLiftAdicFiltrationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVanishingIdealSystemStatement
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.GE

theorem geClosedProj : GEClosedProj := by
  intro R _ _ I hI N P Cs i β hi hβ
  obtain ⟨hbase, hsat, hanti, hcompat⟩ := GlobalTheory.T.thickening_vanishing_ideal_system R I N Cs i β hi hβ
  obtain ⟨n₀, hlift⟩ := GlobalTheory.T.homogeneous_ideal_filtration_saturated R I N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hsat hcompat
  obtain ⟨J, hJ, h⟩ := GlobalTheory.T.homogeneous_lift_adic_filtration R I hI N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hanti n₀ hlift
  exact GlobalTheory.T.homogeneous_ideal_le_thickening R I N Cs i β hi hβ J hJ (fun e => (h e).1) (fun e => (h e).2)

end GlobalTheory.CompanionTheory.GE
