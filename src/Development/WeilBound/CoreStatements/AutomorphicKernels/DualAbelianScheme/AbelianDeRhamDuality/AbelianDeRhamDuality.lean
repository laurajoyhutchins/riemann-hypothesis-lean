module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
public import Development.WeilBound.CoreStatements.AbelianDeRhamStructure.AbelianDeRhamPages.AbelianDeRhamStructureOfPage
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CrystallineDeRham
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.AbelianDeRhamPage
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.AbelianHodgeDeRham
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PoincareDeRhamDualityOfCube
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

@[expose] public section

set_option autoImplicit false

namespace PositivityTheory.DualRT

open GlobalTheory.Published
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CrystallinePoints.Pd

theorem surjAll : CrystallinePoints.Pd.SurjAll := by
  intro R _ A _ g hAb hsm
  haveI := hAb
  haveI : IsProper A.hom := IsAbelianScheme.proper
  have hs : A.hom ≫ 𝟙 (Sp R) = A.hom := Category.comp_id _
  refine toPicard_surjective _ ?_ ?_
  · rw [hs]
    exact (GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne A.hom IsAbelianScheme.smooth inferInstance inferInstance).2
  · rw [hs]
    exact (MainStatements.Hodge.Free.abelianHodgeDeRham R A g hAb hsm).2.2.2.2.1.2.2

theorem duality : AbelianDeRham.Duality :=
  have hS := AbelianDeRhamStructureFromPages.Adrs.abelianDeRhamStructure_of_page MainStatements.Hodge.Free.abelianDeRhamPage
  CrystallinePoints.Pd.duality_of_surjAll (GlobalTheory.abelianDeRhamStructure_toFree hS) hS.2.1 hS.2.2 surjAll

theorem abelianDeRham : AbelianDeRham :=
  have hS := AbelianDeRhamStructureFromPages.Adrs.abelianDeRhamStructure_of_page MainStatements.Hodge.Free.abelianDeRhamPage
  have hF := GlobalTheory.abelianDeRhamStructure_toFree hS
  ⟨hF, hS.2.1, hS.2.2, AbelianDeRham.rigid_of_free_of_crystallineDeRham hF FubiniStudyChowHeightFormula₂.Adr.crystallineDeRham, duality⟩

end PositivityTheory.DualRT
