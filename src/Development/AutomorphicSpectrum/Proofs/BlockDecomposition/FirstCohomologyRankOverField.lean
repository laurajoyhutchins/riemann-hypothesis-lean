module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Mathlib.Algebra.Module.StablyFree.Basic
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open scoped CategoryTheory.Obj

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField

theorem vb_of_field (hFlat : FlatBCSt) (hLe : PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe) (hGe : H1DimGeAbelianDim) (k : Type) [Field k]
    (A : Over (Sp k)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hsm : SmoothOfRelativeDimension g A.hom) : VB k (HO1 A.hom) g := by
  let K := AlgebraicClosure k
  have hφ := isGrpPullback_pullback A (spMap (algebraMap k K))
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hφ
  have hsm' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap k K))).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hsm
  obtain ⟨hfin, hle⟩ := hLe k A g hab hsm
  obtain ⟨hfin', hle'⟩ := hLe K _ g hab' hsm'
  have hge := hGe K _ g hab' hsm' hfin'
  have := hab.proper
  obtain ⟨e, -⟩ := hFlat k K _ _ A.hom _ _ hφ.1 inferInstance inferInstance
  have hrank : Module.finrank k (HO1 A.hom) = g := by
    have h1 := e.finrank_eq
    rw [Module.finrank_baseChange] at h1
    omega
  refine ⟨hfin, inferInstance, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
  rfl

theorem first_cohomology_rank_over_field : FlatBCSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe → H1DimGeAbelianDim → H1StructureFieldDim := by
  intro hFlat hLe hGe R _ A _ g hab hsm hR
  letI := hR.toField
  exact vb_of_field hFlat hLe hGe R A g hab hsm

end GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField
