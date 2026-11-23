module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
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
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Approx


open GlobalTheory.Spread GlobalTheory.SpreadSep in
theorem exists_fg_isClosed_preimage_range (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V]
    [Algebra k V] (X P : Scheme.{0}) (j : X ⟶ P) (q : P ⟶ Sp k) (hj : IsImmersion j)
    (h₁ : LocallyOfFiniteType q) (h₂ : QuasiCompact q)
    (h : IsClosed (pullback.fst q (spMap (algebraMap k V)) ⁻¹' Set.range j)) :
    ∃ R : Subalgebra k V, R.FG ∧
      IsClosed (pullback.fst q (spMap (algebraMap k R)) ⁻¹' Set.range j) := by
  classical
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace ↥P := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian P := {}
  have : QuasiSeparated q := (quasiSeparated_iff_quasiSeparatedSpace q).mpr inferInstance
  obtain ⟨U, Z, hU, hZ, eΔ⟩ := j.isLocallyClosed_range
  let s : (Finset V)ᵒᵖ := .op ∅
  let π : (bcDiagram q V).obj s ⟶ P := pullback.fst q _
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst q _))
  let O : P.Opens := ⟨U, hU⟩
  let O' : P.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have key : ((π ⁻¹ᵁ O : Set _) \ (π ⁻¹ᵁ O' : Set _)) = π ⁻¹' Set.range j := by
    rw [eΔ]
    ext x
    change π x ∈ U ∧ ¬ π x ∉ Z ↔ π x ∈ U ∧ π x ∈ Z
    rw [not_not]
  obtain ⟨i, f, hi⟩ := exists_isClosed_preimage_diff (bcDiagram q V) (bcCone q V) (isLimitBcCone q V)
    (π ⁻¹ᵁ O) (π ⁻¹ᵁ O')
    (QuasiCompact.isCompact_preimage (f := π) _ O.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (QuasiCompact.isCompact_preimage (f := π) _ O'.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (by
      have e : (bcCone q V).π.app s ≫ π = pullback.fst q _ := bcMap_fst _ _
      rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e]
      exact h)
  refine ⟨Algebra.adjoin k (i.unop : Set V), Subalgebra.fg_adjoin_finset _, ?_⟩
  have e : (bcDiagram q V).map f ≫ π = pullback.fst q _ := bcMap_fst _ _
  rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e] at hi
  exact hi

end GlobalTheory.CompanionTheory.Ar.Approx
