module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.AbelianDeRhamPage
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.Bridge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR FubiniStudyChowHeightFormula₂.Hdr

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Free

theorem page_of_hodge (H : GlobalTheory.Published.AbelianHodgeDeRham) : AbelianDeRhamPage := by
  intro R _ A _ g hA hg
  obtain ⟨⟨a1, a2, a3⟩, hw, ⟨f1, f2, f3⟩, ⟨o1, o2, -⟩, ⟨hcl, hinj, hsurj⟩, hbc⟩ := H R A g hA hg
  let i := formEquiv A.hom hcl hinj
  have hk : Hodge1 A.hom = LinearMap.ker (toHO1 A.hom) := (cechHodgeFiltration_eq_range A.hom).symm
  let q : (HH1 A.hom ⧸ Hodge1 A.hom) ≃ₗ[R] HO1 A.hom :=
    (Submodule.quotEquivOfEq _ _ hk).trans ((toHO1 A.hom).quotKerEquivOfSurjective hsurj)
  refine ⟨hw, ⟨⟨a1, a2⟩, a3⟩, ⟨hcl, hinj, ⟨⟨Module.Finite.equiv i, Module.Projective.of_equiv i⟩,
      fun p ↦ by rw [← Module.rankAtStalk_eq_of_equiv i, f3]⟩,
      Module.Finite.equiv q.symm, Module.Projective.of_equiv q.symm⟩,
    ⟨by rw [hk]; exact LinearMap.exact_subtype_ker_map _, hsurj⟩, fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨b1, ⟨e, he⟩, b3⟩ := hbc R' X' s' φ h
  refine ⟨b1, ?_, b3⟩
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  obtain ⟨-, -, -, -, ⟨hcl', hinj', -⟩, -⟩ := H R' (Over.mk s') g hA' hg'
  let i' := formEquiv s' hcl' hinj'
  refine ⟨(LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i'), fun c ↦ ?_⟩
  obtain ⟨c, rfl⟩ := i.surjective c
  have k : ((LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i')) (1 ⊗ₜ i c) = i' (e (1 ⊗ₜ c)) := by
    simp
  rw [k]
  exact IsPullForm.cl (ω := ⟨c, hcl ▸ trivial⟩) (ω' := ⟨e (1 ⊗ₜ c), hcl' ▸ trivial⟩) (he c)

end MainStatements.Hodge.Free
