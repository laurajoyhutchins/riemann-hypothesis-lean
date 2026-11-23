module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.SectionNbhd

theorem isAffine_subscheme_ker_sq :
    ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U)
      [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by
  intro R _ U t e _ het
  have hte : ∀ q : Sp R, t (e q) = q := fun q => by
    have := congr($(het) q)
    simpa using this
  set c := (e.ker ^ 2).subschemeι with hc
  have hrange : ∀ x, ∃ q : Sp R, c x = e q := by
    intro x
    have h1 : c x ∈ Set.range c := ⟨x, rfl⟩
    rw [hc, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_pow _ _ two_ne_zero, Scheme.Hom.support_ker,
      e.isClosedEmbedding.isClosed_range.closure_eq] at h1
    obtain ⟨q, hq⟩ := h1
    exact ⟨q, hq.symm⟩
  have haff : IsAffineHom (c ≫ t) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := e y) (U := ⊤) trivial
    obtain ⟨f, hfle, hyf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le
      (V := e ⁻¹ᵁ V₀) ⟨y, hyV₀⟩ trivial
    refine ⟨(Sp R).basicOpen f, hyf, (isAffineOpen_top (Sp R)).basicOpen f, ?_⟩
    have hV : IsAffineOpen (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      rw [Scheme.preimage_basicOpen]
      have h := Scheme.basicOpen_res U (V := V₀) (t.app ⊤ f) (homOfLE le_top).op
      rw [← h]
      exact hV₀.basicOpen _
    have heq : (c ≫ t) ⁻¹ᵁ (Sp R).basicOpen f = c ⁻¹ᵁ (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      ext x
      constructor
      · intro hx
        have hx' : t (c x) ∈ (Sp R).basicOpen f := hx
        refine ⟨?_, hx'⟩
        obtain ⟨q, hq⟩ := hrange x
        rw [hq, hte] at hx'
        have : e q ∈ V₀ := hfle hx'
        simpa [hq] using this
      · intro hx
        exact hx.2
    rw [heq]
    exact hV.preimage c
  exact isAffine_of_isAffineHom (c ≫ t)

end GlobalTheory.CompanionTheory.SectionNbhd
