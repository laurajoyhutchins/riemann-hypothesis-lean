module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DimZero

theorem isIso_hom_of_relDim_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension 0 A.hom) : IsIso A.hom := by
  haveI := h.proper
  haveI := h.geomConnected
  haveI : Etale A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hd
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  haveI : IsClosedImmersion e := by
    haveI : IsClosedImmersion (e ≫ A.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.hom
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr le_rfl
  haveI : IsOpenImmersion e :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) e A.hom
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal A.hom))) (by rw [he]; infer_instance)
  have hs : ∀ y : S, A.hom (e y) = y := fun y => by rw [← Scheme.Hom.comp_apply, he]; rfl
  haveI : IsIso e := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (top_unique fun a _ => ?_)
    have hc := (A.hom.isConnected_preimage_singleton (A.hom a)).isPreconnected
    have hcl : IsClopen (Set.range e) :=
      ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
    exact hc.subset_isClopen hcl ⟨e (A.hom a), hs _, _, rfl⟩ rfl
  haveI : IsIso (e ≫ A.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e _

theorem over_hom_eq_of_mono {S : Scheme.{0}} {T A : Over S} [Mono A.hom] (x y : T ⟶ A) : x = y := by
  ext1
  rw [← cancel_mono A.hom, Over.w x, Over.w y]

theorem eq_one_of_g_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (hg : P.g = 0) (z : sp (R₀ := R) R ⟶ P.A) :
    z = 1 := by
  have hd : SmoothOfRelativeDimension 0 P.A.hom := hg ▸ P.smoothDim
  haveI := isIso_hom_of_relDim_zero P.A P.isAb hd
  exact over_hom_eq_of_mono _ _

end GlobalTheory.CompanionTheory.Ar.DimZero
