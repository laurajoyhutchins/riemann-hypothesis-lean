module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.UV

theorem subsingleton_cokernel_desc_of_span {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ι → X.Modules} {G : X.Modules} [∀ i, (F i).IsQuasicoherent] [G.IsQuasicoherent]
    [(biproduct F).IsQuasicoherent] (φ : ∀ i, F i ⟶ G) {V : X.Opens} (hV : IsAffineOpen V)
    (h : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) = ⊤) :
    Subsingleton Γ(cokernel (biproduct.desc φ), V) := by
  refine subsingleton_of_forall_eq 0 fun s => ?_
  obtain ⟨t, rfl⟩ := GroundTheory.Arith.SchemeCoh.surjective_cokernel_π_app (biproduct.desc φ) hV s
  have hle : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) ≤
      LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V) := by
    refine Submodule.span_le.2 ?_
    intro y hy
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hy
    have hz : φ i ≫ cokernel.π (biproduct.desc φ) = 0 := by
      rw [← biproduct.ι_desc φ i, Category.assoc, cokernel.condition, comp_zero]
    change (cokernel.π (biproduct.desc φ)).app V ((φ i).app V x) = 0
    rw [GlobalTheory.QCoh.app_app, hz]
    rfl
  have ht : t ∈ LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V) :=
    hle (h ▸ Submodule.mem_top)
  exact ht

theorem span_range_app_eq_top_of_surjective {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ι → X.Modules} {G : X.Modules} (φ : ∀ i, F i ⟶ G) (U : X.Opens)
    (h : Function.Surjective ((biproduct.desc φ).app U)) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  refine (Submodule.eq_top_iff').2 fun s => ?_
  obtain ⟨t, rfl⟩ := h s

  rw [GroundTheory.Arith.SchemeCoh.biproduct_app_eq_sum F U t, map_sum]
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨j, ?_⟩)
  refine ⟨(biproduct.π F j).app U t, ?_⟩
  rw [GlobalTheory.QCoh.app_app (biproduct.ι F j), biproduct.ι_desc]

theorem span_range_app_eq_top_of_local : ∀ {X : AlgebraicGeometry.Scheme.{0}} {ι : Type} [Finite ι]
    {F : ι → X.Modules} {G : X.Modules}, (∀ i, (F i).IsQuasicoherent) → G.IsQuasicoherent →
    ∀ (φ : ∀ i, F i ⟶ G), (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤) →
    ∀ (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  intro X ι _ F G hF hG φ hloc U
  classical
  haveI := Fintype.ofFinite ι
  haveI := hF
  haveI := hG
  haveI : (biproduct F).IsQuasicoherent := GroundTheory.Arith.SchemeCoh.isQuasicoherent_biproduct F
  choose W hxW hW using hloc
  have hcov : TopologicalSpace.IsOpenCover (fun x : X => (W x : X.Opens)) := by
    refine eq_top_iff.2 fun x _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  have hzero : IsZero (cokernel (biproduct.desc φ)) :=
    (GlobalTheory.QCoh.isZero_iff_affineCover (fun x : X => (W x : X.Opens)) hcov (fun x => (W x).2)).2
      fun x => subsingleton_cokernel_desc_of_span φ (W x).2 (hW x)
  haveI : Epi (biproduct.desc φ) := Preadditive.epi_of_isZero_cokernel _ hzero
  exact span_range_app_eq_top_of_surjective φ U
    (GlobalTheory.QCoh.surjective_app_of_epi (biproduct.desc φ) U.2)

end GlobalTheory.CompanionTheory.GE.UV
