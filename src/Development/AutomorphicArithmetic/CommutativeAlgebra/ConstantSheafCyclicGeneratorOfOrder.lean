module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ContinuousSectionsBijectiveAdditiveNatural
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleLocallyHoldsOfPointwiseCoverOrAffineLocal
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
import Mathlib.Tactic.Linter.Style
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

private theorem UpperTheory.continuousSection_nsmul (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T]
    [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (U : Scheme.{0})
    (a : C(U, T)) (c : ℕ) : cSec R T (c • a) = c • cSec R T a := by
  exact map_nsmul (AddMonoidHom.mk' (cSec R T (U := U)) (UpperTheory.continuousSections_bijective_additive_natural R T U).2.1) c a

private theorem UpperTheory.restriction_comp {R : Type} [CommRing R] (M : PMod R) {W' W V : Scheme.{0}}
    (l : W' ⟶ W) (h : W ⟶ V) (z : sec M V) : rs M (l ≫ h) z = rs M l (rs M h z) := by
  simp only [rs, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem UpperTheory.constantSheaf_cyclic_generator_of_order :
    ∀ (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [DiscreteTopology T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (q : ℕ) (t : T), q • t = 0 → (∀ c : ℕ, c • t = 0 → q ∣ c) → (∀ x : T, ∃ c : ℕ, x = c • t) → ∀ U : Scheme.{0}, Gen Scheme.etaleTopology q (cSh R T).obj (cSec R T (ContinuousMap.const U t)) := by
  intro R _ T _ _ _ _ _ _ q t hq hmin hgen U
  have hsm : ∀ (W : Scheme.{0}) (a : C(W, T)) (c : ℕ), cSec R T (c • a) = c • cSec R T a :=
    fun W a c => UpperTheory.continuousSection_nsmul R T W a c
  have h0 : ∀ W : Scheme.{0}, cSec R T (0 : C(W, T)) = 0 := fun W =>
    map_zero (AddMonoidHom.mk' (cSec R T (U := W)) (UpperTheory.continuousSections_bijective_additive_natural R T W).2.1)
  have hrs : ∀ (V : Scheme.{0}) (k : V ⟶ U),
      rs (cSh R T).obj k (cSec R T (ContinuousMap.const U t)) =
        cSec R T (ContinuousMap.const V t) := by
    intro V k
    rw [(UpperTheory.continuousSections_bijective_additive_natural R T U).2.2.1]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsm, show q • ContinuousMap.const U t = 0 by ext; simp [hq], h0]
  · intro V k c hV hc
    obtain ⟨v⟩ := hV
    rw [hrs, ← hsm, ← h0 V] at hc
    have he := (UpperTheory.continuousSections_bijective_additive_natural R T V).1.1 hc
    have hv : c • t = 0 := by simpa using congrArg (fun f : C(V, T) => f v) he
    exact hmin c hv
  · intro V k y
    obtain ⟨b, rfl⟩ := (UpperTheory.continuousSections_bijective_additive_natural R T V).1.2 y
    refine (UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local V _ ?_).1 ?_
    · rintro W W' g' k' ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [UpperTheory.restriction_comp _ k' g', hc, Category.assoc, UpperTheory.restriction_comp _ k' (g' ≫ k)]
      exact map_nsmul ((cSh R T).obj.map k'.op).hom c _
    · intro x
      obtain ⟨c, hc⟩ := hgen (b x)
      let O : V.Opens := ⟨b ⁻¹' {b x}, (isOpen_discrete _).preimage b.continuous⟩
      refine ⟨O, O.ι, inferInstance, ?_, c, ?_⟩
      · rw [Scheme.Opens.range_ι]
        show b x ∈ ({b x} : Set T)
        exact Set.mem_singleton _
      · rw [(UpperTheory.continuousSections_bijective_additive_natural R T V).2.2.1, hrs, ← hsm]
        congr 1
        ext w
        have hw : O.ι w ∈ (O : Set V) := Scheme.Opens.range_ι O ▸ Set.mem_range_self w
        have hw' : b (O.ι w) = b x := hw
        simp [hw', hc]
