module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem hom_eq_zero_of_affineOpens {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.affineOpens) (s : Γ(M, (U : X.Opens))), φ.app (U : X.Opens) s = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  rw [Scheme.Modules.Hom.zero_app]
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  have key : ∀ s : Γ(M, U), φ.app U s = 0 := by
    intro s
    refine TopCat.Sheaf.eq_of_locally_eq' F
      (fun i : {V : X.affineOpens // (V : X.Opens) ≤ U} => (i.1 : X.Opens)) U
      (fun i => homOfLE i.2) ?_ _ _ ?_
    · refine fun x (hx : x ∈ U) => ?_
      obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    · intro i
      have hnat := ConcreteCategory.congr_hom
        ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE i.2).op) s
      simp only [ConcreteCategory.comp_apply] at hnat
      have h2 : N.presheaf.map (homOfLE i.2).op (φ.app U s) = 0 := by
        rw [← h i.1 (M.presheaf.map (homOfLE i.2).op s)]
        exact hnat.symm
      exact h2.trans (map_zero _).symm
  ext s
  simp [key s]

theorem le_iff_secs_subset {X : Scheme.{0}} {E : X.Modules} (S T : Subobject E) :
    S ≤ T ↔ ∀ U : X.affineOpens, secs S (U : X.Opens) ⊆ secs T (U : X.Opens) := by
  unfold GlobalTheory.CompanionTheory.GE.secs
  constructor
  · intro hST U x hx
    obtain ⟨s, rfl⟩ := hx
    refine ⟨(Subobject.ofLE S T hST).app (U : X.Opens) s, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]
  · intro h
    have hzero : S.arrow ≫ cokernel.π T.arrow = 0 := by
      apply GlobalTheory.CompanionTheory.GE.hom_eq_zero_of_affineOpens
      intro U s
      obtain ⟨t, ht⟩ := h U (Set.mem_range_self s)
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ← ht,
        ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition,
        Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply]
    exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow hzero)
      (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
