module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference

@[expose] public section

open Module Submodule

namespace GlobalTheory

theorem exists_basis_span_eq_of_discrete {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology M] (hM : span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤) :
    ∃ b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), span ℤ (Set.range b) = M := by
  have : IsZLattice ℝ M := ⟨hM⟩
  have := ZLattice.module_free ℝ M
  have := ZLattice.module_finite ℝ M
  let b1 := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = N := by
    rw [← finrank_eq_card_basis b1]
    simp
  refine ⟨b1.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Basis.range_reindex]
  exact Basis.ofZLatticeBasis_span ℝ M _

theorem exists_inner_dual_basis {N : ℕ} (b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    ∃ d : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), ∀ j y, inner ℝ (d j) y = b.repr y j := by
  let w : Fin N → EuclideanSpace ℝ (Fin N) := fun j =>
    (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap (b.coord j))
  have hw : ∀ j y, inner ℝ (w j) y = b.repr y j := fun j y => by
    simp [w, InnerProductSpace.toDual_symm_apply]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun x => inner ℝ x (b i)) hg
    simpa [sum_inner, real_inner_smul_left, hw, Finsupp.single_apply] using this
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp), fun j y => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', hw]

theorem transference_discrete_lattice :
    ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))), DiscreteTopology M →
      Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ → ∀ lam : ℝ, 0 < lam →
      (∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → z ≠ 0 →
        lam ≤ ‖z‖) →
      ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧
        ∀ j, ‖v j‖ ≤ (N : ℝ) ^ 2 / lam := by
  intro N M _ hM lam hlam hmin
  obtain ⟨b, rfl⟩ := exists_basis_span_eq_of_discrete M hM
  obtain ⟨d, hd⟩ := exists_inner_dual_basis b
  obtain ⟨y, hli, hint, hy⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual d lam hlam (by
    intro x hx hx0
    refine hmin x (fun y hy => ?_) hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    obtain ⟨e, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hy
    refine ⟨∑ j, c j * e j, ?_⟩
    simp [sum_inner, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hd,
      Finsupp.single_apply])
  refine ⟨y, fun i => ?_, hli, hy⟩
  rw [b.mem_span_iff_repr_mem ℤ]
  intro j
  obtain ⟨m, hm⟩ := hint i j
  exact ⟨m, by rw [← hd, real_inner_comm, hm]; simp⟩

end GlobalTheory
