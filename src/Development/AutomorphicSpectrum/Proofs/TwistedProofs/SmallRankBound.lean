module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

private theorem mem_range_bc_of_entries_mem_intL {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    (g : GL (Fin n) L) (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) :
    g ∈ (Formalism.UG.bc (Formalism.UG.intL L).subtype).range := by
  let M : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h2 i j⟩
  have hM : (Formalism.UG.intL L).subtype.mapMatrix M = g := by ext i j; rfl
  have hM' : (Formalism.UG.intL L).subtype.mapMatrix M' = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have inj : Function.Injective
      ((Formalism.UG.intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) → Matrix (Fin n) (Fin n) L) :=
    fun A B h => Matrix.ext fun i j => Subtype.ext (by simpa [RingHom.mapMatrix_apply] using congrFun (congrFun h i) j)
  refine ⟨⟨M, M', inj ?_, inj ?_⟩, Units.ext hM⟩
  · rw [map_mul, map_one, hM, hM']
    exact g.mul_inv
  · rw [map_mul, map_one, hM, hM']
    exact g.inv_mul

private theorem entry_lemma_2 {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
    (hv : ∀ x, Valued.v (σ x) = Valued.v x) (g : Formalism.UG.GU σ 1) (i j : Fin 1) :
    ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) i j ∈ Formalism.UG.intL L := by
  have hg : Formalism.UG.cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * Formalism.UG.antiJ L 1 *
      ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) = Formalism.UG.antiJ L 1 := g.2
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  set x := ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) 0 0 with hx
  have e : σ x * x = 1 := by
    have := congrFun (congrFun hg 0) 0
    simpa [Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.antiJ, hx] using this
  have e2 : Valued.v x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hv x]
    rw [← map_mul, e, map_one]
  refine (Valuation.mem_integer_iff _ _).mpr ?_
  exact (pow_le_one_iff two_ne_zero).mp e2.le

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hσ hn g
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf]
  refine ⟨g.2, ?_⟩
  interval_cases n
  · exact mem_range_bc_of_entries_mem_intL _ (fun i => i.elim0) (fun i => i.elim0)
  · exact mem_range_bc_of_entries_mem_intL _ (entry_lemma_2 hσ.2.1 g) (entry_lemma_2 hσ.2.1 g⁻¹)

end GlobalTheory.CompanionTheory.InertZeta
