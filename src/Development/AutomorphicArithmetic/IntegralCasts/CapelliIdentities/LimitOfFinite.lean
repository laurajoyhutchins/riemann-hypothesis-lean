module

public import Mathlib.RingTheory.AdicCompletion.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite.{u_1, u_2}
    {A : Type u_1} {M : Type u_2} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m : ℕ, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L : M, ∀ m : ℕ, f m - L ∈ (I ^ m • ⊤ : Submodule A M) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have key : ∀ (J : Ideal A) (x : M), x ∈ (J • ⊤ : Submodule A M) →
      ∃ d : Fin n → A, (∀ i, d i ∈ J) ∧ ∑ i, d i • s i = x := by
    intro J x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      have hy : y ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
      refine ⟨fun i => r * c i, fun i => J.mul_mem_right _ hr, ?_⟩
      rw [← hc, Finset.smul_sum]
      simp [mul_smul]
    · rintro x y ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
      refine ⟨fun i => d i + e i, fun i => J.add_mem (hd i) (he i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
  choose d hd hdf using fun m => key (I ^ m) _ (hf m)
  let g : ℕ → Fin n → A := fun m i => ∑ k ∈ Finset.range m, d k i
  have hg : ∀ m, f m = f 0 - ∑ i, g m i • s i := by
    intro m
    induction m with
    | zero => simp [g]
    | succ m ih =>
      have h1 : ∑ i, g (m + 1) i • s i = ∑ i, g m i • s i + ∑ i, d m i • s i := by
        simp [g, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      rw [h1, hdf m, ← sub_sub, ← ih]
      abel
  have hc : ∀ i, ∀ m k, m ≤ k → g m i - g k i ∈ I ^ m := by
    intro i m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have h1 : g m i - g (k + 1) i = g m i - g k i - d k i := by
        simp only [g, Finset.sum_range_succ]; ring
      rw [h1]
      exact (I ^ m).sub_mem ih (Ideal.pow_le_pow_right hmk (hd k i))
  have hl : ∀ i, ∃ a : A, ∀ m, g m i - a ∈ I ^ m := by
    intro i
    obtain ⟨a, ha⟩ := hI.prec (f := fun m => g m i) (by
      intro m k hmk
      rw [SModEq.sub_mem]
      simpa using hc i m k hmk)
    refine ⟨a, fun m => ?_⟩
    have := ha m
    rw [SModEq.sub_mem] at this
    simpa using this
  choose a ha using hl
  refine ⟨f 0 - ∑ i, a i • s i, fun m => ?_⟩
  have h2 : f m - (f 0 - ∑ i, a i • s i) = -∑ i, (g m i - a i) • s i := by
    rw [hg m]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [h2]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem_smul (ha i m) Submodule.mem_top)
