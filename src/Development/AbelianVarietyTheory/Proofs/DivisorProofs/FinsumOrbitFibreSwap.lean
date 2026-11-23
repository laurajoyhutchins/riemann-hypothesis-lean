module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Preimage

@[expose] public section

open scoped BigOperators

namespace GlobalTheory
namespace OrbitFibre

open MulAction Function

theorem finsum_sigma_iter {ι : Type} {κ : ι → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (support f).Finite) : ∑ᶠ p, f p = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  set s := hf.toFinset with hs
  let t : Finset ι := s.image Sigma.fst
  let u : ∀ i, Finset (κ i) := fun i => s.preimage (Sigma.mk i) sigma_mk_injective.injOn
  have hsub : s ⊆ t.sigma u := by
    intro p hp
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_image_of_mem _ hp, by simpa [u] using hp⟩
  rw [finsum_eq_sum f hf, ← hs, Finset.sum_subset hsub ?_, Finset.sum_sigma]
  · rw [finsum_eq_sum_of_support_subset _ (s := t) ?_]
    · apply Finset.sum_congr rfl
      intro i _
      rw [finsum_eq_sum_of_support_subset _ (s := u i)]
      intro k hk
      simpa [u, hs] using hk
    · intro i hi
      rw [Function.mem_support] at hi
      by_contra hit
      apply hi
      have : ∀ k, f ⟨i, k⟩ = 0 := by
        intro k
        by_contra hk
        apply hit
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨i, k⟩, by simpa [hs] using hk, rfl⟩)
      simp [this]
  · intro p _ hp
    simpa [hs] using hp

variable {Γ A B J : Type} [Group Γ] [MulAction Γ A] [MulAction Γ B]


end OrbitFibre

end GlobalTheory
