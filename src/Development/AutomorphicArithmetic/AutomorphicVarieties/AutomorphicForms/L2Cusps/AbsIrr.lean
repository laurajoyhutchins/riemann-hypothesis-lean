module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.V.KernelIndexFullLattice.absIrr_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsIrr := by
  intro G G₁ H L _ _ _ _ _ _ _ _ π ρ J r hr hρ X hXJ hX
  obtain ⟨⟨hXc, hXinv⟩, hXne, hXmin⟩ := hX
  have hVc : IsClosed ((Submodule.comap J.toLinearMap X : Submodule ℂ H) : Set H) :=
    hXc.preimage J.continuous
  haveI hVcomp : CompleteSpace (Submodule.comap J.toLinearMap X) := hVc.completeSpace_coe
  have hinv : π.IsInvariant (Submodule.comap J.toLinearMap X) := by
    intro g₁ v hv
    obtain ⟨g, rfl⟩ := hr g₁
    show J (π (r g) v) ∈ X
    rw [← hρ]
    exact hXinv g _ hv
  refine ⟨hVcomp, hinv, ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    obtain ⟨h, rfl⟩ := hXJ hx
    refine nontrivial_of_ne (⟨h, hx⟩ : Submodule.comap J.toLinearMap X) 0 ?_
    intro e
    apply hx0
    have e' : h = 0 := congrArg Subtype.val e
    rw [e', map_zero]
  · intro U' hU'c hU'inv
    let V := Submodule.comap J.toLinearMap X
    let U : Submodule ℂ L := (U'.map V.subtype).map J.toLinearMap
    have hUX : U ≤ X := by
      rintro _ ⟨_, ⟨u, _, rfl⟩, rfl⟩
      exact u.2
    have hU'H : IsClosed ((U'.map V.subtype : Submodule ℂ H) : Set H) := by
      rw [Submodule.map_coe]
      exact hVc.isClosedEmbedding_subtypeVal.isClosedMap _ hU'c
    have hUc : IsClosed (U : Set L) := by
      rw [Submodule.map_coe]
      exact J.isometry.isClosedEmbedding.isClosedMap _ hU'H
    have hUinv : ∀ g, ∀ v ∈ U, ρ g v ∈ U := by
      rintro g _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨_, ⟨⟨π (r g) u, hinv _ _ u.2⟩, hU'inv (r g) u hu, rfl⟩, ?_⟩
      exact (hρ g u).symm
    rcases hXmin U hUX ⟨hUc, hUinv⟩ with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      have hJu : J u ∈ U := ⟨u, ⟨u, hu, rfl⟩, rfl⟩
      rw [h, Submodule.mem_bot] at hJu
      rw [Submodule.mem_bot]
      apply Subtype.ext
      have hn : ‖(u : H)‖ = 0 := by rw [← J.norm_map, hJu, norm_zero]
      simpa using hn
    · right
      rw [eq_top_iff]
      intro u _
      have hJu : J u ∈ U := by
        rw [h]
        exact u.2
      obtain ⟨_, ⟨u', hu', rfl⟩, he⟩ := hJu
      have : u' = u := Subtype.ext (J.injective he)
      rw [← this]
      exact hu'
