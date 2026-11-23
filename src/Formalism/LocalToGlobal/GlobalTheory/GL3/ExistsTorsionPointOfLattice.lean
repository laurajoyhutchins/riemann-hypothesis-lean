module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsTwoTorsionOffKernels
public import Formalism.PeriodIntegrals.LatDefs

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical Formalism.MainNotions
open Formalism.L2.Th1 (F2.IsLat F2.HasCM)

theorem sgStar_spec (L : PeriodPair) :
    Differentiable ℂ (Formalism.L2.Th1.F.sgStar L) ∧ deriv (Formalism.L2.Th1.F.sgStar L) 0 = 1 ∧
      (∀ z, Formalism.L2.Th1.F.sgStar L (-z) = -Formalism.L2.Th1.F.sgStar L z) ∧
      ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω (Formalism.L2.Th1.F.sgStar L) z =
        (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * Formalism.L2.Th1.F.sgStar L z := by
  obtain ⟨h1, h2, -, h4, -⟩ := Formalism.L2.Th1.F.sgStarBasic L
  refine ⟨h1, h4, h2, fun ω hω z => ?_⟩
  rw [Formalism.L2.GlobalTheoryTheory.taylorLogMetric_U1_eq_U1, Formalism.L2.Th1.F2.thetaTranslationOperator_apply]
  have hfix := Formalism.L2.Th1.F.sgStarFixed L ω z hω
  by_cases h : ω / 2 ∈ L.lattice
  · have hs : Formalism.L2.Th1.F.semiChar L ω = 1 := by unfold Formalism.L2.Th1.F.semiChar; simp [h]
    have h' : ω / 2 ∈ L.lattice.toAddSubgroup := h
    rw [if_pos h', one_mul, ← hfix, hs, one_mul]
  · have hs : Formalism.L2.Th1.F.semiChar L ω = -1 := by unfold Formalism.L2.Th1.F.semiChar; simp [h]
    have h' : ω / 2 ∉ L.lattice.toAddSubgroup := h
    rw [if_neg h', ← hfix, hs]
    ring

theorem sgStar_eq (L : PeriodPair) : Formalism.MainNotions.TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  have hlat : L.lattice.toAddSubgroup = PI.lat2 L.ω₁ L.ω₂ := Submodule.span_int_eq_addSubgroupClosure _
  have hIm : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
    have := Formalism.L2.Th1.F.areaPos L
    unfold Formalism.L2.Th1.F.area at this
    exact abs_pos.mp this
  have hF := sgStar_spec L
  have hE := Classical.epsilon_spec (p := fun G : ℂ → ℂ => Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
    ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G z =
      (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G z) ⟨_, hF⟩
  have huniq : ∀ G G' : ℂ → ℂ,
      (Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
        ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G z =
          (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G z) →
      (Differentiable ℂ G' ∧ deriv G' 0 = 1 ∧ (∀ z, G' (-z) = -G' z) ∧
        ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G' z =
          (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G' z) → G = G' := by
    intro G G' hG hG'
    rw [hlat] at hG hG'
    exact sigma_star_unique L.ω₁ L.ω₂ hIm G G' hG hG'
  unfold Formalism.MainNotions.TaylorLogMetric.sgStar
  exact huniq _ _ hE hF





end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

end
