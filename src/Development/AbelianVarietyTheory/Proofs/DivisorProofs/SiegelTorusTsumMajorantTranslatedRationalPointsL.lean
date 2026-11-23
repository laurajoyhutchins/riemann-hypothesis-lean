module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorRationalMatricesInBoxStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementInvFinitePartOneDualFrameEigenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInverseLatticeCountStackedEigenprojectionsStatement
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ENNReal.ofReal (GlobalTheory.Unf.maj θ K N (GlobalTheory.SiegelFormula.invPt V a ξ)) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc K hK
  obtain ⟨L, hL, hden⟩ := GlobalTheory.T.exists_bounded_denominator_rational_matrices_in_box D V.rank n K hK
  obtain ⟨N, C, hC, hst⟩ := GlobalTheory.T.torusInverse_latticeCount_stacked_eigenprojections D V.rank n r X Y
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) c hc L hL
  refine ⟨N, C, hC, fun t ht a ha => ?_⟩
  obtain ⟨hfin, hrel⟩ := GlobalTheory.T.siegelTorusElement_inv_finitePart_one_dualFrame_eigen D θ hθ V r X Y hXY t ht.1 a ha
  refine le_trans (ENNReal.tsum_le_tsum fun ξ => ?_)
    (hst t ht (fun τ => compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) hrel)
  have e : (GlobalTheory.SiegelFormula.invPt V a ξ : Matrix (Fin V.rank) (Fin n) (AE D)) =
      HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D) : Matrix (Fin V.rank) (Fin n) (AE D)) := rfl
  have hcomp : ∀ τ, compAt θ τ (GlobalTheory.SiegelFormula.invPt V a ξ) =
      compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) * ξ.map (tauE D τ) := by
    intro τ
    have h1 : compAt θ τ (ξ.map (incA D) : Mx D V.rank n) = ξ.map (tauE D τ) := by
      ext i j
      exact (hθ τ).1 (ξ i j)
    rw [e, ← h1]
    exact Matrix.map_mul (f := (θ τ).comp (infPart D))
  unfold GlobalTheory.Unf.maj
  split_ifs with hb
  · have hmem : ξ ∈ {ξ : Matrix (Fin V.rank) (Fin n) D.host.E |
        ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} := by
      refine hden _ ξ ?_ hb
      rw [e, Matrix.map_mul, hfin, Matrix.one_mul]
    rw [Set.indicator_of_mem hmem]
    simp only [GlobalTheory.Unf.realSize, hcomp, le_refl]
  · simp
