module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardResidueEqQV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValue
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

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DlBridgeAt

theorem val_eq_uniformizer_of_ord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (h : ord k ϖ = 1) :
    valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact uniformizer_ne_zero hy.symm
  have hu : valuation k ((Units.mk0 y hy0 : kˣ) : k) = uniformizer k := hy
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hu
  have h2 : ord k (ϖ * (Units.mk0 y hy0)⁻¹) = 0 := by
    have h3 := ord_mul k (ϖ * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right] at h3
    omega
  have h4 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu] at h4
  have hne : uniformizer k ≠ 0 := uniformizer_ne_zero
  exact (mul_inv_eq_one₀ hne).1 h4

end GlobalTheory.CompanionTheory.DlBridgeAt


open GlobalTheory.CompanionTheory.DlBridgeAt in
theorem GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  intro E _ _ _ w ϖ hϖ
  have hord : ord (w.adicCompletion E) ϖ = 1 := (GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ
  refine ⟨val_eq_uniformizer_of_ord ϖ hord, fun N x => ?_⟩
  have hinv := GlobalTheory.CompanionTheory.JacEigAt.deltaHalf_inv N w ϖ hord x
  have hv := val_deltaHalf (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  have hm := deltaB_eq_modulus (fun i : Fin N => ϖ ^ x i)
  have hpos := modulus_pos (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  rw [Units.val_inv_eq_inv_val, hv] at hinv
  rw [hv, hm]
  change _ = GlobalTheory.BCT.qh w ^ _ at hinv
  rw [← hinv]
  set m := modulus (w.adicCompletion E) (fun _ : Fin N => Unit)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) with hmdef
  have hs : √m * √m = m := Real.mul_self_sqrt hpos.le
  have hs0 : √m ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : ∀ s : ℝ, s ≠ 0 → (s * s)⁻¹ * s = s⁻¹ := fun s h => by field_simp
  have h5 := key _ hs0
  rw [hs] at h5
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, h5]

end
