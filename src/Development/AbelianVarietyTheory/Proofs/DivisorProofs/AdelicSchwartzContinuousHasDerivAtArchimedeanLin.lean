module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SchLine

theorem continuous_pureA (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : Continuous (pureA F f g) := by
  unfold pureA
  refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_)) (hg.1.continuous.comp (continuous_pi fun i => ?_))
  · exact (continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  · exact continuous_snd.comp (continuous_apply i)

theorem continuous_of_mem (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact continuous_pureA F f g hg
  | zero => exact continuous_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul a Φ _ h => exact h.const_smul a

theorem line_shift (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t s : ℝ) :
    x + (fun i => infAd F (s • v i)) = (x + fun i => infAd F (t • v i)) + fun i => infAd F ((s - t) • v i) := by
  funext i
  simp only [Pi.add_apply]
  rw [add_assoc, ← infAd_add, ← add_smul, add_sub_cancel]

theorem schline : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t := by
  intro F _ _ κ _ g hg
  refine ⟨continuous_of_mem F hg, fun v x t => ?_⟩
  set y : κ → AF F := x + fun i => infAd F (t • v i)
  have h0 : HasDerivAt (fun u : ℝ => g (y + fun i => infAd F (u • v i))) (dD F v g y) (t - t) := by
    rw [sub_self]
    exact ((SchAStab.archimedeanDirectionalDerivative_mem_adelicSchwartz F v hg).1 y).hasDerivAt
  have h1 := h0.comp_sub_const t t
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show g (x + fun i => infAd F (s • v i)) = g (y + fun i => infAd F ((s - t) • v i))
  rw [line_shift F x v t s]

end GlobalTheory.ArchDecay.SchLine
