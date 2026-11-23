module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.WeilM

namespace GlobalTheory.ThKOp


open scoped Classical in
theorem continuous_of_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have hr : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
          (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
      funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
    rw [this]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply _)
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    have h1 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 :=
      continuous_pi fun i => hr.comp (continuous_fst.comp (continuous_apply i))
    have h2 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => (x i).2 :=
      continuous_pi fun i => continuous_snd.comp (continuous_apply i)
    exact (f.continuous.comp h1).mul (hg.1.continuous.comp h2)
  | zero => exact continuous_const
  | add _ _ _ _ h h' => exact h.add h'
  | smul c _ _ h => exact continuous_const.mul h

end GlobalTheory.ThKOp
