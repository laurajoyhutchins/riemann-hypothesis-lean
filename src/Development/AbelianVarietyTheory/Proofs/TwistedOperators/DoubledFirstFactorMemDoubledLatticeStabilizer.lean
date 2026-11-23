module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.InertDbl.inlD_mem_KAtD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  intro F E _ _ _ _ _ σ d W v k hk
  refine ⟨?_, fun z hz => ?_⟩
  · intro u hu
    rw [GlobalTheory.InertDbl.matD_inlD]
    have h1 := hk.1 u hu
    have h1' : u • (mat k - 1) = 0 := h1
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have := congrFun (congrFun h1' i) j
      simpa [Matrix.fromBlocks, Matrix.one_apply] using this
    all_goals simp [Matrix.fromBlocks, Matrix.one_apply]
  · have hinv : GlobalTheory.InertDbl.matD (GlobalTheory.InertDbl.inlD σ W k)⁻¹ = Matrix.fromBlocks (mat k⁻¹) 0 0 1 := by
      rw [← map_inv]; rfl
    rw [hinv, GlobalTheory.InertDbl.matD_inlD]
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨a1, a2⟩ := hk.2 _ hz1
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [Matrix.fromBlocks_mulVec]; convert a1 using 1; funext i; simp [Function.comp_def]
    · simpa [Matrix.fromBlocks_mulVec] using hz2
    · simp only [Matrix.fromBlocks_mulVec]; convert a2 using 1; funext i; simp [Function.comp_def]
    · simpa [Matrix.fromBlocks_mulVec] using hz2
