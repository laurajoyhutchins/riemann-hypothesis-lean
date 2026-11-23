module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem act_fin_val {N : ℕ} (g : GL (Fin N) (Af E)) (φ : Sm E N) (x : GA E N) :
    (act (.fin g) φ).1 x = φ.1 (x * finGL E N g) := rfl

theorem memInd2_act_fin {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)}
    (g : GL (Fin (r + s)) (Af E)) {φ : Sm E (r + s)} (h : MemInd2 U₁ U₂ φ) :
    MemInd2 U₁ U₂ (act (.fin g) φ) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, fun k g' => ?_⟩
  · rw [act_fin_val, act_fin_val, mul_assoc, h1]
  · convert h2 k (g' * g) using 2 with m
    rw [act_fin_val, map_mul, mul_assoc, mul_assoc]

theorem indSpan_finStable (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) :
    FinStable (indSpan U₁ U₂) := by
  intro g φ hφ
  change φ ∈ Submodule.span ℂ _ at hφ
  change _ ∈ Submodule.span ℂ _
  induction hφ using Submodule.span_induction with
  | mem φ h => exact Submodule.subset_span (memInd2_act_fin g h)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end GlobalTheory.CompanionTheory.LimV

end
