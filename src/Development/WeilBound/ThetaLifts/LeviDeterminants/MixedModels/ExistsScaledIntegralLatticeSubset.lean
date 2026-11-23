module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm

theorem PositivityTheory.Mix.exists_scaled_integral_lattice_subset : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧ (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  classical
  intro F _ _ κ _ W hW
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hIt⟩ := hW
  choose M hM0 hM using fun i => GlobalTheory.IdeleCharLevel.exists_level F (t i) (ht i)
  have hN0 : (∏ i, M i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hM0 i
  refine ⟨((∏ i, M i : ℕ) : F), by exact_mod_cast hN0, ?_⟩
  intro z hz
  apply hIt
  intro i _
  apply hM i
  intro P
  have h1 : (algebraMap F (P.adicCompletion F) ((∏ i, M i : ℕ) : F))⁻¹ * (z i) P ∈ P.adicCompletionIntegers F := hz i P
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀] at h1
  have hA : Valued.v (algebraMap F (P.adicCompletion F) ((∏ i, M i : ℕ) : F)) =
      P.intValuation ((∏ i, M i : ℕ) : 𝓞 F) := by
    have e : ((∏ i, M i : ℕ) : F) = algebraMap (𝓞 F) F ((∏ i, M i : ℕ) : 𝓞 F) := by simp
    rw [e, ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact Formalism.UG.P.levelaf_valued_algebraMap P ((algebraMap (𝓞 F) F) ↑(∏ i, M i))
  have hB : P.intValuation ((∏ i, M i : ℕ) : 𝓞 F) ≤ P.intValuation ((M i : ℕ) : 𝓞 F) := by
    rw [← Finset.mul_prod_erase Finset.univ M (Finset.mem_univ i), Nat.cast_mul, map_mul]
    exact mul_le_of_le_one_right' (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)
  have h0 : Valued.v (algebraMap F (P.adicCompletion F) ((∏ i, M i : ℕ) : F)) ≠ 0 := by
    rw [hA]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero _ _ (by exact_mod_cast hN0)
  refine le_trans ?_ (hA ▸ hB)
  calc Valued.v ((z i) P)
      = Valued.v (algebraMap F (P.adicCompletion F) ((∏ i, M i : ℕ) : F)) *
        ((Valued.v (algebraMap F (P.adicCompletion F) ((∏ i, M i : ℕ) : F)))⁻¹ * Valued.v ((z i) P)) := by
        rw [mul_inv_cancel_left₀ h0]
    _ ≤ Valued.v (algebraMap F (P.adicCompletion F) ((∏ i, M i : ℕ) : F)) := mul_le_of_le_one_right' h1
