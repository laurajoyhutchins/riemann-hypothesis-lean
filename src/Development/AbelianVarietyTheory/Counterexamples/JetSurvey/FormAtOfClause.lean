module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaValuationTest

open Formalism.MainNotions Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : WeightAlgebra.PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) : 0 ≤ X.phiC la y := by
  unfold WeightAlgebra.PJ.phiC
  split_ifs
  · refine mul_nonneg (Nat.cast_nonneg _) (Real.sInf_nonneg ?_)
    rintro x ⟨l, -, hl, rfl⟩
    by_cases h0 : (P.loc X.dat (WeightAlgebra.resCh la)).beS (X.pt66 la y) = 0
    · rw [h0, map_zero]
    · refine (hl _ (fun a => ?_) h0).le
      obtain ⟨ι, _, b, hb⟩ := (P.loc X.dat (WeightAlgebra.resCh la)).be_posDef (X.pt66 la y)
      show 0 ≤ (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) a a
      by_cases hc : (fun i => ((b.repr a i : ℤ) : ℝ)) = 0
      · have : a = 0 := by
          apply b.repr.injective
          ext i
          have := congrFun hc i
          simpa using this
        simp [this]
      · have h1 := hb _ hc
        have h2 : (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) a a =
            ∑ i, ∑ k, ((b.repr a i : ℤ) : ℝ) * ((b.repr a k : ℤ) : ℝ) *
              (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) (b i) (b k) := by
          conv_lhs => rw [← b.sum_repr a]

          simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
        rw [h2]; exact h1.le
  · exact le_rfl

theorem mem_Mlat (X : WeightAlgebra.PJ D B P j) (i : ℕ) (η : B.Cusp j (Formalism.L2.Pj.wEt D j i)) (h : EtVal X i η) :
    η ∈ B.Mlat j _ := by
  refine (X.Mlat_eq _ η).2 fun la y => le_trans ?_ (h la y)
  exact EReal.coe_nonneg.2 (mul_nonneg (by positivity) (phiC_nonneg X la y))

end GlobalTheory.EtaValuationTest
