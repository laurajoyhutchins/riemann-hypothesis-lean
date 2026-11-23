module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem isNilpotent_of_isDPNilpotent : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D}
    (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  intro D _ _ J dl hdl
  obtain ⟨N, h⟩ := hdl
  have h0 : ∀ l : List D, (∀ b ∈ l, b ∈ J) → N ≤ l.length → l.prod = 0 := by
    intro l hl hN
    have k := h (l.map fun b ↦ (1, b)) (by simpa using hl)
      (by simpa [List.map_map, Function.comp_def] using hN)
    rw [List.map_map] at k
    have e : l.map ((fun p : ℕ × D ↦ dl.dpow p.1 p.2) ∘ fun b ↦ (1, b)) = l.map id :=
      List.map_congr_left fun b hb ↦ dl.dpow_one (hl b hb)
    rwa [e, List.map_id] at k
  have key : ∀ n : ℕ, ∀ x ∈ J ^ n, ∀ l : List D, (∀ b ∈ l, b ∈ J) →
      N ≤ n + l.length → x * l.prod = 0 := by
    intro n
    induction n with
    | zero => intro x _ l hl hN; rw [h0 l hl (by simpa using hN), mul_zero]
    | succ n ih =>
      intro x hx l hl hN
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_)
        fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero]
      have := ih a ha (b :: l) (by simpa using ⟨hb, hl⟩) (by simp; omega)
      rwa [List.prod_cons, ← _root_.mul_assoc] at this
  refine ⟨N, eq_bot_iff.2 fun x hx ↦ ?_⟩
  simpa using key N x hx [] (by simp) (by simp)

end GlobalTheory.AnPer
