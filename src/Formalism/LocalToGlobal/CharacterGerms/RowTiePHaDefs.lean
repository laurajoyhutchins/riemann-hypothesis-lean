module

public import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
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

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.HaP

open MvPolynomial Formalism.L2.Pj

def SatRetrSt : Prop :=
  ∀ (ι : Type) [Fintype ι] (W : Submodule ℤ (ι → ℤ)), (∀ (z : ℤ) (x : ι → ℤ), z ≠ 0 → z • x ∈ W → x ∈ W) →
    ∃ ρ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ), (∀ x, ρ x ∈ W) ∧ ∀ x ∈ W, ρ x = x

def RowInvUpSt : Prop :=
  ∀ (Ty : Type) (r : Ty → ℕ) (n : ℕ) (K : Type) [Field K] [CharZero K] (P : MvPolynomial (Letter Ty r n) K),
    (∀ (σ : Ty) (i i' : Fin (r σ)), i' < i → ∀ q : ℚ, rowShift r n K σ i i' (q : K) P = P) → RowInv r n K P

end Formalism.L2.FormalSeriesBounds.HaP
