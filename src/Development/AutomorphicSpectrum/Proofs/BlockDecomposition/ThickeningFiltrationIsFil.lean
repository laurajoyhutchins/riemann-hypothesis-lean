module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

theorem isFil_thFil : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := by
  intro b L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.pdPow_zero
  · intro T
    change T.pdPow (1 : ℤ).toNat = T.J
    exact le_antisymm (dividedPowerFiltration_one_le T.δ) T.J_le_pdPow_one
  · intro r r' h T
    exact T.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.B from x) ∈ pdP T.δ r := by
      have : (show T.B from x) ∈ T.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.B from y) ∈ pdP T.δ r' := by
      have : (show T.B from y) ∈ T.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := dividedPowerFiltration_mul_le T.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.δ k hx

end GlobalTheory.CompanionTheory.DPFil
