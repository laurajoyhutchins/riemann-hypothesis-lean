module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
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

@[expose] public section

namespace GlobalTheory.CyclotomicQExpansion
open GlobalTheory.KZ

theorem exp_sl_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : X.K) :
    X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  have hdet : 0 < ent g 0 0 * ent g 1 1 := by
    have h := g.2
    have h' : 0 < Matrix.det ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := h
    rw [Matrix.det_fin_two] at h'
    simp only [ent] at hg ⊢
    rw [hg, mul_zero, sub_zero] at h'
    exact h'
  have hd : ent g 1 1 ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hdet; exact lt_irrefl _ hdet
  have ha : ent g 0 0 ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hdet; exact lt_irrefl _ hdet
  have hpos : 0 < ent g 0 0 / ent g 1 1 := by
    have : ent g 0 0 / ent g 1 1 = (ent g 0 0 * ent g 1 1) / (ent g 1 1) ^ 2 := by field_simp
    rw [this]; exact div_pos hdet (by positivity)
  ext s
  unfold sub scale
  rw [dite_eq_left hpos]
  set e := (OrderIso.mulLeft₀ (ent g 0 0 / ent g 1 1) hpos).toOrderEmbedding with he
  have hs : s = e (s * ent g 1 1 / ent g 0 0) := by
    simp only [he, RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  rw [hs, HahnSeries.embDomain_coeff]
  have key := X.exp_upper g hg f (s * ent g 1 1 / ent g 0 0)
  have h2 : s * ent g 1 1 / ent g 0 0 * ent g 0 0 / ent g 1 1 = e (s * ent g 1 1 / ent g 0 0) := by
    rw [← hs]; field_simp
  rw [h2] at key
  rw [key]
  rfl

end GlobalTheory.CyclotomicQExpansion
