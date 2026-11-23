module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ}

private theorem cc_subst_lemma_2 {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem cc_ev_eq {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  exact cc_subst_lemma_2 (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f

theorem constantCoeff_eval_pair {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    constantCoeff (ev ![a, b] f) = constantCoeff f := cc_ev_eq ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MapFB

end Formalism.L2.FormalSeriesBounds
