module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isTay_apply_of_fn_eq_param : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (f : (I → ℂ) → ℂ), (∀ p ∈ W, h.fn p = f p.1) → ρ h = GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] 1 := by
  intro I _ _ g R _ _ N t W W₀ h0 ρ hρ h f hf
  apply GlobalTheory.tensor_hol_ext_of_values W₀ R
  intro p hp
  have e1 := hρ h p hp
  have e2 : (fun z : I → ℂ ↦ h.fn (z, p.2)) =ᶠ[𝓝 0] f := by
    have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := continuous_id.prodMk continuous_const
    have hm : ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, p.2) : Tot I g) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds (h0 p hp))
    filter_upwards [hm] with z hz using hf _ hz
  have e3 := (GlobalTheory.PeriodFamily.taylor_formal_properties (D := R) N t).2.2.2.1 _ _ e2
  change evT R p hp (ρ h) = evT R p hp (GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] (1 : Hol W₀))
  rw [e1, e3]
  simp [evT, Algebra.TensorProduct.lift_tmul]

end GlobalTheory.AnPer
