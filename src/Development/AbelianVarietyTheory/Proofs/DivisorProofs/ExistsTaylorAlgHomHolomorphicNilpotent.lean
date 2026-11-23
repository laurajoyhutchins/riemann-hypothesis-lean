module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
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

set_option autoImplicit false

open Filter Topology TopologicalSpace

namespace GlobalTheory.AnPer.TaylorHom

open GlobalTheory.AnPer GlobalTheory.PeriodFamily

variable {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R]

theorem fn_add_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f + g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z + g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_add f g hq

theorem fn_mul_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f * g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z * g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_mul f g hq

theorem fn_algebraMap_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    (algebraMap ℂ (Hol V) c).fn =ᶠ[𝓝 0] fun _ ↦ c := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_algebraMap c hq

theorem taylor_algebraMap (N : ℕ) (t : I → R) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    GlobalTheory.PeriodFamily.taylor N t (algebraMap ℂ (Hol V) c).fn = algebraMap ℂ R c := by
  rw [taylor_congr_germ N t _ _ (fn_algebraMap_eventually h0 c), taylor_const_fun]

noncomputable def taylorHom (N : ℕ) (t : I → R) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0)
    (V : Opens (I → ℂ)) (h0 : (0 : I → ℂ) ∈ V) : Hol V →ₐ[ℂ] R where
  toFun f := GlobalTheory.PeriodFamily.taylor N t f.fn
  map_one' := by
    have h : (1 : Hol V) = algebraMap ℂ (Hol V) 1 := (map_one _).symm
    change GlobalTheory.PeriodFamily.taylor N t (1 : Hol V).fn = 1
    rw [h, taylor_algebraMap N t h0, map_one]
  map_mul' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f * g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn * GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_mul_eventually h0 f g)]
    exact taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  map_zero' := by
    have h : (0 : Hol V) = algebraMap ℂ (Hol V) 0 := (map_zero _).symm
    change GlobalTheory.PeriodFamily.taylor N t (0 : Hol V).fn = 0
    rw [h, taylor_algebraMap N t h0, map_zero]
  map_add' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f + g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn + GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_add_eventually h0 f g)]
    exact taylor_add_of_analyticAt N t _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  commutes' c := taylor_algebraMap N t h0 c

end GlobalTheory.AnPer.TaylorHom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

theorem GlobalTheory.AnPer.exists_taylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = GlobalTheory.PeriodFamily.taylor N t f.fn := by
  intro I _ _ R _ _ N t ht V h0
  exact ⟨GlobalTheory.AnPer.TaylorHom.taylorHom N t ht V h0, fun f ↦ rfl⟩
