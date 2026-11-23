module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem exists_tensorLift_of_DObj {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R]
    [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (S : K₀.DObj (et : Hol F₀.V →+* R) M) :
    ∃ ψ : R ⊗[ℂ] Hol (K₀.W S.T.k) →+* S.T.C, ∀ (d : R) (h : Hol (K₀.W S.T.k)),
      ψ (d ⊗ₜ[ℂ] h) = algebraMap R S.T.C d * S.T.ρ h := by
  letI : Algebra ℂ S.T.C := ((algebraMap R S.T.C).comp (algebraMap ℂ R)).toAlgebra
  let fR : R →ₐ[ℂ] S.T.C := { algebraMap R S.T.C with commutes' := fun _ ↦ rfl }
  let fH : Hol (K₀.W S.T.k) →ₐ[ℂ] S.T.C :=
    { S.T.ρ with
      commutes' := fun a ↦ by
        have h1 : algebraMap ℂ (Hol (K₀.W S.T.k)) a = K₀.cst S.T.k (algebraMap ℂ (Hol F₀.V) a) :=
          ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K₀.base S.T.k)).commutes a).symm
        change S.T.ρ (algebraMap ℂ (Hol (K₀.W S.T.k)) a) = algebraMap R S.T.C (algebraMap ℂ R a)
        rw [h1, S.T.ρ_cst, S.compat]
        change algebraMap R S.T.C (et (algebraMap ℂ (Hol F₀.V) a)) = _
        rw [et.commutes] }
  refine ⟨(Algebra.TensorProduct.lift fR fH (fun _ _ ↦ Commute.all _ _)).toRingHom, fun d h ↦ ?_⟩
  exact Algebra.TensorProduct.lift_tmul _ _ _ d h

end GlobalTheory.AnPer
