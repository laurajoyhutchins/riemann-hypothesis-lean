module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open PositivityTheory.HtPt.Ml (generic_max mem_of_dense_of_max)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem genericPoints_subset_range_j :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O]
      (β : O →+* c.F) (Y : Model Xo c β),
      IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) →
        genericPoints Y.X ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y hO hFraction v hv
  let := β.toAlgebra
  have : IsFractionRing O c.F := hFraction
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have := Y.flat
  have := Y.jQ_open
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    have := hi
    have := isProper_str O N
    rw [← hs]
    infer_instance
  have : IsNoetherian (pullback Y.s (spMap β)) := {}

  -- Flatness lifts the generic point of the base to a generalization of v.
  let z : Sp c.F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum c.F)
  have hz : (spMap β z).asIdeal = ⊥ := by
    change RingHom.ker β = ⊥
    exact (RingHom.injective_iff_ker_eq_bot β).mp (IsFractionRing.injective O c.F)
  have hspec : spMap β z ⤳ Y.s v := by
    apply (PrimeSpectrum.le_iff_specializes _ _).mp
    change (spMap β z).asIdeal ≤ (Y.s v).asIdeal
    rw [hz]
    exact bot_le
  obtain ⟨v', hv'v, hv'⟩ := Flat.generalizingMap Y.s hspec
  rw [generic_max hv hv'v] at hv'
  obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback v z hv'
  -- Every generalization of q has the same image, and the projection is injective.
  have hqmax : ∀ q', q' ⤳ q → q' = q := by
    intro q' hq'
    apply (pullback.fst Y.s (spMap β)).isEmbedding.injective
    rw [hq]
    exact generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)
  obtain ⟨w, hw⟩ := mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax
  exact ⟨w, by rw [Model.j, Scheme.Hom.comp_apply, hw, hq]⟩

end GlobalTheory.CompanionTheory.Ar.M0
