module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoefRestrictSmallCoverInjectiveStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PdChern

theorem restrict_triv_eq_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ z : SecondDeRham s, IsChern (dp0 R) s L z → (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).pull2 z = 0 := by
  intro R _ X s L hL z hz
  obtain ⟨i, hi, u, ℓ, -, hℓ, hz⟩ := hz
  obtain ⟨c, rfl⟩ := H2.mk_surjective _ z
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨f, hf⟩ := hz
  apply GlobalTheory.T.coef_restrict_small_cover_injective R X s L.ι L.U hL.cover
  rw [map_zero, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
  let P : ObjectProperty (IsTriv s).FullSubcategory :=
    fun T : (IsTriv s).FullSubcategory => IsSmall (dp0 R) s L.U T.obj
  let F : P.FullSubcategory ⥤ (IsSmall (dp0 R) s L.U).FullSubcategory :=
    ObjectProperty.lift _ (P.ι ⋙ (IsTriv s).ι) (fun T => T.property)
  refine ⟨fun T T' φ => f (F.obj T) (F.obj T') (F.map φ), ?_⟩
  funext T T' T'' φ ψ
  have h := congrFun (congrFun (congrFun (congrFun (congrFun hf (F.obj T)) (F.obj T'))
    (F.obj T'')) (F.map φ)) (F.map ψ)
  have h0 : (ℓ.1 (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ) : T''.obj.obj.B) = 0 := by
    have hm : (ℓ.1 (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ) : T''.obj.obj.B) ∈
      T''.obj.obj.J := (hℓ (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ)).1
    have e : T''.obj.obj.J = ⊥ := T''.obj.property
    rw [e] at hm
    exact Ideal.mem_bot.1 hm
  exact h.trans (sub_eq_self.2 h0)

end GlobalTheory.CompanionTheory.PdChern
