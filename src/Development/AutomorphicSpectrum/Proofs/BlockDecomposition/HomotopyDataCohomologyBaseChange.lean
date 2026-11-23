module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
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

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.PerfVB.ContrBC

theorem nonempty_Hc_equiv_of_contraction {S A B C H : Type} [CommRing S] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module S A] [Module S B] [Module S C]
    [Module S H] (f : A →ₗ[S] B) (g : B →ₗ[S] C) (j : H →ₗ[S] B) (π : B →ₗ[S] H)
    (h : B →ₗ[S] A) (h' : C →ₗ[S] B) (hπj : π ∘ₗ j = LinearMap.id) (hgj : g ∘ₗ j = 0)
    (hπf : π ∘ₗ f = 0) (hc : j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id) :
    Nonempty (Hc f g ≃ₗ[S] H) := by
  have hgj' : ∀ y, j y ∈ LinearMap.ker g := fun y => LinearMap.mem_ker.2 (LinearMap.congr_fun hgj y)
  have hπj' : ∀ y, π (j y) = y := fun y => LinearMap.congr_fun hπj y
  have hπf' : ∀ x, π (f x) = 0 := fun x => LinearMap.congr_fun hπf x
  have hc' : ∀ b, j (π b) + f (h b) + h' (g b) = b := fun b => LinearMap.congr_fun hc b
  have hle : Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) ≤
      LinearMap.ker (π ∘ₗ (LinearMap.ker g).subtype) := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨x, rfl⟩ : ∃ x, f x = z := LinearMap.mem_range.1 (Submodule.mem_comap.1 hzN)
    rw [LinearMap.mem_ker]
    exact hπf' x
  refine ⟨LinearEquiv.ofLinear (Submodule.liftQ _ (π ∘ₗ (LinearMap.ker g).subtype) hle)
    ((Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f)).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker g) j hgj') ?_ ?_⟩
  · refine LinearMap.ext fun y => ?_
    exact hπj' y
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f)) q
    have hz' : g z = 0 := LinearMap.mem_ker.1 hz
    have e : z = j (π z) + f (h z) := by
      have := hc' z
      rw [hz', map_zero, add_zero] at this
      exact this.symm
    have key : (⟨j (π z), hgj' (π z)⟩ : LinearMap.ker g) - ⟨z, hz⟩ ∈
        Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) := by
      refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨-h z, ?_⟩)
      change f (-h z) = j (π z) - z
      calc f (-h z) = -f (h z) := map_neg _ _
        _ = j (π z) - (j (π z) + f (h z)) := by abel
        _ = j (π z) - z := by rw [← e]
    exact (Submodule.Quotient.eq _).2 key

theorem nonempty_Hc_baseChange_equiv (R A B C H S : Type) [CommRing R] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C]
    [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B)
    (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B) (_hgf : g ∘ₗ f = 0)
    (hπj : π ∘ₗ j = LinearMap.id) (hgj : g ∘ₗ j = 0) (hπf : π ∘ₗ f = 0)
    (hc : j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id) :
    Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  refine nonempty_Hc_equiv_of_contraction (f.baseChange S) (g.baseChange S) (j.baseChange S)
    (π.baseChange S) (h.baseChange S) (h'.baseChange S) ?_ ?_ ?_ ?_
  · rw [← LinearMap.baseChange_comp, hπj, LinearMap.baseChange_id]
  · rw [← LinearMap.baseChange_comp, hgj, LinearMap.baseChange_zero]
  · rw [← LinearMap.baseChange_comp, hπf, LinearMap.baseChange_zero]
  · rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_add, ← LinearMap.baseChange_add, hc, LinearMap.baseChange_id]

end GlobalTheory.CompanionTheory.PerfVB.ContrBC
