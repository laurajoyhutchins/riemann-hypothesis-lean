module

public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace HChar

variable {L : Type} [Field L] [NumberField L]

theorem inf_eq_one_of_order [_root_.NumberField.IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) (k : Lˣ) :
    χ.inf k = 1 := by

  have hpow : ∀ (w : InfinitePlace L) (u : (w.Completion)ˣ), ∃ y : (w.Completion)ˣ, y ^ n = u := by
    intro w u
    let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (u : w.Completion)) hn
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact u.ne_zero (e.injective (by rw [map_zero]; exact hz.symm))
    refine ⟨Units.mk0 (e.symm z) (by simpa using hz0), Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, RingEquiv.symm_apply_apply]
  have hχn : ∀ x, ((χ : Ideles L →* ℂˣ) x) ^ n = 1 := by
    intro x
    have h' := congrArg (fun ψ : HChar L => (ψ : Ideles L →* ℂˣ) x) (show χ ^ n = 1 from h)
    first
      | simpa using h'
      | exact h'
  show (χ : Ideles L →* ℂˣ) (infDiag k) = 1
  have hp (s : Finset (InfinitePlace L)) :
      (∏ w ∈ s, (infIdele L w).comp (atInf w)) k =
        ∏ w ∈ s, (infIdele L w) (atInf w k) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, ih, MonoidHom.mul_apply]
  rw [infDiag, hp, map_prod]
  apply Finset.prod_eq_one
  intro w _
  obtain ⟨y, hy⟩ := hpow w (atInf w k)
  rw [← hy, map_pow, map_pow, hχn]

end HChar

section Frame

variable {D : D7} (C : CharFrame D)

end Frame

section Tup

variable {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

theorem TupTied.xi_unitary (μ : D.what₂.Tup) : (Tp.xi μ).IsUnitary := by
  obtain ⟨n, hn, h⟩ := Tp.xi_fin μ
  intro x
  have h' := congrArg (fun ψ : HChar D.host.E => (ψ : Ideles D.host.E →* ℂˣ) x) (show Tp.xi μ ^ n = 1 from h)
  have e : ((Tp.xi μ : Ideles D.host.E →* ℂˣ) x) ^ n = 1 := by
    first
      | simpa using h'
      | exact h'
  have e2 : ‖(((Tp.xi μ : Ideles D.host.E →* ℂˣ) x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp e2

theorem TupTied.tup_unitary (μ : D.what₂.Tup) (j : Fin D.R.m) : (Tp.tup μ j).IsUnitary := fun x => by
  show ‖((((C.mu0 j).1 x * (Tp.xi μ).1 x : ℂˣ)) : ℂ)‖ = 1
  rw [Units.val_mul, norm_mul, (C.isMu0 j).unitary x, Tp.xi_unitary μ x, one_mul]

end Tup

section TupAlg

variable {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

end TupAlg

section TupCsd

variable {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

end TupCsd

end Formalism.L2.Host
