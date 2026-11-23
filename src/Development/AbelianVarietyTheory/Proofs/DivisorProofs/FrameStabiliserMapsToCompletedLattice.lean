module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem stab_hatL_mapsTo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Formalism.L2.DIV.IsFrame β Λ → ∀ x ∈ Formalism.L2.DIV.St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  intro hF x hx v hv
  obtain ⟨y, rfl⟩ := hx
  have hw := (hF v).1 hv
  refine (hF _).2 fun i => ?_
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map (Formalism.L2.Herm.intAf F E).subtype with hY
  have hval : ((Formalism.L2.DIV.frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) =
      (β : Matrix (Fin n) (Fin n) _) * Y * ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
    simp only [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Units.val_mul]
    rfl
  have hmv : ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((Formalism.L2.DIV.frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ v) =
      Y *ᵥ (((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ v) := by
    rw [hval, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  rw [hmv]
  simp only [Matrix.mulVec, dotProduct]
  refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
  simp only [hY, Matrix.map_apply]
  exact (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j |>.2

end GlobalTheory
