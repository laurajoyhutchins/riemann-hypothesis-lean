module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
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

universe u v

namespace GlobalTheory.CompanionTheory.BurnsideU

theorem mem_of_irred {K : Type u} {V : Type v} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf : f = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf]
    exact S.zero_mem

  have : IsScalarTower K S V := ⟨fun _ _ _ => rfl⟩
  have : Nontrivial (Submodule S V) := (Submodule.nontrivial_iff S).mpr hV

  have : IsSimpleModule S V :=
    { eq_bot_or_eq_top := fun N => by
        rcases hirr (N.restrictScalars K) (fun g hg v hv => N.smul_mem ⟨g, hg⟩ hv) with h | h
        · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).mp h)
        · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).mp h) }

  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K

  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g v => by
        obtain ⟨c, rfl⟩ := hschur.2 g
        change f ((algebraMap K (Module.End S V) c) v) = (algebraMap K (Module.End S V) c) (f v)
        simp [Module.algebraMap_end_apply, f.map_smul] }

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := V)
  obtain ⟨r, hr⟩ := jacobson_density F s
  have hfr : f = (r : Module.End K V) := by
    apply LinearMap.ext
    intro m
    have hm : m ∈ Submodule.span K (s : Set V) := hs ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact hr m hm
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add (f := _), map_add (f := _), h₁, h₂]
    | smul c _ _ h => rw [map_smul, map_smul, h]
  rw [hfr]
  exact r.2

theorem burnside_surj_of_irred {A : Type u} {V : Type v} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ :=
    by
    intro f
    have hf : f ∈ ρ.range :=
      mem_of_irred ρ.range (fun W hW => hirr W fun h w hw => hW (ρ h) ⟨h, rfl⟩ w hw) f
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range ρ).mp hf
    exact ⟨h, rfl⟩

end GlobalTheory.CompanionTheory.BurnsideU
