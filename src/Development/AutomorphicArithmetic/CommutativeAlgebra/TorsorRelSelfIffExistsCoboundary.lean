module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.PicData
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

open CategoryTheory TensorProduct UpperTheory.PicD

private theorem unit_of_surj {A C : Type} [CommRing A] [CommRing C] [Algebra A C] (t : A →ₗ[A] C)
    (hs : Function.Surjective (LinearMap.liftBaseChange C t)) : ∃ c : C, c * t 1 = 1 := by
  have key : ∀ x : C ⊗[A] A, ∃ c : C, LinearMap.liftBaseChange C t x = c * t 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a =>
      refine ⟨c * algebraMap A C a, ?_⟩
      rw [LinearMap.liftBaseChange_tmul]
      have e : t a = a • t 1 := by rw [← map_smul, smul_eq_mul, mul_one]
      rw [e]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def, smul_eq_mul]
      ring
    | add x y hx hy =>
      obtain ⟨c1, h1⟩ := hx
      obtain ⟨c2, h2⟩ := hy
      exact ⟨c1 + c2, by rw [map_add (f := _), h1, h2, add_mul]⟩
  obtain ⟨x, hx⟩ := hs 1
  obtain ⟨c, hc⟩ := key x
  exact ⟨c, by rw [← hc, hx]⟩

private theorem tensor_inclusions_eq (A : Type) [CommRing A] : (i1 A A).toRingHom = (i2 A A).toRingHom := by
  ext a
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]
  calc a ⊗ₜ[A] (1 : A) = (a • (1 : A)) ⊗ₜ[A] (1 : A) := by rw [smul_eq_mul, mul_one]
    _ = (1 : A) ⊗ₜ[A] (a • (1 : A)) := TensorProduct.smul_tmul _ _ _
    _ = (1 : A) ⊗ₜ[A] a := by rw [smul_eq_mul, mul_one]

theorem UpperTheory.torsorRel_self_iff_exists_coboundary :
    ∀ (P : Data) (A : Type) [CommRing A] (z : P.S1.obj (CommRingCat.of A)),
        P.Rel z A ↔ ∃ y : P.S0.obj (CommRingCat.of A), P.dd A y = z := by
  intro P A _ z
  constructor
  · rintro ⟨C, _, _, _, _, w, g, t, hT⟩
    obtain ⟨c', hc'⟩ := unit_of_surj t hT.bij.2
    let u : Cˣ := ⟨t 1, c', by rw [mul_comm, hc'], hc'⟩
    have hgu : Units.map ((i1 A C).toRingHom : C →* C ⊗[A] C) u * g
        = Units.map ((i2 A C).toRingHom : C →* C ⊗[A] C) u := by
      ext
      have h := hT.ht 1
      rw [Algebra.smul_def] at h
      simpa using h
    have hun : P.un g = P.r0 (i2 A C).toRingHom (P.un u) - P.r0 (i1 A C).toRingHom (P.un u) := by
      rw [Data.mapDegZero_ofUnit, Data.mapDegZero_ofUnit, eq_sub_iff_add_eq, add_comm, ← Data.un_mul]
      congr 1
    have hg := hT.hg
    rw [hun] at hg
    obtain ⟨y, hy⟩ := P.glue A C (w - P.un u) (by
      change P.r0 (i1 A C).toRingHom (w - P.un u) = P.r0 (i2 A C).toRingHom (w - P.un u)
      rw [map_sub, map_sub, sub_eq_sub_iff_sub_eq_sub,
        ← neg_sub (P.r0 (i2 A C).toRingHom w), ← hg, neg_sub])
    have hy' : P.r0 (algebraMap A C) y = w - P.un u := hy
    refine ⟨y, P.sep A C ?_⟩
    change P.r1 (algebraMap A C) (P.dd A y) = P.r1 (algebraMap A C) z
    rw [← Data.diff_mapDegZero, hy', map_sub, hT.dw]
    have e : P.dd C (P.un u) = 0 := (Data.dd_eq_zero P _).mpr ⟨u, rfl⟩
    rw [e, sub_zero]
  · rintro ⟨y, rfl⟩
    refine ⟨A, inferInstance, Algebra.id A, inferInstance, inferInstance,
      P.r0 (algebraMap A A) y, 1, LinearMap.id, ?_⟩
    refine ⟨Data.diff_mapDegZero P _ y, ?_, ?_, ?_⟩
    · rw [Data.un_one, tensor_inclusions_eq, sub_self]
    · intro m
      have e := congrArg (fun f => f m) (tensor_inclusions_eq A)
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply] at e
      rw [LinearMap.id_apply, Units.val_one, Algebra.smul_def, mul_one]
      exact e
    · have e : ⇑(LinearMap.liftBaseChange A (LinearMap.id : A →ₗ[A] A)) = ⇑(TensorProduct.lid A A) := by
        funext x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      rw [e]
      exact (TensorProduct.lid A A).bijective
