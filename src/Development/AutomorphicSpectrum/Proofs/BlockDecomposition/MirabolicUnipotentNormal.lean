module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.UNorm

theorem mirProj_eq_one_of_mem {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) :
    mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) i.castSucc j.castSucc = _
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    u ∈ MirUin k n := by
  have hrow := (GlobalTheory.BZMir.mem_Mir_iff k (u : GL (Fin (n + 1)) k)).mp u.2
  have hrow' : ∀ j, ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      (Pi.single (Fin.last n) (1 : k) : Fin (n + 1) → k) j := by
    intro j
    rw [hrow]
    rfl
  have hblk : ∀ i j : Fin n,
      ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
        (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    exact congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hu
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n)), ?_⟩
  apply Units.ext
  ext i j
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n))))) i j = _
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, hrow']
    | cast j =>
      simp [GlobalTheory.BZMir.colMat, hrow', Matrix.one_apply, Pi.single_apply, Fin.castSucc_ne_last,
        (Fin.castSucc_ne_last j).symm]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last, hblk]

theorem mirUin_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  intro k _ _ _ _ n
  refine ⟨fun u hu g => ?_⟩
  apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, map_inv, GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirProj_eq_one_of_mem u hu,
    mul_one, mul_inv_cancel]

end GlobalTheory.CompanionTheory.LeibPhi.UNorm
