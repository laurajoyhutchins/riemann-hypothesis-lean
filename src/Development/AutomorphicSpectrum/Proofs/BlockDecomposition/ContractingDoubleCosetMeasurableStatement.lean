module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
public import GroundTheory.AutomorphicForms.GLnLocal
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetMeasurable
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
namespace ContractingCosetsPort
open ValuativeRel Matrix GroundTheory.Automorphic.GLnLocal
open GlobalTheory.CompanionTheory.ContractingCosets
variable {k : Type} [Field k] [ValuativeRel k]

theorem coe_leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : Matrix (Fin N) (Fin N) k) =
      diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective x
  obtain ⟨⟨b, l⟩, rfl⟩ := (stdBlocks d hd).surjective y
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      simp only [Zl.JC.zj, Zl.JC.blockIdx, Equiv.symm_apply_apply]
      split_ifs <;> simp
    · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨a, l⟩ := fun e =>
        hil (by simpa using (stdBlocks d hd).injective e)
      rw [diagonal_apply_ne _ hne]
      simp only [Zl.JC.zj]
      split_ifs
      · simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, diagonal_apply_ne _ hil]
      · simp [Matrix.one_apply_ne hil]
  · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨b, l⟩ := fun e =>
      hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
    rw [diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem le_of_mk_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hpos : ∀ a, 0 < d a) (t : kˣ)
    (ht : valuation k (t : k) < 1) (j : Fin h) (hj : j.val + 1 < h) (m : ℕ)
    {x y x' y' : GL (Fin N) k} (hx : x ∈ congruenceSubgroup k N m)
    (hy : y ∈ congruenceSubgroup k N m) (hx' : x' ∈ congruenceSubgroup k N m)
    (hy' : y' ∈ congruenceSubgroup k N m) {r r' : ℕ}
    (e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
      QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y')) :
    r' ≤ r := by
  have hz := QuotientGroup.eq.1 e
  have hK := congruenceSubgroup_le k N m
  have heq := eq_central_mul hz
  refine le_of_eq_central_mul (δ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1) t ht
    (fun i => ?_) (i₁ := stdBlocks d hd ⟨j, ⟨0, hpos j⟩⟩)
    (i₂ := stdBlocks d hd ⟨⟨j.val + 1, hj⟩, ⟨0, hpos _⟩⟩) ?_ ?_
    (coe_leviEmb_zj d hd t j)
    (mul_mem (inv_mem (hK hx')) (hK hx)) (mul_mem (hK hy) (inv_mem (hK hy'))) hz heq
  · by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · simp [Zl.JC.blockIdx]
  · have : ¬ (⟨j.val + 1, hj⟩ : Fin h) ≤ j := by
      rw [Fin.le_def]; simp
    simp [Zl.JC.blockIdx, this]

end ContractingCosetsPort


theorem _root_.GlobalTheory.T.contracting_double_coset_measurable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)], (∀ r : ℕ, MeasurableSet ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y})) ∧ Pairwise (Function.onFun Disjoint fun r : ℕ => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g | ∃ x ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, ∃ y ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd hpos t ht j hj m _ _ _
  refine ⟨fun r => ?_, fun r r' hne => ?_⟩
  · exact (QuotientGroup.isOpenMap_coe _
      (GlobalTheory.CompanionTheory.ContractingCosets.isOpen_doubleCoset _
        (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) _)).measurableSet
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, e₁⟩ ⟨_, ⟨x', hx', y', hy', rfl⟩, e₂⟩
    have e : (QuotientGroup.mk (x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y) : AdGL k N) =
        QuotientGroup.mk (x' * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r' * y') :=
      e₁.trans e₂.symm
    exact hne (le_antisymm
      (ContractingCosetsPort.le_of_mk_eq d hd hpos t ht j hj m hx' hy' hx hy e.symm)
      (ContractingCosetsPort.le_of_mk_eq d hd hpos t ht j hj m hx hy hx' hy' e))
