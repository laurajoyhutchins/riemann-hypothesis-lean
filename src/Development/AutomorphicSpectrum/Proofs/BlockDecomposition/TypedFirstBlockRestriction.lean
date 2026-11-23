module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceL

theorem slice_typeF {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)) :
    IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W →
    ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)),
      IsOpen (K₁ : Set (GL (Fin r) (Af E))) ∧ FiniteDimensional ℂ W₁ ∧
      ∀ f ∈ typeF K W, ∀ y : GA E s,
        (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₁ W₁ := by
  intro hK hW
  have hcf : cf (r + s) k t = finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) := by
    rw [cf, infGL_comm]
  refine ⟨Slice1.levelOne s K t,
    W.map (LinearMap.funLeft ℂ ℂ fun κ : Kinf E r => Slice1.levK E r s κ * k),
    Slice1.isOpen_levelOne hK t, inferInstance, ?_⟩
  intro f hf y
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · have h := Slice1.lev_finGL_right g u y t (Unitary.toUnits k)
    have h' := hf.1 _ (Slice1.mem_levelOne.1 hu)
      (lev (Ad E) r s (g, y) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    rw [← h] at h'
    simpa only [hcf, mul_assoc] using h'
  · refine ⟨_, hf.2 (lev (Ad E) r s (g, y) * finGL E (r + s) t), ?_⟩
    funext κ
    have h := Slice1.lev_infGL_right g (Unitary.toUnits κ) y t (Unitary.toUnits k)
    have e : lev (Cinf E) r s (Unitary.toUnits κ, 1) * Unitary.toUnits k =
        Unitary.toUnits (Slice1.levK E r s κ * k) := by
      rw [map_mul, Slice1.toUnits_levK]
    rw [e] at h
    simp only [LinearMap.funLeft_apply, hcf]
    rw [← h]
    simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceL

end
