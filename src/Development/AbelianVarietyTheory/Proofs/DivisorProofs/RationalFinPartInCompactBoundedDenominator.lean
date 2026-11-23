module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntegralOfMemIntAE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.BoundedDen

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → Af D.host.F ⊗[D.host.F] D.host.E) = fun z => (e z).2 := by
    funext z; exact ((he z).2).symm
  rw [this]
  exact continuous_snd.comp hc



theorem bounded_den : ∀ (D : D7) (K : Set (AE D)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ k ∈ K, ∀ x : D.host.E,
    finPart D (incA D x) = finPart D k → IsIntegral ℤ ((L : D.host.E) * x) := by
  intro D K hK
  let U : AddSubgroup (AE D) := (intAE D).comap (finPart D).toAddMonoidHom
  have hU : IsOpen (U : Set (AE D)) :=
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_finPart D)
  obtain ⟨n, hn⟩ := GlobalTheory.CondBound.exists_small D K hK U hU
  refine ⟨n.factorial, Nat.factorial_pos n, fun k hk x hx => ?_⟩
  have h := hn k hk
  have h2 : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) ∈ intAE D := by
    have e : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) =
        finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * k) := by
      rw [map_mul (incA D), map_mul (finPart D), map_mul (finPart D), hx, GlobalTheory.CondBound.finPart_r]
    rw [e]; exact h
  obtain ⟨y, hy⟩ := GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h2
  have e2 : (((n.factorial : ℕ) : D.host.E) * x) = (y : D.host.E) := hy.symm
  rw [e2]
  exact NumberField.RingOfIntegers.isIntegral_coe y

end GlobalTheory.BoundedDen
