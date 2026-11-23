module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
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
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem smul_eq_zero_of_ev_eq_zero : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) → ∀ (I : Finset ι) (hI : I.Nonempty) (m : glue res), ev res I hI m = 0 → ∃ l : ℕ, xProd A I ^ l • m = 0 := by
  intro ι _ _ A _ P _ _ _ _ res hcomp H I hI m hm
  have key : ∀ i, res {i} ({i} ∪ I) Finset.subset_union_left (m.1 i) = 0 := by
    intro i
    have hJ : ({i} ∪ I).Nonempty := ⟨i, Finset.mem_union_left I (Finset.mem_singleton_self i)⟩
    have h1 := ev_eq hcomp hJ (Finset.mem_union_left I (Finset.mem_singleton_self i)) m
    have h2 := res_ev hcomp hI hJ Finset.subset_union_right m
    rw [hm, map_zero] at h2
    exact h1.symm.trans h2.symm
  choose L hL using fun i => H I {i} (m.1 i) (Finset.singleton_nonempty i) (key i)
  refine ⟨∑ j, L j, ?_⟩
  apply Subtype.ext
  funext i
  simp only [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_zero, Pi.zero_apply]
  have hsum : ∑ j, L j = (∑ j, L j - L i) + L i :=
    (Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm
  rw [hsum, pow_add, mul_smul, hL i, smul_zero]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
