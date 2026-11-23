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
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_xProd_pow_smul_eq_ev : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (T S : Finset ι) (b : P (S ∪ T)), S.Nonempty → ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S (S ∪ T) Finset.subset_union_left)) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) → ∀ (I : Finset ι) (hI : I.Nonempty) (f : P I), ∃ (l : ℕ) (m : glue res), ev res I hI m = xProd A I ^ l • f := by
  intro ι _ A _ P _ _ _ _ res hcomp hsurj hfam I hI f
  classical
  obtain ⟨i, hi⟩ := hI
  have hsub : ({i} : Finset ι) ⊆ I := Finset.singleton_subset_iff.2 hi
  have key : ∀ (J : Finset ι) (hJ : {i} ∪ I = J) (g : P J),
      ∃ (l : ℕ) (a : P {i}), res {i} J (hJ ▸ Finset.subset_union_left) a = xProd A I ^ l • g := by
    intro J hJ
    subst hJ
    intro g
    obtain ⟨l, a, ha⟩ := hsurj I {i} g ⟨i, Finset.mem_singleton_self i⟩
    exact ⟨l, a, ha⟩
  obtain ⟨l, a, ha⟩ := key I (Finset.union_eq_right.2 hsub) f
  obtain ⟨c, N, hc, hci⟩ := hfam i a
  obtain ⟨q, hq⟩ : (MvPolynomial.X i : MvPolynomial ι A) ∣ xProd A I := by
    simpa [xProd] using Finset.dvd_prod_of_mem (fun j => (MvPolynomial.X j : MvPolynomial ι A)) hi
  refine ⟨N + l, q ^ N • ⟨c, mem_glue.2 hc⟩, ?_⟩
  rw [map_smul, ev_eq hcomp ⟨i, hi⟩ hi]
  change q ^ N • res {i} I hsub (c i) = _
  rw [hci, map_smul, show res {i} I hsub a = xProd A I ^ l • f from ha, hq, smul_smul, smul_smul,
    pow_add, mul_pow]
  congr 1
  ring

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
