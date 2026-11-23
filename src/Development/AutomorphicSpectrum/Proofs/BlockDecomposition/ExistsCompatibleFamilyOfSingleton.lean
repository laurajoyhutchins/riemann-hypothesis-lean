module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
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
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_compatible_family_of_singleton : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) := by
  intro ι _ _ A _ P _ _ res hid hcomp hker hext i f
  have inj : ∀ (S S' : Finset ι) (h : S ⊆ S'), S = S' → Function.Injective (res S S' h) := by
    rintro S _ h rfl a b hab
    rwa [hid, hid] at hab
  set x : MvPolynomial ι A := MvPolynomial.X i with hx

  have h1 : ∀ j : ι, ∃ (k : ℕ) (g : P {j}),
      res {j} {i, j} (sub_pair_right i j) g = x ^ k • res {i} {i, j} (sub_pair_left i j) f := by
    intro j
    obtain ⟨k, g, hg⟩ := hext {j} i (res {i} {i, j} (sub_pair_left i j) f)
      (Finset.singleton_nonempty j)
    exact ⟨k, g, hg⟩
  choose k g hg using h1
  set K : ℕ := Finset.univ.sup k with hK
  have hkK : ∀ j, k j ≤ K := fun j => Finset.le_sup (Finset.mem_univ j)
  obtain ⟨f', hres⟩ : ∃ f' : ∀ j : ι, P {j}, ∀ j, res {j} {i, j} (sub_pair_right i j) (f' j)
      = x ^ K • res {i} {i, j} (sub_pair_left i j) f := by
    refine ⟨fun j => x ^ (K - k j) • g j, fun j => ?_⟩
    simp only [map_smul, hg, smul_smul, ← pow_add, Nat.sub_add_cancel (hkK j)]

  have htriple : ∀ (j : ι) (T : Finset ι) (hT : ({i, j} : Finset ι) ⊆ T),
      res {j} T ((sub_pair_right i j).trans hT) (f' j)
        = x ^ K • res {i} T ((sub_pair_left i j).trans hT) f := by
    intro j T hT
    rw [← hcomp _ _ _ (sub_pair_right i j) hT, hres, map_smul, hcomp]
  have h2 : ∀ j l : ι, ∃ n : ℕ, x ^ n • (res {j} {j, l} (sub_pair_left j l) (f' j)
      - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
    intro j l
    refine hker {j, l} i _ (Finset.insert_nonempty _ _) ?_
    have hj : ({i, j} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_left j l)
    have hl : ({i, l} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_right j l)
    rw [map_sub, hcomp, hcomp, sub_eq_zero]
    have e1 := htriple j _ hj
    have e2 := htriple l _ hl
    exact e1.trans e2.symm
  choose n hn using h2
  set N' : ℕ := Finset.univ.sup (fun p : ι × ι => n p.1 p.2) with hN'
  have hnN : ∀ j l, n j l ≤ N' := fun j l =>
    Finset.le_sup (f := fun p : ι × ι => n p.1 p.2) (Finset.mem_univ (j, l))
  refine ⟨fun j => x ^ N' • f' j, N' + K, ?_, ?_⟩
  · intro j l
    have h0 : x ^ N' • (res {j} {j, l} (sub_pair_left j l) (f' j)
        - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
      rw [← Nat.sub_add_cancel (hnN j l), pow_add, mul_smul, hn, smul_zero]
    show res {j} {j, l} (sub_pair_left j l) (x ^ N' • f' j)
      = res {l} {j, l} (sub_pair_right j l) (x ^ N' • f' l)
    rw [map_smul, map_smul, ← sub_eq_zero, ← smul_sub]
    exact h0
  · have hii : ({i} : Finset ι) ⊆ {i, i} := sub_pair_left i i
    have hfi : f' i = x ^ K • f := by
      apply inj {i} {i, i} hii (Finset.pair_eq_singleton i).symm
      rw [map_smul]
      exact hres i
    show x ^ N' • f' i = x ^ (N' + K) • f
    rw [hfi, smul_smul, ← pow_add]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
