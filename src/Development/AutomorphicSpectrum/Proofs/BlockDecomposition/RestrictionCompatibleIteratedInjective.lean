module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.IterInj

theorem restriction_compatible_iterated_injective (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type)
    [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)]
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (hid : ∀ S (h : S ⊆ S) a, res S S h a = a)
    (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    (hloc : ∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty →
      res S (insert j S) (Finset.subset_insert j S) a = 0 →
      ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0)
    (S : Finset ι) (hS : S.Nonempty) (T : Finset ι) :
    ∀ (S' : Finset ι) (_ : S' = S ∪ T) (h : S ⊆ S') (a : P S), res S S' h a = 0 →
      ∃ l : ℕ, xProd A T ^ l • a = 0 := by
  induction T using Finset.induction_on with
  | empty =>
    intro S' hS' h a ha
    have : S' = S := by simpa using hS'
    subst this
    refine ⟨0, ?_⟩
    rw [hid] at ha
    simpa using ha
  | insert j T' hj ih =>
    intro S' hS' h a ha
    have hS'' : S' = insert j (S ∪ T') := by
      rw [hS', Finset.union_insert]
    subst hS''
    have hsub : S ⊆ S ∪ T' := Finset.subset_union_left
    have hb : res (S ∪ T') (insert j (S ∪ T')) (Finset.subset_insert j _) (res S (S ∪ T') hsub a) = 0 := by
      rw [hcomp]; exact ha
    obtain ⟨k, hk⟩ := hloc (S ∪ T') j _ (hS.mono hsub) hb
    have h2 : res S (S ∪ T') hsub ((MvPolynomial.X j : MvPolynomial ι A) ^ k • a) = 0 := by
      rw [map_smul]; exact hk
    obtain ⟨l, hl⟩ := ih (S ∪ T') rfl hsub _ h2
    refine ⟨k + l, ?_⟩
    have hx : xProd A (insert j T') = MvPolynomial.X j * xProd A T' := by
      simp [xProd, Finset.prod_insert hj]
    have : (xProd A (insert j T')) ^ (k + l) =
        ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T' ^ k) *
          (xProd A T' ^ l * (MvPolynomial.X j : MvPolynomial ι A) ^ k) := by
      rw [hx, mul_pow]; ring
    rw [this, mul_smul _ (xProd A T' ^ l * _), mul_smul (xProd A T' ^ l), hl, smul_zero]

theorem iter_localisation_injective : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) := by
  intro ι _ A _ P _ _ res hid hcomp hloc T S a hS ha
  exact restriction_compatible_iterated_injective ι A P res hid hcomp hloc S hS T (S ∪ T) rfl Finset.subset_union_left a ha

end GlobalTheory.CompanionTheory.FormalAlg.IterInj
