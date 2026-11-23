module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
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

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_homLoc_pieces_compatible : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module (MvPolynomial ι A) M] [IsScalarTower A (MvPolynomial ι A) M] (ℳ : ℤ → Submodule A M) [PolyGradedSMul ι ℳ] [DirectSum.Decomposition ℳ] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S') (ev : ∀ I : Finset ι, I.Nonempty → M →ₗ[MvPolynomial ι A] P I), (∀ I hI, IsGradedMap ℳ (𝒢 I) (ev I hI)) → (∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) m, res I J h (ev I hI m) = ev J hJ m) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ I (hI : I.Nonempty) (m : M), ev I hI m = 0 → ∃ l : ℕ, xProd A I ^ l • m = 0) → (∀ I (hI : I.Nonempty) (f : P I), ∃ (l : ℕ) (m : M), ev I hI m = xProd A I ^ l • f) → ∀ t : ℤ, ∃ φ : ∀ I : Finset ι, I.Nonempty → (homLoc ℳ I t →ₗ[A] 𝒢 I t), (∀ I hI, Function.Bijective (φ I hI)) ∧ ∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (z : homLoc ℳ I t), (φ J hJ (homLocRes ℳ h t z) : P J) = res I J h (φ I hI z : P I) := by
  intro ι _ A _ M _ _ _ _ ℳ _ _ P _ _ _ _ 𝒢 _ _ res ev hgr hres hX hker hcok t
  have key : ∀ (I : Finset ι) (hI : I.Nonempty), ∃ φ : homLoc ℳ I t →ₗ[A] 𝒢 I t,
      Function.Bijective φ ∧ ∀ (z : homLoc ℳ I t) (k : ℕ) (m : M),
        awayFrac M (xProd A I) k m = z → xProd A I ^ k • (φ z : P I) = ev I hI m := by
    intro I hI
    exact exists_homLoc_bijective_of (hgr I hI) I
      (xProd_smul_bijective_of I fun i hi => hX i I hi)
      (fun _ y _ hy => hker I hI y hy) (fun _ a _ => hcok I hI a) t
  choose φ hφbij hφ using key
  refine ⟨φ, hφbij, ?_⟩
  intro I J hI hJ h z
  have hb : Function.Bijective fun x : P J => xProd A J • x :=
    xProd_smul_bijective_of J fun i hi => hX i J hi
  have hinj : ∀ (n : ℕ) (x y : P J), xProd A J ^ n • x = xProd A J ^ n • y → x = y := by
    intro n
    induction n with
    | zero => intro x y hxy; simpa using hxy
    | succ n ih =>
      intro x y hxy
      apply ih
      apply hb.1
      show xProd A J • (xProd A J ^ n • x) = xProd A J • (xProd A J ^ n • y)
      rw [← mul_smul, ← mul_smul, ← pow_succ']
      exact hxy
  obtain ⟨k, m, hkm⟩ := exists_awayFrac (z : LocalizedModule.Away (xProd A I) M)
  have hc : xProd A J = (∏ i ∈ J \ I, (MvPolynomial.X i : MvPolynomial ι A)) * xProd A I :=
    (Finset.prod_sdiff h).symm
  have hz : (homLocRes ℳ h t z : LocalizedModule.Away (xProd A J) M) =
      awayFrac M (xProd A J) k ((∏ i ∈ J \ I, (MvPolynomial.X i : MvPolynomial ι A)) ^ k • m) := by
    rw [coe_homLocRes, ← hkm]
    exact locRes_awayFrac MvPolynomial.X h (Finset.prod_sdiff h).symm k m
  have h1 := hφ I hI z k m hkm
  have h2 := hφ J hJ (homLocRes ℳ h t z) k _ hz.symm
  apply hinj k
  rw [h2, map_smul, ← hres I J hI hJ h m, ← h1, map_smul, ← mul_smul, ← mul_pow, hc]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
