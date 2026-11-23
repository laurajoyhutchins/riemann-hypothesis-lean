module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Present

def toModPullZPowIso {X Y : Scheme.{0}} {L : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hL : L.IsLB) (f : Y ⟶ X) (m : ℤ) :
    GlobalTheory.LB.toMod ((GlobalTheory.lbZPow L m).pull f) ≅ GlobalTheory.LB.toMod (GlobalTheory.lbZPow (L.pull f) m) :=
  (GlobalTheory.Twist.unitTwistIso _).symm ≪≫ (GlobalTheory.Twist.twistZPullIso f hL _ m).symm ≪≫ GlobalTheory.Twist.unitTwistIso _

theorem exists_coherent_epi_restrict {X : Scheme.{0}} [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) (O : X.Opens) (E : (O : Scheme.{0}).Modules) (hE : IsCoherent E) :
    ∃ P : X.Modules, IsCoherent P ∧ ∃ f : P.restrict O.ι ⟶ E, Epi f := by
  haveI : CompactSpace (O : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (O : Set X))
  haveI : GlobalTheory.QCoh.IsFiniteQC E := ⟨hE.1, hE.2⟩
  have hA := hH.pull_of_isOpenImmersion O.ι
  obtain ⟨n, k, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := GlobalTheory.Twist.isLB_lbZPow hH.isLB (-n)
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))) := (GlobalTheory.VB.isVB_toMod hL).isFiniteQC
  let P : X.Modules := ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))
  have hP : GlobalTheory.QCoh.IsFiniteQC P := inferInstance
  let e : P.restrict O.ι ≅ ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow (H.pull O.ι) (-n)) :=
    (Scheme.Modules.restrictFunctorIsoPullback O.ι).app P ≪≫
      PreservesCoproduct.iso (Scheme.Modules.pullback O.ι) _ ≪≫
      Sigma.mapIso (fun _ => GlobalTheory.LB.pullbackIso hL O.ι ≪≫ toModPullZPowIso hH.isLB O.ι (-n))
  exact ⟨P, ⟨hP.1, hP.2⟩, e.hom ≫ φ, epi_comp _ _⟩

end GlobalTheory.CompanionTheory.GE.Present
