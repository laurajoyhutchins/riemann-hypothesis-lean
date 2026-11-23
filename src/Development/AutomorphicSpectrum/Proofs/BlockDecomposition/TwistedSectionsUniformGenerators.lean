module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistSectionsGenerateSubsheafStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheafStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSupStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeIdealPowerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMemStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
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

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem exists_alg_of_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ (n₁ : ℤ) (W : ∀ n : ℤ, Set Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ n e, W n ⊆ twSecs H n (S e)) → (∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W n, x - b ∈ twPow I H n P (e + 1)) → ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  intro A _ _ I X _ _ H hA P hP S hS n₁ W hW hgen
  have hH := hA.isLB
  let F : Set (Subobject P) := {B | (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ≤ S e}
  have h0 : (0 : Γ(GlobalTheory.twistZ P H n₁, ⊤)) ∈ twSecs H n₁ (S 0) := ⟨0, map_zero _⟩
  obtain ⟨b₀, hb₀, -⟩ := hgen n₁ le_rfl 0 0 h0
  have hF : F.Nonempty :=
    ⟨genSub hH n₁ b₀, GlobalTheory.T.generated_subsheaf_quasicoherent hH hP.1 n₁ b₀, fun e => GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem hH (S e) n₁ b₀ (hW n₁ e hb₀)⟩
  obtain ⟨M, ⟨hMq, hMS⟩, hMmax⟩ := GlobalTheory.T.coherent_noetherian_maximal_subsheaf hP F hF (fun B hB => hB.1)
  have hgenM : ∀ n, ∀ b ∈ W n, genSub hH n b ≤ M := by
    intro n b hb
    have hmem : M ⊔ genSub hH n b ∈ F :=
      ⟨(GlobalTheory.T.quasicoherent_sup_sections hP.1 M (genSub hH n b) hMq (GlobalTheory.T.generated_subsheaf_quasicoherent hH hP.1 n b)).1,
        fun e => sup_le (hMS e) (GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem hH (S e) n b (hW n e hb))⟩
    rw [← hMmax _ hmem le_sup_left]
    exact le_sup_right
  refine ⟨M, hMq, fun e => le_antisymm (sup_le (hMS e) (hS.pow_le e)) ?_⟩
  have hSe : IsCoherent (S e : X.Modules) := GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.ample_twist_sections_generate_subsheaf hA (S e) hSe
  refine hn₀ (max n₀ n₁) (le_max_left _ _) _ fun x hx => ?_
  obtain ⟨b, hb, hxb⟩ := hgen (max n₀ n₁) (le_max_right _ _) e x hx
  rw [← add_sub_cancel b x]
  exact (GlobalTheory.T.generated_subsheaf_add_le_sup hH _ b (x - b)).trans (sup_le_sup (hgenM _ b hb) (GlobalTheory.T.generated_subsheaf_le_ideal_power I hH hP.1 _ _ _ hxb))

end GlobalTheory.CompanionTheory.GE.TwGen
