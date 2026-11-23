import Formalism.SizeWindowBrackets.ChainSlopeWindows.SlopeInequalityOfLattices
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruenceIntegrated
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp

/-!
# Faithful lattice-to-arithmetic handoff for the sharp integrated loss

Reuse the *original* `LatGeom`, `LatNum`, ramified-frame compression,
and per-unit lattice identities. The strengthened conclusion changes only
the integrated input shortfall from the old logarithmic envelope to the
kernel-checked harmonic term.

No replacement of data, axiom, or assumption of `Data.SlopeIneqIntegrated`.
-/

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates

theorem integrated_flat_lattice_from_source :
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → FrameDeviationLinear Ball γ e → 0 ≤ e → e ≤ 1 / 4 → FrameTraceRatioLinear Ball γ η → 0 ≤ η →
    s - (1 - δ)⁻¹ * ((η + 4 * Real.sqrt e) * HH + 4 * (u * HH / (u + HH)))
      ≤ muDef b' X' cc := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ hG hN hγ hF2 he he4 hF1 hη
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hG
  obtain ⟨n1, n2, n3, n4, n5⟩ := hN
  exact frame_theorem_integrated K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ g1 g2 g3 g4 g5 g6
    g7 g8 g9 g10 g11 n1 n2 n3 n4 n5 g12 g13 g14 g15 hγ hF2 he he4 hF1 hη

theorem integrated_ramification_from_source :
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ)
    (ιf : I → Type) [∀ i, Fintype (ιf i)] [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ) (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (s u HH δ Dstar sg η0 η1 e0 de : ℝ),
    LatGeom b' X' cc b X N B h v Y Y' Ball δ → LatNum b' X' cc b X N h s u HH →
    (∀ i, 0 < γ i) → (∀ i, Ball i = Bf i * Vr i) → (∀ i, (Vr i)ᴴ * Vr i = 1) →
    0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ RsG ιf →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 →
    ∑ i, ((Fintype.card (ιf i) : ℝ) - (Fintype.card (ι i) : ℝ)) ≤ de * RsG ιf →
    InputSG Bf γ Dstar η0 η1 e0 →
    s - Real.log (Fintype.card I : ℝ) -
      (1 - δ)⁻¹ * (4 * (u * HH / (u + HH))
        + ((5 * sg + 3 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * HH)
      ≤ muDef b' X' cc := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ ιf _ _ Bf Vr s u HH δ Dstar sg η0 η1 e0 de hG hN hγ hBV hV hD hsg hsg20 hR h0 h0' h1 he0
    hse hde hde4 hcor hS
  obtain ⟨f1, f2, he, -⟩ := ramification_linear_case_holds I (κ ⊕ κ₁) ιf ι Bf Vr γ Dstar sg η0 η1 e0 de hV
    (fun i => (hγ i).le) hD hsg hsg20 hR h0 h0' h1 he0 hse hde hde4 hcor hS
  have hB : Ball = fun i => Bf i * Vr i := funext hBV
  rw [← hB] at f1 f2
  have hsharp := integrated_flat_lattice_from_source K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH
    (2 * e0) (5 * sg + 3 * Real.sqrt de) δ hG hN hγ f2 (by positivity) he f1 (by positivity)
  have hI : (1 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hlog : 0 ≤ Real.log (Fintype.card I : ℝ) := Real.log_nonneg hI
  linarith

end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
