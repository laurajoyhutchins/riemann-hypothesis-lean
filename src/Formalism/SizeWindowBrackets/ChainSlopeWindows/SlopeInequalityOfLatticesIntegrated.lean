import Formalism.SizeWindowBrackets.ChainSlopeWindows.SlopeInequalityOfLattices
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp
import Formalism.RankGapBounds.RankGapProofs.IntegratedSlopeError

/-!
# Original lattice witnesses imply the integrated arithmetic slope estimate

Unlike a numerical interface that simply assumes `Data.SlopeIneqIntegrated`,
this proof uses the **same** `HypS` lattice witnesses that feed the
published logarithmic slope inequality. It reuses the verified ramification
and slope normalization bridges and invokes `frame_theorem_integrated`.
No new geometric, analytic, or arithmetic assumption is added.
-/

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer

open Formalism.RankGapBounds.WeightedMeanData
open Formalism.LFunctionChainParameters.WeightedSlopeBounds

variable {U0 : Type} [Fintype U0] {W : U0 → Type}
  [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f)

/-- This is the missing source-level bridge for one actual arithmetic
lattice family, with the unchanged `HypS` premises. -/
theorem integrated_slope_of_HypS
    (u0 : U0) {K Wd κ κ₁ : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K]
    [AddCommGroup Wd] [Module K Wd] [Module (𝓞 K) Wd]
    [IsScalarTower (𝓞 K) K Wd]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁]
    {V ι : W u0 → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)]
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i))
    (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i))
    (B : ∀ i, V i →ₗ[K] Wd) (v : InfinitePlace K)
    (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ)
    (γ : W u0 → ℝ)
    {ιf : W u0 → Type} [∀ i, Fintype (ιf i)]
    [∀ i, DecidableEq (ιf i)]
    (Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ)
    (Vr : ∀ i, Matrix (ιf i) (ι i) ℂ)
    (Dstar sg η0 η1 e0 de : ℝ)
    (hyp : HypS D u0 b' X' cc b X N B v Y Y' Ball γ Bf Vr
      Dstar sg η0 η1 e0 de)
    (hSide : SideF D u0) :
    D.s u0 - Real.log (Fintype.card (W u0) : ℝ) -
      (1 - D.del u0)⁻¹ *
        (4 * (D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0)) +
          (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤
      D.muCC u0 := by
  classical
  obtain ⟨hId, hG, hγ, hBV, hV, hD, hsg, hsg20, hR,
    h0, h0', h1, he0, hse, hde, hde4, hcor, hS, hη, he⟩ := hyp
  have hN := lattice_numerics D u0 b' X' cc b X N B v Y Y' Ball
    hId hG hSide
  obtain ⟨f1, f2, heBound, -⟩ :=
    MatrixLatticeEstimates.ramification_linear_case_holds
      (W u0) (κ ⊕ κ₁) ιf ι Bf Vr γ Dstar sg η0 η1 e0 de
      hV (fun i => (hγ i).le) hD hsg hsg20 hR
      h0 h0' h1 he0 hse hde hde4 hcor hS
  have hBall : Ball = fun i => Bf i * Vr i := funext hBV
  rw [← hBall] at f1 f2
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
    g11, g12, g13, g14, g15⟩ := hG
  obtain ⟨n1, n2, n3, n4, n5⟩ := hN
  have hIntegrated :=
    frame_theorem_integrated K Wd κ κ₁ (W u0) V ι
      b' X' cc b X N B (D.h u0) v Y Y' Ball γ
      (D.s u0) (D.uF u0) (D.HH u0)
      (2 * e0) (5 * sg + 3 * Real.sqrt de) (D.del u0)
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
      n1 n2 n3 n4 n5 g12 g13 g14 g15 hγ f2
      (by positivity) heBound f1 (by positivity)
  rw [← hId.2.2.2.1, ← hη, ← he] at hIntegrated
  have hReorder :
      D.s u0 - (1 - D.del u0)⁻¹ *
        ((D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 +
          4 * (D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0))) =
      D.s u0 - (1 - D.del u0)⁻¹ *
        (4 * (D.uF u0 * D.HH u0 / (D.uF u0 + D.HH u0)) +
          (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) := by
    ring
  rw [hReorder] at hIntegrated
  have hCard : 1 ≤ Fintype.card (W u0) := by
    have hp : 0 < Fintype.card (W u0) := Fintype.card_pos
    omega
  have hLog : 0 ≤ Real.log (Fintype.card (W u0) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hCard)
  linarith

#print axioms Formalism.LFunctionChainParameters.LatticeToWeightTransfer.integrated_slope_of_HypS

end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
