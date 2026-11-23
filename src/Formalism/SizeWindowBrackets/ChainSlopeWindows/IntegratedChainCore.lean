import Formalism.SizeWindowBrackets.ChainSlopeWindows.IntegratedInputs2Mean

/-!
# Original source chain with the integrated harmonic slope budget

The unchanged Chain2aCore input provides actual source Fam, InputsB, and
LossBounds. The production-family integrated slope theorem discharges the
stronger arithmetic slope premise without introducing another hypothesis.

We preserve the released ChainCore and give a projection back to it.
No analytic character-sum assertion is strengthened by definition.
-/

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData
open Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism.LFunctionChainParameters.LErr

section
variable {U0 : Type} [Fintype U0]
  {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}

/-- The exact original SizeData₂ assumptions with only the old logarithmic
slope interface replaced by the source-derived integrated one. -/
def SizeData₂Integrated (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : Prop :=
  Dd.HidaSetting C ∧ Dd.DIV C ∧ EComp5 Dd C ∧ Dd.HComp C ∧ Count5 Dd C ∧ Dd.Slopes C ∧
  QuotientSlopeBoundsWith Dd C Xpp ∧ LossBounds Dd C ∧ Dd.SlopeIneqIntegrated ∧
  Dd.HHBound C ∧ Dd.FParams

/-- A stronger chain input still discharges the unchanged original
arithmetic interface. The direction of this implication is essential. -/
theorem sizeData₂_of_integrated (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (h : SizeData₂Integrated Dd C Xpp) : SizeData₂ Dd C Xpp := by
  obtain ⟨hSet, hDIV, hE, hH, hCount, hSl, hSN, hLoss, hSI, hHH, hFP⟩ := h
  exact ⟨hSet, hDIV, hE, hH, hCount, hSl, hSN, hLoss,
    Dd.slopeIneq_of_integrated C hSet hSI, hHH, hFP⟩

/-- The improved source-compatible arithmetic input really gives the
smaller rational error, not merely a comparison with the old budget. -/
theorem mean_bound_of_sizeData₂Integrated [Nonempty U0]
    (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (h : SizeData₂Integrated Dd C Xpp) :
    umean Dd.ASK ≤ umean Dd.Main + errorTermWithIntegrated Dd C Xpp := by
  obtain ⟨hSet, hDIV, hE, hH, hCount, hSl, hSN, hLoss, hSI, hHH, hFP⟩ := h
  exact weighted_mean_bound_integrated Dd C Xpp inferInstance
    hSet hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP

end

/-- Full original ChainCore data, retaining the *same* witnesses and
parameter constraints, with the integrated arithmetic condition. -/
def ChainCoreIntegrated (eD eL K cHH eK CL ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
    (W : H → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0))
    (Top : Type) (_ : Fintype Top)
    (m f : ℕ) (Dd : Data H W Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ : ℝ),
    Dd.x = x ∧ Dd.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    HostFacts D ∧
    Ident Dd D N ell TT a w eT eP ∧
    SizeData₂Integrated Dd C Xpp ∧
    ErrWindows Dd C Xpp eK K ∧
    BNBounds Dd T2 ∧
    GrowthInequalityRemainingHyps D ell N TT T2 a w x ε Dd.b Dd.b' η X' θ CL ∧
    CostWindows x (fPl H) Dd.b η θ ∧
    RestSize ε x (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a

/-- Preserve the released chain input under the stronger checked interface. -/
theorem chainCore_of_integrated {eD eL K cHH eK CL ε x : ℝ}
    (h : ChainCoreIntegrated eD eL K cHH eK CL ε x) :
    ChainCore eD eL K cHH eK CL ε x := by
  rcases h with
    ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp,
     D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
     hx, hε, heD, heL, hcHH, hHost, hIdent, hSD, hWin, hBN, hGrow, hCost, hSize⟩
  exact ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp,
    D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx, hε, heD, heL, hcHH, hHost, hIdent,
    sizeData₂_of_integrated Dd C Xpp hSD,
    hWin, hBN, hGrow, hCost, hSize⟩

end Formalism.LFunctionChainParameters.LChain

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData
open Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain

/-- The source's unchanged Chain2aCore witness entails a fully source-linked
ChainCore with the rational integrated slope error. This repeats no geometry,
and imports no extra existence or uniformity assumption. -/
theorem first_variant_reduction_integrated :
    ∀ eD eL K cHH eK CL ε x : ℝ,
      Chain2aCore eD eL K cHH eK CL ε x →
        ChainCoreIntegrated eD eL K cHH eK CL ε x := by
  rintro eD eL K cHH eK CL ε x
    ⟨H, i1, i2, i3, W, i4, i5, m, D, ell, G, C, cT, N, TT, T2, a, w,
      Fm, η, θ, hx, hε, heD, heL, hcHH, hHost, hB, hLoss⟩
  have hSharp := integrated_slope_of_inputsB D ell G C cT N TT T2 a w Fm
    η θ eK K CL hB
  obtain ⟨hSet, hN5, _, hHHB, hFPar⟩ :=
    sizeConditions_of_split D ell G C cT N TT T2 a w Fm η θ eK K CL hB
  obtain ⟨hLat, hPl, hSz, hv, hd, heB, hDIV, hE, hHC, hCnt, hSl,
      hHH, hFP, hWin, hRest, hCost, hSize⟩ := hB
  exact ⟨H, i1, i2, i3, W, i4, i5, TT, inferInstance, m, _,
    mkData G C.cHH D ell N TT T2 a w Fm, C, XppH H G,
    D, ell, N, TT, T2, a, w, Equiv.refl _, ePhi, η, XpTx G.x G.ε, θ,
    hx, hε, heD, heL, hcHH, hHost,
    ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, rfl, fun _ => rfl⟩,
    ⟨hSet, hDIV, hE, hHC, hCnt, hSl, hN5, hLoss, hSharp, hHHB, hFPar⟩,
    hWin, ⟨le_refl _, le_refl _⟩,
    hx ▸ hε ▸ hRest, hx ▸ hCost, hx ▸ hε ▸ hSize⟩

/-- Compatibility check: the strengthened source theorem implies exactly
the previously exported source reduction, without revising its type. -/
theorem original_first_variant_from_integrated :
    ∀ eD eL K cHH eK CL ε x : ℝ,
      Chain2aCore eD eL K cHH eK CL ε x →
        ChainCore eD eL K cHH eK CL ε x := by
  intro eD eL K cHH eK CL ε x h
  exact chainCore_of_integrated
    (first_variant_reduction_integrated eD eL K cHH eK CL ε x h)

#print axioms Formalism.LFunctionChainParameters.LChain2.first_variant_reduction_integrated
#print axioms Formalism.LFunctionChainParameters.LChain2.original_first_variant_from_integrated
#print axioms Formalism.LFunctionChainParameters.LChain.mean_bound_of_sizeData₂Integrated

end Formalism.LFunctionChainParameters.LChain2
