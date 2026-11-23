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
theorem sizeData₂_of_integrated [Nonempty U0]
    (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
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
  letI : Nonempty H := ⟨0⟩
  exact ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp,
    D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx, hε, heD, heL, hcHH, hHost, hIdent,
    sizeData₂_of_integrated Dd C Xpp hSD,
    hWin, hBN, hGrow, hCost, hSize⟩


/-- First genuinely analytic use of the improved arithmetic budget:
the original source's character-sum comparison is evaluated with the
rational integrated error rather than the older logarithmic allowance.
The original Ident connects these exact data to the same topExcess. -/
theorem topExcess_of_integrated_sizeData
    {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H))
    (hId : Ident Dd D N ell TT a w eT eP)
    (hSD : SizeData₂Integrated Dd C Xpp) :
    topExcess D N ell TT a w ≤ errorTermWithIntegrated Dd C Xpp := by
  letI : Nonempty H := ⟨0⟩
  obtain ⟨hAT, hW, hGam, hLpL, hASK⟩ := hId
  exact top_from_weighted_mean Dd D N ell TT a w eT eP
    (errorTermWithIntegrated Dd C Xpp) hAT hW hGam hLpL hASK
    (mean_bound_of_sizeData₂Integrated Dd C Xpp hSD)

#print axioms Formalism.LFunctionChainParameters.LChain.topExcess_of_integrated_sizeData


/-- The improved arithmetic budget reaches the *same* original analytic
power window with no additional hypotheses. This proves compatibility,
not an improvement of the old power exponent: the logarithmic envelope
is reintroduced only when we compare against the old error estimator. -/
theorem topExcess_integrated_power_bound
    {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ}
    (Dd : Data H W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H))
    (hId : Ident Dd D N ell TT a w eT eP)
    (hSD : SizeData₂Integrated Dd C Xpp)
    (hErr : ErrWindows Dd C Xpp eK K)
    (hLarge : LargeX Dd.x Dd.ε K C.cHH eK) :
    topExcess D N ell TT a w ≤ Dd.x ^ (CErr C * Dd.ε) * ErrText Dd := by
  letI : Nonempty H := ⟨0⟩
  have hSDcopy := hSD
  obtain ⟨hSet, _, hE, hH, hCount, hSl, hSN, hLoss, _, _, _⟩ := hSDcopy
  have hU := UBar5_nonneg Dd C Xpp hSet hE hH hCount hSl hSN hLoss
  have hCompare := errorTermWithIntegrated_le_errorTermWith Dd C Xpp hSet hU
  have hBudget := error_sizes Dd C Xpp eK K hErr hLarge
  exact (topExcess_of_integrated_sizeData Dd C Xpp D N ell TT a w eT eP hId hSD).trans
    (hCompare.trans hBudget)

#print axioms Formalism.LFunctionChainParameters.LChain.topExcess_integrated_power_bound

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


/-- The exact original Inputs2 arithmetic data imply a smaller upper
bound on the first analytic character-sum quantity. Unlike an abstract
error comparison, this theorem applies the source's own character-sum
mean transfer to the verified harmonic mean error from the actual Fam. -/
theorem topExcess_of_inputs2_integrated
    {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {W : H → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {m : ℕ}
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m)
    (η θ eK K CL : ℝ)
    (h : Inputs2 D ell G C cT N TT T2 a w Fm η θ eK K CL) :
    topExcess D N ell TT a w ≤
      errorTermWithIntegrated (mkData G C.cHH D ell N TT T2 a w Fm)
        C (XppH H G) := by
  have hMean := weighted_mean_of_inputs2_integrated D ell G C cT N TT T2 a w Fm
    η θ eK K CL h
  exact top_from_weighted_mean
    (mkData G C.cHH D ell N TT T2 a w Fm)
    D N ell TT a w (Equiv.refl _) ePhi
    (errorTermWithIntegrated (mkData G C.cHH D ell N TT T2 a w Fm) C (XppH H G))
    (fun _ => rfl) (fun _ _ _ => rfl) rfl rfl (fun _ => rfl) hMean

#print axioms Formalism.LFunctionChainParameters.LChain2.topExcess_of_inputs2_integrated

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
