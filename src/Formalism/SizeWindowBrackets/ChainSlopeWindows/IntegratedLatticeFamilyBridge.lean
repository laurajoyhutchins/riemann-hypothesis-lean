import Formalism.SizeWindowBrackets.ChainSlopeWindows.IntegratedLatticeArithmeticBridge

/-!
# Derive the sharp arithmetic slope inequality from actual per-unit lattices

This discharges \`Data.SlopeIneqIntegrated\` from the same existential
\`LatForS\` family already used by the source's old slope inequality.
Unlike a restated implication, no sharp inequality is assumed: for every
unit, the original \`HypS\` data are unpacked and passed to the checked
source geometric-and-ramified-frame bridge.
-/

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer

open Formalism.RankGapBounds.WeightedMeanData
open Formalism.LFunctionChainParameters.WeightedSlopeBounds

variable {U0 : Type} [Fintype U0]
  {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

/-- The existing per-unit lattice witnesses prove the stronger, rational
integrated-slope arithmetic premise; the original arithmetic data and
its parameter normalization are not changed. -/
theorem integrated_slope_of_lattices
    (hLat : ∀ u0, LatForS D u0) : D.SlopeIneqIntegrated := by
  intro u0 hδ0 hδ1 hη0 he0 he4 hHbound hHpos
  classical
  have hSide : SideF D u0 :=
    ⟨hδ0, hδ1, hη0, he0, he4, hHbound, hHpos⟩
  rcases hLat u0 with
    ⟨K, Wd, κ, κ₁, fld, nf, starK, totK,
     addWd, modWd, modOWd, towerWd,
     finκ, decκ, finκ₁, decκ₁,
     V, ι, addV, modV, modOV, towerV, finι, decι,
     b', X', cc, b, X, N, B, v, Y, Y', Ball, γ,
     ιf, finιf, decιf, Bf, Vr, Dstar, sg, η0, η1, e0, de, hHyp⟩
  letI : Field K := fld
  letI : NumberField K := nf
  letI : StarRing K := starK
  letI : IsTotallyComplex K := totK
  letI : AddCommGroup Wd := addWd
  letI : Module K Wd := modWd
  letI : Module (𝓞 K) Wd := modOWd
  letI : IsScalarTower (𝓞 K) K Wd := towerWd
  letI : Fintype κ := finκ
  letI : DecidableEq κ := decκ
  letI : Fintype κ₁ := finκ₁
  letI : DecidableEq κ₁ := decκ₁
  letI : ∀ i, AddCommGroup (V i) := addV
  letI : ∀ i, Module K (V i) := modV
  letI : ∀ i, Module (𝓞 K) (V i) := modOV
  letI : ∀ i, IsScalarTower (𝓞 K) K (V i) := towerV
  letI : ∀ i, Fintype (ι i) := finι
  letI : ∀ i, DecidableEq (ι i) := decι
  letI : ∀ i, Fintype (ιf i) := finιf
  letI : ∀ i, DecidableEq (ιf i) := decιf
  exact function_slope_integrated D u0 K Wd κ κ₁ V ι
    b' X' cc b X N B v Y Y' Ball γ ιf Bf Vr
    Dstar sg η0 η1 e0 de hHyp hSide

/-- Source-level arithmetic payoff. The same \`LatForS\` premise as in
the original lattice transfer now entails the improved uniform mean
bound. No independent \`SlopeIneqIntegrated\` hypothesis is assumed. -/
theorem weighted_mean_of_lattices_integrated (Xpp : ℝ) :
    Nonempty U0 → D.HidaSetting C → D.DIV C →
      EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
      QuotientSlopeBoundsWith D C Xpp → LossBounds D C →
      (∀ u0, LatForS D u0) → D.HHBound C → D.FParams →
      umean D.ASK ≤ umean D.Main + errorTermWithIntegrated D C Xpp := by
  intro hne hS hDIV hE hH hCount hSl hSN hLoss hLat hHH hFP
  have hSI : D.SlopeIneqIntegrated :=
    integrated_slope_of_lattices D hLat
  exact weighted_mean_bound_integrated D C Xpp hne hS hDIV hE hH hCount hSl hSN
    hLoss hSI hHH hFP

#print axioms Formalism.LFunctionChainParameters.LatticeToWeightTransfer.integrated_slope_of_lattices
#print axioms Formalism.LFunctionChainParameters.LatticeToWeightTransfer.weighted_mean_of_lattices_integrated

end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
