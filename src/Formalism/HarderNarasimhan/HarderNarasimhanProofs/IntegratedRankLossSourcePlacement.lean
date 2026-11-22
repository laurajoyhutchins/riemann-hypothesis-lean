import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp

/-!
# Exact-corank instantiation of the original geometric placement theorem

This declaration invokes the unmodified `Formalism.HN.thmF_place`,
choosing its real corank parameter to be the actual coefficient-field rank
deficit divided by total coefficient-field input rank.

Nothing about the submodules depends on a fixed threshold: a caller may
instantiate this theorem separately with `Nt τ` for every real `τ`.
The further identification of this fraction with the low-slope counting
function is a distinct obligation, discharged locally in the original
`theoremFSharp_of` only before that source replaces it by a pointwise
envelope.
-/

namespace Formalism.HN

open Module NumberField Finset

/-- `thmF_place` specialized to the actual input corank share.
    This is an instance of the original theorem, not a stronger axiom. -/
theorem thmF_place_exact_corank
    {K W κ κ₁ I : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I]
    {V ι : I → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)]
    (hLA : FrameLA1)
    (b' : Basis κ K W) (b : ∀ i, Basis (ι i) K (V i))
    (B : ∀ i, V i →ₗ[K] W)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ)
    (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (c : I → ℝ)
    (e η : ℝ) (Nt : ∀ i, Submodule (𝓞 K) (V i))
    (hY : ∀ i, IsUnit (Y i).det) (hY' : IsUnit Y'.det)
    (hc : ∀ i, 0 < c i)
    (hpos : 0 < ∑ i, Fintype.card (ι i))
    (hBall : ∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j =
        (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map
          v.embedding * Y i) k j)
    (hF2 : (∑ i, hs2 (frK (c i) (Matrix.toEuclideanLin (Ball i)) -
        LinearMap.id)) ≤ e * ∑ i, (Fintype.card (ι i) : ℝ))
    (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hη : 0 ≤ η)
    (hF1 : (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ c (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ c (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ)) :
    (Fintype.card κ : ℝ) -
      rkK (⨆ i, (Nt i).map ((B i).restrictScalars (𝓞 K))) ≤
      (η + 4 *
        ((∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt i))) /
         (∑ i, (Fintype.card (ι i) : ℝ))) +
        4 * Real.sqrt e) * (Fintype.card (κ ⊕ κ₁) : ℝ) := by
  classical
  have hR : (∑ i, (Fintype.card (ι i) : ℝ)) ≠ 0 := by
    have hr : (0 : ℝ) < ∑ i, (Fintype.card (ι i) : ℝ) := by
      exact_mod_cast hpos
    exact hr.ne'
  have hcor :
      (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt i))) ≤
        ((∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt i))) /
         (∑ i, (Fintype.card (ι i) : ℝ))) *
         (∑ i, (Fintype.card (ι i) : ℝ)) := by
    rw [div_mul_cancel₀ _ hR]
  exact thmF_place hLA b' b B v Y Y' Ball c e η
    ((∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt i))) /
      (∑ i, (Fintype.card (ι i) : ℝ)))
    Nt hY hY' hc hpos hBall hF2 he0 he1 hη hF1 hcor

end Formalism.HN

#print axioms Formalism.HN.thmF_place_exact_corank
