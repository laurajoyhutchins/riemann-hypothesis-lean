import Formalism.HarderNarasimhan.StatementFrameF

/-!
# Stronger integrated statement without modifying the released theorem

The hypotheses are copied *exactly* from the original `TheoremFSharp`
proposition. The new bound replaces only the logarithmic loss. The joint
proposition is a proof-sharing interface: we prove both conclusions
in one source derivation, then project the original theorem unchanged.
-/

open Module NumberField Formalism.CorankShareLayerCake.FR

noncomputable section

namespace Formalism.HN

/-- Source hypotheses and the logarithm-free integrated conclusion. -/
def TheoremFIntegrated : Prop :=
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
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    0 < ∑ i, Fintype.card (ι i) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) →
    0 ≤ u → (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    0 ≤ δ → δ < 1 → (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) →
    (∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j) →
    (∀ i, 0 < γ i) →
    (∑ i, hs2 (frK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) →
    0 ≤ η →
    s - (1 - δ)⁻¹ * ((η + 4 * Real.sqrt e) * HH + 4 * (u * HH / (u + HH))) ≤ muDef b' X' cc

/-- Source hypotheses with both original and sharp conclusions. -/
def TheoremFJoint : Prop :=
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
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    0 < ∑ i, Fintype.card (ι i) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) →
    0 ≤ u → (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    0 ≤ δ → δ < 1 → (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) →
    (∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j) →
    (∀ i, 0 < γ i) →
    (∑ i, hs2 (frK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) →
    0 ≤ η →
    (s - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc) ∧
    (s - (1 - δ)⁻¹ * ((η + 4 * Real.sqrt e) * HH + 4 * (u * HH / (u + HH))) ≤ muDef b' X' cc)

end Formalism.HN
