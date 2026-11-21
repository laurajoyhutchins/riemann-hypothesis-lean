import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

section ProOpen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.HomExtProOpen

open GlobalTheory GlobalTheory.HomExt GlobalTheory.HomExtNormal

theorem existsUnique_hom_extension_of_dvr
    (H : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f))
    (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (hX : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G G' : Over X) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') (hf : IsMonHom f) :
    ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f := by
  have : QuasiCompact (pullback.fst G.hom j) :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom j))
  exact GlobalTheory.HomExtNormal.existsUnique_hom_extension_of_dvr_core
    H X U j hX G G' hG hG' f hf

end GlobalTheory.HomExtProOpen

end ProOpen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj

theorem GlobalTheory.exists_oAct_extend_dedekindModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [Field K] (ω : R →+* K) (U Y : Scheme.{0}) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)) (G' : Over Y) [GrpObj G'] [IsCommMonObj G'] (t₀ : SAB H U) (φ : t₀.G.left ⟶ G'.left), IsDedFrac ω → Geo.Tor.IsNormalScheme Y → IsProjOver sY → Flat sY → IsOpenImmersion jQ → Dense (Set.range jQ) → IsSemiAbelian G' → IsGrpPullback t₀.G G' (jQ ≫ pullback.fst _ _) φ → ∃ act : OAct (𝓞 E) G', ∀ a, (t₀.act.act a).left ≫ φ = φ ≫ (act.act a).left := by
  intro E _ _ _ H R K _ _ ω U Y sY jQ G' _ _ t₀ φ hω hY hP hF hjQ hD hG' hφ
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hω
  letI := ω.toAlgebra
  obtain ⟨hN, -, -, hpre, hfl, hdom, hqc⟩ :=
    GlobalTheory.genericPart_dense_proOpen R K Y U sY jQ hF hP hjQ hD
  set j : U ⟶ Y := jQ ≫ pullback.fst sY (spMap ω) with hj
  have := hG'.smooth
  have := hG'.separated
  have : GlobalTheory.IsNormalScheme Y := (GlobalTheory.isNormalScheme_iff Y).mpr hY
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  have key : ∀ x, ∃ F : G' ⟶ G', (t₀.act.act x).left ≫ φ = φ ≫ F.left := by
    intro x
    obtain ⟨e, he, he'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G' j)
    have := t₀.act.hom x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
      GlobalTheory.homExtension_semiAbelian_dvr Y U j hY G' G' hG' hG' (e.inv ≫ t₀.act.act x ≫ e.hom) inferInstance
    refine ⟨F, ?_⟩
    have h1 : ((Over.pullback j).map F).left ≫ pullback.fst G'.hom j = pullback.fst G'.hom j ≫ F.left :=
      GlobalTheory.ExtUnique.pullback_map_left_fst j F
    rw [hF] at h1
    have h2 : e.hom ≫ e.inv ≫ t₀.act.act x ≫ e.hom = t₀.act.act x ≫ e.hom := e.hom_inv_id_assoc _
    rw [← he', Category.assoc, ← h1, ← Over.comp_left_assoc (f := e.hom), h2, Over.comp_left_assoc]
  obtain ⟨a, ha, -⟩ := GlobalTheory.ExtUnique.existsUnique_oAct_of_isGrpPullback hφ t₀.act key
  exact ⟨a, ha⟩
