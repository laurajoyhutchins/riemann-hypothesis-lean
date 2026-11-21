import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSquareSqMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

theorem tanScal_iff {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] (A : Over S) [GrpObj A] (A' : Over S')
    [GrpObj A'] (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A')
    (h : IsGrpPullback A' A f φ) (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (R' : Type) [CommRing R']
    (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A)
    (hv : v₀.left = v.left ≫ φ) :
    GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀ := by
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ :=
    (congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))).symm
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have E : (v₀ ≫ act.act b).left = (v ≫ act'.act b).left ≫ φ := by
    rw [Over.comp_left, Over.comp_left, hv, Category.assoc, Category.assoc, hact]
  refine and_congr ?_ ?_
  · rw [one, hv]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · rw [E, hv]
    refine ⟨fun E' => by rw [E']; exact Category.assoc _ _ _,
      fun E' => h.1.hom_ext (E'.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ act'.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem kerGen {S S' : Scheme.{0}} {f : S' ⟶ S} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A']
    (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A f φ) (P : LB (G2 A).left) (T : Over S') (x : T ⟶ A')
    (ht : ∃ t : ((P.pull (sqMap h.1.w)).pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd A (Over.mk (T.hom ≫ f)) ≫ pushPt h.1.w x) (fst A (Over.mk (T.hom ≫ f)))).left).Gen,
      t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let Z' : Over S' := Over.mk ((snd A T₀).left ≫ T.hom)
  have eq : (fst A T₀).left ≫ A.hom = Z'.hom ≫ f :=
    (Over.w (fst A T₀)).trans ((Over.w (snd A T₀)).symm.trans (Category.assoc _ _ _).symm)
  let a' : Z' ⟶ A' := Over.homMk (h.1.lift (fst A T₀).left Z'.hom eq) (h.1.lift_snd _ _ _)
  let t' : Z' ⟶ T := Over.homMk (snd A T₀).left rfl
  let u : Over.mk (Z'.hom ≫ f) ⟶ A ⊗ T₀ := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (A ⊗ T₀).hom = ((snd A T₀).left ≫ T.hom) ≫ f
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (snd A T₀)).symm)
  have hc : (lift (t' ≫ x) a').left ≫ sqMap h.1.w = u.left ≫ (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left :=
    sqMap_of h.1.w u _ _ _ _ (Over.OverMorphism.ext (by
      show ((snd A T₀).left ≫ x.left) ≫ φ = 𝟙 _ ≫ (snd A T₀).left ≫ x.left ≫ φ
      rw [Category.id_comp, Category.assoc]))
      (Over.OverMorphism.ext (by
        show h.1.lift (fst A T₀).left Z'.hom eq ≫ φ = 𝟙 _ ≫ (fst A T₀).left
        rw [Category.id_comp, h.1.lift_fst]))
  have hψ : (lift a' t').left ≫ (lift (snd A' T ≫ x) (fst A' T)).left = (lift (t' ≫ x) a').left := by
    rw [← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst]
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullIn P (fun _ : PUnit => sqMap h.1.w) (fun _ => 1)
    (lift (snd A' T ≫ x) (fst A' T)).left) t ht
  refine gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left)
    (fun _ => (lift (snd A' T ≫ x) (fst A' T)).left ≫ sqMap h.1.w) (fun _ => 1) (lift a' t').left fun _ => ?_) t₁ ht₁
  rw [← Category.assoc, hψ, hc]
  exact (Category.id_comp _).symm

end GlobalTheory.UPel.HT.Pull

namespace GlobalTheory.UPel.HT.Pull

open GlobalTheory.UPel.HT

theorem exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : GlobalTheory.UPel.HT.Obj b N s), ∃ o' : GlobalTheory.UPel.HT.Obj b N (f ≫ s), Nonempty (GlobalTheory.UPel.HT.ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  exact GlobalTheory.HTPullEvery.exists_objMap p D R b N S S' s (f ≫ s) f rfl o

end GlobalTheory.UPel.HT.Pull
