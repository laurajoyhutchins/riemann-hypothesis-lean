module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompatStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

noncomputable section

namespace GlobalTheory.CompanionTheory.CechOne

private theorem equiv₀_terminalEquiv_eq_equivZero.{w, v, u}
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) {T : C} (hT : IsTerminal T) (x : F.H' 0 T) :
    Sheaf.H.equiv₀ F hT (GlobalTheory.SiteCoh.terminalEquiv F 0 hT x) =
      GlobalTheory.SheafLES.equivZero.{w} F T x :=
  (GlobalTheory.SiteCoh.equiv₀_terminalEquiv F hT x).trans
    (show GlobalTheory.SiteCoh.zeroEquiv F T x = GlobalTheory.SheafLES.equivZero.{w} F T x from rfl)

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (s : G.obj.obj (op ⊤)) :
    hPull f φ 0 ((Sheaf.H.equiv₀ G isTerminalTop).symm s) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm
        (G'.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.hom.app (op ⊤) s)) := by
  let i : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤ := homOfLE le_top
  let e := GlobalTheory.SiteCoh.terminalEquiv.{0, 0, 0} G 0 isTerminalTop
  let e' := GlobalTheory.SiteCoh.terminalEquiv.{0, 0, 0} G' 0 isTerminalTop
  let a := GlobalTheory.SheafLES.equivZero.{0} G ⊤
  let x := a.symm s
  have hx : e x = (Sheaf.H.equiv₀ G isTerminalTop).symm s :=
    (Sheaf.H.equiv₀ G isTerminalTop).eq_symm_apply.mpr
      ((equiv₀_terminalEquiv_eq_equivZero G isTerminalTop x).trans (a.apply_symm_apply s))
  let p := pull.{0, 0} f φ 0 i
  have hcomp : hPull f φ 0 (e x) = e' (p x) :=
    congrArg (fun y => e' (p y)) (e.symm_apply_apply x)
  have hp : e' (p x) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm (G'.obj.map i.op (φ.hom.app (op ⊤) s)) :=
    (Sheaf.H.equiv₀ G' isTerminalTop).eq_symm_apply.mpr
      ((equiv₀_terminalEquiv_eq_equivZero G' isTerminalTop (p x)).trans
        ((SheafPull.equivZero_pull f φ i x).trans
          (congrArg (fun y => G'.obj.map i.op (φ.hom.app (op ⊤) y)) (a.apply_symm_apply s))))
  exact (congrArg (hPull f φ 0) hx.symm).trans (hcomp.trans hp)

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (φ.app (op ⊤) s))).1 := by
  funext t
  let h := inter_le_map f V U τ hτ t
  let k : inter V (τ ∘ t) ≤ ⊤ := le_top
  let s' := φ.app (op ⊤) s
  exact (congrArg (res Q h) (app_res_map f φ k s)).trans
    ((res_res Q h ((Opens.map f).monotone k) s').trans
      (res_res Q (le_top : inter U t ≤ ⊤) (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤) s').symm)

theorem cechHOneEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1) :
    (cechHOneEquiv U hU hS' hC' hI' : GroundTheory.Arith.SchemeCoh.cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  obtain ⟨s, rfl⟩ := cechOneProj_surjective V hV hC hI x
  have h₁₂ : ∀ W y, α.τ₂.hom.app W (S.f.hom.app W y) = S'.f.hom.app _ (α.τ₁.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₁₂.symm) W) y
  have h₂₃ : ∀ W y, α.τ₃.hom.app W (S.g.hom.app W y) = S'.g.hom.app _ (α.τ₂.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₂₃.symm) W) y
  let s' := S'.X₃.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
    (α.τ₃.hom.app (op ⊤) s)
  have hmap : cechPullH f α.τ₁.hom V U τ hτ 1 (cechOneProj V hC s) = cechOneProj U hC' s' :=
    (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC'
      α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ 0 (globalCocycle S.X₃.obj V s)).trans
      (congrArg (hC'.delta 0) (Subtype.ext (pullCoch_globalCocycle f α.τ₃.hom V U τ hτ s)))
  have hconn : hPull f α.τ₁ 1 (hOneProj hS s) = hOneProj hS' s' :=
    (GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α 0
      ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s)).trans
      (congrArg (H.δ hS' 0 1 rfl) (hPull_zero f α.τ₃ s))
  calc
    _ = cechHOneEquiv U hU hS' hC' hI' (cechOneProj U hC' s') :=
      congrArg (cechHOneEquiv U hU hS' hC' hI') hmap
    _ = hOneProj hS' s' := cechHOneEquiv_cechOneProj U hU hS' hC' hI' s'
    _ = hPull f α.τ₁ 1 (hOneProj hS s) := hconn.symm
    _ = _ := congrArg (hPull f α.τ₁ 1) (cechHOneEquiv_cechOneProj V hV hS hC hI s).symm

end GlobalTheory.CompanionTheory.CechOne
