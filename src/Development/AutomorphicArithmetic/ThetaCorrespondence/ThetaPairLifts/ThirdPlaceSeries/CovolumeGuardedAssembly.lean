import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

-- Experimental proof-sharing module. The two pre-existing covolume theorems
-- remain untouched. Compile this module before replacing either proof body.
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2
  Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj
  Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/-- A proposition on each point of each family. Unlike a realization
    conversion, this does not identify the original and alternative guards. -/
abbrev PointAdmissibility :=
  ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x)
    (ι : Fm.Ix x) (p : Pt Fm x hx ι), Prop

/-- Eventually, every admissible point satisfies `Q`. -/
def EventuallyUnder (guard : PointAdmissibility)
    {eps : ℝ} (Fm : FamP eps)
    (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x),
      Pt Fm x hx ι → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x →
    ∀ (ι : Fm.Ix x) (p : Pt Fm x hx ι),
      guard Fm x hx ι p → Q x hx ι p

theorem EventuallyUnder.and {guard : PointAdmissibility}
    {eps : ℝ} {Fm : FamP eps}
    {Q Q' : ∀ (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x),
      Pt Fm x hx ι → Prop}
    (h : EventuallyUnder guard Fm Q)
    (h' : EventuallyUnder guard Fm Q') :
    EventuallyUnder guard Fm
      (fun x hx ι p => Q x hx ι p ∧ Q' x hx ι p) := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact ⟨max a b, fun x hx hle ι p hp =>
    ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp,
     hb x hx ((le_max_right _ _).trans hle) ι p hp⟩⟩

/-- Universally quantified bounds whose meaning is independent of which
    realization predicate is used to select a family point. -/
def LiftsUnder (guard : PointAdmissibility)
    (Q : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ)
      (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (PP C : ℝ), Prop) : Prop :=
  Closed FamHyp fun Fm _ =>
    ∃ C : ℝ, 0 ≤ C ∧
      EventuallyUnder guard Fm
        (fun x hx ι p =>
          ∀ i, Q Fm x hx ι p i (Fm.parT x hx ι).PP C)

/-- The original covolume conclusion, but with a parameterized admissibility
    predicate on the points at which the eventual bound is asserted. -/
def CovolumeUnder (guard : PointAdmissibility) : Prop :=
  Closed FamHyp fun Fm CH =>
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      EventuallyUnder guard Fm
        (fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH))

namespace Assembly

/-- The shared eight-bound assembly. Its proof uses only the eight *local*
    mathematical estimates and `lcv_le`, not the definition of `guard`.

    The two source-specific specializations below are separate exact-type
    obligations: neither implies the other, and no realization equivalence
    is postulated. -/
theorem covolume_of_guarded_steps (guard : PointAdmissibility) :
    LiftsUnder guard (fun _ _ _ _ p i _ _ => GramAt p i) →
    LiftsUnder guard (fun _ _ _ _ p i _ _ => RecAt p i) →
    LiftsUnder guard (fun _ _ _ _ p i _ _ => CutAt p i) →
    LiftsUnder guard (fun _ _ _ _ p i _ _ => BadAt p i) →
    LiftsUnder guard (fun _ _ _ _ p i _ C => LamAt p i C) →
    LiftsUnder guard (fun _ _ _ _ p i PP C => SizeAt p i PP C) →
    LiftsUnder guard (fun _ _ _ _ p i _ C => CoreAt p i C) →
    LiftsUnder guard (fun _ _ _ _ p i _ C => LowAt p i C) →
    CovolumeUnder guard := by
  intro hG hR hC hB hL hS hK hW
  refine Closed.imp (Closed.and (Closed.and (Closed.and hG hR) (Closed.and hC hB))
    (Closed.and (Closed.and hL hS) (Closed.and hK hW))) ?_
  rintro eps Fm CH he ⟨⟨⟨⟨_, -, g⟩, ⟨_, -, r⟩⟩, ⟨⟨_, -, c⟩, ⟨_, -, b⟩⟩⟩,
    ⟨⟨A, -, l⟩, ⟨B, -, s⟩⟩, ⟨C1, h1, k⟩, ⟨C2, h2, w⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  obtain ⟨x0, hx0⟩ :=
    exists_loss_le (show 0 < Fm.ez / 7 by positivity) A B (C1 + C2 + 1)
  obtain ⟨x1, h⟩ := (((g.and r).and (c.and b)).and ((l.and s).and (k.and w)))
  refine ⟨C1 + C2 + 1, by linarith, max x0 x1,
    fun x hx hle ι p hp C hC i => ?_⟩
  obtain ⟨⟨⟨g, r⟩, c, b⟩, ⟨l, s⟩, k, w⟩ :=
    h x hx ((le_max_right _ _).trans hle) ι p hp
  have ex := Fm.L_x x ι hx
  have ee := Fm.L_ez x ι
  have hs := hx0 x ((le_max_left _ _).trans hle)
  have hx' : 0 < x := (zero_lt_one.trans Fm.one_lt_family_threshold).trans hx
  have main := lcv_le p i (ex.symm ▸ hx') h1 h2
    (by rw [ex, ee]; exact hs) (g i) (r i) (c i) (b i)
    (l i) (s i) (k i) (w i)
  have hE : 0 ≤ unitE p := by
    obtain ⟨s1, s2, -⟩ := s i
    linarith
  refine main.trans ?_
  show mainT p i + (C1 + C2 + 1) * unitE p ≤
    mainT p i + C * unitE p
  have := mul_le_mul_of_nonneg_right hC hE
  linarith

/-- Old row predicate: exact same proposition as the original theorem.
    No proof body is replaced until a real Lean build accepts this. -/
theorem covolX_of_steps_from_guard :
    Gram → Rec → Cut → Bad → abelian₂ → Size → CoreLe → Low → CovolX := by
  exact covolume_of_guarded_steps
    (fun _ _ _ _ p => RowsT p)

/-- Alternative row predicate: exact same proposition as the third-place
    assembly theorem, without assuming `RowsTAlt → RowsT`. -/
theorem covolX_of_lift_bounds_from_guard :
    _root_.GlobalTheory.CovTop.GramCondition →
    _root_.GlobalTheory.CovTop.LiftRecursive →
    _root_.GlobalTheory.CovTop.LiftTruncation →
    _root_.GlobalTheory.CovTop.LiftBadSet →
    _root_.GlobalTheory.CovTop.LiftLambdaBound →
    _root_.GlobalTheory.CovTop.SizeCondition →
    _root_.GlobalTheory.CovTop.CoreBound' →
    _root_.GlobalTheory.CovTop.LiftLowBound →
    _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  exact covolume_of_guarded_steps
    (fun _ _ _ _ p => RowsTAlt p)

end Assembly
end GlobalTheory.CovTop
