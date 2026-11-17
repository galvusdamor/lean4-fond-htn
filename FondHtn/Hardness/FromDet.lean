import FondHtn.Transfer.DetDesc
import HtnComplexity.Article.StripsReg
import HtnComplexity.Article.StripsAcyc
import HtnComplexity.Article.SATRegDesc
import HtnComplexity.Article.SATNoHTN
import HtnComplexity.Article.NExpHard
import HtnComplexity.Article.ExpSpaceHard
import HtnComplexity.Article.TOHard
import HtnComplexity.Article.Undecidability
/-!
# Lower bounds inherited from deterministic HTN planning

Deterministic HTN problems are FOND problems in which every action has a single effect
(with the state goal checked by an appended last task, `FOND.detDesc`).  Hence every hardness
result of the deterministic development transfers to every fixed-method criterion of [CB21] and to
weak and strong solvability with method-based policies [CB22]:

* `FOND.redP_planExFM`, `FOND.redP_planExMP` — the polynomial-time reductions;
* the inherited lower bounds `FOND.hard_*` and `FOND.undecidable_*`.

Strong *cyclic* solvability is not covered: on deterministic recursive problems it does not agree
with solvability under the literal definition of [CB22, Def. 7].
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.TaskNetwork

/-! ## Facts about well-formed deterministic descriptions -/

theorem lookup_mem {β : Type} {l : List (ℕ × β)} {x : ℕ} {b : β} (h : l.lookup x = some b) :
    (x, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons q l ih =>
    simp only [List.lookup] at h
    split at h
    · rename_i hq
      cases h
      have : q.1 = x := by simp at hq; omega
      exact List.mem_cons.2 (Or.inl (by rw [← this]))
    · exact List.mem_cons_of_mem _ (ih h)

theorem label_declared {prim : ℕ → Prop} {t : TnDesc} (h : TnValid prim t) {x n : ℕ}
    (hx : t.label x = Sum.inl n) : n = 0 ∨ prim n := by
  unfold TnDesc.label at hx
  split at hx
  · cases hx
  · rename_i b hb
    cases hx
    right
    exact h.prim_ok _ (lookup_mem hb) rfl
  · cases hx; exact Or.inl rfl

theorem goalName_pos (p : ProbDesc) : 0 < goalName p := Nat.succ_pos _

theorem freshName_goalName {p : ProbDesc} (hp : p.Valid) : FreshName p.toProblem (goalName p) := by
  have key : ∀ {t : TnDesc}, TnValid p.Declared t → ∀ x, t.label x ≠ Sum.inl (goalName p) := by
    intro t ht x hx
    rcases label_declared ht hx with h | h
    · exact absurd h (Nat.pos_iff_ne_zero.1 (goalName_pos p))
    · exact goalName_not_mem p h
  refine ⟨fun t _ => key hp.tnI t, ?_⟩
  rintro m ⟨e, he, rfl⟩ t _
  exact key (hp.methods e he) t

theorem goalId_not_mem_T (p : ProbDesc) : goalId p ∉ p.toProblem.tnI.T := by
  simp only [ProbDesc.toProblem, TnDesc.toTaskNetwork, List.mem_toFinset]
  exact goalId_not_mem p

theorem toProblem_wf' (p : ProbDesc) : p.toProblem.WF :=
  ⟨TnDesc.toTaskNetwork_wf _, by rintro m ⟨e, -, rfl⟩; exact TnDesc.toTaskNetwork_wf _⟩

/-! ## Classes -/

/-- `Y` (deterministic) and `Y'` (FOND) **match** if `detDesc` preserves membership. -/
def Matches (Y : PClass) (Y' : FClass) : Prop :=
  ∀ p : ProbDesc, p.Valid → (Y p.toProblem ↔ Y' (detDesc p).toProblem)

theorem Matches.inter {Y Z : PClass} {Y' Z' : FClass} (h₁ : Matches Y Y') (h₂ : Matches Z Z') :
    Matches (fun P => Y P ∧ Z P) (FClass.inter Y' Z') :=
  fun p hp => and_congr (h₁ p hp) (h₂ p hp)

theorem sameShape_detDesc {p : ProbDesc} (hp : p.Valid) :
    HTN.Problem.SameShape (detDesc p).toProblem.toArt.toPos p.toProblem.toPos := by
  rw [toProblem_detDesc hp]
  exact detFond_sameShape (goalId_not_mem_T p)

theorem matches_ACYC : Matches (fun P => P.IsACYC) FClass.ACYC :=
  fun _ hp => (sameShape_detDesc hp).isAcyclic.symm

theorem matches_REG : Matches (fun P => P.IsREG) FClass.REG :=
  fun _ hp => (sameShape_detDesc hp).isRegularM.symm

theorem matches_TR : Matches (fun P => P.IsTailREC) FClass.TR :=
  fun _ hp => (sameShape_detDesc hp).isTailRecursive.symm

theorem matches_TOM : Matches (fun P => P.IsTO_M) FClass.TOM :=
  fun _ hp => (sameShape_detDesc hp).isTO_M.symm

theorem matches_TOtn : Matches (fun P => P.IsTO_tnI) FClass.TOtn := by
  intro p hp
  change p.toProblem.tnI.IsTotallyOrdered ↔ (detDesc p).toProblem.tnI.IsTotallyOrdered
  rw [toProblem_detDesc hp]
  exact (appendLast_isTotallyOrdered_iff (toProblem_wf' p).tnI (goalId_not_mem_T p)).symm

theorem matches_TO : Matches (fun P => P.IsTO) FClass.TO := by
  intro p hp
  change p.toProblem.toPos.IsTO_tnI ∧ p.toProblem.toPos.IsTO_M ↔
    (detDesc p).toProblem.toArt.toPos.IsTO_tnI ∧ (detDesc p).toProblem.toArt.toPos.IsTO_M
  exact and_congr (matches_TOtn p hp) (matches_TOM p hp)

theorem matches_PRIM : Matches (fun P => P.IsNoHTN) FClass.PRIM := by
  intro p hp
  change p.toProblem.tnI.IsPrimitive ↔ (detDesc p).toProblem.tnI.IsPrimitive
  rw [toProblem_detDesc hp]
  exact (appendLast_isPrimitive_iff (goalId_not_mem_T p)).symm

theorem matches_UNRES : Matches UNRES FClass.UNRES := fun _ _ => Iff.rfl

/-! ## The reductions -/

/-- A description that is not well formed (two actions with the same name). -/
def badDesc : FProbDesc := (([(0, [], [], [([], [])]), (0, [], [], [([], [])])], []), ([], ([], [], [])))

theorem badDesc_not_valid : ¬ badDesc.Valid := fun h => by
  have := h.names_nodup
  simp [badDesc, FProbDesc.actions, FActDesc.name] at this

/-- The reduction: well-formed descriptions are translated, the others mapped to `badDesc`. -/
def detRed (p : ProbDesc) : FProbDesc := if p.Valid then detDesc p else badDesc

theorem pt_detRed : PT detRed := by
  refine (PT.cond pt_validB pt_detDesc (PT.const badDesc)).of_eq fun p => ?_
  simp only [detRed]
  by_cases hp : p.Valid
  · rw [if_pos hp, (validB_iff p).2 hp]; rfl
  · rw [if_neg hp]
    have : validB p = false := by
      cases h : validB p
      · rfl
      · exact absurd ((validB_iff p).1 h) hp
    rw [this]; rfl

/-- The solvability of the translated problem. -/
theorem detDesc_solvable_iff {p : ProbDesc} (hp : p.Valid) :
    ((detDesc p).toProblem.WeakLDSolvable ↔ p.toProblem.Solvable) ∧
    ((detDesc p).toProblem.StrongLDSolvable ↔ p.toProblem.Solvable) ∧
    ((detDesc p).toProblem.WeakODSolvable ↔ p.toProblem.Solvable) ∧
    ((detDesc p).toProblem.StrongODSolvable ↔ p.toProblem.Solvable) ∧
    ((detDesc p).toProblem.MPWeakSolvable ↔ p.toProblem.Solvable) ∧
    ((detDesc p).toProblem.MPStrongSolvable ↔ p.toProblem.Solvable) := by
  rw [toProblem_detDesc hp]
  exact detFond_solvable_iff (toProblem_wf' p) (goalId_not_mem_T p) (freshName_goalName hp)

theorem fm_solvable_detDesc (c : FMCrit) {p : ProbDesc} (hp : p.Valid) :
    c.Solvable (detDesc p).toProblem ↔ p.toProblem.Solvable := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := detDesc_solvable_iff hp
  cases c
  exacts [h1, h2, h3, h4]

/-- **Deterministic plan existence reduces to every fixed-method criterion.** -/
theorem redP_planExFM (c : FMCrit) {Y : PClass} {Y' : FClass} (hY : Matches Y Y') :
    Cx.RedP (PlanEx Y) (PlanExFM c Y') := by
  refine redP_codeLang pt_detRed (fun p => ?_) badDesc (fun h => badDesc_not_valid h.1)
  by_cases hp : p.Valid
  · simp only [detRed, if_pos hp]
    exact ⟨fun ⟨_, hy, hs⟩ => ⟨detDesc_valid hp, (hY p hp).1 hy, (fm_solvable_detDesc c hp).2 hs⟩,
      fun ⟨_, hy, hs⟩ => ⟨hp, (hY p hp).2 hy, (fm_solvable_detDesc c hp).1 hs⟩⟩
  · simp only [detRed, if_neg hp]
    exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 badDesc_not_valid⟩

/-- **Deterministic plan existence reduces to weak and strong method-based solvability.** -/
theorem redP_planExMP (c : MPCrit) (hc : c ≠ .strongCyclic) {Y : PClass} {Y' : FClass}
    (hY : Matches Y Y') : Cx.RedP (PlanEx Y) (PlanExMP c Y') := by
  have hsol : ∀ {p : ProbDesc}, p.Valid →
      (c.Solvable (detDesc p).toProblem ↔ p.toProblem.Solvable) := by
    intro p hp
    obtain ⟨-, -, -, -, h5, h6⟩ := detDesc_solvable_iff hp
    cases c
    exacts [h5, absurd rfl hc, h6]
  refine redP_codeLang pt_detRed (fun p => ?_) badDesc (fun h => badDesc_not_valid h.1)
  by_cases hp : p.Valid
  · simp only [detRed, if_pos hp]
    exact ⟨fun ⟨_, hy, hs⟩ => ⟨detDesc_valid hp, (hY p hp).1 hy, (hsol hp).2 hs⟩,
      fun ⟨_, hy, hs⟩ => ⟨hp, (hY p hp).2 hy, (hsol hp).1 hs⟩⟩
  · simp only [detRed, if_neg hp]
    exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 badDesc_not_valid⟩

/-! ## Inherited lower bounds

Each statement holds for every fixed-method criterion `c` and, with `c ≠ strong cyclic`, for
method-based policies. -/

section

variable (c : FMCrit) (d : MPCrit) (hd : d ≠ .strongCyclic)

/-- Primitive problems: NP-hard ([CB21, Thm. 4.1] for weak; inherited for all). -/
theorem hard_PRIM_fm : Cx.Hard Cx.NP (PlanExFM c FClass.PRIM) :=
  thm_4_3_8.of_redP (redP_planExFM c matches_PRIM)

include hd in
theorem hard_PRIM_mp : Cx.Hard Cx.NP (PlanExMP d FClass.PRIM) :=
  thm_4_3_8.of_redP (redP_planExMP d hd matches_PRIM)

/-- Regular, acyclic and totally ordered problems: NP-hard. -/
theorem hard_REG_ACYC_TO_fm :
    Cx.Hard Cx.NP (PlanExFM c (FClass.inter FClass.REG (FClass.inter FClass.ACYC FClass.TO))) :=
  thm_4_3_12_TO.of_redP (redP_planExFM c (matches_REG.inter (matches_ACYC.inter matches_TO)))

include hd in
theorem hard_REG_ACYC_TO_mp :
    Cx.Hard Cx.NP (PlanExMP d (FClass.inter FClass.REG (FClass.inter FClass.ACYC FClass.TO))) :=
  thm_4_3_12_TO.of_redP (redP_planExMP d hd (matches_REG.inter (matches_ACYC.inter matches_TO)))

/-- Regular totally ordered problems: PSPACE-hard. -/
theorem hard_REG_TO_fm : Cx.Hard Cx.PSPACE (PlanExFM c (FClass.inter FClass.REG FClass.TO)) :=
  thm_4_3_1.1.of_redP (redP_planExFM c (matches_REG.inter matches_TO))

include hd in
theorem hard_REG_TO_mp : Cx.Hard Cx.PSPACE (PlanExMP d (FClass.inter FClass.REG FClass.TO)) :=
  thm_4_3_1.1.of_redP (redP_planExMP d hd (matches_REG.inter matches_TO))

/-- Tail-recursive totally ordered problems: PSPACE-hard. -/
theorem hard_TR_TO_fm : Cx.Hard Cx.PSPACE (PlanExFM c (FClass.inter FClass.TR FClass.TO)) :=
  cor_4_3_2.1.of_redP (redP_planExFM c (matches_TR.inter matches_TO))

include hd in
theorem hard_TR_TO_mp : Cx.Hard Cx.PSPACE (PlanExMP d (FClass.inter FClass.TR FClass.TO)) :=
  cor_4_3_2.1.of_redP (redP_planExMP d hd (matches_TR.inter matches_TO))

/-- Acyclic totally ordered problems: PSPACE-hard. -/
theorem hard_ACYC_TO_fm : Cx.Hard Cx.PSPACE (PlanExFM c (FClass.inter FClass.ACYC FClass.TO)) :=
  thm_4_3_4.1.of_redP (redP_planExFM c (matches_ACYC.inter matches_TO))

include hd in
theorem hard_ACYC_TO_mp : Cx.Hard Cx.PSPACE (PlanExMP d (FClass.inter FClass.ACYC FClass.TO)) :=
  thm_4_3_4.1.of_redP (redP_planExMP d hd (matches_ACYC.inter matches_TO))

/-- Totally ordered problems: EXPTIME-hard. -/
theorem hard_TO_fm : Cx.Hard Cx.EXPTIME (PlanExFM c FClass.TO) :=
  thm_4_3_6.of_redP (redP_planExFM c matches_TO)

include hd in
theorem hard_TO_mp : Cx.Hard Cx.EXPTIME (PlanExMP d FClass.TO) :=
  thm_4_3_6.of_redP (redP_planExMP d hd matches_TO)

/-- Acyclic problems (with a totally ordered initial network): NEXPTIME-hard. -/
theorem hard_ACYC_fm : Cx.Hard Cx.NEXPTIME (PlanExFM c (FClass.inter FClass.ACYC FClass.TOtn)) :=
  thm_4_3_7_acyc.of_redP (redP_planExFM c (matches_ACYC.inter matches_TOtn))

include hd in
theorem hard_ACYC_mp : Cx.Hard Cx.NEXPTIME (PlanExMP d (FClass.inter FClass.ACYC FClass.TOtn)) :=
  thm_4_3_7_acyc.of_redP (redP_planExMP d hd (matches_ACYC.inter matches_TOtn))

/-- Tail-recursive problems (with a totally ordered initial network): EXPSPACE-hard. -/
theorem hard_TR_fm : Cx.Hard Cx.EXPSPACE (PlanExFM c (FClass.inter FClass.TR FClass.TOtn)) :=
  thm_4_3_7_tr.of_redP (redP_planExFM c (matches_TR.inter matches_TOtn))

include hd in
theorem hard_TR_mp : Cx.Hard Cx.EXPSPACE (PlanExMP d (FClass.inter FClass.TR FClass.TOtn)) :=
  thm_4_3_7_tr.of_redP (redP_planExMP d hd (matches_TR.inter matches_TOtn))

/-- Unrestricted problems: undecidable ([CB21, Thm. 3.1], [CB22]). -/
theorem undecidable_fm : ¬ Cx.Decidable (PlanExFM c FClass.UNRES) := fun h =>
  thm_4_1_1 (ComputablePred.computable_of_manyOneReducible
    (redP_planExFM c matches_UNRES).redC h)

include hd in
theorem undecidable_mp : ¬ Cx.Decidable (PlanExMP d FClass.UNRES) := fun h =>
  thm_4_1_1 (ComputablePred.computable_of_manyOneReducible
    (redP_planExMP d hd matches_UNRES).redC h)

end

end FOND
