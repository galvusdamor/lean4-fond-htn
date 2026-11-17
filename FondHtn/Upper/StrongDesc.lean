import FondHtn.Upper.StrongCompile
import FondHtn.Hardness.FromDet
import FondHtn.Cx.Closure2
import HtnComplexity.Article.NoHTNNP
import HtnComplexity.Article.TOExp
import HtnComplexity.Article.ProgCors
import HtnComplexity.Article.AcycNExp
import HtnComplexity.Article.AcycRegNP
import HtnComplexity.Article.SemiDec
/-!
# Strong LD plan existence reduces to deterministic plan existence ([CB21, Thm. 4.7, Cor. 4.8])

`FOND.strongDesc : FProbDesc → ProbDesc` is the description-level version of
`FOND.Problem.strongDet` (facts `f` ↦ `2f` for the intersection copy and `2f + 1` for the union
copy).  It keeps the methods and the initial task network, so every structural class is
preserved, and it runs in polynomial time.  With the closure of the complexity classes under
`≤ₚ` (`FondHtn/Cx/Closure*.lean`) every deterministic upper bound becomes an upper bound for strong
LD plan existence, and for totally ordered problems also for strong OD plan existence
([CB21, Prop. 2.15]).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

/-! ## The fact coding -/

/-- The intersection copy. -/
def e₁ (n : ℕ) : ℕ := 2 * n
/-- The union copy. -/
def e₂ (n : ℕ) : ℕ := 2 * n + 1

/-- The fact split of `ℕ` into even and odd numbers. -/
def κN : FactSplit ℕ ℕ where
  ι₁ := e₁
  ι₂ := e₂
  inj₁ := fun a b h => by simp only [e₁] at h; omega
  inj₂ := fun a b h => by simp only [e₂] at h; omega
  ne := fun a b h => by simp only [e₁, e₂] at h; omega

theorem pt_e₁ : PT e₁ := (PT.affine 2 0 PT.id).of_eq fun _ => rfl
theorem pt_e₂ : PT e₂ := (PT.affine 2 1 PT.id).of_eq fun _ => rfl

/-! ## Effects as lists -/

section Lists

variable (L : List (List ℕ × List ℕ))

/-- Facts added by every effect. -/
def addIL : List ℕ := L.headI.1.filter fun f => L.all fun e => decide (f ∈ e.1)
/-- Facts deleted and not re-added by some effect. -/
def delIL : List ℕ := L.flatMap fun e => e.2.filter fun f => !decide (f ∈ e.1)
/-- Facts added by some effect. -/
def addUL : List ℕ := L.flatMap fun e => e.1
/-- Facts deleted by every effect. -/
def delUL : List ℕ := L.headI.2.filter fun f => L.all fun e => decide (f ∈ e.2)

end Lists

/-- The deterministic action description. -/
def strongActDesc (x : FActDesc) : ActDesc :=
  (x.1, x.2.1.map e₁, x.2.2.1.map e₂, (addIL x.effs).map e₁ ++ (addUL x.effs).map e₂,
    (delIL x.effs).map e₁ ++ (delUL x.effs).map e₂)

/-- **The translation.** -/
def strongDesc (p : FProbDesc) : ProbDesc :=
  ((p.actions.map strongActDesc, p.methods), (p.init.map e₁ ++ p.init.map e₂, p.tnI, [], []))

/-! ## Polynomial time -/

theorem pt_strongActDesc : PT strongActDesc := by
  have hE : PT fun x : FActDesc => x.effs := PT.snd.comp (PT.snd.comp PT.snd)
  have hAI : PT fun x : FActDesc => addIL x.effs := by
    unfold addIL
    exact PT.filter (PT.fst.comp (PT.headI hE))
      (PT.all (hE.comp PT.fst) (PT.elem (PT.fst.comp PT.snd) (PT.snd.comp PT.fst)))
  have hDI : PT fun x : FActDesc => delIL x.effs := by
    unfold delIL
    exact PT.flatMap hE (PT.filter (PT.snd.comp PT.snd)
      (PT.not (PT.elem (PT.fst.comp (PT.snd.comp PT.fst)) PT.snd)))
  have hAU : PT fun x : FActDesc => addUL x.effs := by
    unfold addUL; exact PT.flatMap hE (PT.fst.comp PT.snd)
  have hDU : PT fun x : FActDesc => delUL x.effs := by
    unfold delUL
    exact PT.filter (PT.snd.comp (PT.headI hE))
      (PT.all (hE.comp PT.fst) (PT.elem (PT.snd.comp PT.snd) (PT.snd.comp PT.fst)))
  unfold strongActDesc
  exact PT.pair PT.fst (PT.pair (PT.map (PT.fst.comp PT.snd) (pt_e₁.comp PT.snd))
    (PT.pair (PT.map (PT.fst.comp (PT.snd.comp PT.snd)) (pt_e₂.comp PT.snd))
      (PT.pair (PT.append (PT.map hAI (pt_e₁.comp PT.snd)) (PT.map hAU (pt_e₂.comp PT.snd)))
        (PT.append (PT.map hDI (pt_e₁.comp PT.snd)) (PT.map hDU (pt_e₂.comp PT.snd))))))

theorem pt_strongDesc : PT strongDesc := by
  have hacts : PT fun p : FProbDesc => p.actions := PT.fst.comp PT.fst
  have hinit : PT fun p : FProbDesc => p.init := PT.fst.comp PT.snd
  unfold strongDesc
  exact PT.pair (PT.pair (PT.map hacts (pt_strongActDesc.comp PT.snd)) (PT.snd.comp PT.fst))
    (PT.pair (PT.append (PT.map hinit (pt_e₁.comp PT.snd)) (PT.map hinit (pt_e₂.comp PT.snd)))
      (PT.pair (PT.snd.comp PT.snd) (PT.const _)))

/-! ## Well-formedness -/

theorem strongDesc_names (p : FProbDesc) :
    (strongDesc p).actions.map ActDesc.name = p.actions.map FActDesc.name := by
  simp [strongDesc, ProbDesc.actions, strongActDesc, ActDesc.name, FActDesc.name]

theorem strongDesc_declared (p : FProbDesc) (n : ℕ) :
    (strongDesc p).Declared n ↔ p.Declared n := by
  unfold ProbDesc.Declared FProbDesc.Declared; rw [strongDesc_names]

theorem strongDesc_valid {p : FProbDesc} (hp : p.Valid) : (strongDesc p).Valid where
  names_nodup := by rw [strongDesc_names]; exact hp.names_nodup
  tnI := hp.tnI.mono fun n hn => (strongDesc_declared p n).2 hn
  methods := fun m hm => (hp.methods m hm).mono fun n hn => (strongDesc_declared p n).2 hn

/-! ## The described problem -/

section Sets

variable {L : List (List ℕ × List ℕ)}

theorem toAction_effs (x : FActDesc) :
    x.toAction.effs = {e | ∃ y ∈ x.effs, e = ({f | f ∈ y.1}, {f | f ∈ y.2})} := rfl

theorem mem_addIL (hL : L ≠ []) (f : ℕ) : f ∈ addIL L ↔ ∀ y ∈ L, f ∈ y.1 := by
  simp only [addIL, List.mem_filter, List.all_eq_true, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨h _ ?_, h⟩
    obtain ⟨y, l, rfl⟩ := List.exists_cons_of_ne_nil hL
    simp

theorem mem_delUL (hL : L ≠ []) (f : ℕ) : f ∈ delUL L ↔ ∀ y ∈ L, f ∈ y.2 := by
  simp only [delUL, List.mem_filter, List.all_eq_true, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨h _ ?_, h⟩
    obtain ⟨y, l, rfl⟩ := List.exists_cons_of_ne_nil hL
    simp

theorem mem_delIL (f : ℕ) : f ∈ delIL L ↔ ∃ y ∈ L, f ∈ y.2 ∧ f ∉ y.1 := by
  simp [delIL]

theorem mem_addUL (f : ℕ) : f ∈ addUL L ↔ ∃ y ∈ L, f ∈ y.1 := by
  simp [addUL]

end Sets

theorem strongActDesc_toAction {x : FActDesc} (hx : x.effs ≠ []) :
    (strongActDesc x).toAction = x.toAction.strongAct κN := by
  have himg : ∀ (e : ℕ → ℕ) (l : List ℕ), {g | g ∈ l.map e} = e '' {f | f ∈ l} := by
    intro e l; ext g; simp
  simp only [ActDesc.toAction, strongActDesc, Action.strongAct, κN, List.mem_append]
  congr 1
  · exact himg _ _
  · exact himg _ _
  · ext g
    simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_map, Set.mem_image]
    refine or_congr ?_ ?_
    · refine exists_congr fun f => and_congr_left fun _ => ?_
      rw [mem_addIL hx]
      simp only [Action.addI, toAction_effs, Set.mem_setOf_eq]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩; exact h y hy
      · intro h y hy; exact h _ ⟨y, hy, rfl⟩
    · refine exists_congr fun f => and_congr_left fun _ => ?_
      rw [mem_addUL]
      simp only [Action.addU, toAction_effs, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, hy, hf⟩; exact ⟨_, ⟨y, hy, rfl⟩, hf⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, hf⟩; exact ⟨y, hy, hf⟩
  · ext g
    simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_map, Set.mem_image]
    refine or_congr ?_ ?_
    · refine exists_congr fun f => and_congr_left fun _ => ?_
      rw [mem_delIL]
      simp only [Action.delI, toAction_effs, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, hy, hf⟩; exact ⟨_, ⟨y, hy, rfl⟩, hf⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, hf⟩; exact ⟨y, hy, hf⟩
    · refine exists_congr fun f => and_congr_left fun _ => ?_
      rw [mem_delUL hx]
      simp only [Action.delU, toAction_effs, Set.mem_setOf_eq]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩; exact h y hy
      · intro h y hy; exact h _ ⟨y, hy, rfl⟩

theorem strongDesc_δ {p : FProbDesc} (hp : p.Valid) (a : ℕ) :
    (strongDesc p).δ a = (p.δ a).strongAct κN := by
  simp only [ProbDesc.δ, FProbDesc.δ]
  have hfind : ((strongDesc p).actions.find? fun x => x.name == a) =
      (p.actions.find? fun x => x.name == a).map strongActDesc := by
    simp only [strongDesc, ProbDesc.actions, List.find?_map]
    rfl
  rw [hfind]
  cases hf : p.actions.find? (fun x => x.name == a) with
  | some x =>
    simp only [Option.map_some]
    exact strongActDesc_toAction (hp.effs_ne x (List.mem_of_find?_eq_some hf))
  | none =>
    simp only [Option.map_none]
    simp [Action.strongAct, Action.addI, Action.delI, Action.addU, Action.delU]

/-- **The described problem is `strongDet`.** -/
theorem toProblem_strongDesc {p : FProbDesc} (hp : p.Valid) :
    (strongDesc p).toProblem = p.toProblem.strongDet κN := by
  have hδ : (strongDesc p).δ = fun a => (p.toProblem.δ a).strongAct κN :=
    funext (strongDesc_δ hp)
  have hinit : ({f | f ∈ (strongDesc p).init} : Set ℕ) = κN.enc {p.toProblem.init} := by
    ext g
    simp only [strongDesc, ProbDesc.init, List.mem_append, List.mem_map, Set.mem_setOf_eq,
      FactSplit.enc, Set.sInter_singleton, Set.sUnion_singleton, Set.mem_union, Set.mem_image]
    rfl
  unfold ProbDesc.toProblem Problem.strongDet
  rw [hδ, hinit]
  congr 1 <;> ext <;> simp [strongDesc, ProbDesc.goalPos, ProbDesc.goalNeg]

/-- Strong LD solvability of a well-formed description is plan existence of its translation. -/
theorem strongLD_iff_strongDesc {p : FProbDesc} (hp : p.Valid) :
    p.toProblem.StrongLDSolvable ↔ (strongDesc p).toProblem.Solvable := by
  rw [toProblem_strongDesc hp]
  exact Problem.strongLDSolvable_iff (FProbDesc.toProblem_wf hp)

/-! ## Classes and reductions -/

/-- The deterministic class `Y` and the FOND class `Y'` agree on translations. -/
def SMatches (Y' : FClass) (Y : PClass) : Prop :=
  ∀ p : FProbDesc, p.Valid → (Y' p.toProblem ↔ Y (strongDesc p).toProblem)

theorem SMatches.inter {Y' Z' : FClass} {Y Z : PClass} (h₁ : SMatches Y' Y) (h₂ : SMatches Z' Z) :
    SMatches (FClass.inter Y' Z') (fun P => Y P ∧ Z P) :=
  fun p hp => and_congr (h₁ p hp) (h₂ p hp)

theorem sameShape_strongDesc (p : FProbDesc) :
    HTN.Problem.SameShape p.toProblem.toArt.toPos (strongDesc p).toProblem.toPos :=
  ⟨rfl, fun _ => ⟨HTN.Problem.reachableName_of (P := p.toProblem.toArt.toPos)
      (P' := (strongDesc p).toProblem.toPos) rfl (fun t ht c hc => ⟨t, ht, hc⟩),
    HTN.Problem.reachableName_of (P := (strongDesc p).toProblem.toPos)
      (P' := p.toProblem.toArt.toPos) rfl (fun t ht c hc => ⟨t, ht, hc⟩)⟩⟩

theorem sMatches_ACYC : SMatches FClass.ACYC (fun P => P.IsACYC) :=
  fun p _ => (sameShape_strongDesc p).isAcyclic
theorem sMatches_REG : SMatches FClass.REG (fun P => P.IsREG) :=
  fun p _ => (sameShape_strongDesc p).isRegularM
theorem sMatches_TR : SMatches FClass.TR (fun P => P.IsTailREC) :=
  fun p _ => (sameShape_strongDesc p).isTailRecursive
theorem sMatches_TOtn : SMatches FClass.TOtn (fun P => P.IsTO_tnI) := fun _ _ => Iff.rfl
theorem sMatches_TOM : SMatches FClass.TOM (fun P => P.IsTO_M) :=
  fun p _ => (sameShape_strongDesc p).isTO_M
theorem sMatches_TO : SMatches FClass.TO (fun P => P.IsTO) :=
  fun p hp => and_congr (sMatches_TOtn p hp) (sMatches_TOM p hp)
theorem sMatches_PRIM : SMatches FClass.PRIM (fun P => P.IsNoHTN) := fun _ _ => Iff.rfl
theorem sMatches_UNRES : SMatches FClass.UNRES UNRES := fun _ _ => Iff.rfl

/-- A description that is not well formed. -/
def badPDesc : ProbDesc := (([(0, [], [], [], []), (0, [], [], [], [])], []), ([], ([], [], []), [], []))

theorem badPDesc_not_valid : ¬ badPDesc.Valid := fun h => by
  have := h.names_nodup
  simp [badPDesc, ProbDesc.actions, ActDesc.name] at this

/-- The reduction. -/
def strongRed (p : FProbDesc) : ProbDesc := if p.Valid then strongDesc p else badPDesc

theorem pt_strongRed : PT strongRed := by
  refine (PT.cond FProbDesc.pt_validB pt_strongDesc (PT.const badPDesc)).of_eq fun p => ?_
  simp only [strongRed]
  by_cases hp : p.Valid
  · rw [if_pos hp, (FProbDesc.validB_iff p).2 hp]; rfl
  · rw [if_neg hp]
    have : p.validB = false := by
      cases h : p.validB
      · rfl
      · exact absurd ((FProbDesc.validB_iff p).1 h) hp
    rw [this]; rfl

/-- **Strong LD plan existence reduces to deterministic plan existence** (class by class). -/
theorem redP_strongLD {Y' : FClass} {Y : PClass} (hY : SMatches Y' Y) :
    Cx.RedP (PlanExFM .strongLD Y') (PlanEx Y) := by
  refine redP_codeLang pt_strongRed (fun p => ?_) badPDesc (fun h => badPDesc_not_valid h.1)
  by_cases hp : p.Valid
  · simp only [strongRed, if_pos hp]
    exact ⟨fun ⟨_, hy, hs⟩ => ⟨strongDesc_valid hp, (hY p hp).1 hy, (strongLD_iff_strongDesc hp).1 hs⟩,
      fun ⟨_, hy, hs⟩ => ⟨hp, (hY p hp).2 hy, (strongLD_iff_strongDesc hp).2 hs⟩⟩
  · simp only [strongRed, if_neg hp]
    exact ⟨fun h => absurd h.1 hp, fun h => absurd h.1 badPDesc_not_valid⟩

theorem toTotallyOrdered {P : Problem ℕ ℕ ℕ ℕ} (h : FClass.TO P) : P.IsTotallyOrdered := by
  have hs : HTN.Problem.SameShape P.toArt.toPos P.skeleton :=
    ⟨rfl, fun c => ⟨HTN.Problem.reachableName_of (P := P.toArt.toPos) (P' := P.skeleton) rfl
        (fun t ht c hc => ⟨t, ht, hc⟩),
      HTN.Problem.reachableName_of (P := P.skeleton) (P' := P.toArt.toPos) rfl
        (fun t ht c hc => ⟨t, ht, hc⟩)⟩⟩
  exact ⟨h.1, hs.isTO_M_of h.2⟩

/-- For totally ordered problems strong OD plan existence is strong LD plan existence. -/
theorem planExFM_strongOD_TO {Y' : FClass} (hY : ∀ P, Y' P → FClass.TO P) :
    PlanExFM .strongOD Y' = PlanExFM .strongLD Y' := by
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hp, hy, hs⟩
    refine ⟨p, rfl, hp, hy, ?_⟩
    exact (Problem.strongLDSolvable_iff_strongODSolvable (toTotallyOrdered (hY _ hy))
      (FProbDesc.toProblem_wf hp).tnI).2 hs
  · rintro ⟨p, rfl, hp, hy, hs⟩
    refine ⟨p, rfl, hp, hy, ?_⟩
    exact (Problem.strongLDSolvable_iff_strongODSolvable (toTotallyOrdered (hY _ hy))
      (FProbDesc.toProblem_wf hp).tnI).1 hs

end FOND
