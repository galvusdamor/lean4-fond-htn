import FondHtn.Transfer.Classes
/-!
# Deterministic descriptions as FOND descriptions

`FOND.detDesc : ProbDesc → FProbDesc` writes a description of the deterministic article model as
a FOND description: every action gets its single effect, a fresh action `g` checks the goal, and
the initial task network is followed by a fresh task `i ↦ g`.

* `FOND.detDesc_valid` — well-formedness is preserved;
* `FOND.toProblem_detDesc` — the described problem is `detFond p.toProblem i g`;
* `FOND.pt_detDesc` — the translation runs in polynomial time.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.TaskNetwork

/-- The maximum step. -/
def maxStep (b s : ℕ) : ℕ := bif decide (b < s) then s else b

/-- A number larger than all entries of a list. -/
def freshOf (l : List ℕ) : ℕ := l.foldr maxStep 0 + 1

theorem le_foldr_maxStep {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr maxStep 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp only [List.foldr_cons, maxStep]
    rcases List.mem_cons.1 h with rfl | h
    · by_cases hy : x < l.foldr maxStep 0 <;> simp [hy] <;> omega
    · have := ih h
      by_cases hy : y < l.foldr maxStep 0 <;> simp [hy] <;> omega

theorem lt_freshOf {l : List ℕ} {x : ℕ} (h : x ∈ l) : x < freshOf l :=
  Nat.lt_succ_of_le (le_foldr_maxStep h)

theorem freshOf_not_mem (l : List ℕ) : freshOf l ∉ l := fun h => lt_irrefl _ (lt_freshOf h)

theorem pt_freshOf {α : Type} [BEnc α] {f : α → List ℕ} (hf : PT f) :
    PT fun a => freshOf (f a) := by
  obtain ⟨cl, dl, hl'⟩ := hf.pb
  unfold freshOf
  refine PT.succ (PT.foldr (g := fun _ b s => maxStep b s) hf (PT.const 0) ?_ (c := cl) (d := dl)
    fun a s b hb => ?_)
  · exact PT.cond (PT.lt (PT.fst.comp PT.snd) (PT.snd.comp PT.snd)) (PT.snd.comp PT.snd)
      (PT.fst.comp PT.snd)
  · have := (sz_le_of_mem hb).trans (hl' a)
    unfold maxStep
    by_cases hbs : b < s <;> simp [hbs] <;> omega

/-- The FOND version of a deterministic action description. -/
def detAct (a : ActDesc) : FActDesc := (a.1, a.2.1, a.2.2.1, [(a.2.2.2.1, a.2.2.2.2)])

/-- The fresh goal action name. -/
def goalName (p : ProbDesc) : ℕ := freshOf (p.actions.map ActDesc.name)

/-- The fresh id of the goal task. -/
def goalId (p : ProbDesc) : ℕ := freshOf p.tnI.ids

/-- The initial task network followed by the goal task. -/
def appendDesc (t : TnDesc) (i g : ℕ) : TnDesc :=
  (t.ids ++ [i], t.ordList ++ t.ids.map (fun x => (x, i)), t.lbl ++ [(i, false, g)])

/-- **The translation.** -/
def detDesc (p : ProbDesc) : FProbDesc :=
  ((p.actions.map detAct ++ [(goalName p, p.goalPos, p.goalNeg, [([], [])])], p.methods),
    (p.init, appendDesc p.tnI (goalId p) (goalName p)))

/-! ## Polynomial time -/

theorem pt_detDesc : PT detDesc := by
  have hacts : PT fun p : ProbDesc => p.actions := PT.fst.comp PT.fst
  have htn : PT fun p : ProbDesc => p.tnI := PT.fst.comp (PT.snd.comp PT.snd)
  have hg : PT goalName := pt_freshOf (PT.map hacts (PT.fst.comp PT.snd))
  have hi : PT goalId := pt_freshOf (PT.fst.comp htn)
  have hdetAct : PT detAct := by
    unfold detAct
    exact PT.pair PT.fst (PT.pair (PT.fst.comp PT.snd) (PT.pair (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.single (PT.pair (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd)))
        (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))))
  have hacts' : PT fun p : ProbDesc =>
      p.actions.map detAct ++ [(goalName p, p.goalPos, p.goalNeg, [([], [])])] :=
    PT.append (PT.map hacts (hdetAct.comp PT.snd))
      (PT.single (PT.pair hg (PT.pair (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd)))
        (PT.pair (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))) (PT.const _)))))
  have happ : PT fun p : ProbDesc => appendDesc p.tnI (goalId p) (goalName p) := by
    unfold appendDesc
    refine PT.pair (PT.append (PT.fst.comp htn) (PT.single hi)) (PT.pair ?_ ?_)
    · exact PT.append (PT.fst.comp (PT.snd.comp htn))
        (PT.map (PT.fst.comp htn) (PT.pair PT.snd (hi.comp PT.fst)))
    · exact PT.append (PT.snd.comp (PT.snd.comp htn))
        (PT.single (PT.pair hi (PT.pair (PT.const false) hg)))
  unfold detDesc
  exact PT.pair (PT.pair hacts' (PT.snd.comp PT.fst)) (PT.pair (PT.fst.comp PT.snd) happ)

/-! ## Well-formedness -/

theorem _root_.HTN.Article.TnValid.mono {prim prim' : ℕ → Prop} {t : TnDesc} (h : TnValid prim t)
    (hp : ∀ n, prim n → prim' n) : TnValid prim' t :=
  ⟨h.nodup, h.ord_mem, h.irrefl, h.trans, h.lbl_perm, fun q hq hq' => hp _ (h.prim_ok q hq hq')⟩

@[simp] theorem appendDesc_ids (t : TnDesc) (i g : ℕ) : (appendDesc t i g).ids = t.ids ++ [i] :=
  rfl

@[simp] theorem appendDesc_ordList (t : TnDesc) (i g : ℕ) :
    (appendDesc t i g).ordList = t.ordList ++ t.ids.map (fun x => (x, i)) := rfl

@[simp] theorem appendDesc_lbl (t : TnDesc) (i g : ℕ) :
    (appendDesc t i g).lbl = t.lbl ++ [(i, false, g)] := rfl

theorem appendDesc_valid {prim : ℕ → Prop} {t : TnDesc} (h : TnValid prim t) {i g : ℕ}
    (hi : i ∉ t.ids) (hg : prim g) : TnValid prim (appendDesc t i g) where
  nodup := List.nodup_append.2 ⟨h.nodup, List.nodup_singleton _, by
    intro x hx y hy; simp at hy; subst hy; exact fun e => hi (e ▸ hx)⟩
  ord_mem := by
    intro q hq
    simp only [appendDesc_ordList, appendDesc_ids, List.mem_append, List.mem_map,
      List.mem_singleton] at hq ⊢
    rcases hq with hq | ⟨x, hx, rfl⟩
    · exact ⟨Or.inl (h.ord_mem q hq).1, Or.inl (h.ord_mem q hq).2⟩
    · exact ⟨Or.inl hx, Or.inr rfl⟩
  irrefl := by
    intro a ha
    simp only [appendDesc_ordList, List.mem_append, List.mem_map, Prod.mk.injEq] at ha
    rcases ha with ha | ⟨x, hx, rfl, rfl⟩
    · exact h.irrefl a ha
    · exact hi hx
  trans := by
    intro a b c hab hbc
    simp only [appendDesc_ordList, List.mem_append, List.mem_map, Prod.mk.injEq] at hab hbc ⊢
    rcases hab with hab | ⟨x, hx, rfl, rfl⟩ <;> rcases hbc with hbc | ⟨y, hy, rfl, rfl⟩
    · exact Or.inl (h.trans _ _ _ hab hbc)
    · exact Or.inr ⟨a, (h.ord_mem _ hab).1, rfl, rfl⟩
    · exact absurd (h.ord_mem _ hbc).1 hi
    · exact absurd hy hi
  lbl_perm := by
    simp only [appendDesc_lbl, appendDesc_ids, List.map_append, List.map_cons, List.map_nil]
    exact h.lbl_perm.append_right _
  prim_ok := by
    intro q hq hq'
    simp only [appendDesc_lbl, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact h.prim_ok q hq hq'
    · exact hg

theorem goalName_not_mem (p : ProbDesc) : goalName p ∉ p.actions.map ActDesc.name :=
  freshOf_not_mem _

theorem goalId_not_mem (p : ProbDesc) : goalId p ∉ p.tnI.ids := freshOf_not_mem _

theorem detDesc_names (p : ProbDesc) :
    (detDesc p).actions.map FActDesc.name = p.actions.map ActDesc.name ++ [goalName p] := by
  simp [detDesc, FProbDesc.actions, List.map_append, detAct, FActDesc.name, ActDesc.name]

theorem detDesc_valid {p : ProbDesc} (hp : p.Valid) : (detDesc p).Valid where
  names_nodup := by
    rw [detDesc_names]
    exact List.nodup_append.2 ⟨hp.names_nodup, List.nodup_singleton _, by
      intro x hx y hy; simp at hy; subst hy; exact fun e => goalName_not_mem p (e ▸ hx)⟩
  effs_ne := by
    intro a ha
    simp only [detDesc, FProbDesc.actions, List.mem_append, List.mem_map, List.mem_singleton] at ha
    rcases ha with ⟨b, -, rfl⟩ | rfl <;> simp [FActDesc.effs, detAct]
  tnI := by
    refine appendDesc_valid (hp.tnI.mono fun n hn => ?_) (goalId_not_mem p) ?_
    · unfold FProbDesc.Declared; rw [detDesc_names]
      exact List.mem_append_left _ hn
    · unfold FProbDesc.Declared; rw [detDesc_names]; simp
  methods := by
    intro m hm
    refine (hp.methods m hm).mono fun n hn => ?_
    unfold FProbDesc.Declared; rw [detDesc_names]
    exact List.mem_append_left _ hn

/-! ## The described problem -/

theorem lookup_append {β : Type} (l l' : List (ℕ × β)) (x : ℕ) :
    (l ++ l').lookup x = (l.lookup x).or (l'.lookup x) := by
  induction l with
  | nil => simp [List.lookup]
  | cons q l ih =>
    simp only [List.cons_append, List.lookup]
    split <;> simp_all

theorem lookup_eq_none {β : Type} {l : List (ℕ × β)} {x : ℕ} (h : x ∉ l.map Prod.fst) :
    l.lookup x = none := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup]
    split
    · rename_i hq; exact absurd (by simp at hq; omega) h.1
    · exact ih h.2

theorem appendDesc_toTaskNetwork {prim : ℕ → Prop} {t : TnDesc} (h : TnValid prim t)
    {i g : ℕ} (hi : i ∉ t.ids) (hg : prim g) :
    (appendDesc t i g).toTaskNetwork = t.toTaskNetwork.appendLast i g := by
  have h' := appendDesc_valid h hi hg
  refine ext' ?_ ?_ ?_
  · ext x; simp [appendDesc, TnDesc.toTaskNetwork, TnDesc.ids, appendLast, or_comm]
  · funext x y
    apply propext
    change (appendDesc t i g).ordOf x y ↔ _
    rw [h'.ordOf_iff]
    simp only [appendLast, TnDesc.toTaskNetwork, h.ordOf_iff]
    simp only [appendDesc, TnDesc.ordList, List.mem_append, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro (hxy | ⟨z, hz, rfl, rfl⟩)
      · exact Or.inl ⟨hxy, fun e => hi (e ▸ (h.ord_mem _ hxy).1),
          fun e => hi (e ▸ (h.ord_mem _ hxy).2)⟩
      · exact Or.inr ⟨by simpa [TnDesc.ids] using hz, fun e => hi (e ▸ hz), rfl⟩
    · rintro (⟨hxy, -, -⟩ | ⟨hx, -, rfl⟩)
      · exact Or.inl hxy
      · exact Or.inr ⟨x, by simpa [TnDesc.toTaskNetwork] using hx, rfl, rfl⟩
  · funext x
    have hnone : t.lbl.lookup i = none := lookup_eq_none (fun hm =>
      hi ((h.lbl_perm.mem_iff).1 hm))
    change (appendDesc t i g).label x = (if x = i then Sum.inl g else t.label x)
    unfold TnDesc.label
    rw [appendDesc_lbl, lookup_append]
    by_cases hx : x = i
    · subst hx; rw [hnone]; simp [List.lookup]
    · have : ([(i, false, g)] : List (ℕ × Bool × ℕ)).lookup x = none := by
        simp only [List.lookup]; split <;> simp_all
      rw [this, Option.or_none, if_neg hx]

theorem detDesc_δ {p : ProbDesc} (hp : p.Valid) (a : ℕ) :
    (detDesc p).δ a = (detFond p.toProblem (goalId p) (goalName p)).δ a := by
  simp only [FProbDesc.δ, detFond, ProbDesc.toProblem, ProbDesc.δ]
  have hfind : ((detDesc p).actions.find? fun x => x.name == a) =
      ((p.actions.find? fun x => x.name == a).map detAct).or
        ([(goalName p, p.goalPos, p.goalNeg, [([], [])])].find? fun x => x.name == a) := by
    simp only [detDesc, FProbDesc.actions, List.find?_append, List.find?_map]
    rfl
  rw [hfind]
  cases hf : p.actions.find? (fun x => x.name == a) with
  | some x =>
    have hxa : x.name = a := by simpa using List.find?_some hf
    have hag : a ≠ goalName p := by
      rintro rfl
      exact goalName_not_mem p (List.mem_map.2 ⟨x, List.mem_of_find?_eq_some hf, hxa⟩)
    simp only [Option.map_some, Option.some_or, hag, if_false]
    apply Action.ext' <;> ext <;>
      simp [FActDesc.toAction, ActDesc.toAction, Action.ofDet, detAct, FActDesc.effs]
  | none =>
    simp only [Option.map_none, Option.none_or]
    by_cases hag : a = goalName p
    · subst hag
      have : ([(goalName p, p.goalPos, p.goalNeg, [([], [])])] : List FActDesc).find?
          (fun x => x.name == goalName p) = some (goalName p, p.goalPos, p.goalNeg, [([], [])]) := by
        simp [FActDesc.name]
      rw [this, if_pos rfl]
      apply Action.ext' <;> ext <;> simp [FActDesc.toAction, FActDesc.effs]
    · have : ([(goalName p, p.goalPos, p.goalNeg, [([], [])])] : List FActDesc).find?
          (fun x => x.name == a) = none := by
        simp [FActDesc.name, Ne.symm hag]
      rw [this, if_neg hag]
      apply Action.ext' <;> simp [Action.ofDet]

/-- **The described problem is `detFond`.** -/
theorem toProblem_detDesc {p : ProbDesc} (hp : p.Valid) :
    (detDesc p).toProblem = detFond p.toProblem (goalId p) (goalName p) := by
  have hv : TnValid (detDesc p).Declared p.tnI := hp.tnI.mono fun n hn => by
    unfold FProbDesc.Declared; rw [detDesc_names]; exact List.mem_append_left _ hn
  have hg : (detDesc p).Declared (goalName p) := by
    unfold FProbDesc.Declared; rw [detDesc_names]; simp
  have htn : (detDesc p).tnI.toTaskNetwork =
      p.tnI.toTaskNetwork.appendLast (goalId p) (goalName p) :=
    appendDesc_toTaskNetwork hv (goalId_not_mem p) hg
  have hδ : (detDesc p).δ = (detFond p.toProblem (goalId p) (goalName p)).δ :=
    funext (detDesc_δ hp)
  unfold FProbDesc.toProblem
  rw [hδ, htn]
  rfl

end FOND
