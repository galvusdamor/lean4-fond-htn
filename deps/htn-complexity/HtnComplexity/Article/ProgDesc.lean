import HtnComplexity.Article.RunCheck
import HtnComplexity.Article.AcycCert
import HtnPlanning.Article.ProgIso
/-!
# Progression on descriptions

A **configuration** (`HTN.Article.PCfg`) is a state (a list of facts) and a task network
description; it stands for the task network `HTN.Article.cfgNet` with the *listed* order (not
its closure).  `HTN.Article.succs p c` lists the progressions of `c` (Def. 4.2): an unconstrained
primitive task that is applicable is applied and removed (`HTN.Article.progDesc`), an
unconstrained compound task is decomposed by a method of its name (`HTN.Article.decDesc`).  A
decomposition inserts a copy of the method's network (`HTN.Article.copyDesc`) on the *least*
numbers not used as ids (`HTN.Article.freshIds`), so ids stay small.

This file: the definitions, and the copy of a method's network as an isomorphic network.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- A configuration: the state and the remaining task network. -/
abbrev PCfg : Type := List ℕ × TnDesc

/-- **The network of a configuration**, with the listed order. -/
def cfgNet (d : TnDesc) : TaskNetwork ℕ ℕ ℕ where
  T := d.ids.toFinset
  ord a b := (a, b) ∈ d.ordList
  α := d.label

/-- The least `k` numbers that are not in `l`. -/
def freshIds (l : List ℕ) (k : ℕ) : List ℕ :=
  ((List.range (l.length + k)).filter fun x => decide (x ∉ l)).take k

/-- Renaming the ids `src` to `dst`, position by position. -/
def renOf (src dst : List ℕ) (x : ℕ) : ℕ := dst.getI (src.idxOf x)

/-- **The copy of a network description on the ids `dst`.** -/
def copyDesc (t : TnDesc) (dst : List ℕ) : TnDesc :=
  (dst, t.ordList.map (fun q => (renOf t.ids dst q.1, renOf t.ids dst q.2)),
    t.ids.map fun y => (renOf t.ids dst y, lblOf t y))

/-! ### Fresh ids -/

theorem length_freshIds (l : List ℕ) (k : ℕ) : (freshIds l k).length = k := by
  unfold freshIds
  rw [List.length_take]
  apply min_eq_left
  have h1 : ((List.range (l.length + k)).filter fun x => decide (x ∈ l)).length ≤ l.length := by
    have hnd : ((List.range (l.length + k)).filter fun x => decide (x ∈ l)).Nodup :=
      (List.nodup_range).filter _
    calc _ = ((List.range (l.length + k)).filter fun x => decide (x ∈ l)).toFinset.card :=
          (List.toFinset_card_of_nodup hnd).symm
      _ ≤ l.toFinset.card := Finset.card_le_card fun x hx => by
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx ⊢; exact hx.2
      _ ≤ l.length := List.toFinset_card_le _
  have h2 := List.length_eq_length_filter_add (l := List.range (l.length + k))
    (fun x => decide (x ∈ l))
  rw [List.length_range] at h2
  have h3 : ((List.range (l.length + k)).filter fun x => !decide (x ∈ l)) =
      ((List.range (l.length + k)).filter fun x => decide (x ∉ l)) :=
    List.filter_congr fun x _ => by simp
  rw [h3] at h2
  omega

theorem freshIds_nodup (l : List ℕ) (k : ℕ) : (freshIds l k).Nodup :=
  ((List.nodup_range).filter _).sublist (List.take_sublist _ _)

theorem not_mem_of_mem_freshIds {l : List ℕ} {k x : ℕ} (h : x ∈ freshIds l k) : x ∉ l := by
  have := (List.mem_filter.1 (List.mem_of_mem_take h)).2
  simpa using this

theorem lt_of_mem_freshIds {l : List ℕ} {k x : ℕ} (h : x ∈ freshIds l k) : x < l.length + k :=
  List.mem_range.1 (List.mem_filter.1 (List.mem_of_mem_take h)).1

/-! ### Renaming -/

section Ren

variable {src dst : List ℕ} (hs : src.Nodup) (hd : dst.Nodup) (hl : dst.length = src.length)
include hs hd hl

theorem renOf_mem {x : ℕ} (hx : x ∈ src) : renOf src dst x ∈ dst := by
  unfold renOf
  have hi : src.idxOf x < dst.length := hl ▸ List.idxOf_lt_length_of_mem hx
  rw [List.getI_eq_getElem _ hi]
  exact List.getElem_mem _

theorem renOf_inj {x y : ℕ} (hx : x ∈ src) (hy : y ∈ src) (e : renOf src dst x = renOf src dst y) :
    x = y := by
  unfold renOf at e
  have hix : src.idxOf x < dst.length := hl ▸ List.idxOf_lt_length_of_mem hx
  have hiy : src.idxOf y < dst.length := hl ▸ List.idxOf_lt_length_of_mem hy
  rw [List.getI_eq_getElem _ hix, List.getI_eq_getElem _ hiy] at e
  have := (List.Nodup.getElem_inj_iff hd).1 e
  rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hx),
    ← List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)]
  simp only [this]

theorem renOf_surj {z : ℕ} (hz : z ∈ dst) : ∃ x ∈ src, renOf src dst x = z := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  have hi' : i < src.length := hl ▸ hi
  refine ⟨src[i], List.getElem_mem _, ?_⟩
  unfold renOf
  rw [List.Nodup.idxOf_getElem hs, List.getI_eq_getElem _ hi]

end Ren

theorem lookup_map_ren {β : Type} {src : List ℕ} {f : ℕ → ℕ} {g : ℕ → β}
    (hinj : ∀ x ∈ src, ∀ y ∈ src, f x = f y → x = y) {x : ℕ} (hx : x ∈ src) :
    (src.map fun y => (f y, g y)).lookup (f x) = some (g x) := by
  induction src with
  | nil => simp at hx
  | cons a src ih =>
    by_cases hax : a = x
    · subst hax; simp [List.lookup]
    · have hfa : f a ≠ f x := fun e => hax (hinj a (by simp) x hx e)
      have : (f x == f a) = false := by simpa using Ne.symm hfa
      rw [List.map_cons, List.lookup, this]
      exact ih (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb]))
        (by simpa [Ne.symm hax] using hx)

theorem label_eq_of_lookup {d : TnDesc} {x : ℕ} {l : Bool × ℕ} (h : d.lbl.lookup x = some l) :
    d.label x = toSum l := by
  rw [label_eq_toSum]; unfold lblOf; rw [h]; rfl

/-! ### The copy of a method's network -/

section Copy

variable {t : TnDesc} {prim : ℕ → Prop} (ht : TnValid prim t) {dst : List ℕ} (hd : dst.Nodup)
  (hl : dst.length = t.ids.length)
include ht hd hl

/-- **The copy is isomorphic to the method's network.** -/
theorem isoVia_copyDesc : IsoVia (renOf t.ids dst) t.toTaskNetwork (cfgNet (copyDesc t dst)) := by
  have hs := ht.nodup
  have hinj := fun x hx y hy e => renOf_inj hs hd hl (x := x) (y := y) hx hy e
  refine ⟨⟨fun x hx => ?_, fun x hx y hy e => ?_, fun z hz => ?_⟩, fun x hx y hy => ?_,
    fun x hx => ?_⟩
  · simp only [TnDesc.toTaskNetwork, Finset.mem_coe, List.mem_toFinset] at hx
    simp only [cfgNet, copyDesc, TnDesc.ids, Finset.mem_coe, List.mem_toFinset]
    exact renOf_mem hs hd hl hx
  · simp only [TnDesc.toTaskNetwork, Finset.mem_coe, List.mem_toFinset] at hx hy
    exact hinj x hx y hy e
  · simp only [cfgNet, copyDesc, TnDesc.ids, Finset.mem_coe, List.mem_toFinset] at hz
    obtain ⟨x, hx, rfl⟩ := renOf_surj hs hd hl hz
    exact ⟨x, by simpa [TnDesc.toTaskNetwork] using hx, rfl⟩
  · simp only [TnDesc.toTaskNetwork, List.mem_toFinset] at hx hy
    simp only [TnDesc.toTaskNetwork, cfgNet, copyDesc, TnDesc.ordList]
    rw [ht.ordOf_iff]
    constructor
    · intro h
      exact List.mem_map.2 ⟨(x, y), h, rfl⟩
    · intro h
      obtain ⟨⟨x', y'⟩, hq, e⟩ := List.mem_map.1 h
      simp only [Prod.mk.injEq] at e
      obtain ⟨hx', hy'⟩ := ht.ord_mem _ hq
      rw [← hinj x' hx' x hx e.1, ← hinj y' hy' y hy e.2]
      exact hq
  · simp only [TnDesc.toTaskNetwork, List.mem_toFinset] at hx
    simp only [TnDesc.toTaskNetwork, cfgNet]
    rw [label_eq_of_lookup (d := copyDesc t dst) (show (copyDesc t dst).lbl.lookup _ = _ from
      lookup_map_ren hinj hx), label_eq_toSum]

/-- **The copy is well formed.** -/
theorem wf_copyDesc : (cfgNet (copyDesc t dst)).WF := by
  have hs := ht.nodup
  have hinj := fun x hx y hy e => renOf_inj hs hd hl (x := x) (y := y) hx hy e
  have hiso := isoVia_copyDesc ht hd hl
  have hwf := TnDesc.toTaskNetwork_wf t
  have hmem : ∀ a b, (cfgNet (copyDesc t dst)).ord a b → ∃ x ∈ t.ids, ∃ y ∈ t.ids,
      renOf t.ids dst x = a ∧ renOf t.ids dst y = b ∧ (x, y) ∈ t.ordList := by
    intro a b h
    obtain ⟨⟨x, y⟩, hq, e⟩ := List.mem_map.1 h
    simp only [Prod.mk.injEq] at e
    exact ⟨x, (ht.ord_mem _ hq).1, y, (ht.ord_mem _ hq).2, e.1, e.2, hq⟩
  refine ⟨fun h => ?_, fun h => ?_, fun a h => ?_, fun h₁ h₂ => ?_⟩
  · obtain ⟨x, hx, y, hy, rfl, rfl, -⟩ := hmem _ _ h
    exact hiso.mem (by simpa [TnDesc.toTaskNetwork] using hx)
  · obtain ⟨x, hx, y, hy, rfl, rfl, -⟩ := hmem _ _ h
    exact hiso.mem (by simpa [TnDesc.toTaskNetwork] using hy)
  · obtain ⟨x, hx, y, hy, e1, e2, hq⟩ := hmem _ _ h
    rw [← e2] at e1
    exact ht.irrefl x (by rw [hinj x hx y hy e1] at hq ⊢; exact hq)
  · obtain ⟨x, hx, y, hy, rfl, rfl, hq⟩ := hmem _ _ h₁
    obtain ⟨y', hy', z, hz, e, rfl, hq'⟩ := hmem _ _ h₂
    rw [hinj y' hy' y hy e] at hq'
    exact List.mem_map.2 ⟨(x, z), ht.trans _ _ _ hq hq', rfl⟩

end Copy

/-! ### Progression steps on descriptions -/

/-- Progressing the task `x`: it is removed. -/
def progDesc (d : TnDesc) (x : ℕ) : TnDesc :=
  (d.ids.filter (fun y => decide (y ≠ x)), d.ordList.filter (fun q => decide (q.1 ≠ x ∧ q.2 ≠ x)),
    d.lbl.filter (fun q => decide (q.1 ≠ x)))

/-- Decomposing the task `x` with the method `e`: the copy of `e`'s network on fresh ids
replaces `x`, inheriting its predecessors and successors. -/
def decDesc (d : TnDesc) (x : ℕ) (e : MethodDesc) : TnDesc :=
  ((d.ids.filter fun y => decide (y ≠ x)) ++ freshIds d.ids e.2.ids.length,
    ((copyDesc e.2 (freshIds d.ids e.2.ids.length)).ordList ++
      (d.ordList.filter fun q => decide (q.2 = x)).flatMap
        (fun q => (freshIds d.ids e.2.ids.length).map fun n => (q.1, n)) ++
      (d.ordList.filter fun q => decide (q.1 = x)).flatMap
        (fun q => (freshIds d.ids e.2.ids.length).map fun n => (n, q.2)) ++
      d.ordList.filter fun q => decide (q.1 ≠ x ∧ q.2 ≠ x)).dedup,
    (d.lbl.filter fun q => decide (q.1 ≠ x)) ++ (copyDesc e.2 (freshIds d.ids e.2.ids.length)).lbl)

/-- **The progressions of a configuration** (Def. 4.2). -/
def succs (p : ProbDesc) (c : PCfg) : List PCfg :=
  c.2.ids.flatMap fun x =>
    if c.2.ordList.all (fun q => q.2 != x) then
      if (lblOf c.2 x).1 then
        (p.methods.filter fun e => e.1 == (lblOf c.2 x).2).map fun e => (c.1, decDesc c.2 x e)
      else if (runStep p (true, c.1) (lblOf c.2 x).2).1 then
        [((runStep p (true, c.1) (lblOf c.2 x).2).2.dedup, progDesc c.2 x)]
      else []
    else []

/-- The initial configuration. -/
def initCfg (p : ProbDesc) : PCfg := (p.init.dedup, (p.tnI.ids, p.tnI.ordList.dedup, p.tnI.lbl))

/-- The goal test. -/
def goalB (p : ProbDesc) (s : List ℕ) : Bool :=
  p.goalPos.all (fun f => decide (f ∈ s)) && p.goalNeg.all (fun f => !decide (f ∈ s))

theorem goalB_iff (p : ProbDesc) (s : List ℕ) :
    goalB p s = true ↔ p.toProblem.GoalState {f | f ∈ s} := by
  simp only [goalB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => h1 f hf, Set.disjoint_left.2 fun f hf => h2 f hf⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => h1 hf, fun f hf => Set.disjoint_left.1 h2 hf⟩

/-- **The invariant of configurations.** -/
structure CfgInv (c : PCfg) : Prop where
  ids_nodup : c.2.ids.Nodup
  lbl_mem : ∀ q ∈ c.2.lbl, q.1 ∈ c.2.ids
  lbl_nodup : (c.2.lbl.map Prod.fst).Nodup
  ord_nodup : c.2.ordList.Nodup
  st_nodup : c.1.Nodup
  wf : (cfgNet c.2).WF

/-! ### Lookups -/

theorem lookup_filter_ne {β : Type} (l : List (ℕ × β)) {x y : ℕ} (h : y ≠ x) :
    (l.filter fun q => decide (q.1 ≠ x)).lookup y = l.lookup y := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨k, b⟩ := q
    by_cases hk : k = x
    · rw [List.filter_cons_of_neg (by simp [hk]), ih]
      subst hk
      have : (y == k) = false := by simpa using h
      simp only [List.lookup, this]
    · rw [List.filter_cons_of_pos (by simp [hk])]
      by_cases hyk : y = k
      · subst hyk; simp [List.lookup]
      · have : (y == k) = false := by simpa using hyk
        simp only [List.lookup, this]
        exact ih

theorem lookup_append' {β : Type} (l₁ l₂ : List (ℕ × β)) (y : ℕ) :
    (l₁ ++ l₂).lookup y = (l₁.lookup y).or (l₂.lookup y) := by
  induction l₁ with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨k, b⟩ := q
    by_cases hyk : y = k
    · subst hyk; simp [List.lookup]
    · have : (y == k) = false := by simpa using hyk
      simp [List.lookup, this, ih]

theorem lookup_none_of_not_mem {β : Type} {l : List (ℕ × β)} {y : ℕ} (h : ∀ q ∈ l, q.1 ≠ y) :
    l.lookup y = none :=
  List.lookup_eq_none_iff.2 fun q hq => by
    have := h q hq
    simp only [bne_iff_ne, ne_eq]
    exact fun e => this e.symm

theorem label_congr {d d' : TnDesc} {y : ℕ} (h : d.lbl.lookup y = d'.lbl.lookup y) :
    d.label y = d'.label y := by
  unfold TnDesc.label; rw [h]

theorem toSum_eq_inl {l : Bool × ℕ} {a : ℕ} : toSum l = Sum.inl a ↔ l = (false, a) := by
  obtain ⟨_ | _, n⟩ := l <;> simp [toSum]

theorem _root_.HTN.TaskNetwork.WF.of_agree {tn u : TaskNetwork ℕ ℕ ℕ} (h : tn.WF) (hag : tn.Agree u) :
    u.WF := by
  obtain ⟨hT, ho, -⟩ := hag
  exact ⟨fun hab => hT ▸ h.mem_left (ho ▸ hab), fun hab => hT ▸ h.mem_right (ho ▸ hab),
    fun a hab => h.irrefl a (ho ▸ hab), fun h₁ h₂ => ho ▸ h.trans (ho ▸ h₁) (ho ▸ h₂)⟩

/-! ### Agreement with the semantic steps -/

theorem unconstrained_cfgNet {d : TnDesc} {x : ℕ} (hx : x ∈ d.ids)
    (hu : ∀ q ∈ d.ordList, q.2 ≠ x) : (cfgNet d).Unconstrained x :=
  ⟨List.mem_toFinset.2 hx, fun y _ h => hu _ h rfl⟩

theorem agree_progDesc {d : TnDesc} {x : ℕ} (hu : ∀ q ∈ d.ordList, q.2 ≠ x) :
    ((cfgNet d).progress x).Agree (cfgNet (progDesc d x)) := by
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · ext y; simp [cfgNet, progDesc, TaskNetwork.progress, TnDesc.ids, and_comm]
  · funext a b
    simp only [cfgNet, progDesc, TaskNetwork.progress, TnDesc.ordList, List.mem_filter,
      decide_eq_true_eq, eq_iff_iff]
    constructor
    · rintro ⟨h, ha⟩
      exact ⟨h, ha, fun hb => hu _ h hb⟩
    · rintro ⟨h, ha, -⟩
      exact ⟨h, ha⟩
  · have hyx : y ≠ x := (Finset.mem_erase.1 hy).1
    exact label_congr (lookup_filter_ne _ hyx).symm

section Dec

variable {d : TnDesc} {x : ℕ} {e : MethodDesc} {prim : ℕ → Prop} (he : TnValid prim e.2)

theorem copy_keys_sub (he : TnValid prim e.2) :
    ∀ q ∈ (copyDesc e.2 (freshIds d.ids e.2.ids.length)).lbl,
      q.1 ∈ freshIds d.ids e.2.ids.length := by
  intro q hq
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
  exact renOf_mem he.nodup (freshIds_nodup _ _) (length_freshIds _ _) hy

theorem agree_decDesc (hd : CfgInv ((default : List ℕ), d)) (he : TnValid prim e.2) :
    (HTN.decomposeWith (cfgNet d) x (cfgNet (copyDesc e.2 (freshIds d.ids e.2.ids.length)))).Agree
      (cfgNet (decDesc d x e)) := by
  set fr := freshIds d.ids e.2.ids.length with hfr
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · ext y
    simp only [HTN.decomposeWith, cfgNet, decDesc, copyDesc, TnDesc.ids, Finset.mem_union,
      Finset.mem_erase, List.mem_toFinset, List.mem_append, List.mem_filter, decide_eq_true_eq]
    tauto
  · funext a b
    simp only [HTN.decomposeWith, cfgNet, decDesc, copyDesc, TnDesc.ids, TnDesc.ordList,
      List.mem_toFinset, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_filter,
      List.mem_map, decide_eq_true_eq, Prod.mk.injEq, eq_iff_iff]
    constructor
    · rintro (h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, hax, hbx⟩)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr ⟨(a, x), ⟨h, rfl⟩, b, hb, rfl, rfl⟩))
      · exact Or.inl (Or.inr ⟨(x, b), ⟨h, rfl⟩, a, ha, rfl, rfl⟩)
      · exact Or.inr ⟨h, hax, hbx⟩
    · rintro (((h | ⟨q, ⟨hq, hqx⟩, n, hn, h1, h2⟩) | ⟨q, ⟨hq, hqx⟩, n, hn, h1, h2⟩) | ⟨h, hax, hbx⟩)
      · exact Or.inl h
      · subst h1 h2; obtain ⟨q1, q2⟩ := q; simp only at hqx; subst hqx
        exact Or.inr (Or.inl ⟨hq, hn⟩)
      · subst h1 h2; obtain ⟨q1, q2⟩ := q; simp only at hqx; subst hqx
        exact Or.inr (Or.inr (Or.inl ⟨hq, hn⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hax, hbx⟩))
  · show (HTN.decomposeWith (cfgNet d) x (cfgNet (copyDesc e.2 fr))).α y = (decDesc d x e).label y
    simp only [HTN.decomposeWith]
    have hcopyk := copy_keys_sub (d := d) he
    split_ifs with hyf
    · have hyf' : y ∈ fr := by simpa [cfgNet, copyDesc] using hyf
      have hyd : y ∉ d.ids := not_mem_of_mem_freshIds hyf'
      apply label_congr
      show _ = List.lookup y (_ ++ _)
      rw [lookup_append', lookup_none_of_not_mem (l := d.lbl.filter fun q => decide (q.1 ≠ x))
        fun q hq e' => hyd (by
        rw [← e']; exact hd.lbl_mem q (List.mem_filter.1 hq).1)]
      rfl
    · have hyf' : y ∉ fr := by simpa [cfgNet, copyDesc] using hyf
      have hyx : y ≠ x := by
        rcases mem_decomposeWith_T.1 hy with ⟨-, h⟩ | h
        · exact h
        · exact absurd h hyf
      apply label_congr
      show _ = List.lookup y (_ ++ _)
      rw [lookup_append', lookup_filter_ne _ hyx,
        lookup_none_of_not_mem (l := (copyDesc e.2 fr).lbl) fun q hq e' => hyf' (by
          rw [← e']; exact hcopyk q hq)]
      cases d.lbl.lookup y <;> rfl

theorem inv_decDesc {s : List ℕ} (hc : CfgInv (s, d)) (he : TnValid prim e.2) :
    CfgInv (s, decDesc d x e) := by
  set fr := freshIds d.ids e.2.ids.length with hfr
  have hfrn : fr.Nodup := freshIds_nodup _ _
  have hfrd : ∀ y ∈ fr, y ∉ d.ids := fun y hy => not_mem_of_mem_freshIds hy
  have hcopyk := copy_keys_sub (d := d) he
  have hcwf : (cfgNet (copyDesc e.2 fr)).WF := wf_copyDesc he hfrn (length_freshIds _ _)
  have hdis : Disjoint (cfgNet d).T (cfgNet (copyDesc e.2 fr)).T := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    exact hfrd y (by simpa [cfgNet, copyDesc] using hy') (by simpa [cfgNet] using hy)
  refine ⟨?_, fun q hq => ?_, ?_, List.nodup_dedup _, hc.st_nodup, ?_⟩
  · show ((d.ids.filter fun y => decide (y ≠ x)) ++ fr).Nodup
    exact List.nodup_append.2 ⟨hc.ids_nodup.filter _, hfrn,
      fun a ha b hb e' => hfrd b hb (e' ▸ (List.mem_filter.1 ha).1)⟩
  · rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨hq, hqx⟩ := List.mem_filter.1 hq
      exact List.mem_append_left _ (List.mem_filter.2 ⟨hc.lbl_mem q hq, hqx⟩)
    · exact List.mem_append_right _ (hcopyk q hq)
  · show (((d.lbl.filter fun q => decide (q.1 ≠ x)) ++ (copyDesc e.2 fr).lbl).map Prod.fst).Nodup
    rw [List.map_append]
    refine List.nodup_append.2 ⟨(hc.lbl_nodup.sublist (List.filter_sublist.map _)), ?_,
      fun a ha b hb e' => ?_⟩
    · show ((e.2.ids.map fun y => (renOf e.2.ids fr y, lblOf e.2 y)).map Prod.fst).Nodup
      rw [List.map_map]
      exact he.nodup.map_on fun a ha b hb h =>
        renOf_inj he.nodup hfrn (length_freshIds _ _) ha hb h
    · obtain ⟨qa, hqa, rfl⟩ := List.mem_map.1 ha
      obtain ⟨qb, hqb, rfl⟩ := List.mem_map.1 hb
      exact hfrd _ (hcopyk qb hqb) (e' ▸ hc.lbl_mem qa (List.mem_filter.1 hqa).1)
  · exact (decomposeWith_wf hc.wf hcwf hdis).of_agree
      (agree_decDesc ⟨hc.ids_nodup, hc.lbl_mem, hc.lbl_nodup, hc.ord_nodup, List.nodup_nil, hc.wf⟩ he)

end Dec

theorem inv_progDesc {s s' : List ℕ} {d : TnDesc} {x : ℕ} (hc : CfgInv (s, d)) (hx : x ∈ d.ids)
    (hu : ∀ q ∈ d.ordList, q.2 ≠ x) (hs' : s'.Nodup) : CfgInv (s', progDesc d x) := by
  refine ⟨hc.ids_nodup.filter _, fun q hq => ?_, ?_, hc.ord_nodup.filter _, hs', ?_⟩
  · obtain ⟨hq, hqx⟩ := List.mem_filter.1 hq
    exact List.mem_filter.2 ⟨hc.lbl_mem q hq, hqx⟩
  · exact hc.lbl_nodup.sublist (List.filter_sublist.map _)
  · exact (TaskNetwork.progress_wf hc.wf (unconstrained_cfgNet hx hu)).of_agree (agree_progDesc hu)

end Article

end HTN
