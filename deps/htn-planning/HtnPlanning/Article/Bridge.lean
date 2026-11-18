import HtnPlanning.Article.Model
import HtnPlanning.Core.Problem
/-!
# Bridges between the article's model and `HTN.Problem`

The article's model (`HtnPlanning/Article/Model.lean`) and the model `HTN.Problem` of the rest of
the development define the same plan-existence problem:

* **`HTN.Article.Problem.solvable_ofPos_iff`** — a problem of `HTN.Problem` (no negative
  preconditions, positive goal), read in the article's model, has a solution in the article's
  sense (every linearisation executable, ordering insertion allowed) iff it has one in the sense
  of `HTN.Problem` (some linearisation executable);
* **`HTN.Article.Problem.sol_dual`** — negative preconditions and negative goals are compiled
  away by the dual-rail encoding `HTN.Article.Problem.dual` (a fact `inl f` for "`f` holds" and a
  fact `inr f` for "`f` does not hold"), which keeps the hierarchy (methods, initial task network)
  unchanged and has *literally the same* solutions;
* **`HTN.Article.Problem.solvable_iff_toPos`** — hence every problem of the article's model is
  solvable iff its dual-rail translation `HTN.Article.Problem.toPos`, a problem of `HTN.Problem`
  with the same methods and initial task network, is solvable.

Every class of Section 3 depends on the methods and the initial task network only, so the
translation stays inside every class (`HtnPlanning/Article/Classes.lean`).
-/

namespace HTN

namespace Article

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### Ordering insertion -/

section OI

variable {tn tn₁ tn₂ : TaskNetwork I A C}

theorem OIStep.T (h : OIStep tn₁ tn₂) : tn₂.T = tn₁.T := by
  obtain ⟨t, t', -, -, -, -, rfl, -⟩ := h; rfl

theorem OIStep.α (h : OIStep tn₁ tn₂) : tn₂.α = tn₁.α := by
  obtain ⟨t, t', -, -, -, -, rfl, -⟩ := h; rfl

theorem OIStep.ord_le (h : OIStep tn₁ tn₂) {a b : I} (hab : tn₁.ord a b) : tn₂.ord a b := by
  obtain ⟨t, t', -, -, -, -, rfl, -⟩ := h
  exact Relation.TransGen.single (Or.inl hab)

theorem OIReach.T (h : OIReach tn₁ tn₂) : tn₂.T = tn₁.T := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [hs.T, ih]

theorem OIReach.α (h : OIReach tn₁ tn₂) : tn₂.α = tn₁.α := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [hs.α, ih]

theorem OIReach.ord_le (h : OIReach tn₁ tn₂) {a b : I} (hab : tn₁.ord a b) : tn₂.ord a b := by
  induction h with
  | refl => exact hab
  | tail _ hs ih => exact hs.ord_le ih

theorem OIReach.wf (h : OIReach tn₁ tn₂) (h₁ : tn₁.WF) : tn₂.WF := by
  induction h with
  | refl => exact h₁
  | tail _ hs _ => obtain ⟨-, -, -, -, -, -, -, hwf⟩ := hs; exact hwf

/-- A linearisation after ordering insertion is a linearisation before it. -/
theorem OIReach.isLinearization (h : OIReach tn₁ tn₂) {l : List I}
    (hl : tn₂.IsLinearization l) : tn₁.IsLinearization l := by
  refine ⟨hl.1, fun t => by rw [← h.T]; exact hl.2.1 t, ?_⟩
  exact hl.2.2.imp fun hn hab => hn (h.ord_le hab)

/-- The task network `tn` with the pairs `ps` added to its order and the order closed. -/
def ordExt (tn : TaskNetwork I A C) (ps : List (I × I)) : TaskNetwork I A C where
  T := tn.T
  ord := Relation.TransGen fun a b => tn.ord a b ∨ (a, b) ∈ ps
  α := tn.α

theorem ordExt_nil (htr : ∀ {a b c : I}, tn.ord a b → tn.ord b c → tn.ord a c) :
    ordExt tn [] = tn := by
  refine TaskNetwork.ext' rfl ?_ rfl
  funext a b
  apply propext
  constructor
  · intro h
    induction h with
    | single h => simpa using h
    | tail _ h ih => exact htr ih (by simpa using h)
  · intro h
    exact Relation.TransGen.single (Or.inl h)

theorem ordInsert_ordExt (ps : List (I × I)) (p : I × I) :
    ordInsert (ordExt tn ps) p.1 p.2 = ordExt tn (p :: ps) := by
  refine TaskNetwork.ext' rfl ?_ rfl
  funext a b
  apply propext
  constructor
  · intro h
    induction h with
    | single h =>
      rcases h with h | ⟨rfl, rfl⟩
      · exact Relation.TransGen.mono (fun x y hxy => hxy.imp_right (List.mem_cons_of_mem _)) h
      · exact Relation.TransGen.single (Or.inr (List.mem_cons_self ..))
    | tail _ h ih =>
      rcases h with h | ⟨rfl, rfl⟩
      · exact ih.trans
          (Relation.TransGen.mono (fun x y hxy => hxy.imp_right (List.mem_cons_of_mem _)) h)
      · exact ih.tail (Or.inr (List.mem_cons_self ..))
  · intro h
    induction h with
    | single h =>
      rcases h with h | h
      · exact Relation.TransGen.single (Or.inl (Relation.TransGen.single (Or.inl h)))
      · rcases List.mem_cons.1 h with h | h
        · exact Relation.TransGen.single (Or.inr (by rw [← h]; exact ⟨rfl, rfl⟩))
        · exact Relation.TransGen.single (Or.inl (Relation.TransGen.single (Or.inr h)))
    | tail _ h ih =>
      rcases h with h | h
      · exact ih.tail (Or.inl (Relation.TransGen.single (Or.inl h)))
      · rcases List.mem_cons.1 h with h | h
        · exact ih.tail (Or.inr (by rw [← h]; exact ⟨rfl, rfl⟩))
        · exact ih.tail (Or.inl (Relation.TransGen.single (Or.inr h)))

theorem ordExt_wf (hwf : tn.WF) {ps : List (I × I)}
    (hps : ∀ p ∈ ps, p.1 ∈ tn.T ∧ p.2 ∈ tn.T)
    (hirr : ∀ a, ¬ (ordExt tn ps).ord a a) : (ordExt tn ps).WF where
  mem_left := by
    intro a b h
    induction h using Relation.TransGen.head_induction_on with
    | single h => rcases h with h | h; exact hwf.mem_left h; exact (hps _ h).1
    | head h _ _ => rcases h with h | h; exact hwf.mem_left h; exact (hps _ h).1
  mem_right := by
    intro a b h
    induction h with
    | single h => rcases h with h | h; exact hwf.mem_right h; exact (hps _ h).2
    | tail _ h _ => rcases h with h | h; exact hwf.mem_right h; exact (hps _ h).2
  irrefl := hirr
  trans := fun h₁ h₂ => h₁.trans h₂

theorem ordExt_mono {ps : List (I × I)} (p : I × I) {a b : I} (h : (ordExt tn ps).ord a b) :
    (ordExt tn (p :: ps)).ord a b :=
  Relation.TransGen.mono (fun x y hxy => hxy.imp_right (List.mem_cons_of_mem _)) h

/-- **Adding a list of constraints between primitive tasks is a sequence of ordering
insertions**, provided the result is a strict partial order. -/
theorem oiReach_ordExt (hwf : tn.WF) (ps : List (I × I))
    (hps : ∀ p ∈ ps, p.1 ∈ tn.T ∧ p.2 ∈ tn.T ∧ tn.IsPrimitiveId p.1 ∧ tn.IsPrimitiveId p.2)
    (hirr : ∀ a, ¬ (ordExt tn ps).ord a a) : OIReach tn (ordExt tn ps) := by
  induction ps with
  | nil => rw [ordExt_nil hwf.trans]; exact Relation.ReflTransGen.refl
  | cons p ps ih =>
    have hirr' : ∀ a, ¬ (ordExt tn ps).ord a a := fun a h => hirr a (ordExt_mono p h)
    refine (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hirr').tail ?_
    obtain ⟨h1, h2, h3, h4⟩ := hps p List.mem_cons_self
    refine ⟨p.1, p.2, h1, h2, h3, h4, (ordInsert_ordExt ps p).symm, ?_⟩
    exact ordExt_wf hwf (fun q hq => ⟨(hps q hq).1, (hps q hq).2.1⟩) hirr

/-- The consecutive pairs of a list. -/
def chain (l : List I) : List (I × I) := l.zip l.tail

theorem idxOf_lt_of_mem_chain [DecidableEq I] {l : List I} (hl : l.Nodup) {a b : I}
    (h : (a, b) ∈ chain l) : l.idxOf a < l.idxOf b ∧ a ∈ l ∧ b ∈ l := by
  induction l with
  | nil => simp [chain] at h
  | cons x l ih =>
    cases l with
    | nil => simp [chain] at h
    | cons y l =>
      have hn := List.nodup_cons.1 hl
      simp only [chain, List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · refine ⟨?_, by simp, by simp⟩
        have hy : b ≠ a := fun h => hn.1 (h ▸ List.mem_cons_self ..)
        rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hy)]
        exact Nat.succ_pos _
      · obtain ⟨h1, h2, h3⟩ := ih hn.2 h
        have ha : a ≠ x := fun e => hn.1 (e ▸ h2)
        have hb : b ≠ x := fun e => hn.1 (e ▸ h3)
        refine ⟨?_, List.mem_cons_of_mem _ h2, List.mem_cons_of_mem _ h3⟩
        rw [List.idxOf_cons_ne _ (Ne.symm ha), List.idxOf_cons_ne _ (Ne.symm hb)]
        simpa using h1

theorem idxOf_lt_of_ord [DecidableEq I] (hwf : tn.WF) {l : List I}
    (hl : tn.IsLinearization l) {a b : I} (h : tn.ord a b) : l.idxOf a < l.idxOf b := by
  have ha := (hl.2.1 a).2 (hwf.mem_left h)
  have hb := (hl.2.1 b).2 (hwf.mem_right h)
  by_contra hcon
  rcases Nat.lt_or_eq_of_le (not_lt.1 hcon) with hlt | heq
  · have hp := hl.2.2
    rw [List.pairwise_iff_getElem] at hp
    have hbl : l.idxOf b < l.length := List.idxOf_lt_length_iff.2 hb
    have hal : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 ha
    have := hp _ _ hbl hal hlt
    simp only [List.getElem_idxOf] at this
    exact this h
  · have : a = b := by
      have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 ha)
      have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hb)
      rw [← h1, ← h2]
      congr 1
      exact heq.symm
    subst this
    exact hwf.irrefl a h

/-- In the extension of `tn` along a linearisation `l`, the order strictly increases the
position in `l`. -/
theorem idxOf_lt_of_ordExt_chain [DecidableEq I] (hwf : tn.WF) {l : List I}
    (hl : tn.IsLinearization l) {a b : I} (h : (ordExt tn (chain l)).ord a b) :
    l.idxOf a < l.idxOf b := by
  induction h with
  | single h =>
    rcases h with h | h
    · exact idxOf_lt_of_ord hwf hl h
    · exact (idxOf_lt_of_mem_chain hl.1 h).1
  | tail _ h ih =>
    rcases h with h | h
    · exact ih.trans (idxOf_lt_of_ord hwf hl h)
    · exact ih.trans (idxOf_lt_of_mem_chain hl.1 h).1

/-- Consecutive elements of a list are related by the transitive closure of `chain`. -/
theorem transGen_chain {l : List I} :
    ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length), i < j →
      Relation.TransGen (fun a b => (a, b) ∈ chain l) l[i] l[j] := by
  intro i j hi hj hij
  induction j, hij using Nat.le_induction with
  | base =>
    refine Relation.TransGen.single ?_
    simp only [chain, List.mem_iff_getElem, List.getElem_zip, List.getElem_tail,
      List.length_zip, List.length_tail]
    exact ⟨i, by omega, rfl⟩
  | succ j hij ih =>
    refine (ih (by omega)).tail ?_
    simp only [chain, List.mem_iff_getElem, List.getElem_zip, List.getElem_tail,
      List.length_zip, List.length_tail]
    exact ⟨j, by omega, rfl⟩

/-- **A total extension along a linearisation.** If `l` is a linearisation of a well-formed
primitive task network `tn`, then ordering insertions turn `tn` into a well-formed network whose
*only* linearisation is `l`. -/
theorem exists_oiReach_unique_lin [DecidableEq I] (hwf : tn.WF) (hprim : tn.IsPrimitive)
    {l : List I} (hl : tn.IsLinearization l) :
    ∃ tn', tn' = ordExt tn (chain l) ∧ OIReach tn tn' ∧ tn'.WF ∧ tn'.T = tn.T ∧ tn'.α = tn.α ∧
      ∀ l', tn'.IsLinearization l' → l' = l := by
  have hirr : ∀ a, ¬ (ordExt tn (chain l)).ord a a := fun a h =>
    lt_irrefl _ (idxOf_lt_of_ordExt_chain hwf hl h)
  have hps : ∀ p ∈ chain l, p.1 ∈ tn.T ∧ p.2 ∈ tn.T ∧ tn.IsPrimitiveId p.1 ∧
      tn.IsPrimitiveId p.2 := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := idxOf_lt_of_mem_chain hl.1 hp
    have h1' := (hl.2.1 _).1 h1
    have h2' := (hl.2.1 _).1 h2
    exact ⟨h1', h2', hprim _ h1', hprim _ h2'⟩
  refine ⟨ordExt tn (chain l), rfl, oiReach_ordExt hwf _ hps hirr,
    ordExt_wf hwf (fun p hp => ⟨(hps p hp).1, (hps p hp).2.1⟩) hirr, rfl, rfl, ?_⟩
  intro l' hl'
  -- `l'` is sorted by the position in `l`
  have hmem : ∀ t, t ∈ l' ↔ t ∈ l := fun t => (hl'.2.1 t).trans (hl.2.1 t).symm
  have hperm : l'.Perm l := (List.perm_ext_iff_of_nodup hl'.1 hl.1).2 hmem
  let r : I → I → Prop := fun a b => l.idxOf a < l.idxOf b
  have hsorted : l.Pairwise r := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [r, List.idxOf_getElem hl.1]
    exact hij
  have hsorted' : l'.Pairwise r := by
    refine (hl'.1.and (List.Pairwise.and_mem.1 hl'.2.2)).imp ?_
    rintro a b ⟨hne, ha, hb, hn⟩
    have ha' := (hmem a).1 ha
    have hb' := (hmem b).1 hb
    rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
    · exact h
    · exfalso
      exact hne ((List.idxOf_inj ha').1 h)
    · exfalso
      apply hn
      have hbl := List.idxOf_lt_length_iff.2 hb'
      have hal := List.idxOf_lt_length_iff.2 ha'
      have := transGen_chain hbl hal h
      simp only [List.getElem_idxOf] at this
      exact Relation.TransGen.mono (fun x y hxy => Or.inr hxy) this
  exact hperm.eq_of_pairwise
    (fun a b _ _ (h1 : r a b) (h2 : r b a) => absurd (h1.trans h2) (lt_irrefl _)) hsorted' hsorted

end OI

/-! ### Problems without negative preconditions -/

namespace Problem

/-- A problem of `HTN.Problem` read in the article's model: no negative preconditions, no
negative goals. -/
def ofPos (Q : HTN.Problem F A C I) : Problem F A C I where
  δ a := ⟨Q.prec a, ∅, Q.add a, Q.del a⟩
  methods := Q.methods
  init := Q.init
  tnI := Q.tnI
  goalPos := Q.goal
  goalNeg := ∅

theorem run_ofPos_iff (Q : HTN.Problem F A C I) (as : List A) (s s' : Set F) :
    (ofPos Q).Run as s s' ↔ Q.SeqApplicable as s ∧ s' = Q.transitionSeq as s := by
  induction as generalizing s with
  | nil => simp [Run, ActionModel.SeqApplicable, ActionModel.transitionSeq]
  | cons a as ih =>
    simp only [Run, ActionModel.SeqApplicable, ActionModel.transitionSeq, ih]
    simp [Action.Applicable, Action.apply, ofPos, ActionModel.Applicable,
      ActionModel.transition, and_assoc]

theorem goalState_ofPos_iff (Q : HTN.Problem F A C I) (s : Set F) :
    (ofPos Q).GoalState s ↔ Q.GoalState s := by
  simp [GoalState, HTN.Problem.GoalState, ofPos]

/-- **The article's HTN solution criterion and that of `HTN.Problem` agree on plan existence.**
-/
theorem solvable_ofPos_iff [DecidableEq I] (Q : HTN.Problem F A C I) (hQ : Q.WF) :
    (ofPos Q).Solvable ↔ Q.Solvable := by
  constructor
  · rintro ⟨tnS, hex, hgoal, tn, hdec, hoi⟩
    have hprim := hex.1
    have hwf : tn.WF := hdec.wf hQ.tnI
    have hwfS : tnS.WF := hoi.wf hwf
    obtain ⟨l, as, hl, has⟩ := TaskNetwork.exists_linearization_actionSeq hwfS hprim
    obtain ⟨s', hrun⟩ := hex.2 l as hl has
    have hg := hgoal s' ⟨l, as, hl, has, hrun⟩
    rw [run_ofPos_iff] at hrun
    rw [goalState_ofPos_iff] at hg
    refine ⟨tn, hdec, ?_, l, as, hoi.isLinearization hl, ?_, hrun.1, hrun.2 ▸ hg⟩
    · intro t ht
      have := hprim t (by rw [hoi.T]; exact ht)
      obtain ⟨a, ha⟩ := this
      exact ⟨a, by rw [← hoi.α]; exact ha⟩
    · unfold TaskNetwork.IsActionSeq at has ⊢
      rw [← hoi.α]; exact has
  · rintro ⟨tn, hreach, hprim, l, as, hl, has, happ, hgoal⟩
    have hwf : tn.WF := HTN.DecomposesTo.wf hreach hQ.tnI
    obtain ⟨tn', -, hoi, hwf', hT, hα, huniq⟩ := exists_oiReach_unique_lin hwf hprim hl
    have hprim' : tn'.IsPrimitive := by
      intro t ht; rw [hT] at ht; obtain ⟨a, ha⟩ := hprim t ht; exact ⟨a, by rw [hα]; exact ha⟩
    have has' : tn'.IsActionSeq l as := by
      unfold TaskNetwork.IsActionSeq at has ⊢; rw [hα]; exact has
    have key : ∀ l' as', tn'.IsLinearization l' → tn'.IsActionSeq l' as' → l' = l ∧ as' = as := by
      intro l' as' hl' has''
      obtain rfl := huniq l' hl'
      exact ⟨rfl, TaskNetwork.isActionSeq_unique has'' has'⟩
    refine ⟨tn', ⟨hprim', fun l' as' hl' has'' => ?_⟩, fun s ⟨l', as', hl', has'', hrun⟩ => ?_,
      tn, hreach, hoi⟩
    · obtain ⟨rfl, rfl⟩ := key l' as' hl' has''
      exact ⟨_, (run_ofPos_iff Q _ _ _).2 ⟨happ, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := key l' as' hl' has''
      rw [run_ofPos_iff] at hrun
      rw [goalState_ofPos_iff, hrun.2]
      exact hgoal

end Problem

/-! ### Compiling negative preconditions and goals away -/

/-- The dual-rail encoding of a state: `inl f` for the facts that hold, `inr f` for those that
do not. -/
def encState (s : Set F) : Set (F ⊕ F) := Sum.inl '' s ∪ Sum.inr '' sᶜ

@[simp] theorem inl_mem_encState {s : Set F} {f : F} : Sum.inl f ∈ encState s ↔ f ∈ s := by
  simp [encState]

@[simp] theorem inr_mem_encState {s : Set F} {f : F} : Sum.inr f ∈ encState s ↔ f ∉ s := by
  simp [encState]

theorem encState_injective : Function.Injective (encState (F := F)) := by
  intro s t h
  ext f
  rw [← inl_mem_encState, h, inl_mem_encState]

/-- The dual-rail translation of an action. -/
def Action.dual (a : Action F) : Action (F ⊕ F) where
  pre := Sum.inl '' a.pre ∪ Sum.inr '' a.preNeg
  preNeg := ∅
  add := Sum.inl '' a.add ∪ Sum.inr '' (a.del \ a.add)
  del := Sum.inr '' a.add ∪ Sum.inl '' (a.del \ a.add)

theorem Action.applicable_dual_iff (a : Action F) (s : Set F) :
    a.dual.Applicable (encState s) ↔ a.Applicable s := by
  simp only [Action.Applicable, Action.dual, Set.union_subset_iff, Set.image_subset_iff,
    Set.empty_disjoint, and_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => by simpa using h1 hf, Set.disjoint_left.2 fun f hf hs => ?_⟩
    simpa [hs] using h2 hf
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => by simpa using h1 hf,
      fun f hf => by simpa using Set.disjoint_left.1 h2 hf⟩

theorem Action.apply_dual (a : Action F) (s : Set F) :
    a.dual.apply (encState s) = encState (a.apply s) := by
  ext x
  rcases x with f | f <;>
    by_cases h1 : f ∈ a.add <;> by_cases h2 : f ∈ a.del <;> by_cases h3 : f ∈ s <;>
    simp [Action.apply, Action.dual, encState, h1, h2, h3]

namespace Problem

/-- **The dual-rail translation of a problem**: facts `F ⊕ F`, no negative preconditions, no
negative goals; the hierarchy is unchanged. -/
def dual (P : Problem F A C I) : Problem (F ⊕ F) A C I where
  δ a := (P.δ a).dual
  methods := P.methods
  init := encState P.init
  tnI := P.tnI
  goalPos := Sum.inl '' P.goalPos ∪ Sum.inr '' P.goalNeg
  goalNeg := ∅

theorem run_dual_iff (P : Problem F A C I) (as : List A) (s : Set F) (t : Set (F ⊕ F)) :
    P.dual.Run as (encState s) t ↔ ∃ s', t = encState s' ∧ P.Run as s s' := by
  induction as generalizing s with
  | nil => simp [Run]
  | cons a as ih =>
    simp only [Run, dual]
    rw [Action.applicable_dual_iff, Action.apply_dual]
    have := ih ((P.δ a).apply s)
    simp only [dual] at this
    rw [this]
    constructor
    · rintro ⟨h, s', rfl, hr⟩; exact ⟨s', rfl, h, hr⟩
    · rintro ⟨s', rfl, h, hr⟩; exact ⟨h, s', rfl, hr⟩

theorem goalState_dual_iff (P : Problem F A C I) (s : Set F) :
    P.dual.GoalState (encState s) ↔ P.GoalState s := by
  simp only [GoalState, dual, Set.union_subset_iff, Set.image_subset_iff,
    Set.empty_disjoint, and_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => by simpa using h1 hf,
      Set.disjoint_left.2 fun f hf hs => by simpa [hs] using h2 hf⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => by simpa using h1 hf,
      fun f hf => by simpa using Set.disjoint_left.1 h2 hf⟩

theorem executableIn_dual_iff (P : Problem F A C I) (tn : TaskNetwork I A C) (s : Set F) :
    P.dual.ExecutableIn tn (encState s) ↔ P.ExecutableIn tn s := by
  unfold ExecutableIn
  refine and_congr Iff.rfl (forall_congr' fun l => forall_congr' fun as =>
    imp_congr Iff.rfl (imp_congr Iff.rfl ?_))
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨s', -, h⟩ := (run_dual_iff P as s t).1 ht
    exact ⟨s', h⟩
  · rintro ⟨s', h⟩
    exact ⟨_, (run_dual_iff P as s _).2 ⟨s', rfl, h⟩⟩

theorem generates_dual_iff (P : Problem F A C I) (tn : TaskNetwork I A C) (s : Set F)
    (t : Set (F ⊕ F)) :
    P.dual.Generates tn (encState s) t ↔ ∃ s', t = encState s' ∧ P.Generates tn s s' := by
  unfold Generates
  simp only [run_dual_iff]
  constructor
  · rintro ⟨l, as, hl, has, s', rfl, h⟩; exact ⟨s', rfl, l, as, hl, has, h⟩
  · rintro ⟨s', rfl, l, as, hl, has, h⟩; exact ⟨l, as, hl, has, s', rfl, h⟩

/-- **The dual-rail translation has exactly the same HTN solutions.** -/
theorem sol_dual [DecidableEq I] (P : Problem F A C I) : P.dual.Sol = P.Sol := by
  ext tn
  simp only [Sol, Set.mem_setOf_eq, IsSol]
  have hinit : P.dual.init = encState P.init := rfl
  rw [hinit, executableIn_dual_iff]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  constructor
  · intro h s hs
    exact (goalState_dual_iff P s).1 (h _ ((generates_dual_iff P tn _ _).2 ⟨s, rfl, hs⟩))
  · intro h t ht
    obtain ⟨s', rfl, hs'⟩ := (generates_dual_iff P tn _ _).1 ht
    exact (goalState_dual_iff P s').2 (h s' hs')

/-- **The dual-rail translation has exactly the same TIHTN solutions.** -/
theorem solTI_dual [DecidableEq I] (P : Problem F A C I) : P.dual.SolTI = P.SolTI := by
  ext tn
  simp only [SolTI, Set.mem_setOf_eq, IsSolTI]
  have hinit : P.dual.init = encState P.init := rfl
  rw [hinit, executableIn_dual_iff]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  constructor
  · intro h s hs
    exact (goalState_dual_iff P s).1 (h _ ((generates_dual_iff P tn _ _).2 ⟨s, rfl, hs⟩))
  · intro h t ht
    obtain ⟨s', rfl, hs'⟩ := (generates_dual_iff P tn _ _).1 ht
    exact (goalState_dual_iff P s').2 (h s' hs')

/-- The dual-rail translation as a problem of `HTN.Problem`. -/
def toPos (P : Problem F A C I) : HTN.Problem (F ⊕ F) A C I where
  prec a := (P.δ a).dual.pre
  add a := (P.δ a).dual.add
  del a := (P.δ a).dual.del
  methods := P.methods
  init := encState P.init
  goal := Sum.inl '' P.goalPos ∪ Sum.inr '' P.goalNeg
  tnI := P.tnI

theorem ofPos_toPos (P : Problem F A C I) : ofPos P.toPos = P.dual := rfl

theorem toPos_wf (P : Problem F A C I) (hP : P.WF) : P.toPos.WF := ⟨hP.tnI, hP.methods⟩

@[simp] theorem toPos_methods (P : Problem F A C I) : P.toPos.methods = P.methods := rfl

@[simp] theorem toPos_tnI (P : Problem F A C I) : P.toPos.tnI = P.tnI := rfl

/-- **Plan existence in the article's model is plan existence of `HTN.Problem`**, through the
dual-rail translation `toPos`, which keeps the methods and the initial task network. -/
theorem solvable_iff_toPos [DecidableEq I] (P : Problem F A C I) (hP : P.WF) :
    P.Solvable ↔ P.toPos.Solvable := by
  rw [← solvable_ofPos_iff _ (toPos_wf P hP), ofPos_toPos, Solvable, Solvable, sol_dual]

end Problem

end Article

end HTN
