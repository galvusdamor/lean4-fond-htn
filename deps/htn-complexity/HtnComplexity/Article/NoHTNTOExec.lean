import HtnComplexity.Article.NoHTNTORank
/-!
# The execution check fact by fact

The execution check `HTN.Article.NoHTN.execB` runs the dual-rail translation of a description and
stores whole states.  Fact by fact it needs only two bits: whether `f` holds after `k` steps
(`HTN.Article.NoHTNTO.hP`) and whether `f` does not hold (`HTN.Article.NoHTNTO.hN`), each a
recursion over the steps that looks only at the effects of one action
(`HTN.Article.NoHTNTO.execB_iff_execF`).
-/

namespace HTN

namespace Article

namespace NoHTNTO

open Syn Syn.PolyDom NoHTN

variable (p : ProbDesc)

/-- The action described under the name `a` (the first one), or the empty action. -/
def actOf (a : ℕ) : ActDesc := (p.actions.find? fun x => x.1 == a).getD default

/-- **`f` holds after the first `k` actions of `as`.** -/
def hP (as : List ℕ) : ℕ → ℕ → Bool
  | 0, f => decide (f ∈ p.init)
  | k + 1, f => decide (f ∈ (actOf p (as.getD k 0)).2.2.2.1) ||
      (hP as k f && !decide (f ∈ (actOf p (as.getD k 0)).2.2.2.2))

/-- **`f` does not hold after the first `k` actions of `as`** (for a fact of the description). -/
def hN (as : List ℕ) : ℕ → ℕ → Bool
  | 0, f => !decide (f ∈ p.init)
  | k + 1, f => (decide (f ∈ (actOf p (as.getD k 0)).2.2.2.2) &&
      !decide (f ∈ (actOf p (as.getD k 0)).2.2.2.1)) ||
      (hN as k f && !decide (f ∈ (actOf p (as.getD k 0)).2.2.2.1))

/-- **The execution check, fact by fact**: every precondition holds when its action is applied, and
the goal holds at the end. -/
def ExecF (as : List ℕ) : Prop :=
  (∀ k < as.length, (∀ f ∈ (actOf p (as.getD k 0)).2.1, hP p as k f = true) ∧
    ∀ f ∈ (actOf p (as.getD k 0)).2.2.1, hN p as k f = true) ∧
  (∀ f ∈ p.goalPos, hP p as as.length f = true) ∧ ∀ f ∈ p.goalNeg, hN p as as.length f = true

theorem actLists_toSynDom (a : ℕ) : actLists (toSynDom p) a = (actToSyn (actOf p a)).2 := by
  unfold actLists actOf
  show ((p.actions.map actToSyn).lookup a).elim _ _ = _
  rw [lookup_actToSyn]
  simp only [ActDesc.name]
  cases (p.actions.find? fun x => x.1 == a)
  · show ([], [], []) = (actToSyn (0, [], [], [], [])).2
    simp [actToSyn, delOnly]
  · rfl

theorem mem_map_posF (f : ℕ) (l : List ℕ) : posF f ∈ l.map posF ↔ f ∈ l := by
  simp [posF]

theorem mem_map_negF (f : ℕ) (l : List ℕ) : negF f ∈ l.map negF ↔ f ∈ l := by
  simp [negF]

theorem posF_not_mem_map_negF (f : ℕ) (l : List ℕ) : posF f ∉ l.map negF := by
  simp only [List.mem_map, not_exists, not_and, posF, negF]; intro x _; omega

theorem negF_not_mem_map_posF (f : ℕ) (l : List ℕ) : negF f ∉ l.map posF := by
  simp only [List.mem_map, not_exists, not_and, posF, negF]; intro x _; omega

theorem mem_facts_of_actOf (a : ℕ) {f : ℕ} (hf : f ∈ (actOf p a).2.2.1) : f ∈ p.facts := by
  unfold actOf at hf
  rcases h : p.actions.find? (fun x => x.1 == a) with _ | x
  · rw [h] at hf
    change f ∈ ([] : List ℕ) at hf
    simp at hf
  · rw [h] at hf
    simp only [Option.getD_some] at hf
    have hx := List.mem_of_find?_eq_some h
    simp only [ProbDesc.facts, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨x, hx, by simp [hf]⟩

/-- The state after the first `k` actions. -/
def st (as : List ℕ) (k : ℕ) : Bool × List ℕ :=
  (as.take k).foldl (execStep (toSynDom p)) (true, (toSynInst p).initList)

theorem st_succ (as : List ℕ) (k : ℕ) (hk : k < as.length) :
    st p as (k + 1) = execStep (toSynDom p) (st p as k) (as.getD k 0) := by
  unfold st
  rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
    List.getD_eq_getElem _ _ hk]
  rfl

theorem execStep_fst (b : Bool) (s : List ℕ) (a : ℕ) :
    (execStep (toSynDom p) (b, s) a).1 = (b && (actLists (toSynDom p) a).1.all fun f => decide (f ∈ s)) := rfl

theorem mem_execStep_snd (b : Bool) (s : List ℕ) (a g : ℕ) :
    g ∈ (execStep (toSynDom p) (b, s) a).2 ↔
      (g ∈ s ∧ g ∉ (actLists (toSynDom p) a).2.2) ∨ g ∈ (actLists (toSynDom p) a).2.1 := by
  simp [execStep]

/-- **The facts of the state, fact by fact.** -/
theorem st_facts (as : List ℕ) : ∀ k ≤ as.length, ∀ f,
    (posF f ∈ (st p as k).2 ↔ hP p as k f = true) ∧
      (f ∈ p.facts → (negF f ∈ (st p as k).2 ↔ hN p as k f = true)) := by
  intro k
  induction k with
  | zero =>
    intro _ f
    simp only [st, List.take_zero, List.foldl_nil, toSynInst, InstDesc.initList, List.mem_append,
      mem_map_posF, posF_not_mem_map_negF, or_false, hP, decide_eq_true_eq, true_and,
      negF_not_mem_map_posF, false_or, mem_map_negF, List.mem_filter, hN, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact fun hf => ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
  | succ k ih =>
    intro hk f
    obtain ⟨ihP, ihN⟩ := ih (by omega) f
    rw [st_succ p as k (by omega)]
    rcases hs : st p as k with ⟨b, s⟩
    rw [hs] at ihP ihN
    rw [mem_execStep_snd, mem_execStep_snd, actLists_toSynDom]
    simp only [actToSyn, delOnly, List.mem_append, mem_map_posF, posF_not_mem_map_negF, or_false,
      false_or, mem_map_negF, negF_not_mem_map_posF, List.mem_filter, hP, hN]
    generalize actOf p (as.getD k 0) = A
    refine ⟨?_, fun hf => ?_⟩
    · rw [ihP]
      by_cases h1 : f ∈ A.2.2.2.1 <;> by_cases h2 : f ∈ A.2.2.2.2 <;> simp [h1, h2, posF, negF] <;> omega
    · rw [ihN hf]
      by_cases h1 : f ∈ A.2.2.2.1 <;> by_cases h2 : f ∈ A.2.2.2.2 <;> simp [h1, h2, posF, negF] <;> omega

/-- The preconditions of an action hold in a state, fact by fact. -/
theorem prec_iff (as : List ℕ) (k : ℕ) (hk : k ≤ as.length) (a : ℕ) :
    ((actLists (toSynDom p) a).1.all fun f => decide (f ∈ (st p as k).2)) = true ↔
      (∀ f ∈ (actOf p a).2.1, hP p as k f = true) ∧ ∀ f ∈ (actOf p a).2.2.1, hN p as k f = true := by
  rw [actLists_toSynDom]
  simp only [actToSyn, List.all_append, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    decide_eq_true_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine and_congr (forall₂_congr fun f _ => (st_facts p as k hk f).1) (forall₂_congr fun f hf => ?_)
  exact (st_facts p as k hk f).2 (mem_facts_of_actOf p a hf)

theorem st_fst (as : List ℕ) : ∀ k ≤ as.length, (st p as k).1 = true ↔
    ∀ j < k, ((actLists (toSynDom p) (as.getD j 0)).1.all fun f => decide (f ∈ (st p as j).2)) = true := by
  intro k
  induction k with
  | zero => intro _; simp [st]
  | succ k ih =>
    intro hk
    rw [st_succ p as k (by omega)]
    have := ih (by omega)
    rcases hs : st p as k with ⟨b, s⟩
    rw [hs] at this
    rw [execStep_fst, Bool.and_eq_true, this]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_or_ge j k with h | h
      · exact h1 j h
      · rw [show j = k by omega, hs]; exact h2
    · intro h
      exact ⟨fun j hj => h j (by omega), by have := h k (by omega); rwa [hs] at this⟩

/-- **The execution check is the fact-by-fact check.** -/
theorem execB_iff_execF (as : List ℕ) :
    execB (toSynDom p) (toSynInst p) as = true ↔ ExecF p as := by
  have hst : as.foldl (execStep (toSynDom p)) (true, (toSynInst p).initList) = st p as as.length := by
    simp [st]
  unfold execB ExecF
  simp only [hst, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  rw [st_fst p as _ le_rfl]
  refine and_congr (forall₂_congr fun k hk => prec_iff p as k hk.le _) ?_
  simp only [toSynInst, InstDesc.goalList, List.mem_append, List.mem_map]
  constructor
  · intro h
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact (st_facts p as _ le_rfl f).1.1 (h _ (Or.inl ⟨f, hf, rfl⟩))
    · exact ((st_facts p as _ le_rfl f).2 (by simp [ProbDesc.facts, hf])).1 (h _ (Or.inr ⟨f, hf, rfl⟩))
  · rintro ⟨h1, h2⟩ g (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩)
    · exact (st_facts p as _ le_rfl f).1.2 (h1 f hf)
    · exact ((st_facts p as _ le_rfl f).2 (by simp [ProbDesc.facts, hf])).2 (h2 f hf)

end NoHTNTO

end Article

end HTN
