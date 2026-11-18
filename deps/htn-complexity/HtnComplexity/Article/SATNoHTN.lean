import HtnComplexity.Article.SAT
import HtnComplexity.Article.Valid
import HtnPlanning.Article.Flat
import HtnPlanning.Article.OfSyn
import HtnComplexity.Undec.Encoding
/-!
# Non-hierarchical HTN planning is NP-hard (Thm. 4.3.8)

The article's encoding of a formula `φ` with variables `x₁, …, xₙ` and clauses `φ₁, …, φₘ`:
facts `xᵢ` and `cⱼ`; actions `xᵢ ↦ ⊤ = ({xᵢ}, ∅, {cⱼ | xᵢ ∈ φⱼ}, {xᵢ})`,
`xᵢ ↦ ⊥ = ({xᵢ}, ∅, {cⱼ | ¬xᵢ ∈ φⱼ}, {xᵢ})`, `φ ↦ ⊤ = ({c₁, …, cₘ}, ∅, X, ∅)`; the initial state
`X`, no goal, and the initial task network of the `2n + 1` actions, unordered.  Each pair
`xᵢ ↦ ⊤`, `xᵢ ↦ ⊥` deletes its common precondition, which only `φ ↦ ⊤` restores, so exactly one
of them precedes `φ ↦ ⊤`, and these choices form a satisfying assignment.

Here the variables of a formula are numbered by their position `i` in the list
`HTN.Article.SATNo.vars φ` of the distinct variable names (the formula's variable names are
arbitrary numbers, so numbering by name would not be polynomial):

* facts: `i` for the `i`-th variable (`i < N`), `N + j` for the `j`-th clause;
* actions: `2i` is `xᵢ ↦ ⊤`, `2i + 1` is `xᵢ ↦ ⊥`, `2N` is `φ ↦ ⊤`.

Results:

* `HTN.Article.SATNo.solvable_satProb_iff` — the problem is solvable iff `φ` is satisfiable;
* **`HTN.Article.thm_4_3_8`** — `PlanEx^noHTN_htn` is NP-hard;
* **`HTN.Article.cor_4_3_9`** — even without negative preconditions;
* **`HTN.Article.cor_4_3_10`** — `PlanEx^ACYC_h_htn` is NP-hard for every `h`;
* **`HTN.Article.cor_4_3_11`** — `PlanEx^REG∩ACYC_htn` is NP-hard.

(The article's formal statement of the initial task network has an index error: it labels
`t_{2i+1}` with `φ ↦ ⊤` for every `i` and `t_{2i}` with both `x_{2i} ↦ ⊤` and `xᵢ ↦ ⊥`; the intended
network, used here, has each of the `2n + 1` actions exactly once.)
-/

namespace HTN

namespace Article

namespace SATNo

open Syn Syn.PolyDom PTime NPHard

variable (φ : CNF)

/-- The distinct variables of a formula. -/
def vars : List ℕ := (φ.flatMap fun c => c.map Prod.fst).dedup

/-- The number of variables. -/
def nv : ℕ := (vars φ).length

/-- The clauses containing the literal `(the i-th variable, b)`. -/
def clauseIdx (i : ℕ) (b : Bool) : List ℕ :=
  (List.range φ.length).filter fun j => decide (((vars φ).getI i, b) ∈ φ.getD j [])

/-- The action `a`: precondition, add and delete list. -/
def actOf (a : ℕ) : List ℕ × List ℕ × List ℕ :=
  if a < 2 * nv φ then ([a / 2], (clauseIdx φ (a / 2) (a % 2 == 0)).map (nv φ + ·), [a / 2])
  else ((List.range φ.length).map (nv φ + ·), List.range (nv φ), [])

/-- **The domain of the encoding**: the `2N + 1` actions, no methods. -/
def satDom : DomDesc := ((List.range (2 * nv φ + 1)).map fun a => (a, actOf φ a), [])

/-- **The instance of the encoding**: initial state `X`, no goal, the actions unordered. -/
def satInst : InstDesc := (List.range (nv φ), [], flatTn (2 * nv φ + 1))

/-- **The encoding, in the article's format.** -/
def satProb : ProbDesc := ofSyn (satDom φ) (satInst φ)

/-! ### The action model -/

variable {φ}

theorem lookup_satDom {a : ℕ} (ha : a < 2 * nv φ + 1) :
    (satDom φ).actions.lookup a = some (actOf φ a) :=
  Undec.lookup_map_self _ _ (List.mem_range.2 ha)

abbrev P (φ : CNF) : HTN.Problem ℕ ℕ ℕ ℕ := problem (satDom φ) (satInst φ)

theorem prec_eq {a : ℕ} (ha : a < 2 * nv φ + 1) : (P φ).prec a = {f | f ∈ (actOf φ a).1} := by
  show (satDom φ).prec a = _
  simp [DomDesc.prec, lookup_satDom ha]

theorem add_eq {a : ℕ} (ha : a < 2 * nv φ + 1) : (P φ).add a = {f | f ∈ (actOf φ a).2.1} := by
  show (satDom φ).add a = _
  simp [DomDesc.add, lookup_satDom ha]

theorem del_eq {a : ℕ} (ha : a < 2 * nv φ + 1) : (P φ).del a = {f | f ∈ (actOf φ a).2.2} := by
  show (satDom φ).del a = _
  simp [DomDesc.del, lookup_satDom ha]

theorem add_out {a : ℕ} (ha : ¬ a < 2 * nv φ + 1) : (P φ).add a = ∅ := by
  show (satDom φ).add a = _
  have : (satDom φ).actions.lookup a = none :=
    Undec.lookup_map_self_none _ _ (fun hm => ha (List.mem_range.1 hm))
  simp [DomDesc.add, this]

/-- Only `φ ↦ ⊤` adds variable facts. -/
theorem not_mem_add {a i : ℕ} (hi : i < nv φ) (ha : a ≠ 2 * nv φ) : i ∉ (P φ).add a := by
  by_cases ha' : a < 2 * nv φ + 1
  · rw [add_eq ha']
    have : a < 2 * nv φ := by omega
    simp [actOf, this]
    omega
  · rw [add_out ha']; simp

/-! ### Executions -/

theorem not_mem_transitionSeq {w : List ℕ} {s : Set ℕ} {f : ℕ} (hw : ∀ a ∈ w, f ∉ (P φ).add a)
    (hs : f ∉ s) : f ∉ (P φ).transitionSeq w s := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih =>
    rw [ActionModel.transitionSeq_cons]
    refine ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)) ?_
    simp only [ActionModel.transition, Set.mem_union, Set.mem_diff, not_or, not_and, not_not]
    exact ⟨fun h => absurd h hs, hw a List.mem_cons_self⟩

theorem exists_add_of_mem {w : List ℕ} {s : Set ℕ} {f : ℕ} (h : f ∈ (P φ).transitionSeq w s)
    (hs : f ∉ s) : ∃ a ∈ w, f ∈ (P φ).add a := by
  by_contra hc
  push_neg at hc
  exact not_mem_transitionSeq hc hs h

/-- **A pair is not executed twice without `φ ↦ ⊤` in between.** -/
theorem not_pair_twice {i : ℕ} (hi : i < nv φ) {a b : ℕ} (ha : a / 2 = i) (hb : b / 2 = i)
    (ha' : a < 2 * nv φ) (hb' : b < 2 * nv φ) {v : List ℕ} {s : Set ℕ}
    (hv : 2 * nv φ ∉ v) (hbv : b ∈ v) (h : (P φ).SeqApplicable (a :: v) s) : False := by
  obtain ⟨-, happ⟩ := h
  have hdel : i ∉ (P φ).transition a s := by
    simp only [ActionModel.transition, Set.mem_union, Set.mem_diff, not_or, not_and, not_not]
    refine ⟨fun _ => ?_, not_mem_add hi (by omega)⟩
    rw [del_eq (by omega)]; simp [actOf, ha', ha]
  obtain ⟨v₁, v₂, rfl⟩ := List.append_of_mem hbv
  rw [ActionModel.seqApplicable_append] at happ
  obtain ⟨-, hb₂, -⟩ := happ
  have hni : i ∉ (P φ).transitionSeq v₁ ((P φ).transition a s) :=
    not_mem_transitionSeq (fun c hc => not_mem_add hi (fun h => hv (by
      rw [← h]; exact List.mem_append_left _ hc))) hdel
  apply hni
  have := hb₂ (show i ∈ (P φ).prec b from by rw [prec_eq (by omega)]; simp [actOf, hb', hb])
  exact this

/-- In an executable list without `φ ↦ ⊤`, at most one action of each pair. -/
theorem not_both {i : ℕ} (hi : i < nv φ) {w : List ℕ} {s : Set ℕ} (hw : 2 * nv φ ∉ w)
    (h2i : 2 * i ∈ w) (h2i1 : 2 * i + 1 ∈ w) (h : (P φ).SeqApplicable w s) : False := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem h2i
  rcases List.mem_append.1 h2i1 with hu | hv'
  · obtain ⟨u₁, u₂, rfl⟩ := List.append_of_mem hu
    have e : u₁ ++ (2 * i + 1) :: u₂ ++ 2 * i :: v = u₁ ++ ((2 * i + 1) :: (u₂ ++ 2 * i :: v)) := by
      simp
    rw [e, ActionModel.seqApplicable_append] at h
    rw [e] at hw
    exact not_pair_twice (a := 2 * i + 1) (b := 2 * i) hi (by omega) (by omega) (by omega)
      (by omega) (fun hc => hw (List.mem_append_right _ (List.mem_cons_of_mem _ hc))) (by simp) h.2
  · have hv : 2 * i + 1 ∈ v := (List.mem_cons.1 hv').resolve_left (by omega)
    rw [ActionModel.seqApplicable_append] at h
    exact not_pair_twice (a := 2 * i) (b := 2 * i + 1) hi (by omega) (by omega) (by omega)
      (by omega) (fun hc => hw (List.mem_append_right _ (List.mem_cons_of_mem _ hc))) hv h.2

/-! ### Variables -/

theorem nodup_vars : (vars φ).Nodup := List.nodup_dedup _

theorem mem_vars {c : List (ℕ × Bool)} (hc : c ∈ φ) {x : ℕ} {b : Bool} (hx : (x, b) ∈ c) :
    x ∈ vars φ := by
  unfold vars
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨c, hc, List.mem_map.2 ⟨(x, b), hx, rfl⟩⟩

theorem getI_idxOf {x : ℕ} (hx : x ∈ vars φ) : (vars φ).getI ((vars φ).idxOf x) = x := by
  rw [List.getI_eq_getElem _ (List.idxOf_lt_length_iff.2 hx), List.getElem_idxOf]

theorem idxOf_getI {i : ℕ} (hi : i < nv φ) : (vars φ).idxOf ((vars φ).getI i) = i := by
  rw [List.getI_eq_getElem _ hi]
  exact List.idxOf_getElem nodup_vars _ _

theorem mem_clauseIdx {i : ℕ} {b : Bool} {j : ℕ} :
    j ∈ clauseIdx φ i b ↔ j < φ.length ∧ ((vars φ).getI i, b) ∈ φ.getD j [] := by
  simp [clauseIdx]

/-! ### From a plan to an assignment -/

theorem sat_of_plan {l : List ℕ} (hl : l.Perm (List.range (2 * nv φ + 1)))
    (happ : (P φ).SeqApplicable l {f | f ∈ List.range (nv φ)}) : Satisfiable φ := by
  set N := nv φ with hN
  have hmemN : ∀ x, x ∈ l ↔ x < 2 * N + 1 := fun x => by rw [hl.mem_iff, List.mem_range]
  have hnd : l.Nodup := hl.nodup_iff.2 List.nodup_range
  obtain ⟨u, v, rfl⟩ := List.append_of_mem ((hmemN (2 * N)).2 (by omega))
  have hnd' := List.nodup_append.1 hnd
  have h2u : 2 * N ∉ u := fun h => by
    have := hnd'.2.2 _ h _ List.mem_cons_self; exact this rfl
  have h2v : 2 * N ∉ v := fun h => by
    have := (List.nodup_cons.1 hnd'.2.1).1; exact this h
  rw [ActionModel.seqApplicable_append] at happ
  obtain ⟨hu, hpre, hv⟩ := happ
  -- exactly one action of each pair before `φ ↦ ⊤`
  have hone : ∀ i < N, (2 * i ∈ u ↔ 2 * i + 1 ∉ u) := by
    intro i hi
    have hloc : ∀ x, x < 2 * N → (x ∈ u ∨ x ∈ v) := fun x hx => by
      rcases List.mem_append.1 ((hmemN x).2 (by omega)) with h | h
      · exact Or.inl h
      · exact Or.inr ((List.mem_cons.1 h).resolve_left (by omega))
    constructor
    · intro h1 h2; exact not_both hi h2u h1 h2 hu
    · intro h2
      rcases hloc (2 * i) (by omega) with h | h
      · exact h
      · exfalso
        rcases hloc (2 * i + 1) (by omega) with h' | h'
        · exact h2 h'
        · exact not_both hi h2v h h' hv
  refine ⟨fun x => decide (2 * (vars φ).idxOf x ∈ u), fun c hc => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
  have hNj : N + j ∈ (P φ).transitionSeq u {f | f ∈ List.range N} :=
    hpre (by rw [prec_eq (by omega)]; simp [actOf, ← hN, hj])
  obtain ⟨a, hau, hadd⟩ := exists_add_of_mem hNj (by simp)
  have ha : a < 2 * N := by
    have := (hmemN a).1 (List.mem_append_left _ hau)
    rcases Nat.lt_or_ge a (2 * N) with h | h
    · exact h
    · exact absurd (show a = 2 * N by omega) (fun e => h2u (e ▸ hau))
  rw [add_eq (by omega)] at hadd
  simp only [actOf, ← hN, ha, if_true, Set.mem_setOf_eq, List.mem_map] at hadd
  obtain ⟨j', hj', hjj⟩ := hadd
  obtain rfl : j' = j := by omega
  rw [mem_clauseIdx] at hj'
  obtain ⟨-, hlit⟩ := hj'
  rw [List.getD_eq_getElem _ _ hj] at hlit
  refine ⟨_, hlit, ?_⟩
  simp only
  rw [idxOf_getI (by omega)]
  cases hb : a % 2 == 0
  · have ha1 : a = 2 * (a / 2) + 1 := by simp at hb; omega
    have h1 : 2 * (a / 2) + 1 ∈ u := ha1 ▸ hau
    have := (hone (a / 2) (by omega)).1
    simpa using fun h => this h h1
  · have ha0 : a = 2 * (a / 2) := by simp at hb; omega
    simpa using (ha0 ▸ hau : 2 * (a / 2) ∈ u)

/-! ### From an assignment to a plan -/

/-- The action of the `i`-th variable chosen by the assignment, and the other one. -/
def chosen (τ : ℕ → Bool) (i : ℕ) : ℕ := if τ i then 2 * i else 2 * i + 1

def other (τ : ℕ → Bool) (i : ℕ) : ℕ := if τ i then 2 * i + 1 else 2 * i

theorem chosen_div (τ : ℕ → Bool) (i : ℕ) : chosen τ i / 2 = i := by
  unfold chosen; split_ifs <;> omega

theorem other_div (τ : ℕ → Bool) (i : ℕ) : other τ i / 2 = i := by
  unfold other; split_ifs <;> omega

theorem chosen_mod (τ : ℕ → Bool) (i : ℕ) : (chosen τ i % 2 == 0) = τ i := by
  unfold chosen; cases τ i <;> simp <;> omega

/-- The state after the first `k` chosen actions. -/
def S1 (φ : CNF) (τ : ℕ → Bool) (k : ℕ) : Set ℕ :=
  {f | k ≤ f ∧ f < nv φ} ∪ {f | ∃ j, f = nv φ + j ∧ ∃ i < k, j ∈ clauseIdx φ i (τ i)}

theorem exec_chosen (τ : ℕ → Bool) :
    ∀ k ≤ nv φ, (P φ).SeqApplicable ((List.range k).map (chosen τ)) {f | f ∈ List.range (nv φ)} ∧
      (P φ).transitionSeq ((List.range k).map (chosen τ)) {f | f ∈ List.range (nv φ)} = S1 φ τ k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨trivial, ?_⟩
    ext f; simp [S1]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hck : chosen τ k < 2 * nv φ := by unfold chosen; split_ifs <;> omega
    rw [List.range_succ, List.map_append, ActionModel.seqApplicable_append,
      ActionModel.transitionSeq_append, h2]
    refine ⟨⟨h1, ?_, trivial⟩, ?_⟩
    · show (P φ).prec (chosen τ k) ⊆ _
      rw [prec_eq (by omega)]
      simp only [actOf, hck, if_true, chosen_div]
      intro f hf
      simp only [Set.mem_setOf_eq, List.mem_singleton] at hf
      rw [hf]
      left; exact ⟨le_rfl, by omega⟩
    · show ActionModel.transition _ (chosen τ k) (S1 φ τ k) = S1 φ τ (k + 1)
      unfold ActionModel.transition
      rw [del_eq (by omega), add_eq (by omega)]
      simp only [actOf, hck, if_true, chosen_div, chosen_mod]
      ext f
      simp only [S1, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.mem_singleton,
        List.mem_map]
      constructor
      · rintro (⟨(⟨h1, h2⟩ | ⟨j, rfl, i, hi, hj⟩), hne⟩ | ⟨j, hj, rfl⟩)
        · left; exact ⟨by omega, h2⟩
        · right; exact ⟨j, rfl, i, by omega, hj⟩
        · right; exact ⟨j, rfl, k, by omega, hj⟩
      · rintro (⟨h1, h2⟩ | ⟨j, rfl, i, hi, hj⟩)
        · left; exact ⟨Or.inl ⟨by omega, h2⟩, by omega⟩
        · rcases Nat.lt_or_ge i k with hik | hik
          · left; exact ⟨Or.inr ⟨j, rfl, i, hik, hj⟩, by omega⟩
          · obtain rfl : i = k := by omega
            right; exact ⟨j, hj, rfl⟩

theorem exec_other (τ : ℕ → Bool) (T : Set ℕ) (hT : ∀ i < nv φ, i ∈ T) :
    ∀ k ≤ nv φ, (P φ).SeqApplicable ((List.range k).map (other τ)) T ∧
      ∀ i, k ≤ i → i < nv φ → i ∈ (P φ).transitionSeq ((List.range k).map (other τ)) T := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨trivial, fun i _ hi => hT i hi⟩
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hok : other τ k < 2 * nv φ := by unfold other; split_ifs <;> omega
    rw [List.range_succ, List.map_append, ActionModel.seqApplicable_append,
      ActionModel.transitionSeq_append]
    refine ⟨⟨h1, ?_, trivial⟩, fun i hi hiN => ?_⟩
    · show (P φ).prec (other τ k) ⊆ _
      rw [prec_eq (by omega)]
      simp only [actOf, hok, if_true, other_div]
      intro f hf
      simp only [Set.mem_setOf_eq, List.mem_singleton] at hf
      rw [hf]
      exact h2 k le_rfl (by omega)
    · show i ∈ ActionModel.transition _ (other τ k) _
      unfold ActionModel.transition
      rw [del_eq (by omega)]
      simp only [actOf, hok, if_true, other_div]
      left
      refine ⟨h2 i (by omega) hiN, ?_⟩
      simp; omega

theorem plan_of_sat (h : Satisfiable φ) :
    ∃ l, l.Perm (List.range (2 * nv φ + 1)) ∧
      (P φ).SeqApplicable l {f | f ∈ List.range (nv φ)} := by
  obtain ⟨σ, hσ⟩ := h
  set N := nv φ with hN
  let τ : ℕ → Bool := fun i => σ ((vars φ).getI i)
  let u := (List.range N).map (chosen τ)
  let v := (List.range N).map (other τ)
  refine ⟨u ++ 2 * N :: v, ?_, ?_⟩
  · have hu : ∀ x, x ∈ u ↔ ∃ i < N, chosen τ i = x := by simp [u]
    have hv : ∀ x, x ∈ v ↔ ∃ i < N, other τ i = x := by simp [v]
    have hcl : ∀ i, chosen τ i = 2 * i ∨ chosen τ i = 2 * i + 1 := fun i => by
      unfold chosen; split_ifs <;> simp
    have hol : ∀ i, other τ i = 2 * i ∨ other τ i = 2 * i + 1 := fun i => by
      unfold other; split_ifs <;> simp
    have hco : ∀ i, chosen τ i ≠ other τ i := fun i => by unfold chosen other; split_ifs <;> omega
    refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun x => ?_
    · refine List.nodup_append.2 ⟨?_, List.nodup_cons.2 ⟨?_, ?_⟩, ?_⟩
      · refine List.Nodup.map_on (fun i _ j _ h => ?_) List.nodup_range
        have := congrArg (· / 2) h; simpa [chosen_div] using this
      · rw [hv]; rintro ⟨i, hi, he⟩; rcases hol i with h | h <;> omega
      · refine List.Nodup.map_on (fun i _ j _ h => ?_) List.nodup_range
        have := congrArg (· / 2) h; simpa [other_div] using this
      · intro x hx y hy hxy
        subst hxy
        rw [hu] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        rcases List.mem_cons.1 hy with h | h
        · rcases hcl i with h' | h' <;> omega
        · rw [hv] at h
          obtain ⟨j, hj, he⟩ := h
          have : i = j := by
            have h1 := chosen_div τ i; have h2 := other_div τ j; rw [he] at h2; omega
          subst this
          exact hco i he.symm
    · simp only [List.mem_append, List.mem_cons, List.mem_range, hu, hv]
      constructor
      · rintro (⟨i, hi, rfl⟩ | rfl | ⟨i, hi, rfl⟩)
        · rcases hcl i with h | h <;> omega
        · omega
        · rcases hol i with h | h <;> omega
      · intro hx
        rcases Nat.lt_or_ge x (2 * N) with hx' | hx'
        · by_cases hc : chosen τ (x / 2) = x
          · exact Or.inl ⟨x / 2, by omega, hc⟩
          · refine Or.inr (Or.inr ⟨x / 2, by omega, ?_⟩)
            rcases hcl (x / 2) with h | h <;> rcases hol (x / 2) with h' | h' <;>
              first | omega | (exfalso; exact hco _ (h.trans h'.symm))
        · exact Or.inr (Or.inl (by omega))
  · obtain ⟨hu, hst⟩ := exec_chosen τ N le_rfl
    rw [ActionModel.seqApplicable_append, ActionModel.seqApplicable_cons, hst]
    refine ⟨hu, ?_, ?_⟩
    · show (P φ).prec (2 * N) ⊆ S1 φ τ N
      rw [prec_eq (by omega)]
      simp only [actOf, ← hN, lt_irrefl, if_false]
      intro f hf
      simp only [Set.mem_setOf_eq, List.mem_map, List.mem_range] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      obtain ⟨lit, hlit, hσl⟩ := hσ _ (List.getElem_mem hj)
      have hx : lit.1 ∈ vars φ := mem_vars (List.getElem_mem hj) (b := lit.2) (by simpa using hlit)
      right
      refine ⟨j, rfl, (vars φ).idxOf lit.1, List.idxOf_lt_length_iff.2 hx, ?_⟩
      rw [mem_clauseIdx, getI_idxOf hx, List.getD_eq_getElem _ _ hj]
      refine ⟨hj, ?_⟩
      simp only [τ, getI_idxOf hx, hσl]
      exact hlit
    · refine (exec_other τ _ (fun i hi => ?_) N le_rfl).1
      unfold ActionModel.transition
      rw [add_eq (by omega)]
      simp only [actOf, ← hN, lt_irrefl, if_false]
      right; simpa using hi

/-! ### Correctness -/

/-- **The encoding is correct**: the problem is solvable iff the formula is satisfiable. -/
theorem solvable_satDom_iff : Syn.Solvable (satDom φ) (satInst φ) ↔ Satisfiable φ := by
  rw [satInst, solvable_flat_iff rfl]
  constructor
  · rintro ⟨l, hl, happ, -⟩
    exact sat_of_plan hl happ
  · intro h
    obtain ⟨l, hl, happ⟩ := plan_of_sat h
    exact ⟨l, hl, happ, by simp⟩

theorem solvable_satProb_iff : (satProb φ).toProblem.Solvable ↔ Satisfiable φ :=
  (solvable_ofSyn_iff _ _).trans solvable_satDom_iff

/-! ### Well-formedness and class -/

theorem names_satDom : (satDom φ).actions.map Prod.fst = List.range (2 * nv φ + 1) := by
  simp [satDom, DomDesc.actions, Function.comp_def]

theorem tnValid_flatTn {prim : ℕ → Prop} {k : ℕ} (hk : ∀ i < k, prim i) :
    TnValid prim (flatTn k) where
  nodup := List.nodup_range
  ord_mem := by simp [flatTn, TnDesc.ordList]
  irrefl := by simp [flatTn, TnDesc.ordList]
  trans := by simp [flatTn, TnDesc.ordList]
  lbl_perm := by simp [flatTn, TnDesc.lbl, TnDesc.ids, Function.comp_def]
  prim_ok := by
    intro q hq _
    simp only [flatTn, TnDesc.lbl, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact hk i hi

theorem valid_satProb : (satProb φ).Valid := by
  refine valid_ofSyn ?_ ?_ ?_
  · rw [names_satDom]; exact List.nodup_range
  · exact tnValid_flatTn fun i hi => by rw [names_satDom]; exact List.mem_range.2 hi
  · simp [satDom, DomDesc.methods]

theorem not_reachableName (c : ℕ) : ¬ (satProb φ).toProblem.toPos.ReachableName c := by
  intro h
  cases h with
  | tnI ht hc =>
    rename_i t
    have ht' : t < 2 * nv φ + 1 := by
      simpa [satProb, ofSyn, ProbDesc.toProblem, ProbDesc.tnI, Problem.toPos, satInst, flatTn, InstDesc.tnI,
        TnDesc.ids] using ht
    have : (flatTn (2 * nv φ + 1)).label t = Sum.inr c := hc
    rw [label_flatTn ht'] at this
    exact Sum.inl_ne_inr this
  | method hm => obtain ⟨e, he, -⟩ := hm; simp [satProb, ofSyn, ProbDesc.methods, satDom, DomDesc.methods] at he

theorem not_reachableMethod (m : Method ℕ ℕ ℕ) : ¬ (satProb φ).toProblem.toPos.ReachableMethod m :=
  fun h => not_reachableName _ h.2

theorem isNoHTN_satProb : (satProb φ).toProblem.IsNoHTN := by
  intro t ht
  have ht' : t < 2 * nv φ + 1 := by
    simpa [satProb, ofSyn, ProbDesc.toProblem, ProbDesc.tnI, Problem.toPos, satInst, flatTn, InstDesc.tnI,
      TnDesc.ids] using ht
  exact ⟨t, label_flatTn ht'⟩

theorem noNeg_satProb (a : ℕ) : ((satProb φ).toProblem.δ a).preNeg = ∅ := by
  show ((ofSyn _ _).δ a).preNeg = ∅
  rw [δ_ofSyn]

theorem isACYC_h_satProb (h : ℕ) : (satProb φ).toProblem.IsACYC_h h := by
  refine ⟨fun _ _ => False, ⟨⟨fun c hc => absurd hc (not_reachableName c),
    fun c _ _ hc => absurd hc (not_reachableName c), fun c _ hc => absurd hc (not_reachableName c)⟩,
    fun c _ hc => absurd hc (not_reachableName c), fun m hm => absurd hm (not_reachableMethod m)⟩,
    fun _ => 0, fun c hc => absurd hc (not_reachableName c),
    fun c _ hc => absurd hc (not_reachableName c)⟩

theorem isREG_satProb : (satProb φ).toProblem.IsREG :=
  fun m hm => absurd hm (not_reachableMethod m)

theorem isACYC_satProb : (satProb φ).toProblem.IsACYC := by
  obtain ⟨le, hle, -⟩ := isACYC_h_satProb (φ := φ) 0
  exact ⟨le, hle⟩

end SATNo

/-! ### The theorems -/

open SATNo Syn.PolyDom NPHard

/-- The invalid description used for the non-codes. -/
def badProb : ProbDesc := (([(0, [], [], [], []), (0, [], [], [], [])], []), ([], ([], [], []), [], []))

theorem not_valid_badProb : ¬ badProb.Valid := by
  intro h
  have := h.names_nodup
  simp [badProb, ProbDesc.actions, ActDesc.name] at this

/-- **A reduction of satisfiability to plan existence**, from a polynomial-time encoding. -/
theorem redP_sat {Y : PClass} {f : CNF → ProbDesc} (hf : PT f)
    (hok : ∀ φ, (f φ).Valid ∧ Y (f φ).toProblem)
    (hsol : ∀ φ, (f φ).toProblem.Solvable ↔ Satisfiable φ) : Cx.RedP SAT (PlanEx Y) :=
  redP_codeLang (α := CNF) (β := ProbDesc) (R := fun p => p.Valid ∧ Y p.toProblem ∧
    p.toProblem.Solvable) hf (fun φ => ⟨fun h => ⟨(hok φ).1, (hok φ).2, (hsol φ).2 h⟩,
      fun h => (hsol φ).1 h.2.2⟩) badProb (fun h => not_valid_badProb h.1)

/-- NP-hardness of plan existence from a polynomial-time encoding of satisfiability. -/
theorem npHard_of_sat {Y : PClass} {f : CNF → ProbDesc} (hf : PT f)
    (hok : ∀ φ, (f φ).Valid ∧ Y (f φ).toProblem)
    (hsol : ∀ φ, (f φ).toProblem.Solvable ↔ Satisfiable φ) : Cx.Hard Cx.NP (PlanEx Y) :=
  fun L hL => (sat_npHard L hL).trans (redP_sat hf hok hsol)

theorem pt_vars : PT vars := by
  unfold vars
  exact PT.dedup (PT.flatMap PT.id (PT.map PT.snd (PT.fst.comp PT.snd)))

theorem pt_nv : PT nv := PT.length pt_vars

theorem pt_clauseIdx : PT fun x : CNF × ℕ × Bool => clauseIdx x.1 x.2.1 x.2.2 := by
  unfold clauseIdx
  have hlit : PT fun y : (CNF × ℕ × Bool) × ℕ => ((vars y.1.1).getI y.1.2.1, y.1.2.2) :=
    PT.pair (PT.getI (pt_vars.comp (PT.fst.comp PT.fst)) (PT.fst.comp (PT.snd.comp PT.fst)))
      (PT.snd.comp (PT.snd.comp PT.fst))
  have hcl : PT fun y : (CNF × ℕ × Bool) × ℕ => y.1.1.getD y.2 [] :=
    (PT.getI (PT.fst.comp PT.fst) PT.snd).of_eq fun y => rfl
  exact PT.filter (p := fun (x : CNF × ℕ × Bool) (j : ℕ) =>
      decide (((vars x.1).getI x.2.1, x.2.2) ∈ x.1.getD j []))
    (PT.rangeLength PT.fst) ((PT.elem hcl hlit).of_eq fun _ => by congr)

theorem pt_actOf : PT fun x : CNF × ℕ => actOf x.1 x.2 := by
  unfold actOf
  have hN : PT fun x : CNF × ℕ => nv x.1 := pt_nv.comp PT.fst
  have hhalf : PT fun x : CNF × ℕ => x.2 / 2 := PT.divC PT.snd (by norm_num)
  have hpar : PT fun x : CNF × ℕ => (x.2 % 2 == 0) :=
    PT.beq (PT.modC PT.snd (by norm_num)) (PT.const 0)
  refine PT.ite (PT.lt PT.snd (PT.affine 2 0 hN)) ?_ ?_
  · refine PT.pair (PT.single hhalf) (PT.pair ?_ (PT.single hhalf))
    exact PT.map (pt_clauseIdx.comp (PT.pair PT.fst (PT.pair hhalf hpar)))
      (PT.add (hN.comp PT.fst) PT.snd)
  · exact PT.pair (PT.map (PT.rangeLength PT.fst) (PT.add (hN.comp PT.fst) PT.snd))
      (PT.pair (PT.rangeLength (pt_vars.comp PT.fst)) PT.nil)

theorem pt_flatTn {α : Type} [BEnc α] {f : α → List ℕ} (hf : PT f) :
    PT fun a => flatTn (f a).length := by
  unfold flatTn
  exact PT.pair (PT.rangeLength hf) (PT.pair PT.nil
    (PT.map (PT.rangeLength hf) (PT.pair PT.snd (PT.pair (PT.const false) PT.snd))))

theorem pt_satProb : PT satProb := by
  have hlen : ∀ φ : CNF, (vars φ ++ vars φ ++ [0]).length = 2 * nv φ + 1 := fun φ => by
    simp [nv]; ring
  have hL : PT fun φ : CNF => vars φ ++ vars φ ++ [0] :=
    PT.append (PT.append pt_vars pt_vars) (PT.const [0])
  have hdom : PT satDom := by
    unfold satDom
    refine (PT.pair (PT.map (g := fun (φ : CNF) (a : ℕ) => (a, actOf φ a)) (PT.rangeLength hL)
      (PT.pair PT.snd pt_actOf)) PT.nil).of_eq
      fun φ => by rw [hlen]
  have hinst : PT satInst := by
    unfold satInst
    refine (PT.pair (PT.rangeLength pt_vars) (PT.pair PT.nil (pt_flatTn hL))).of_eq
      fun φ => by rw [hlen]; rfl
  unfold satProb ofSyn
  have hact : PT ofSynAct := by
    unfold ofSynAct
    exact PT.pair PT.fst (PT.pair (PT.fst.comp PT.snd) (PT.pair PT.nil
      (PT.pair (PT.fst.comp (PT.snd.comp PT.snd)) (PT.snd.comp (PT.snd.comp PT.snd)))))
  exact PT.pair (PT.pair (PT.map (PT.fst.comp hdom) (hact.comp PT.snd)) (PT.snd.comp hdom))
    (PT.pair (PT.fst.comp hinst) (PT.pair (PT.snd.comp (PT.snd.comp hinst))
      (PT.pair (PT.fst.comp (PT.snd.comp hinst)) PT.nil)))

/-- **Theorem 4.3.8.** `PlanEx^noHTN_htn` is NP-hard. -/
theorem thm_4_3_8 : Cx.Hard Cx.NP (PlanEx fun P => P.IsNoHTN) :=
  npHard_of_sat pt_satProb (fun _ => ⟨valid_satProb, isNoHTN_satProb⟩)
    (fun _ => solvable_satProb_iff)

/-- **Corollary 4.3.9.** NP-hard already without negative preconditions. -/
theorem cor_4_3_9 :
    Cx.Hard Cx.NP (PlanEx fun P => P.IsNoHTN ∧ ∀ a, (P.δ a).preNeg = ∅) :=
  npHard_of_sat pt_satProb (fun _ => ⟨valid_satProb, isNoHTN_satProb, noNeg_satProb⟩)
    (fun _ => solvable_satProb_iff)

/-- **Corollary 4.3.10.** `PlanEx^ACYC_h_htn` is NP-hard for every fixed `h`. -/
theorem cor_4_3_10 (h : ℕ) : Cx.Hard Cx.NP (PlanEx fun P => P.IsACYC_h h) :=
  npHard_of_sat pt_satProb (fun _ => ⟨valid_satProb, isACYC_h_satProb h⟩)
    (fun _ => solvable_satProb_iff)

/-- **Corollary 4.3.11.** `PlanEx^REG∩ACYC_htn` is NP-hard. -/
theorem cor_4_3_11 : Cx.Hard Cx.NP (PlanEx fun P => P.IsREG ∧ P.IsACYC) :=
  npHard_of_sat pt_satProb (fun _ => ⟨valid_satProb, isREG_satProb, isACYC_satProb⟩)
    (fun _ => solvable_satProb_iff)


end Article

end HTN
