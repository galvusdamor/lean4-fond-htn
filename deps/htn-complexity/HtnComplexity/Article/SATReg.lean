import HtnComplexity.Article.SATNoHTN
import HtnComplexity.Article.CFGDesc
/-!
# Regular acyclic totally ordered HTN planning is NP-hard (Thm. 4.3.12)

The article's encoding of a formula `φ`: a compound task `xᵢ` per variable with the two methods
`xᵢ → (xᵢ ↦ ⊤) xᵢ₊₁` and `xᵢ → (xᵢ ↦ ⊥) xᵢ₊₁` (the last variable without the successor), the
actions `xᵢ ↦ ⊤ = (∅, ∅, {cⱼ | xᵢ ∈ φⱼ}, ∅)` and `xᵢ ↦ ⊥ = (∅, ∅, {cⱼ | ¬xᵢ ∈ φⱼ}, ∅)`, the
initial task `x₁`, the empty initial state and the goal `{c₁, …, cₘ}`.  A solution chooses one
method per variable, an assignment, and reaches the goal iff the assignment satisfies `φ`.

The construction needs at least one variable (for a formula without variables the initial task
`x₁` does not exist); here the variables are those of `HTN.Article.SATNo.vars φ` followed by one
dummy variable that occurs in no clause.  Over the identifiers `ℕ × ℕ` of grids:

* the facts are the clause indices `j < m`;
* the actions are `2i` (`xᵢ ↦ ⊤`) and `2i + 1` (`xᵢ ↦ ⊥`) for `i < K = N + 1`;
* the compound tasks are the variable indices `i < K`.

Results: `HTN.Article.SATReg.solvable_regProb_iff`, and **`HTN.Article.thm_4_3_12`**.
-/

namespace HTN

namespace Article

namespace SATReg

open Syn Syn.PolyDom PTime NPHard SATNo TaskNetwork HTN.Domain

variable (φ : CNF)

/-- The number of variables, with the dummy one. -/
def K : ℕ := nv φ + 1

/-- The clauses made true by the literal `(i-th variable, b)`; none for the dummy. -/
def clauses (i : ℕ) (b : Bool) : List ℕ := if i < nv φ then clauseIdx φ i b else []

/-- The body of a method of `xᵢ`, choosing `2i + c`. -/
def body (i c : ℕ) : List (ℕ ⊕ ℕ) :=
  if i + 1 < K φ then [Sum.inl (2 * i + c), Sum.inr (i + 1)] else [Sum.inl (2 * i + c)]

/-- **The domain of the encoding.** -/
def semDom : HTN.Domain ℕ ℕ ℕ (ℕ × ℕ) where
  prec _ := ∅
  add n := if n < 2 * K φ then {j | j ∈ clauses φ (n / 2) (n % 2 == 0)} else ∅
  del _ := ∅
  methods := {m | ∃ i < K φ, ∃ c < 2, m = ⟨i, grid [body φ i c]⟩}

/-- **The instance of the encoding.** -/
def semInst : HTN.Instance ℕ ℕ ℕ (ℕ × ℕ) where
  init := ∅
  goal := {j | j < φ.length}
  tnI := grid [[Sum.inr 0]]

/-- The problem. -/
def semProblem : HTN.Problem ℕ ℕ ℕ (ℕ × ℕ) := (semDom φ).mkProblem (semInst φ)

variable {φ}

theorem semDom_grid : ∀ m ∈ (semDom φ).methods, ∃ ls, m.subtasks = grid ls := by
  rintro m ⟨i, -, c, -, rfl⟩; exact ⟨_, rfl⟩

theorem seqBody_iff {x : ℕ} {bs : List (ℕ ⊕ ℕ)} :
    (semDom φ).SeqBody x bs ↔ x < K φ ∧ ∃ c < 2, bs = body φ x c := by
  constructor
  · rintro ⟨m, ⟨i, hi, c, hc, rfl⟩, rfl, hb⟩
    exact ⟨hi, c, hc, (Method.hasSeqBody_of_subtasks_grid_single rfl).1 hb⟩
  · rintro ⟨hx, c, hc, rfl⟩
    exact ⟨_, ⟨x, hx, c, hc, rfl⟩, rfl, (Method.hasSeqBody_of_subtasks_grid_single rfl).2 rfl⟩

theorem chainClosed : (semDom φ).ChainClosed Set.univ := by
  rintro c _ ls ⟨m, ⟨i, -, c', -, rfl⟩, -, hsub⟩
  exact ⟨_, hsub.symm, fun _ _ => trivial⟩

/-- The run of a choice from the variable `i` on. -/
def run (τ : ℕ → Bool) (i : ℕ) : List ℕ :=
  (List.range' i (K φ - i)).map fun k => 2 * k + cond (τ k) 0 1

theorem yieldSeq_iff : ∀ (n i : ℕ), K φ - i = n → i < K φ → ∀ as : List ℕ,
    (semDom φ).YieldSeq [Sum.inr i] as ↔ ∃ τ : ℕ → Bool, as = run (φ := φ) τ i := by
  intro n
  induction n with
  | zero => intro i hn hi; omega
  | succ n ih =>
    intro i hn hi as
    constructor
    · intro h
      cases h with
      | comp hm h =>
        obtain ⟨-, c, hc, rfl⟩ := seqBody_iff.1 hm
        simp only [List.append_nil] at h
        unfold body at h
        split_ifs at h with hi1
        · cases h with
          | prim h =>
            obtain ⟨τ, rfl⟩ := (ih (i + 1) (by omega) hi1 _).1 h
            refine ⟨Function.update τ i (c == 0), ?_⟩
            have hr : K φ - i = (K φ - (i + 1)) + 1 := by omega
            simp only [run, hr, List.range'_succ, List.map_cons, Function.update_self]
            refine List.cons_eq_cons.2 ⟨by cases c <;> simp_all; omega, ?_⟩
            refine List.map_congr_left fun k hk => ?_
            simp only [List.mem_range'] at hk
            rw [Function.update_of_ne (by omega)]
        · cases h with
          | prim h =>
            cases h
            refine ⟨fun _ => c == 0, ?_⟩
            have hr : K φ - i = 1 := by omega
            simp only [run, hr, List.range'_one, List.map_cons, List.map_nil]
            congr 1
            interval_cases c <;> simp
    · rintro ⟨τ, rfl⟩
      have hc : (cond (τ i) 0 1 : ℕ) < 2 := by cases τ i <;> simp
      refine YieldSeq.comp (seqBody_iff.2 ⟨hi, _, hc, rfl⟩) ?_
      simp only [List.append_nil]
      unfold body
      split_ifs with hi1
      · have hr : K φ - i = (K φ - (i + 1)) + 1 := by omega
        simp only [run, hr, List.range'_succ, List.map_cons]
        exact YieldSeq.prim ((ih (i + 1) (by omega) hi1 _).2 ⟨τ, rfl⟩)
      · have hr : K φ - i = 1 := by omega
        simp only [run, hr, List.range'_one, List.map_cons, List.map_nil]
        exact YieldSeq.prim YieldSeq.nil

theorem gridYield_tnI_iff {as : List ℕ} :
    (semDom φ).GridYield [[Sum.inr 0]] as ↔ ∃ τ : ℕ → Bool, as = run (φ := φ) τ 0 := by
  rw [gridYield_singleton_iff, chainYield_iff_yieldSeq semDom_grid chainClosed (fun _ _ => trivial)]
  exact yieldSeq_iff _ 0 rfl (by unfold K; omega) as

theorem seqApplicable_any (as : List ℕ) (s : Set ℕ) : (semDom φ).SeqApplicable as s := by
  induction as generalizing s with
  | nil => trivial
  | cons a as ih => exact ⟨by simp [ActionModel.Applicable, semDom], ih _⟩

theorem transitionSeq_run (τ : ℕ → Bool) : ∀ (n i : ℕ), K φ - i = n → ∀ s : Set ℕ,
    (semDom φ).transitionSeq (run (φ := φ) τ i) s =
      s ∪ {j | ∃ k, i ≤ k ∧ k < K φ ∧ j ∈ clauses φ k (τ k)} := by
  intro n
  induction n with
  | zero =>
    intro i hn s
    simp only [run, hn, List.range'_zero, List.map_nil, ActionModel.transitionSeq_nil]
    ext j; simp; omega
  | succ n ih =>
    intro i hn s
    have hr : K φ - i = (K φ - (i + 1)) + 1 := by omega
    have hrun : run (φ := φ) τ i = (2 * i + cond (τ i) 0 1) :: run (φ := φ) τ (i + 1) := by
      simp only [run, hr, List.range'_succ, List.map_cons]
    rw [hrun, ActionModel.transitionSeq_cons, ih (i + 1) (by omega)]
    have hlt : 2 * i + cond (τ i) 0 1 < 2 * K φ := by cases τ i <;> simp <;> omega
    have hdiv : (2 * i + cond (τ i) 0 1) / 2 = i := by cases τ i <;> simp <;> omega
    have hmod : ((2 * i + cond (τ i) 0 1) % 2 == 0) = τ i := by cases τ i <;> simp <;> omega
    simp only [ActionModel.transition, semDom, hlt, if_true, hdiv, hmod, Set.diff_empty]
    ext j
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ((h | h) | ⟨k, hk, hkK, hj⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, le_rfl, by omega, h⟩
      · exact Or.inr ⟨k, by omega, hkK, hj⟩
    · rintro (h | ⟨k, hk, hkK, hj⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk'
        · exact Or.inl (Or.inr hj)
        · exact Or.inr ⟨k, by omega, hkK, hj⟩

/-- **Correctness of the encoding.** -/
theorem solvable_semProblem_iff : (semProblem φ).Solvable ↔ Satisfiable φ := by
  rw [semProblem, HTN.Problem.solvable_iff_netYield]
  have key : ∀ as, (semDom φ).NetYield (grid [[Sum.inr 0]]) as ↔
      ∃ τ : ℕ → Bool, as = run (φ := φ) τ 0 :=
    fun as => (netYield_grid_iff semDom_grid).trans gridYield_tnI_iff
  have hfin : ∀ τ : ℕ → Bool, (semDom φ).transitionSeq (run (φ := φ) τ 0) ∅ =
      {j | ∃ k, k < K φ ∧ j ∈ clauses φ k (τ k)} := fun τ => by
    rw [transitionSeq_run τ _ 0 rfl]; ext j; simp
  constructor
  · rintro ⟨as, hy, -, hgoal⟩
    obtain ⟨τ, rfl⟩ := (key as).1 hy
    have hg : ∀ j < φ.length, ∃ k, k < K φ ∧ j ∈ clauses φ k (τ k) := by
      intro j hj
      have := hgoal (show j ∈ {j | j < φ.length} from hj)
      rw [show (HTN.Domain.mkProblem (semDom φ) (semInst φ)).transitionSeq (run τ 0)
        (HTN.Domain.mkProblem (semDom φ) (semInst φ)).init = (semDom φ).transitionSeq (run τ 0) ∅
        from rfl, hfin] at this
      exact this
    refine ⟨fun x => τ ((vars φ).idxOf x), fun c hc => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
    obtain ⟨k, hk, hkj⟩ := hg j hj
    unfold clauses at hkj
    split_ifs at hkj with hkn
    · rw [mem_clauseIdx, List.getD_eq_getElem _ _ hj] at hkj
      refine ⟨_, hkj.2, ?_⟩
      simp only [idxOf_getI hkn]
    · simp at hkj
  · rintro ⟨σ, hσ⟩
    let τ : ℕ → Bool := fun k => σ ((vars φ).getI k)
    refine ⟨run (φ := φ) τ 0, (key _).2 ⟨τ, rfl⟩, seqApplicable_any _ _, ?_⟩
    show {j | j < φ.length} ⊆ (semDom φ).transitionSeq (run τ 0) ∅
    rw [hfin]
    intro j hj
    obtain ⟨lit, hlit, hσl⟩ := hσ _ (List.getElem_mem hj)
    have hx : lit.1 ∈ vars φ := mem_vars (List.getElem_mem hj) (b := lit.2) (by simpa using hlit)
    have hk : (vars φ).idxOf lit.1 < nv φ := List.idxOf_lt_length_iff.2 hx
    refine ⟨(vars φ).idxOf lit.1, by unfold K; omega, ?_⟩
    unfold clauses
    rw [if_pos hk, mem_clauseIdx, getI_idxOf hx, List.getD_eq_getElem _ _ hj]
    refine ⟨hj, ?_⟩
    simp only [τ, getI_idxOf hx, hσl]
    exact hlit

end SATReg

end Article

end HTN
