import ComplexityTheory.Undec.Machine
import HtnComplexity.Computable.GridDesc
import HtnPlanning.Interleave.GridYield
/-!
# Encoding a two-stack machine as an HTN planning problem

Let `M` be a two-stack machine (`ComplexityTheory/Undec/Machine.lean`).  The HTN problem
`(tsmDom M, tsmInst M s₁ s₂)` simulates `M` started with the stacks `s₁` and `s₂`:

* a **fact** is a control state of `M`; the state of the planning problem is always the
  singleton of the current control state of the machine;
* an **action** is (the position of) a transition of `M`; it has the source state of the
  transition as its precondition, adds its target state and deletes its source state;
* a **compound task** `tskName b a` stands for the symbol `a` sitting on the stack `b`; its
  methods are the transitions that pop `a` from `b`, and the body of the method of the
  transition `t` at position `n` is the chain

      n · tskName b (w₁) · … · tskName b (w_k)      (`w = t.push`)

  — first the action of the transition, then the compound tasks of the pushed word;
* the **initial task network** is the parallel composition of two chains, one per stack: the
  compound tasks of the symbols of `s₁`, and those of `s₂`.  The two chains are unordered
  relative to each other, which is what lets the plan interleave the two stacks; inside a chain
  the tasks are totally ordered, which is what makes each chain behave as a stack;
* the **goal** is the accepting state of `M`.

A plan has to process *all* tasks, so it has to empty both chains, and the state facts serialise
the plan into a run of `M`: the described problem is solvable exactly when `M` halts, which is
proved in `HtnComplexity/Undec/Correct.lean`.

This file only sets up the two descriptions, the semantic problem they denote, and the
elementary facts about both.
-/

namespace HTN

namespace Undec

open Syn TaskNetwork

/-! ### Names -/

/-- The compound task standing for the symbol `a` on the stack `b`. -/
def tskName (b : Bool) (a : ℕ) : ℕ := Nat.pair (cond b 1 0) a

theorem tskName_injective {b b' : Bool} {a a' : ℕ} (h : tskName b a = tskName b' a') :
    b = b' ∧ a = a' := by
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 h
  refine ⟨?_, h2⟩
  cases b <;> cases b' <;> simp_all

/-- The chain of compound tasks of a stack content, top first. -/
def stackChain (b : Bool) (s : List ℕ) : List (ℕ ⊕ ℕ) := s.map fun a => Sum.inr (tskName b a)

@[simp] theorem stackChain_nil (b : Bool) : stackChain b [] = [] := rfl

@[simp] theorem stackChain_cons (b : Bool) (a : ℕ) (s : List ℕ) :
    stackChain b (a :: s) = Sum.inr (tskName b a) :: stackChain b s := rfl

@[simp] theorem stackChain_append (b : Bool) (s s' : List ℕ) :
    stackChain b (s ++ s') = stackChain b s ++ stackChain b s' := List.map_append

theorem stackChain_eq_nil {b : Bool} {s : List ℕ} (h : stackChain b s = []) : s = [] := by
  cases s with
  | nil => rfl
  | cons a s => simp [stackChain] at h

/-- The body of the method of the transition `t`, named `n`: the action `n`, then the compound
tasks of the pushed word. -/
def bodyOf (n : ℕ) (t : Tr) : List (List (ℕ ⊕ ℕ)) := [Sum.inl n :: stackChain t.stk t.push]

namespace TSM

variable (M : TSM)

/-- The transition at a position of the list, `default` outside it. -/
def trAt (n : ℕ) : Tr := M.trans.getD n default

variable {M}

theorem mem_trans_trAt {n : ℕ} (h : n < M.trans.length) : M.trAt n ∈ M.trans := by
  rw [trAt, List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem exists_trAt {t : Tr} (h : t ∈ M.trans) : ∃ n, n < M.trans.length ∧ M.trAt n = t := by
  obtain ⟨n, hn, hnt⟩ := List.getElem_of_mem h
  exact ⟨n, hn, by rw [trAt, List.getD_eq_getElem _ _ hn, hnt]⟩

end TSM

/-! ### The semantic problem -/

/-- **The domain of the encoding**, as a semantic object over the identifiers `ℕ × ℕ` of a
grid. -/
def semDom (M : TSM) : Domain ℕ ℕ ℕ (ℕ × ℕ) where
  prec := fun n => if n < M.trans.length then {(M.trAt n).src} else ∅
  add := fun n => if n < M.trans.length then {(M.trAt n).tgt} else ∅
  del := fun n => if n < M.trans.length then {(M.trAt n).src} else ∅
  methods := {m | ∃ n < M.trans.length,
    m = ⟨tskName (M.trAt n).stk (M.trAt n).pop, TaskNetwork.grid (bodyOf n (M.trAt n))⟩}

/-- **The instance of the encoding**, semantically. -/
def semInst (M : TSM) (s1 s2 : List ℕ) : Instance ℕ ℕ ℕ (ℕ × ℕ) where
  init := {M.start}
  goal := {M.acc}
  tnI := TaskNetwork.grid [stackChain false s1, stackChain true s2]

/-- The semantic problem of the encoding. -/
def semProblem (M : TSM) (s1 s2 : List ℕ) : Problem ℕ ℕ ℕ (ℕ × ℕ) :=
  (semDom M).mkProblem (semInst M s1 s2)

/-- Every method of the encoded domain has a grid body — the hypothesis of
`HTN.Domain.netYield_grid_iff`. -/
theorem semDom_grid (M : TSM) :
    ∀ m ∈ (semDom M).methods, ∃ ls, m.subtasks = TaskNetwork.grid ls := by
  rintro m ⟨n, -, rfl⟩
  exact ⟨_, rfl⟩

/-- The grid bodies of the encoded domain are the bodies of the transitions — as *networks*:
`TaskNetwork.grid` is not injective, so a body is only determined up to the grid it denotes. -/
theorem gridBody_semDom {M : TSM} {c : ℕ} {ls : List (List (ℕ ⊕ ℕ))}
    (h : (semDom M).GridBody c ls) : ∃ n, ∃ _ : n < M.trans.length,
      c = tskName (M.trAt n).stk (M.trAt n).pop ∧
        TaskNetwork.grid ls = TaskNetwork.grid (bodyOf n (M.trAt n)) := by
  obtain ⟨m, ⟨n, hn, rfl⟩, hc, hsub⟩ := h
  exact ⟨n, hn, hc.symm, hsub.symm⟩

/-- Conversely, every transition contributes a grid body. -/
theorem gridBody_semDom_of_lt {M : TSM} {n : ℕ} (hn : n < M.trans.length) :
    (semDom M).GridBody (tskName (M.trAt n).stk (M.trAt n).pop) (bodyOf n (M.trAt n)) :=
  ⟨_, ⟨n, hn, rfl⟩, rfl, rfl⟩

/-! ### The descriptions -/

/-- **The described domain of the encoding.** -/
def tsmDom (M : TSM) : DomDesc :=
  ((List.range M.trans.length).map fun n =>
      (n, ([(M.trAt n).src], [(M.trAt n).tgt], [(M.trAt n).src])),
    (List.range M.trans.length).map fun n =>
      (tskName (M.trAt n).stk (M.trAt n).pop, gridDescOf id id (bodyOf n (M.trAt n))))

/-- **The described instance of the encoding**, for the two initial stacks. -/
def tsmInst (M : TSM) (s1 s2 : List ℕ) : InstDesc :=
  ([M.start], [M.acc], gridDescOf id id [stackChain false s1, stackChain true s2])

@[simp] theorem tsmInst_initList (M : TSM) (s1 s2 : List ℕ) :
    (tsmInst M s1 s2).initList = [M.start] := rfl

@[simp] theorem tsmInst_goalList (M : TSM) (s1 s2 : List ℕ) :
    (tsmInst M s1 s2).goalList = [M.acc] := rfl

@[simp] theorem tsmInst_tnI (M : TSM) (s1 s2 : List ℕ) :
    (tsmInst M s1 s2).tnI = gridDescOf id id [stackChain false s1, stackChain true s2] := rfl

/-! ### Looking up a list of the form `l.map fun x => (x, F x)` -/

theorem lookup_map_self {β : Type} (F : ℕ → β) (l : List ℕ) {k : ℕ} (hk : k ∈ l) :
    (l.map fun x => (x, F x)).lookup k = some (F k) := by
  induction l with
  | nil => simp at hk
  | cons x xs ih =>
    rw [List.map_cons, List.lookup_cons]
    by_cases h : k = x
    · subst h; simp
    · rw [show (k == x) = false by simp [h]]
      exact ih ((List.mem_cons.1 hk).resolve_left h)

theorem lookup_map_self_none {β : Type} (F : ℕ → β) (l : List ℕ) {k : ℕ} (hk : k ∉ l) :
    (l.map fun x => (x, F x)).lookup k = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.lookup_cons]
    have h : k ≠ x := fun he => hk (by simp [he])
    rw [show (k == x) = false by simp [h]]
    exact ih fun hm => hk (List.mem_cons_of_mem _ hm)

/-- The action model of the described domain is the action model of `semDom`. -/
theorem tsmDom_lookup {M : TSM} {n : ℕ} (hn : n < M.trans.length) :
    (tsmDom M).actions.lookup n =
      some ([(M.trAt n).src], [(M.trAt n).tgt], [(M.trAt n).src]) :=
  lookup_map_self _ _ (List.mem_range.2 hn)

theorem tsmDom_lookup_none {M : TSM} {n : ℕ} (hn : ¬ n < M.trans.length) :
    (tsmDom M).actions.lookup n = none :=
  lookup_map_self_none _ _ (fun hm => hn (List.mem_range.1 hm))

theorem prec_tsmDom (M : TSM) (n : ℕ) : (tsmDom M).prec n = (semDom M).prec n := by
  by_cases hn : n < M.trans.length
  · show {f | f ∈ _} = _
    rw [tsmDom_lookup hn]
    simp [semDom, hn]
  · show {f | f ∈ _} = _
    rw [tsmDom_lookup_none hn]
    simp [semDom, hn]

theorem add_tsmDom (M : TSM) (n : ℕ) : (tsmDom M).add n = (semDom M).add n := by
  by_cases hn : n < M.trans.length
  · show {f | f ∈ _} = _
    rw [tsmDom_lookup hn]
    simp [semDom, hn]
  · show {f | f ∈ _} = _
    rw [tsmDom_lookup_none hn]
    simp [semDom, hn]

theorem del_tsmDom (M : TSM) (n : ℕ) : (tsmDom M).del n = (semDom M).del n := by
  by_cases hn : n < M.trans.length
  · show {f | f ∈ _} = _
    rw [tsmDom_lookup hn]
    simp [semDom, hn]
  · show {f | f ∈ _} = _
    rw [tsmDom_lookup_none hn]
    simp [semDom, hn]

end Undec

end HTN
