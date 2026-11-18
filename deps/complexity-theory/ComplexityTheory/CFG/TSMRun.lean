import ComplexityTheory.CFG.Basic
import ComplexityTheory.Undec.Machine
/-!
# Runs of a two-stack machine as words of transitions

A halting run of a two-stack machine (`ComplexityTheory/Undec/Machine.lean`) is recorded by the
word of the positions of the transitions it takes.  Such a word `w` is a halting run iff

* restricted to the transitions on the first stack, it **runs the first stack down**
  (`HTN.CFG.RunDown M false s₁`): every transition pops the top symbol and pushes its word, and
  at the end the stack is empty;
* the same for the second stack;
* the control states **chain** from the initial to the accepting state (`HTN.CFG.SRun`).

This is `HTN.CFG.halts_iff`.  Each of the first two conditions together with the third is a
context-free condition on `w` (`ComplexityTheory/CFG/TSMGram.lean`), which is how the halting
problem becomes the intersection problem of two context-free grammars.
-/

namespace HTN

namespace CFG

open Undec

variable (M : TSM)

/-- The transition at a position (a default transition beyond the list). -/
def trn (n : ℕ) : Tr := M.trans.getD n default

/-- **Running a stack down**: `RunDown M b s y` — the transitions `y`, all on the stack `b`,
started with the stack `s`, pop it empty. -/
inductive RunDown (b : Bool) : List ℕ → List ℕ → Prop
  | nil : RunDown b [] []
  | step {n : ℕ} {rest y : List ℕ} (hn : n < M.trans.length) (hb : (trn M n).stk = b)
      (h : RunDown b ((trn M n).push ++ rest) y) : RunDown b ((trn M n).pop :: rest) (n :: y)

/-- **A chain of control states**: the transitions `w` lead from the state `p` to `q`. -/
inductive SRun : ℕ → List ℕ → ℕ → Prop
  | nil (p : ℕ) : SRun p [] p
  | cons {n p q : ℕ} {w : List ℕ} (hn : n < M.trans.length) (hp : p = (trn M n).src)
      (h : SRun (trn M n).tgt w q) : SRun p (n :: w) q

/-- The transitions of a word that act on the stack `b`. -/
def onStk (b : Bool) (w : List ℕ) : List ℕ := w.filter fun n => (trn M n).stk == b

variable {M}

theorem trn_eq {n : ℕ} (hn : n < M.trans.length) : trn M n = M.trans[n] := by
  unfold trn; rw [List.getD_eq_getElem _ _ hn]

theorem trn_mem {n : ℕ} (hn : n < M.trans.length) : trn M n ∈ M.trans := by
  rw [trn_eq hn]; exact List.getElem_mem hn

theorem exists_trn {t : Tr} (ht : t ∈ M.trans) : ∃ n, n < M.trans.length ∧ trn M n = t := by
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 ht
  exact ⟨n, hn, trn_eq hn⟩

@[simp] theorem onStk_nil (b : Bool) : onStk M b [] = [] := rfl

theorem onStk_cons (b : Bool) (n : ℕ) (w : List ℕ) :
    onStk M b (n :: w) = if (trn M n).stk = b then n :: onStk M b w else onStk M b w := by
  by_cases h : (trn M n).stk = b <;> simp [onStk, List.filter_cons, h]

theorem onStk_append (b : Bool) (u v : List ℕ) :
    onStk M b (u ++ v) = onStk M b u ++ onStk M b v := List.filter_append ..

/-! ### Running a stack down -/

namespace RunDown

variable {b : Bool}

theorem nil_inv {y : List ℕ} (h : RunDown M b [] y) : y = [] := by
  cases h; rfl

theorem ne_nil {x : ℕ} {s y : List ℕ} (h : RunDown M b (x :: s) y) : y ≠ [] := by
  cases h; simp

theorem cons_inv {s y : List ℕ} {n : ℕ} (h : RunDown M b s (n :: y)) :
    ∃ rest, s = (trn M n).pop :: rest ∧ n < M.trans.length ∧ (trn M n).stk = b ∧
      RunDown M b ((trn M n).push ++ rest) y := by
  cases h with
  | step hn hb h => exact ⟨_, rfl, hn, hb, h⟩

theorem append {s t y z : List ℕ} (hs : RunDown M b s y) (ht : RunDown M b t z) :
    RunDown M b (s ++ t) (y ++ z) := by
  induction hs with
  | nil => simpa using ht
  | step hn hb _ ih => exact RunDown.step hn hb (by simpa using ih)

theorem split {u y : List ℕ} (h : RunDown M b u y) :
    ∀ s t, u = s ++ t → ∃ y₁ y₂, y = y₁ ++ y₂ ∧ RunDown M b s y₁ ∧ RunDown M b t y₂ := by
  induction h with
  | nil =>
    intro s t h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
    exact ⟨[], [], rfl, RunDown.nil, RunDown.nil⟩
  | @step n rest y hn hb hr ih =>
    intro s t h
    cases s with
    | nil =>
      subst h
      exact ⟨[], n :: y, rfl, RunDown.nil, RunDown.step hn hb hr⟩
    | cons x s =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨y₁, y₂, rfl, h₁, h₂⟩ := ih ((trn M n).push ++ s) t (by simp)
      exact ⟨n :: y₁, y₂, rfl, RunDown.step hn hb h₁, h₂⟩

theorem append_iff {s t y : List ℕ} :
    RunDown M b (s ++ t) y ↔ ∃ y₁ y₂, y = y₁ ++ y₂ ∧ RunDown M b s y₁ ∧ RunDown M b t y₂ := by
  constructor
  · intro h; exact h.split s t rfl
  · rintro ⟨y₁, y₂, rfl, h₁, h₂⟩; exact h₁.append h₂

end RunDown

/-! ### Chains of control states -/

namespace SRun

theorem nil_inv {p q : ℕ} (h : SRun M p [] q) : p = q := by
  cases h; rfl

theorem cons_inv {p q n : ℕ} {w : List ℕ} (h : SRun M p (n :: w) q) :
    n < M.trans.length ∧ p = (trn M n).src ∧ SRun M (trn M n).tgt w q := by
  cases h with
  | cons hn hp h => exact ⟨hn, hp, h⟩

theorem append {p r q : ℕ} {u v : List ℕ} (hu : SRun M p u r) (hv : SRun M r v q) :
    SRun M p (u ++ v) q := by
  induction hu with
  | nil => simpa using hv
  | cons hn hp _ ih => exact SRun.cons hn hp (ih hv)

theorem split {p q : ℕ} {u v : List ℕ} (h : SRun M p (u ++ v) q) :
    ∃ r, SRun M p u r ∧ SRun M r v q := by
  induction u generalizing p with
  | nil => exact ⟨p, SRun.nil p, by simpa using h⟩
  | cons n u ih =>
    obtain ⟨hn, hp, h'⟩ := h.cons_inv
    obtain ⟨r, h₁, h₂⟩ := ih h'
    exact ⟨r, SRun.cons hn hp h₁, h₂⟩

theorem append_iff {p q : ℕ} {u v : List ℕ} :
    SRun M p (u ++ v) q ↔ ∃ r, SRun M p u r ∧ SRun M r v q :=
  ⟨split, fun ⟨_, h₁, h₂⟩ => h₁.append h₂⟩

theorem lt {p q : ℕ} {w : List ℕ} (h : SRun M p w q) : ∀ n ∈ w, n < M.trans.length := by
  induction h with
  | nil => simp
  | cons hn _ _ ih =>
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hn
    · exact ih m hm

end SRun

/-! ### Halting runs -/

/-- **A two-stack machine halts iff some word of transitions runs both stacks down along a chain
of control states from the initial to the accepting state.** -/
theorem reaches_iff {p : ℕ} {s₁ s₂ : List ℕ} :
    M.Reaches ⟨p, s₁, s₂⟩ ⟨M.acc, [], []⟩ ↔
      ∃ w, RunDown M false s₁ (onStk M false w) ∧ RunDown M true s₂ (onStk M true w) ∧
        SRun M p w M.acc := by
  constructor
  · intro h
    have key : ∀ c : Cfg, M.Reaches c ⟨M.acc, [], []⟩ →
        ∃ w, RunDown M false c.s1 (onStk M false w) ∧ RunDown M true c.s2 (onStk M true w) ∧
          SRun M c.st w M.acc := by
      intro c hc
      induction hc using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨[], RunDown.nil, RunDown.nil, SRun.nil _⟩
      | head hstep _ ih =>
        rename_i c₀ c₁ _
        obtain ⟨w, h₁, h₂, h₃⟩ := ih
        obtain ⟨t, ht, hsrc, hcase⟩ := hstep
        obtain ⟨n, hn, rfl⟩ := exists_trn ht
        rcases hcase with ⟨hstk, rest, hrest, rfl⟩ | ⟨hstk, rest, hrest, rfl⟩
        · refine ⟨n :: w, ?_, ?_, SRun.cons hn hsrc h₃⟩
          · rw [onStk_cons, if_pos hstk, hrest]; exact RunDown.step hn hstk h₁
          · rw [onStk_cons, if_neg (by simp [hstk])]; exact h₂
        · refine ⟨n :: w, ?_, ?_, SRun.cons hn hsrc h₃⟩
          · rw [onStk_cons, if_neg (by simp [hstk])]; exact h₁
          · rw [onStk_cons, if_pos hstk, hrest]; exact RunDown.step hn hstk h₂
    exact key _ h
  · rintro ⟨w, h₁, h₂, h₃⟩
    induction w generalizing p s₁ s₂ with
    | nil =>
      rw [h₃.nil_inv]
      rw [onStk_nil] at h₁ h₂
      cases h₁; cases h₂
      exact Relation.ReflTransGen.refl
    | cons n w ih =>
      obtain ⟨hn, hp, h₃'⟩ := h₃.cons_inv
      rw [onStk_cons] at h₁ h₂
      cases hb : (trn M n).stk
      · simp only [hb, if_true, Bool.false_eq_true, if_false] at h₁ h₂
        obtain ⟨rest, rfl, -, -, hr⟩ := h₁.cons_inv
        exact Relation.ReflTransGen.head
          (TSM.step_left (trn_mem hn) hb p hp rest s₂) (ih hr h₂ h₃')
      · simp only [hb, if_true, Bool.true_eq_false, if_false] at h₁ h₂
        obtain ⟨rest, rfl, -, -, hr⟩ := h₂.cons_inv
        exact Relation.ReflTransGen.head
          (TSM.step_right (trn_mem hn) hb p hp s₁ rest) (ih h₁ hr h₃')

theorem halts_iff {s₁ s₂ : List ℕ} :
    M.Halts s₁ s₂ ↔ ∃ w, RunDown M false s₁ (onStk M false w) ∧
      RunDown M true s₂ (onStk M true w) ∧ SRun M M.start w M.acc :=
  reaches_iff

end CFG

end HTN
