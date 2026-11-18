import HtnPlanning.Core.Classical
/-!
# Boolean semaphores in a classical action model

Several constructions in HTN planning — in particular the `ask_X` / `accept_X` and
`done_X` / `wait_X` handshakes of the TO-HTN ⟶ HTN-AC compilation of
`HtnComplexity/ToHtnAc/ToHtnAc.lean` — use a single fact as a *boolean semaphore*: some actions
raise the fact (the *signalling* actions) and some actions require it and lower it again (the
*consuming* actions), and no other action touches it.

This file proves the resulting counting invariant once and for all:

* `HTN.ActionModel.Semaphore` — the hypotheses on the action model;
* `HTN.ActionModel.Semaphore.countP_add_ind_le` — along any applicable action sequence, the
  number of consuming actions plus the value of the semaphore at the end is at most the number
  of signalling actions plus its value at the start;
* `HTN.ActionModel.Semaphore.countP_con_le` and
  `HTN.ActionModel.Semaphore.countP_con_le_succ` — hence, if the semaphore is initially down,
  every applicable sequence contains at most as many consuming as signalling actions, and if it
  is initially up, at most one more.

Since a prefix of an applicable sequence is applicable, these bounds hold for every prefix of an
applicable sequence, which is the form in which they are used.
-/

namespace HTN

universe u v

namespace ActionModel

variable {F : Type u} {A : Type v} {δ : ActionModel F A}

open Classical in
/-- The value of the fact `f` in the state `s`, as a natural number. -/
noncomputable def ind (f : F) (s : Set F) : ℕ := if f ∈ s then 1 else 0

lemma ind_eq_one {f : F} {s : Set F} (h : f ∈ s) : ind f s = 1 := by
  simp [ind, h]

lemma ind_eq_zero {f : F} {s : Set F} (h : f ∉ s) : ind f s = 0 := by
  simp [ind, h]

lemma ind_le_one (f : F) (s : Set F) : ind f s ≤ 1 := by
  unfold ind; split <;> omega

/-- The fact `f` is a *boolean semaphore* of the action model `δ`, raised by the actions
satisfying `sig` and lowered by the actions satisfying `con`, which require it to be up.  No
other action may touch `f`. -/
structure Semaphore (δ : ActionModel F A) (f : F) (sig con : A → Bool) : Prop where
  /-- A consuming action requires the semaphore to be up. -/
  con_prec : ∀ a, con a → f ∈ δ.prec a
  /-- A consuming action lowers the semaphore. -/
  con_del : ∀ a, con a → f ∈ δ.del a
  /-- A consuming action does not raise the semaphore again. -/
  con_not_add : ∀ a, con a → f ∉ δ.add a
  /-- Only signalling actions raise the semaphore. -/
  add_sig : ∀ a, f ∈ δ.add a → sig a
  /-- Only consuming actions lower the semaphore. -/
  del_con : ∀ a, f ∈ δ.del a → con a

namespace Semaphore

variable {f : F} {sig con : A → Bool}

/-- **The semaphore counting invariant.**  Along an applicable action sequence, the number of
consuming actions plus the final value of the semaphore is at most the number of signalling
actions plus its initial value. -/
theorem countP_add_ind_le (h : δ.Semaphore f sig con) :
    ∀ (as : List A) (s : Set F), δ.SeqApplicable as s →
      as.countP con + ind f (δ.transitionSeq as s) ≤ as.countP sig + ind f s := by
  intro as
  induction as with
  | nil => intro s _; simp
  | cons a as ih =>
      intro s happ
      obtain ⟨ha, has⟩ := happ
      have key : (if con a then 1 else 0) + ind f (δ.transition a s) ≤
          (if sig a then 1 else 0) + ind f s := by
        by_cases hc : con a
        · have hs : f ∈ s := ha (h.con_prec a hc)
          have hnot : f ∉ δ.transition a s := by
            simp only [transition, Set.mem_union, Set.mem_diff, not_or, not_and, not_not]
            exact ⟨fun _ => h.con_del a hc, h.con_not_add a hc⟩
          simp [hc, ind_eq_one hs, ind_eq_zero hnot]
        · by_cases hg : sig a
          · have := ind_le_one f (δ.transition a s)
            simp only [hc, hg, Bool.false_eq_true, if_false, if_true, zero_add]
            omega
          · have hadd : f ∉ δ.add a := fun hf => hg (h.add_sig a hf)
            have hdel : f ∉ δ.del a := fun hf => hc (h.del_con a hf)
            have hiff : f ∈ δ.transition a s ↔ f ∈ s := by
              simp only [transition, Set.mem_union, Set.mem_diff]
              constructor
              · rintro (⟨hh, -⟩ | hh)
                · exact hh
                · exact absurd hh hadd
              · intro hh
                exact Or.inl ⟨hh, hdel⟩
            by_cases hs : f ∈ s
            · simp [hc, hg, ind_eq_one hs, ind_eq_one (hiff.2 hs)]
            · simp [hc, hg, ind_eq_zero hs, ind_eq_zero (fun hh => hs (hiff.1 hh))]
      have hih := ih (δ.transition a s) has
      simp only [List.countP_cons, transitionSeq_cons]
      omega

/-- If the semaphore is initially down, an applicable sequence has at most as many consuming as
signalling actions. -/
theorem countP_con_le (h : δ.Semaphore f sig con) {as : List A} {s : Set F}
    (happ : δ.SeqApplicable as s) (hs : f ∉ s) : as.countP con ≤ as.countP sig := by
  have := h.countP_add_ind_le as s happ
  rw [ind_eq_zero hs] at this
  omega

/-- If the semaphore is initially up, an applicable sequence has at most one more consuming than
signalling action. -/
theorem countP_con_le_succ (h : δ.Semaphore f sig con) {as : List A} {s : Set F}
    (happ : δ.SeqApplicable as s) : as.countP con ≤ as.countP sig + 1 := by
  have := h.countP_add_ind_le as s happ
  have := ind_le_one f s
  omega

/-- **A boolean semaphore whose signals are all consumed alternates.**  If the semaphore is
initially down and the sequence contains exactly as many consuming as signalling actions — so
that no signal is lost — then at *every* point of the sequence the value of the semaphore is
exactly the number of signals given so far minus the number of signals consumed so far.  In
particular that difference never exceeds one: a second signal is never given before the first
one has been consumed. -/
theorem countP_prefix_add_ind (h : δ.Semaphore f sig con) {as p q : List A} {s : Set F}
    (happ : δ.SeqApplicable as s) (hs : f ∉ s) (htot : as.countP sig = as.countP con)
    (hpq : as = p ++ q) :
    p.countP sig = p.countP con + ind f (δ.transitionSeq p s) := by
  subst hpq
  obtain ⟨happp, happq⟩ := (seqApplicable_append _ p q s).1 happ
  have h₁ := h.countP_add_ind_le p s happp
  have h₂ := h.countP_add_ind_le q (δ.transitionSeq p s) happq
  rw [ind_eq_zero hs] at h₁
  simp only [List.countP_append] at htot
  omega

/-- The alternation bound: with all signals consumed, at every point at most one signal is
outstanding. -/
theorem countP_prefix_le_succ (h : δ.Semaphore f sig con) {as p q : List A} {s : Set F}
    (happ : δ.SeqApplicable as s) (hs : f ∉ s) (htot : as.countP sig = as.countP con)
    (hpq : as = p ++ q) : p.countP sig ≤ p.countP con + 1 := by
  have := h.countP_prefix_add_ind happ hs htot hpq
  have := ind_le_one f (δ.transitionSeq p s)
  omega

end Semaphore

end ActionModel

end HTN
