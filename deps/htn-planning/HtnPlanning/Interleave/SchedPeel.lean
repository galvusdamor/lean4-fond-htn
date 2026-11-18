import HtnPlanning.Interleave.Sched
import HtnPlanning.Core.Classical
/-!
# Peeling a schedule: the actions of the only component that can move

`HTN.Sched ls z` (`HtnPlanning/Interleave/Sched.lean`) is the operational description of an
interleaving: at each point the first remaining action of one of the components `ls` is
executed.  For the analysis of a plan of a construction in which the components synchronise —
the HTN-AC compilation of `HtnComplexity/ToHtnAc/ToHtnAc.lean` is the case at hand — one wants the
converse reading: *if every component but one is blocked, the plan must continue with the
actions of that one component.*

This file provides the three generic ingredients:

* `HTN.eq_of_split_of_forall` — a list has only one decomposition `pre ++ x :: post` singling
  out an element that fails a predicate all the other elements satisfy;
* `HTN.Sched.perm` — a schedule does not depend on the order in which the components are
  listed, so the component under consideration may always be moved to the front;
* `HTN.Sched.peel` and `HTN.Sched.peel_run` — if the components `rest` cannot move in the
  current state (and, for `peel_run`, in any state reachable while the active component runs),
  then the schedule of `(a :: t) :: rest` starts with `a`, resp. the schedule of `(u ++ t) :: rest`
  starts with `u`.
-/

namespace HTN

universe u v

variable {α : Type u}

/-- **A distinguished element determines the decomposition.**  If `pre ++ x :: post` is also
`pre' ++ y :: post'`, and `y` fails a predicate that every element of `pre` and of `post`
satisfies, then the two decompositions are the same. -/
lemma eq_of_split_of_forall {P : α → Prop} : ∀ {pre post pre' post' : List α} {x y : α},
    pre ++ x :: post = pre' ++ y :: post' → (∀ z ∈ pre, P z) → (∀ z ∈ post, P z) → ¬ P y →
    pre = pre' ∧ x = y ∧ post = post' := by
  intro pre
  induction pre with
  | nil =>
      intro post pre' post' x y h hpre hpost hy
      cases pre' with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at h
          exact ⟨rfl, h.1, h.2⟩
      | cons c pre'' =>
          exfalso
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          exact hy (hpost y (h.2 ▸ List.mem_append_right _ (List.mem_cons_self)))
  | cons a pre₀ ih =>
      intro post pre' post' x y h hpre hpost hy
      cases pre' with
      | nil =>
          exfalso
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
          exact hy (h.1 ▸ hpre a (List.mem_cons_self))
      | cons c pre'' =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h'⟩ := h
          obtain ⟨h₁, h₂, h₃⟩ := ih h' (fun z hz => hpre z (List.mem_cons_of_mem _ hz)) hpost hy
          exact ⟨by rw [h₁], h₂, h₃⟩

/-- **A schedule does not depend on the order of the components.** -/
theorem Sched.perm {ls ls' : List (List α)} {z : List α} (hs : Sched ls z) :
    ls.Perm ls' → Sched ls' z := by
  induction hs generalizing ls' with
  | @nil ls h =>
      intro hp
      exact Sched.nil fun l hl => h l (hp.mem_iff.2 hl)
  | @step pre post a t z _ ih =>
      intro hp
      have hmem : (a :: t) ∈ ls' := hp.mem_iff.1 (by simp)
      obtain ⟨pre', post', rfl⟩ := List.append_of_mem hmem
      have hcancel : (pre ++ post).Perm (pre' ++ post') := by
        have h₁ : (pre ++ (a :: t) :: post).Perm ((a :: t) :: (pre ++ post)) :=
          List.perm_middle
        have h₂ : (pre' ++ (a :: t) :: post').Perm ((a :: t) :: (pre' ++ post')) :=
          List.perm_middle
        exact (h₁.symm.trans (hp.trans h₂)).cons_inv
      refine Sched.step (pre := pre') (post := post') (ih ?_)
      exact (List.perm_middle.trans (hcancel.cons t)).trans List.perm_middle.symm

namespace Sched

variable {Fa : Type u} {Ac : Type v} {δ : ActionModel Fa Ac}

/-- A component that is exhausted, or whose next action is inapplicable in `s`, cannot move. -/
def Stuck (δ : ActionModel Fa Ac) (s : Set Fa) (l : List Ac) : Prop :=
  ∀ b t, l = b :: t → ¬ δ.Applicable b s

/-- **Peeling one action.**  If no component of `rest` can move in `s`, the schedule of
`(a :: t) :: rest` executable in `s` starts with `a`. -/
theorem peel {a : Ac} {t : List Ac} {rest : List (List Ac)} {z : List Ac} {s : Set Fa}
    (hsched : Sched ((a :: t) :: rest) z) (happ : δ.SeqApplicable z s)
    (hblocked : ∀ l ∈ rest, Stuck δ s l) :
    ∃ z', z = a :: z' ∧ Sched (t :: rest) z' := by
  cases z with
  | nil =>
      exact absurd (hsched.forall_nil (a :: t) (by simp)) (by simp)
  | cons b z₀ =>
      obtain ⟨pre, post, t', hls, hs⟩ := hsched.exists_of_cons
      have happb : δ.Applicable b s := happ.1
      have hsplit := eq_of_split_of_forall (P := Stuck δ s)
        (pre := []) (post := rest) (pre' := pre) (post' := post) (x := a :: t) (y := b :: t')
        (by simpa using hls) (by simp) hblocked (fun hc => hc b t' rfl happb)
      obtain ⟨hpre, hxy, hpost⟩ := hsplit
      subst hpre
      subst hpost
      simp only [List.cons.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨z₀, rfl, by simpa using hs⟩

/-- **Peeling a whole run.**  If an invariant `Inv` holds in `s`, is preserved by every action
of `u`, and blocks every component of `rest`, then the schedule of `(u ++ t) :: rest` executable
in `s` starts with `u`. -/
theorem peel_run {Inv : Set Fa → Prop} :
    ∀ {u : List Ac} {t : List Ac} {rest : List (List Ac)} {z : List Ac} {s : Set Fa},
      Sched ((u ++ t) :: rest) z → δ.SeqApplicable z s → Inv s →
      (∀ a ∈ u, ∀ s' : Set Fa, Inv s' → Inv (δ.transition a s')) →
      (∀ s' : Set Fa, Inv s' → ∀ l ∈ rest, Stuck δ s' l) →
      ∃ z', z = u ++ z' ∧ Sched (t :: rest) z' := by
  intro u
  induction u with
  | nil => intro t rest z s hsched _ _ _ _; exact ⟨z, rfl, by simpa using hsched⟩
  | cons a u ih =>
      intro t rest z s hsched happ hinv hpres hblock
      obtain ⟨z', rfl, hs'⟩ :=
        peel (by simpa using hsched) happ (hblock s hinv)
      have happ' : δ.SeqApplicable z' (δ.transition a s) :=
        happ.2
      obtain ⟨z'', rfl, hs''⟩ :=
        ih hs' happ' (hpres a (by simp) s hinv)
          (fun b hb => hpres b (List.mem_cons_of_mem _ hb)) hblock
      exact ⟨z'', by simp, hs''⟩

end Sched

end HTN
