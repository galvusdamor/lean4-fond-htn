import HtnPlanning.Interleave.Interleave
/-!
# Interleavings of a list of lists, and prefixes of an interleaving

`HtnPlanning/Interleave/Interleave.lean` introduces the binary interleaving relation.  A refinement
of a parallel task network with many branches — for instance the `2·bound` parallel copies that
the initial task of the HTN-AC compilation unfolds into — is an interleaving of *many* lists,
which this file describes:

`HTN.InterleaveList ls z` — `z` is an interleaving of the lists `ls`.

The two facts proved here are the ones a global analysis of such a plan needs:

* `HTN.Interleave.exists_prefix` / `HTN.InterleaveList.exists_prefix` — **every prefix of an
  interleaving is an interleaving of prefixes of the parts**, so an invariant that holds at
  every prefix of the whole can be evaluated part by part;
* `HTN.Interleave.countP` (already available) and `HTN.InterleaveList.countP` — the number of
  occurrences of a kind of element is the sum of the numbers in the parts.
-/

namespace HTN

universe u

variable {α : Type u}

namespace Interleave

/-- **Every prefix of an interleaving is an interleaving of prefixes.** -/
lemma exists_prefix {xs ys zs p : List α} (h : Interleave xs ys zs) (hp : p <+: zs) :
    ∃ px py : List α, px <+: xs ∧ py <+: ys ∧ Interleave px py p := by
  induction h generalizing p with
  | nil =>
      rw [List.prefix_nil] at hp
      exact ⟨[], [], List.nil_prefix, List.nil_prefix, hp ▸ Interleave.nil⟩
  | @left xs ys zs a h ih =>
      cases p with
      | nil => exact ⟨[], [], List.nil_prefix, List.nil_prefix, Interleave.nil⟩
      | cons b p =>
          obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.1 hp
          obtain ⟨px, py, hpx, hpy, hint⟩ := ih hp'
          exact ⟨b :: px, py, List.cons_prefix_cons.2 ⟨rfl, hpx⟩, hpy, Interleave.left b hint⟩
  | @right xs ys zs a h ih =>
      cases p with
      | nil => exact ⟨[], [], List.nil_prefix, List.nil_prefix, Interleave.nil⟩
      | cons b p =>
          obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.1 hp
          obtain ⟨px, py, hpx, hpy, hint⟩ := ih hp'
          exact ⟨px, b :: py, hpx, List.cons_prefix_cons.2 ⟨rfl, hpy⟩, Interleave.right b hint⟩

end Interleave

/-- `InterleaveList ls z`: the list `z` is an interleaving of the lists `ls`, each of them
keeping its order. -/
inductive InterleaveList : List (List α) → List α → Prop
  /-- The interleaving of no list at all is the empty list. -/
  | nil : InterleaveList [] []
  /-- Interleave the first list with an interleaving of the remaining ones. -/
  | cons {as bs cs : List α} {ls : List (List α)} (h : InterleaveList ls bs)
      (hint : Interleave as bs cs) : InterleaveList (as :: ls) cs

namespace InterleaveList

/-- An interleaving of the empty lists is empty. -/
lemma of_forall_nil : ∀ {ls : List (List α)}, (∀ l ∈ ls, l = []) → InterleaveList ls [] := by
  intro ls
  induction ls with
  | nil => intro _; exact InterleaveList.nil
  | cons l ls ih =>
      intro h
      have hl : l = [] := h l (by simp)
      subst hl
      exact InterleaveList.cons (ih fun m hm => h m (by simp [hm])) Interleave.nil

/-- **The number of occurrences of a kind of element is additive.** -/
lemma countP {ls : List (List α)} {z : List α} (h : InterleaveList ls z) (p : α → Bool) :
    z.countP p = (ls.map (fun l => l.countP p)).sum := by
  induction h with
  | nil => simp
  | cons h hint ih => rw [hint.countP p, ih]; simp

/-- **Every prefix of an interleaving of many lists is an interleaving of prefixes of them.** -/
lemma exists_prefix {ls : List (List α)} {z p : List α} (h : InterleaveList ls z)
    (hp : p <+: z) : ∃ ps : List (List α), InterleaveList ps p ∧ List.Forall₂ (· <+: ·) ps ls := by
  induction h generalizing p with
  | nil =>
      rw [List.prefix_nil] at hp
      exact ⟨[], hp ▸ InterleaveList.nil, List.Forall₂.nil⟩
  | @cons as bs cs ls h hint ih =>
      obtain ⟨pa, pb, hpa, hpb, hint'⟩ := hint.exists_prefix hp
      obtain ⟨ps, hps, hall⟩ := ih hpb
      exact ⟨pa :: ps, InterleaveList.cons hps hint', List.Forall₂.cons hpa hall⟩

/-- **Interleaving two groups of components is interleaving all of them.** -/
lemma append : ∀ {ls₁ ls₂ : List (List α)} {z₁ z₂ z : List α},
    InterleaveList ls₁ z₁ → InterleaveList ls₂ z₂ → Interleave z₁ z₂ z →
      InterleaveList (ls₁ ++ ls₂) z := by
  intro ls₁ ls₂ z₁ z₂ z h₁
  induction h₁ generalizing z with
  | nil =>
      intro h₂ hint
      rw [hint.eq_of_nil_left]
      simpa using h₂
  | @cons as bs cs ls h hint ih =>
      intro h₂ hint'
      obtain ⟨y, hy₁, hy₂⟩ := hint.assoc hint'
      exact InterleaveList.cons (ih h₂ hy₁) hy₂

end InterleaveList

end HTN
