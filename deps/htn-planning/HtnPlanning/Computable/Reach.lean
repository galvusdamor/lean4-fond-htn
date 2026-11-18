import HtnPlanning.Computable.Syntax
/-!
# Reachability in a listed graph, computably

The ordering of a described task network (`HtnPlanning/Computable/Syntax.lean`) is the
strict part of the **transitive closure** of the listed ordering pairs.  A compilation that has
to look at the order of the subtasks of a method — the compilation of regular problems into
`STRIPS` of `HtnComplexity/Computable/RegStrips.lean` is one — therefore needs to *compute*
that transitive closure.

This file does that once and for all:

* `HTN.Syn.reachB E a b` — a `Bool` deciding `Relation.TransGen (fun x y => (x, y) ∈ E) a b`
  (`HTN.Syn.reachB_iff`);
* `HTN.Syn.primrec_reachB` — it is primitive recursive.

The computation is the usual saturation: `reachIter E a n` is the set of nodes reachable from
`a` in at most `n + 1` steps, and it is iterated `E.length + 1` times.  That this is enough is
the only mathematical content: the iteration is increasing, all its values are second
components of listed pairs, so it can grow at most `E.length` times, hence it is stable after
`E.length + 1` steps; a stable value is closed under taking successors and therefore contains
everything the transitive closure reaches.
-/

namespace HTN

namespace Syn

/-- The relation a list of pairs describes. -/
def listRelOf (E : List (ℕ × ℕ)) (a b : ℕ) : Prop := (a, b) ∈ E

/-- The immediate successors of a node. -/
def succsOfNode (E : List (ℕ × ℕ)) (a : ℕ) : List ℕ :=
  E.filterMap fun q => if q.1 = a then some q.2 else none

/-- The immediate successors of a list of nodes. -/
def succsOfList (E : List (ℕ × ℕ)) (S : List ℕ) : List ℕ :=
  E.filterMap fun q => if memB S q.1 then some q.2 else none

@[simp] theorem mem_succsOfNode {E : List (ℕ × ℕ)} {a b : ℕ} :
    b ∈ succsOfNode E a ↔ (a, b) ∈ E := by
  simp only [succsOfNode, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, hb⟩
    by_cases h : q.1 = a
    · rw [if_pos h] at hb
      have : q.2 = b := by simpa using hb
      rwa [← h, ← this, Prod.mk.eta]
    · rw [if_neg h] at hb
      exact absurd hb (by simp)
  · intro h
    exact ⟨(a, b), h, by simp⟩

@[simp] theorem mem_succsOfList {E : List (ℕ × ℕ)} {S : List ℕ} {b : ℕ} :
    b ∈ succsOfList E S ↔ ∃ a ∈ S, (a, b) ∈ E := by
  simp only [succsOfList, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, hb⟩
    by_cases h : memB S q.1 = true
    · rw [if_pos h] at hb
      have hb' : q.2 = b := by simpa using hb
      exact ⟨q.1, memB_iff.1 h, by rwa [← hb', Prod.mk.eta]⟩
    · rw [if_neg h] at hb
      exact absurd hb (by simp)
  · rintro ⟨a, ha, hab⟩
    exact ⟨(a, b), hab, by simp [memB_iff.2 ha]⟩

theorem succsOfList_mono {E : List (ℕ × ℕ)} {S S' : List ℕ} (h : S ⊆ S') :
    succsOfList E S ⊆ succsOfList E S' := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := mem_succsOfList.1 hb
  exact mem_succsOfList.2 ⟨a, h ha, hab⟩

/-- The nodes reachable from `a` in at most `n + 1` steps. -/
def reachIter (E : List (ℕ × ℕ)) (a : ℕ) : ℕ → List ℕ
  | 0 => succsOfNode E a
  | n + 1 => reachIter E a n ++ succsOfList E (reachIter E a n)

/-- The nodes reachable from `a`. -/
def reachList (E : List (ℕ × ℕ)) (a : ℕ) : List ℕ := reachIter E a (E.length + 1)

/-- **Reachability in a listed graph, as a `Bool`.** -/
def reachB (E : List (ℕ × ℕ)) (a b : ℕ) : Bool := memB (reachList E a) b

section Correct

variable {E : List (ℕ × ℕ)} {a : ℕ}

@[simp] theorem reachIter_zero : reachIter E a 0 = succsOfNode E a := rfl

@[simp] theorem reachIter_succ (n : ℕ) :
    reachIter E a (n + 1) = reachIter E a n ++ succsOfList E (reachIter E a n) := rfl

/-- Everything the iteration produces is reachable. -/
theorem transGen_of_mem_reachIter : ∀ (n : ℕ) {b : ℕ}, b ∈ reachIter E a n →
    Relation.TransGen (listRelOf E) a b := by
  intro n
  induction n with
  | zero =>
    intro b hb
    exact Relation.TransGen.single (mem_succsOfNode.1 hb)
  | succ n ih =>
    intro b hb
    rw [reachIter_succ, List.mem_append] at hb
    rcases hb with hb | hb
    · exact ih hb
    · obtain ⟨x, hx, hxb⟩ := mem_succsOfList.1 hb
      exact (ih hx).tail hxb

theorem reachIter_subset_succ (n : ℕ) : reachIter E a n ⊆ reachIter E a (n + 1) := by
  intro b hb
  rw [reachIter_succ]
  exact List.mem_append_left _ hb

theorem reachIter_mono {m n : ℕ} (h : m ≤ n) : reachIter E a m ⊆ reachIter E a n := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.1 h
    subst this
    exact fun x hx => hx
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact fun x hx => reachIter_subset_succ n (ih (Nat.lt_succ_iff.1 hlt) hx)
    · have : m = n + 1 := le_antisymm h hge
      subst this
      exact fun x hx => hx

/-- Everything the iteration produces is the target of a listed pair. -/
theorem mem_targets_of_mem_reachIter : ∀ (n : ℕ) {b : ℕ}, b ∈ reachIter E a n →
    b ∈ E.map Prod.snd := by
  intro n
  induction n with
  | zero =>
    intro b hb
    exact List.mem_map.2 ⟨(a, b), mem_succsOfNode.1 hb, rfl⟩
  | succ n ih =>
    intro b hb
    rw [reachIter_succ, List.mem_append] at hb
    rcases hb with hb | hb
    · exact ih hb
    · obtain ⟨x, -, hxb⟩ := mem_succsOfList.1 hb
      exact List.mem_map.2 ⟨(x, b), hxb, rfl⟩

/-- The iteration is *stable* at `n` when it does not grow at the next step. -/
def Stable (E : List (ℕ × ℕ)) (a n : ℕ) : Prop := reachIter E a (n + 1) ⊆ reachIter E a n

theorem stable_succ {n : ℕ} (h : Stable E a n) : Stable E a (n + 1) := by
  intro b hb
  rw [reachIter_succ, List.mem_append] at hb
  rcases hb with hb | hb
  · exact hb
  · have h1 : succsOfList E (reachIter E a (n + 1)) ⊆ succsOfList E (reachIter E a n) :=
      succsOfList_mono h
    have h2 : b ∈ succsOfList E (reachIter E a n) := h1 hb
    rw [reachIter_succ]
    exact List.mem_append_right _ h2

theorem stable_of_le {n m : ℕ} (h : Stable E a n) (hnm : n ≤ m) : Stable E a m := by
  induction m with
  | zero =>
    have : n = 0 := Nat.le_zero.1 hnm
    subst this
    exact h
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact stable_succ (ih (Nat.lt_succ_iff.1 hlt))
    · have : n = m + 1 := le_antisymm hnm hge
      subst this
      exact h

theorem card_lt_of_not_stable {n : ℕ} (h : ¬ Stable E a n) :
    (reachIter E a n).toFinset.card < (reachIter E a (n + 1)).toFinset.card := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro x hx
    exact List.mem_toFinset.2 (reachIter_subset_succ n (List.mem_toFinset.1 hx))
  · intro hsub
    exact h fun x hx => List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hx))

theorem le_card_of_not_stable (n : ℕ) (h : ∀ k < n, ¬ Stable E a k) :
    n ≤ (reachIter E a n).toFinset.card := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hn := ih fun k hk => h k (by omega)
    have := card_lt_of_not_stable (E := E) (a := a) (h n (by omega))
    omega

theorem card_reachIter_le (n : ℕ) : (reachIter E a n).toFinset.card ≤ E.length := by
  have hsub : (reachIter E a n).toFinset ⊆ (E.map Prod.snd).toFinset := by
    intro x hx
    exact List.mem_toFinset.2 (mem_targets_of_mem_reachIter n (List.mem_toFinset.1 hx))
  calc (reachIter E a n).toFinset.card ≤ (E.map Prod.snd).toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ (E.map Prod.snd).length := List.toFinset_card_le _
    _ = E.length := by simp

theorem stable_length : Stable E a (E.length + 1) := by
  by_cases h : ∃ k ≤ E.length + 1, Stable E a k
  · obtain ⟨k, hk, hstab⟩ := h
    exact stable_of_le hstab hk
  · push_neg at h
    have hall : ∀ k < E.length + 1, ¬ Stable E a k := fun k hk => h k (by omega)
    have h1 := le_card_of_not_stable (E := E) (a := a) (E.length + 1) hall
    have h2 := card_reachIter_le (E := E) (a := a) (E.length + 1)
    omega

/-- **Correctness of `reachB`**: it decides the transitive closure of the listed relation. -/
theorem reachB_iff {E : List (ℕ × ℕ)} {a b : ℕ} :
    reachB E a b = true ↔ Relation.TransGen (listRelOf E) a b := by
  rw [reachB, memB_iff, reachList]
  constructor
  · exact transGen_of_mem_reachIter _
  · intro h
    induction h with
    | single hab =>
      exact reachIter_mono (Nat.zero_le _) (mem_succsOfNode.2 hab)
    | tail _ hxb ih =>
      have : _ ∈ reachIter E a (E.length + 1 + 1) :=
        List.mem_append_right (reachIter E a (E.length + 1)) (mem_succsOfList.2 ⟨_, ih, hxb⟩)
      exact stable_length this

end Correct

/-! ### Computability -/

open Primrec

theorem primrec_succsOfNode : Primrec₂ succsOfNode := by
  refine Primrec₂.of_eq (f := fun (E : List (ℕ × ℕ)) (a : ℕ) =>
    E.filterMap fun q => if q.1 = a then some q.2 else none) ?_ (fun _ _ => rfl)
  refine listFilterMap (β := ℕ × ℕ) (σ := ℕ) Primrec.fst ?_
  refine Primrec.ite ?_ (option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
  exact PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)

theorem primrec_succsOfList : Primrec₂ succsOfList := by
  refine Primrec₂.of_eq (f := fun (E : List (ℕ × ℕ)) (S : List ℕ) =>
    E.filterMap fun q => if memB S q.1 then some q.2 else none) ?_ (fun _ _ => rfl)
  refine listFilterMap (β := ℕ × ℕ) (σ := ℕ) Primrec.fst ?_
  refine Primrec.ite ?_ (option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
  exact PrimrecRel.comp Primrec.eq
    (primrec_memB.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.const true)

theorem primrec_reachIter :
    Primrec₂ (fun (p : List (ℕ × ℕ) × ℕ) (n : ℕ) => reachIter p.1 p.2 n) := by
  have hbase : Primrec fun p : List (ℕ × ℕ) × ℕ => succsOfNode p.1 p.2 :=
    primrec_succsOfNode.comp Primrec.fst Primrec.snd
  have hstep : Primrec₂ fun (p : List (ℕ × ℕ) × ℕ) (z : ℕ × List ℕ) =>
      z.2 ++ succsOfList p.1 z.2 := by
    have h1 : Primrec fun w : (List (ℕ × ℕ) × ℕ) × (ℕ × List ℕ) => w.2.2 :=
      Primrec.snd.comp Primrec.snd
    have h2 : Primrec fun w : (List (ℕ × ℕ) × ℕ) × (ℕ × List ℕ) => succsOfList w.1.1 w.2.2 :=
      primrec_succsOfList.comp (Primrec.fst.comp Primrec.fst) h1
    exact Primrec.list_append.comp h1 h2
  refine Primrec₂.of_eq (Primrec.nat_rec hbase hstep) ?_
  intro p n
  induction n with
  | zero => rfl
  | succ n ih => simpa [reachIter] using congrArg (fun l => l ++ succsOfList p.1 l) ih

/-- `reachB` is primitive recursive. -/
theorem primrec_reachB : Primrec₂ (fun (p : List (ℕ × ℕ) × ℕ) (b : ℕ) => reachB p.1 p.2 b) := by
  have hlist : Primrec fun p : List (ℕ × ℕ) × ℕ => reachList p.1 p.2 := by
    refine (primrec_reachIter.comp Primrec.id ?_).of_eq fun p => rfl
    exact Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)
  exact primrec_memB.comp (hlist.comp Primrec.fst) Primrec.snd

end Syn

end HTN
