import FondHtn.MethodPoliciesStrong
import HtnPlanning.Core.TONormalForm
/-!
# The strong method-based game on sequences of task names

For problems all of whose methods are totally ordered, a (well-formed, totally ordered) task
network is a sequence of task names (`HTN.TaskNetwork.IsSeqNet`).  This file introduces the
**leftmost list game** `FOND.Problem.LRunH`, graded by height and with a postcondition `Φ` on the
final states:

* the empty sequence is won in the states of `Φ`;
* a leading primitive task is executed (applicable, all outcomes won);
* a leading compound task is replaced by the body of one of its methods.

Only the *first* task is ever executed or decomposed.  The calculus (`LRunH.mono`,
`lrunH_append`, `lrunH_append'`) composes games along concatenation.  The bridge to the AND/OR
characterisation of strong method-based solvability ([CB22]) is in
`FondHtn/HardMP/Bridge.lean`.
-/

namespace FOND

open HTN HTN.TaskNetwork

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable (P : Problem F A C I)

/-- `P` has a method for `c` whose (totally ordered) body is `bs`. -/
def SeqBodyF (c : C) (bs : List (A ⊕ C)) : Prop :=
  ∃ m ∈ P.methods, m.abstractTask = c ∧ m.HasSeqBody bs

/-- **The leftmost list game**, graded by height, with postcondition `Φ`. -/
inductive LRunH : ℕ → List (A ⊕ C) → Set F → Set (Set F) → Prop
  /-- The empty sequence: the state must satisfy the postcondition. -/
  | nil {n : ℕ} {s : Set F} {Φ : Set (Set F)} (h : s ∈ Φ) : LRunH n [] s Φ
  /-- Execute the leading primitive task. -/
  | prim {n : ℕ} {a : A} {xs : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)}
      (happ : (P.δ a).Applicable s) (hall : ∀ s' ∈ (P.δ a).outcomes s, LRunH n xs s' Φ) :
      LRunH (n + 1) (Sum.inl a :: xs) s Φ
  /-- Decompose the leading compound task. -/
  | comp {n : ℕ} {c : C} {bs xs : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)}
      (hb : P.SeqBodyF c bs) (h : LRunH n (bs ++ xs) s Φ) : LRunH (n + 1) (Sum.inr c :: xs) s Φ

variable {P}

theorem LRunH.mono {n : ℕ} {xs : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)}
    (h : P.LRunH n xs s Φ) : ∀ {n' : ℕ} {Ψ : Set (Set F)}, n ≤ n' → Φ ⊆ Ψ → P.LRunH n' xs s Ψ := by
  induction h with
  | nil h => exact fun _ hΦ => .nil (hΦ h)
  | prim happ _ ih =>
    intro n' Ψ hn hΦ
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .prim happ fun s' hs' => ih s' hs' (by omega) hΦ
  | comp hb _ ih =>
    intro n' Ψ hn hΦ
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .comp hb (ih (by omega) hΦ)

theorem lrunH_nil_iff {n : ℕ} {s : Set F} {Φ : Set (Set F)} : P.LRunH n [] s Φ ↔ s ∈ Φ :=
  ⟨fun h => by cases h with | nil h => exact h, fun h => .nil h⟩

theorem lrunH_prim_iff {n : ℕ} {a : A} {xs : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)} :
    P.LRunH (n + 1) (Sum.inl a :: xs) s Φ ↔
      (P.δ a).Applicable s ∧ ∀ s' ∈ (P.δ a).outcomes s, P.LRunH n xs s' Φ :=
  ⟨fun h => by cases h with | prim happ hall => exact ⟨happ, hall⟩,
    fun ⟨happ, hall⟩ => .prim happ hall⟩

theorem lrunH_comp_iff {n : ℕ} {c : C} {xs : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)} :
    P.LRunH (n + 1) (Sum.inr c :: xs) s Φ ↔ ∃ bs, P.SeqBodyF c bs ∧ P.LRunH n (bs ++ xs) s Φ :=
  ⟨fun h => by cases h with | comp hb h => exact ⟨_, hb, h⟩, fun ⟨_, hb, h⟩ => .comp hb h⟩

theorem not_lrunH_zero_cons {y : A ⊕ C} {xs : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)} :
    ¬ P.LRunH 0 (y :: xs) s Φ := fun h => by cases h

/-- **Sequential composition**, first direction. -/
theorem lrunH_append {n : ℕ} {l : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)}
    (h : P.LRunH n l s Φ) : ∀ {xs ys : List (A ⊕ C)}, l = xs ++ ys →
      P.LRunH n xs s {s' | P.LRunH n ys s' Φ} := by
  induction h with
  | @nil n s Φ hs =>
    intro xs ys he
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 he.symm
    exact .nil (.nil hs)
  | @prim n a l s Φ happ hall ih =>
    intro xs ys he
    rcases xs with _ | ⟨y, xs⟩
    · exact .nil (by rw [List.nil_append] at he; rw [← he]; exact .prim happ hall)
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .prim happ fun s' hs' =>
        (ih s' hs' rfl).mono (by omega) fun _ h' => h'.mono (by omega) le_rfl
  | @comp n c bs l s Φ hb h ih =>
    intro xs ys he
    rcases xs with _ | ⟨y, xs⟩
    · exact .nil (by rw [List.nil_append] at he; rw [← he]; exact .comp hb h)
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .comp hb ((ih (by rw [List.append_assoc])).mono (by omega)
        fun _ h' => h'.mono (by omega) le_rfl)

/-- **Sequential composition**, second direction. -/
theorem lrunH_append' {n m : ℕ} {xs ys : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)}
    (h : P.LRunH n xs s {s' | P.LRunH m ys s' Φ}) : P.LRunH (n + m) (xs ++ ys) s Φ := by
  generalize hΨ : {s' | P.LRunH m ys s' Φ} = Ψ at h
  induction h with
  | nil h => subst hΨ; exact (show P.LRunH m ys _ Φ from h).mono (by omega) le_rfl
  | prim happ _ ih =>
    rw [List.cons_append, show ∀ k, k + 1 + m = k + m + 1 from fun k => by omega]
    exact .prim happ fun s' hs' => ih s' hs' hΨ
  | comp hb _ ih =>
    rw [List.cons_append, show ∀ k, k + 1 + m = k + m + 1 from fun k => by omega]
    exact .comp hb (by rw [← List.append_assoc]; exact ih hΨ)

end Problem

end FOND
