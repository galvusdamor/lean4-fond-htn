import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Interleavings of lists

A task network that is a *parallel composition* of two subnetworks is linearized by
interleaving linearizations of the two parts.  This file introduces the corresponding
relation on lists,

`HTN.Interleave xs ys zs` — `zs` is obtained by interleaving `xs` and `ys`,

together with the lemmas that are needed to reason about the refinements of parallel task
networks: interleaving with the empty list, symmetry, concatenation, the interleaving induced
by a decidable predicate (`HTN.interleave_filter`), membership, permutation and length.
-/

namespace HTN

universe u

variable {α : Type u} {β : Type u}

/-- `Interleave xs ys zs`: the list `zs` is an interleaving of the lists `xs` and `ys`, i.e. it
consists of the elements of `xs` and of `ys`, each family in its original order. -/
inductive Interleave : List α → List α → List α → Prop
  /-- The empty list is the interleaving of two empty lists. -/
  | nil : Interleave [] [] []
  /-- Take the next element from the left list. -/
  | left {xs ys zs : List α} (a : α) (h : Interleave xs ys zs) :
      Interleave (a :: xs) ys (a :: zs)
  /-- Take the next element from the right list. -/
  | right {xs ys zs : List α} (a : α) (h : Interleave xs ys zs) :
      Interleave xs (a :: ys) (a :: zs)

namespace Interleave

variable {xs ys zs : List α}

/-- The empty list interleaved on the left. -/
lemma nil_left (ys : List α) : Interleave [] ys ys := by
  induction ys with
  | nil => exact Interleave.nil
  | cons a ys ih => exact Interleave.right a ih

/-- The empty list interleaved on the right. -/
lemma nil_right (xs : List α) : Interleave xs [] xs := by
  induction xs with
  | nil => exact Interleave.nil
  | cons a xs ih => exact Interleave.left a ih

/-- Concatenation is a particular interleaving. -/
lemma append (xs ys : List α) : Interleave xs ys (xs ++ ys) := by
  induction xs with
  | nil => simpa using nil_left ys
  | cons a xs ih => exact Interleave.left a ih

/-- Interleaving is symmetric in its two arguments. -/
lemma symm (h : Interleave xs ys zs) : Interleave ys xs zs := by
  induction h with
  | nil => exact Interleave.nil
  | left a _ ih => exact Interleave.right a ih
  | right a _ ih => exact Interleave.left a ih

/-- An interleaving is a permutation of the concatenation. -/
lemma perm (h : Interleave xs ys zs) : zs.Perm (xs ++ ys) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left a _ ih => exact (ih.cons a)
  | right a _ ih =>
      refine List.Perm.trans (ih.cons a) ?_
      exact (List.perm_middle).symm

lemma length (h : Interleave xs ys zs) : zs.length = xs.length + ys.length := by
  simpa using h.perm.length_eq

lemma countP (h : Interleave xs ys zs) (p : α → Bool) :
    zs.countP p = xs.countP p + ys.countP p := by
  simpa using h.perm.countP_eq p

lemma mem_iff (h : Interleave xs ys zs) {a : α} : a ∈ zs ↔ a ∈ xs ∨ a ∈ ys := by
  simpa using h.perm.mem_iff (a := a)

lemma nodup (h : Interleave xs ys zs) (hz : zs.Nodup) : xs.Nodup ∧ ys.Nodup := by
  have := h.perm.nodup_iff.1 hz
  exact ⟨(List.Nodup.of_append_left this), (List.Nodup.of_append_right this)⟩

lemma eq_nil_of_left (h : Interleave xs ys []) : xs = [] ∧ ys = [] := by
  cases h; exact ⟨rfl, rfl⟩

/-- Interleaving with the empty list on the right changes nothing. -/
lemma eq_of_nil_right' (h : Interleave xs ys zs) (hy : ys = []) : zs = xs := by
  induction h with
  | nil => rfl
  | left a _ ih => rw [ih hy]
  | right a _ _ => simp at hy

/-- Interleaving with the empty list on the right changes nothing. -/
lemma eq_of_nil_right (h : Interleave xs [] zs) : zs = xs := h.eq_of_nil_right' rfl

/-- Interleaving with the empty list on the left changes nothing. -/
lemma eq_of_nil_left (h : Interleave [] ys zs) : zs = ys := h.symm.eq_of_nil_right

/-- A relation that holds pairwise inside both parts and across them holds pairwise in an
interleaving. -/
lemma pairwise {R : α → α → Prop} (h : Interleave xs ys zs) (hx : xs.Pairwise R)
    (hy : ys.Pairwise R) (hcross : ∀ a ∈ xs, ∀ b ∈ ys, R a b ∧ R b a) : zs.Pairwise R := by
  induction h with
  | nil => simp
  | @left xs ys zs a hint ih =>
      rw [List.pairwise_cons] at hx
      refine List.pairwise_cons.2 ⟨?_, ih hx.2 hy (fun b hb c hc => hcross b (by simp [hb]) c hc)⟩
      intro c hc
      rcases hint.mem_iff.1 hc with hc' | hc'
      · exact hx.1 c hc'
      · exact (hcross a (by simp) c hc').1
  | @right xs ys zs a hint ih =>
      rw [List.pairwise_cons] at hy
      refine List.pairwise_cons.2 ⟨?_, ih hx hy.2 (fun b hb c hc => hcross b hb c (by simp [hc]))⟩
      intro c hc
      rcases hint.mem_iff.1 hc with hc' | hc'
      · exact (hcross c hc' a (by simp)).2
      · exact hy.1 c hc'

/-- **Associativity of interleaving.**  Interleaving `a` with `b` and the result with `c` is the
same as interleaving `b` with `c` and `a` with the result. -/
lemma assoc {a b x c z : List α} (h₁ : Interleave a b x) (h₂ : Interleave x c z) :
    ∃ y, Interleave b c y ∧ Interleave a y z := by
  induction h₂ generalizing a b with
  | nil =>
      cases h₁
      exact ⟨[], Interleave.nil, Interleave.nil⟩
  | @left x c z e h ih =>
      cases h₁ with
      | @left a' b' _ _ h₁' =>
          obtain ⟨y, hy₁, hy₂⟩ := ih h₁'
          exact ⟨y, hy₁, Interleave.left e hy₂⟩
      | @right a' b' _ _ h₁' =>
          obtain ⟨y, hy₁, hy₂⟩ := ih h₁'
          exact ⟨e :: y, Interleave.left e hy₁, Interleave.right e hy₂⟩
  | @right x c z e h ih =>
      obtain ⟨y, hy₁, hy₂⟩ := ih h₁
      exact ⟨e :: y, Interleave.right e hy₁, Interleave.right e hy₂⟩

/-- **Associativity of interleaving**, the other way round. -/
lemma assoc' {a b y c z : List α} (h₁ : Interleave b c y) (h₂ : Interleave a y z) :
    ∃ x, Interleave a b x ∧ Interleave x c z := by
  obtain ⟨x, hx₁, hx₂⟩ := assoc h₁.symm h₂.symm
  exact ⟨x, hx₁.symm, hx₂.symm⟩

/-- Interleavings can be mapped along a function. -/
lemma map (f : α → β) (h : Interleave xs ys zs) :
    Interleave (xs.map f) (ys.map f) (zs.map f) := by
  induction h with
  | nil => exact Interleave.nil
  | left a _ ih => exact Interleave.left (f a) ih
  | right a _ ih => exact Interleave.right (f a) ih

/-- Appending interleavings. -/
lemma append_append {xs' ys' zs' : List α} (h : Interleave xs ys zs)
    (h' : Interleave xs' ys' zs') : Interleave (xs ++ xs') (ys ++ ys') (zs ++ zs') := by
  induction h with
  | nil => simpa using h'
  | left a _ ih => exact Interleave.left a ih
  | right a _ ih => exact Interleave.right a ih

end Interleave

/-- Splitting a list along a decidable predicate gives an interleaving of the two
sublists. -/
lemma interleave_filter (p : α → Bool) (l : List α) :
    Interleave (l.filter p) (l.filter (fun a => ! p a)) l := by
  induction l with
  | nil => exact Interleave.nil
  | cons a l ih =>
      by_cases h : p a
      · simpa [List.filter_cons, h] using Interleave.left a ih
      · simp only [List.filter_cons, h, Bool.not_eq_true] at *
        simpa [h] using Interleave.right a ih

/-- Every interleaving arises by splitting along a predicate, provided the two parts are
disjoint: if `zs` is an interleaving of `xs` and `ys` and `p` holds exactly on the elements of
`xs` among those of `zs`, then `xs` and `ys` are the two filtered sublists. -/
lemma Interleave.filter_eq {p : α → Bool} {xs ys zs : List α} (h : Interleave xs ys zs)
    (hx : ∀ a ∈ xs, p a) (hy : ∀ a ∈ ys, ¬ p a) :
    zs.filter p = xs ∧ zs.filter (fun a => ! p a) = ys := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @left xs ys zs a _ ih =>
      have ha : p a := hx a (by simp)
      obtain ⟨h1, h2⟩ := ih (fun b hb => hx b (by simp [hb])) hy
      exact ⟨by simp [ha, h1], by simp [ha, h2]⟩
  | @right xs ys zs a _ ih =>
      have ha : ¬ p a := hy a (by simp)
      obtain ⟨h1, h2⟩ := ih hx (fun b hb => hy b (by simp [hb]))
      simp only [Bool.not_eq_true] at ha
      exact ⟨by simp [ha, h1], by simp [ha, h2]⟩

/-- If in the list `l` every element satisfying `p` precedes every element not satisfying `p`,
then `l` is the concatenation of its two filtered sublists. -/
lemma eq_filter_append_filter {p : α → Bool} {l : List α}
    (h : l.Pairwise (fun a b => p b → p a)) :
    l = l.filter p ++ l.filter (fun a => ! p a) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.pairwise_cons] at h
      by_cases ha : p a
      · simp only [List.filter_cons, ha, if_pos, Bool.not_eq_true', List.cons_append]
        simpa [ha] using congrArg (a :: ·) (ih h.2)
      · have hnone : ∀ b ∈ l, ¬ p b := by
          intro b hb hpb
          exact ha (h.1 b hb hpb)
        have h1 : l.filter p = [] := by
          refine List.filter_eq_nil_iff.2 ?_
          intro b hb
          simpa using hnone b hb
        have h2 : l.filter (fun a => ! p a) = l := by
          refine List.filter_eq_self.2 ?_
          intro b hb
          simpa using hnone b hb
        simp [ha, h1, h2]

end HTN
