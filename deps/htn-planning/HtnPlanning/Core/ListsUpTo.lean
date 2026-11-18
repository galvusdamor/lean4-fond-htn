import Mathlib

/-!
# Enumerating short lists

`HTN.listsUpTo n s` lists every list of length at most `n` whose entries come from `s`.  It is
what turns a *bound on the size* of an object built from a finite vocabulary into a *finite
list* of the possible objects, which is how the decision procedures of this development bound
the number of search configurations they may have to visit:

* `HTN.mem_listsUpTo` — a short list over `s` is listed;
* `HTN.length_listsUpTo_le` — there are at most `(|s| + 1) ^ n` of them.
-/

namespace HTN

universe u v

/-- All lists of length at most `n` over the entries of `s`. -/
def listsUpTo {α : Type u} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | n + 1, s => listsUpTo n s ++ s.flatMap (fun a => (listsUpTo n s).map (fun l => a :: l))

theorem mem_listsUpTo {α : Type u} {s : List α} {l : List α} :
    ∀ {n : ℕ}, l.length ≤ n → (∀ x ∈ l, x ∈ s) → l ∈ listsUpTo n s := by
  intro n
  induction n generalizing l with
  | zero =>
    intro hlen _
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
    simp [listsUpTo, this]
  | succ n ih =>
    intro hlen hsub
    match l with
    | [] =>
      refine List.mem_append.2 (Or.inl (ih (by simp) ?_))
      simp
    | a :: l' =>
      refine List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨a, hsub a (by simp), ?_⟩))
      refine List.mem_map.2 ⟨l', ih ?_ ?_, rfl⟩
      · simpa using hlen
      · exact fun x hx => hsub x (List.mem_cons_of_mem _ hx)

/-- A bound on the length of a `flatMap`. -/
theorem length_flatMap_le' {α : Type u} {β : Type v} (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ n) : (l.flatMap f).length ≤ l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hle := h a (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    calc (f a).length + (l.flatMap f).length ≤ n + l.length * n := by omega
      _ = (l.length + 1) * n := by ring

theorem length_listsUpTo_le {α : Type u} (s : List α) :
    ∀ n : ℕ, (listsUpTo n s).length ≤ (s.length + 1) ^ n := by
  intro n
  induction n with
  | zero => simp [listsUpTo]
  | succ n ih =>
    have hfm : (s.flatMap (fun a => (listsUpTo n s).map (fun l => a :: l))).length
        ≤ s.length * (listsUpTo n s).length :=
      length_flatMap_le' _ _ _ (fun a _ => by simp)
    calc (listsUpTo (n + 1) s).length
        = (listsUpTo n s).length
          + (s.flatMap (fun a => (listsUpTo n s).map (fun l => a :: l))).length := by
          simp [listsUpTo]
      _ ≤ (listsUpTo n s).length + s.length * (listsUpTo n s).length := by omega
      _ = (s.length + 1) * (listsUpTo n s).length := by ring
      _ ≤ (s.length + 1) * (s.length + 1) ^ n := Nat.mul_le_mul_left _ ih
      _ = (s.length + 1) ^ (n + 1) := by ring

/-- A list of bounded length over a finite vocabulary lies in an explicitly bounded finite
set. -/
theorem card_image_le_of_short {α : Type u} {β : Type v} [DecidableEq β] (s : Finset α) (f : α → List β)
    (voc : List β) (n : ℕ) (hlen : ∀ a ∈ s, (f a).length ≤ n)
    (hvoc : ∀ a ∈ s, ∀ x ∈ f a, x ∈ voc) :
    (s.image f).card ≤ (voc.length + 1) ^ n := by
  classical
  have hsub : s.image f ⊆ (listsUpTo n voc).toFinset := by
    intro l hl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hl
    exact List.mem_toFinset.2 (mem_listsUpTo (hlen a ha) (hvoc a ha))
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (List.toFinset_card_le _) (length_listsUpTo_le _ _))

end HTN
