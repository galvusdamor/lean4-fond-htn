import Mathlib

/-!
# Petri nets and the reachability problem

A **Petri net** over a type of places `P` is given by a list of transitions, a transition being a
pair `(pre, post)` of lists of places, read as multisets.  A marking is a multiset of places; a
transition is enabled at a marking `m` if `pre ≤ m`, and firing it yields `m - pre + post`.

`HTN.Petri.PetriReachDecidable` is the statement that **reachability is decidable** for Petri
nets whose places are natural numbers: the predicate "the marking `m₁` is reachable from `m₀` in
the net `N`" on (codes of) triples `(N, m₀, m₁)` is computable.  This is the theorem of Mayr
(1981) and Kosaraju (1982), see also Leroux (2011) and Leroux–Schmitz (2019), which is used —
as an explicit hypothesis, it is not proved here — by the decision procedure of Dekker and
Behnke for one-hole-digging HTN planning.

The only general fact proved here is that reachability is invariant under an injective renaming
of the places (`HTN.Petri.reach_map_iff`), which is what transfers reachability from the
structured places used by the reduction to natural numbers.
-/

namespace HTN

namespace Petri

variable {P Q : Type*} [DecidableEq P] [DecidableEq Q]

/-- A transition: the places it consumes and the places it produces. -/
abbrev Trans (P : Type*) : Type _ := List P × List P

/-- **Firing a transition** of the net `N`. -/
def Fire (N : List (Trans P)) (m m' : Multiset P) : Prop :=
  ∃ t ∈ N, (t.1 : Multiset P) ≤ m ∧ m' = m - (t.1 : Multiset P) + (t.2 : Multiset P)

/-- **Reachability** in the net `N`. -/
def Reach (N : List (Trans P)) : Multiset P → Multiset P → Prop := Relation.ReflTransGen (Fire N)

/-- **Reachability in Petri nets is decidable** (Mayr; Kosaraju): the reachability predicate is
computable on triples (net, initial marking, target marking), places being natural numbers and
markings being given as lists. -/
def PetriReachDecidable : Prop :=
  ComputablePred fun x : List (Trans ℕ) × List ℕ × List ℕ =>
    Reach x.1 (x.2.1 : Multiset ℕ) (x.2.2 : Multiset ℕ)

/-- Renaming the places of a net. -/
def mapNet (f : P → Q) (N : List (Trans P)) : List (Trans Q) :=
  N.map fun t => (t.1.map f, t.2.map f)

theorem map_sub_of_le (f : P → Q) {s t : Multiset P} (h : t ≤ s) :
    (s - t).map f = s.map f - t.map f := by
  obtain ⟨u, rfl⟩ := le_iff_exists_add.1 h
  rw [add_tsub_cancel_left, Multiset.map_add, add_tsub_cancel_left]

theorem fire_map {f : P → Q} {N : List (Trans P)} {m m' : Multiset P} (h : Fire N m m') :
    Fire (mapNet f N) (m.map f) (m'.map f) := by
  obtain ⟨t, ht, hle, rfl⟩ := h
  refine ⟨(t.1.map f, t.2.map f), List.mem_map_of_mem ht, ?_, ?_⟩
  · simpa using Multiset.map_le_map hle
  · simp [Multiset.map_add, map_sub_of_le f hle]

theorem fire_of_map {f : P → Q} (hf : Function.Injective f) {N : List (Trans P)}
    {m : Multiset P} {z : Multiset Q} (h : Fire (mapNet f N) (m.map f) z) :
    ∃ m', z = m'.map f ∧ Fire N m m' := by
  obtain ⟨t', ht', hle, rfl⟩ := h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht'
  have hle' : (t.1 : Multiset P) ≤ m := by
    rw [← Multiset.map_le_map_iff hf]
    simpa using hle
  refine ⟨m - t.1 + t.2, ?_, t, ht, hle', rfl⟩
  simp [Multiset.map_add, map_sub_of_le f hle']

/-- **Reachability is invariant under injective renamings of the places.** -/
theorem reach_map_iff {f : P → Q} (hf : Function.Injective f) {N : List (Trans P)}
    {m m' : Multiset P} : Reach (mapNet f N) (m.map f) (m'.map f) ↔ Reach N m m' := by
  constructor
  · intro h
    have key : ∀ z, Reach (mapNet f N) (m.map f) z → ∃ m'', z = m''.map f ∧ Reach N m m'' := by
      intro z hz
      induction hz with
      | refl => exact ⟨m, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hstep ih =>
        obtain ⟨m'', rfl, hr⟩ := ih
        obtain ⟨m''', rfl, hf'⟩ := fire_of_map hf hstep
        exact ⟨m''', rfl, hr.tail hf'⟩
    obtain ⟨m'', he, hr⟩ := key _ h
    rwa [← Multiset.map_injective hf he] at hr
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (fire_map hstep)

end Petri

end HTN
