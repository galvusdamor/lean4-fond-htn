import HtnComplexity.Computable.DescEnum
import HtnPlanning.Computable.PermFix
/-!
# How many languages a bounded advice can decide at one length

Fix an instance encoder `E` and a bound `s`, and look at the words of one length `n`.  A
domain description `D` of size at most `s` decides the family of questions
`Solvable D (E w)`, `w` of length `n`; this file bounds the number of **functions** on the
words of length `n` that arise this way.

The two ingredients are the equivariance of the semantics
(`HtnPlanning/Computable/Rename.lean`) and the enumeration of the descriptions over a
fixed pool of names (`HtnComplexity/Computable/DescEnum.lean`):

* `HTN.Syn.advicePool E s n` — the names the instances of length `n` use, together with a
  block of `2 * s` fresh names;
* `HTN.Syn.exists_mem_domsUpTo_congr` — every description of size at most `s` behaves, on the
  instances of length `n`, like one over the pool;
* `HTN.Syn.exists_unrealizable` — hence, as soon as the number of descriptions over the pool is
  smaller than `2 ^ 2 ^ n`, some function on the words of length `n` is **not** of this form.

The bound on the pool is the crux: an instance of size at most `s` mentions at most `2 * s`
names, so the `2 ^ n` instances of length `n` mention at most `2 ^ n * 2 * s` names in total,
and the number of descriptions over so many names is `2 ^ poly`, not `2 ^ 2 ^ n`.
-/

namespace HTN

namespace Syn

open Classical

/-! ### The pool of names of one length -/

/-- The names the instances of the words of length `n` use, with `0` — the name of the default
action — thrown in. -/
noncomputable def instNames (E : List Bool → InstDesc) (n : ℕ) : List ℕ :=
  0 :: ((Finset.univ : Finset (Fin n → Bool)).toList.flatMap fun v => (E (List.ofFn v)).names)

lemma zero_mem_instNames (E : List Bool → InstDesc) (n : ℕ) : 0 ∈ instNames E n := by
  simp [instNames]

lemma mem_instNames (E : List Bool → InstDesc) {n : ℕ} (v : Fin n → Bool) :
    ∀ x ∈ (E (List.ofFn v)).names, x ∈ instNames E n := by
  intro x hx
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨v, ?_, hx⟩)
  simp

lemma length_instNames_le (E : List Bool → InstDesc) {n s : ℕ}
    (hE : ∀ v : Fin n → Bool, (E (List.ofFn v)).size ≤ s) :
    (instNames E n).length ≤ 1 + 2 ^ n * (2 * s) := by
  have hcard : (Finset.univ : Finset (Fin n → Bool)).toList.length = 2 ^ n := by
    rw [Finset.length_toList, Finset.card_univ]
    simp
  have hb : ∀ v ∈ (Finset.univ : Finset (Fin n → Bool)).toList,
      ((E (List.ofFn v)).names).length ≤ 2 * s := by
    intro v _
    have h1 := (E (List.ofFn v)).length_names_le
    have h2 := hE v
    omega
  have h := length_flatMap_le (Finset.univ : Finset (Fin n → Bool)).toList
    (fun v => (E (List.ofFn v)).names) (2 * s) hb
  rw [hcard] at h
  simp only [instNames, List.length_cons]
  omega

/-- The pool of names: those of the instances of length `n`, and `2 * s` fresh ones. -/
noncomputable def advicePool (E : List Bool → InstDesc) (s n : ℕ) : List ℕ :=
  instNames E n ++ freshBlock (instNames E n) (2 * s)

lemma length_advicePool_le (E : List Bool → InstDesc) {n s : ℕ}
    (hE : ∀ v : Fin n → Bool, (E (List.ofFn v)).size ≤ s) :
    (advicePool E s n).length ≤ 1 + 2 ^ n * (2 * s) + 2 * s := by
  have h := length_instNames_le E hE
  simp only [advicePool, List.length_append, length_freshBlock]
  omega

/-! ### Every description behaves like one over the pool -/

/-- **A description of size at most `s` behaves, on the instances of the words of length `n`,
like a description over the pool.** -/
theorem exists_mem_domsUpTo_congr (E : List Bool → InstDesc) {n s : ℕ} {D : DomDesc}
    (hD : D.size ≤ s) :
    ∃ D' ∈ domsUpTo (advicePool E s n) s,
      ∀ v : Fin n → Bool, (Solvable D' (E (List.ofFn v)) ↔ Solvable D (E (List.ofFn v))) := by
  obtain ⟨π, hfix, hmap⟩ := exists_perm_fixing (instNames E n)
    (freshBlock (instNames E n) (2 * s)) (freshBlock_nodup _ _) (freshBlock_notMem _ _)
    D.names (by
      have h := D.length_names_le
      simp only [length_freshBlock]
      omega)
  have h0 : π 0 = 0 := hfix 0 (zero_mem_instNames E n)
  have hinj : Function.Injective π := π.injective
  refine ⟨D.rename π, mem_domsUpTo (by simpa using hD) ?_, fun v => ?_⟩
  · intro x hx
    rw [DomDesc.names_rename] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hmap y hy
  · have hE : (E (List.ofFn v)).rename π = E (List.ofFn v) :=
      InstDesc.rename_eq_self fun x hx => hfix x (mem_instNames E v x hx)
    calc Solvable (D.rename π) (E (List.ofFn v))
        ↔ Solvable (D.rename π) ((E (List.ofFn v)).rename π) := by rw [hE]
      _ ↔ Solvable D (E (List.ofFn v)) := solvable_rename_iff hinj h0 _ _

/-! ### A function no bounded advice realises -/

/-- A list shorter than a finite type misses one of its elements. -/
lemma exists_not_mem_of_length_lt {α : Type} [Fintype α] [DecidableEq α] (l : List α)
    (h : l.length < Fintype.card α) : ∃ a : α, a ∉ l := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset α) ⊆ l.toFinset := fun a _ => List.mem_toFinset.2 (hcon a)
  have h1 := Finset.card_le_card hsub
  have h2 : l.toFinset.card ≤ l.length := List.toFinset_card_le l
  rw [Finset.card_univ] at h1
  omega

/-- **Some function on the words of length `n` is not decided by any description of size at
most `s`** — as soon as the descriptions over the pool are fewer than the functions. -/
theorem exists_unrealizable (E : List Bool → InstDesc) {n s : ℕ}
    (hcount : ((advicePool E s n).length + 2) ^ (16 * (s + 1) ^ 2) < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ D : DomDesc, D.size ≤ s →
      ¬ ∀ v : Fin n → Bool, (Solvable D (E (List.ofFn v)) ↔ f v = true) := by
  classical
  set beh : DomDesc → ((Fin n → Bool) → Bool) :=
    fun D v => decide (Solvable D (E (List.ofFn v))) with hbeh
  have hlen : ((domsUpTo (advicePool E s n) s).map beh).length <
      Fintype.card ((Fin n → Bool) → Bool) := by
    have h1 := length_domsUpTo_le (advicePool E s n) s
    have h2 : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
      simp
    rw [List.length_map, h2]
    omega
  obtain ⟨f, hf⟩ := exists_not_mem_of_length_lt _ hlen
  refine ⟨f, fun D hD hcontra => hf ?_⟩
  obtain ⟨D', hD', hcongr⟩ := exists_mem_domsUpTo_congr (n := n) E hD
  refine List.mem_map.2 ⟨D', hD', ?_⟩
  funext v
  have h := (hcongr v).trans (hcontra v)
  by_cases hp : Solvable D' (E (List.ofFn v))
  · simp [hbeh, hp, h.1 hp]
  · have hfv : f v ≠ true := fun hft => hp (h.2 hft)
    simp [hbeh, hp, Bool.eq_false_iff.2 hfv]

end Syn

end HTN
