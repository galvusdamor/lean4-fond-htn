import HtnComplexity.Complexity.AltFamily
/-!
# Alternation makes the plans exponentially long

`HtnComplexity/Complexity/AltFamily.lean` puts an *alternating* automaton into the fixed
domain description.  This file records what alternation buys, on the smallest possible example:
the one-state alternating automaton `HTN.Syn.allTrueAlt`, whose only transition is the universal
transition `(0, true, 0, 0)`.

For a word of length `n` the encoded domain `HTN.Syn.altDom allTrueAlt n` has

* **size at most `16 n + 1`** (`HTN.Syn.size_altDom_allTrueAlt_le`) — linear in `n`;
* a **solvable** instance for the all-`true` word (`HTN.Syn.solvable_altDom_allTrueAlt`);
* and **every** refinement of its root task into a sequence of actions has exactly `2 ^ n - 1`
  actions (`HTN.Syn.length_yieldSeq_altDom_allTrueAlt_root`, stated as `as.length + 1 = 2 ^ n`
  to stay inside ℕ).

The reason is that a universal method body contains *both* successors, so the refinement of the
root is a complete binary tree of depth `n` rather than a chain: a description of linear size
forces plans of exponential length.  This is the feature the space-bounded hardness
constructions of the literature use, and it is the structural difference between `altDom` and
the chain-shaped `HTN.Syn.autDom` of `HtnComplexity/Complexity/AutFamily.lean`, whose plans
have exactly `n` actions.
-/

namespace HTN

namespace Syn

/-! ### The size of the example domain -/

theorem size_altDom_allTrueAlt_le (n : ℕ) : (altDom allTrueAlt n).size ≤ 16 * n + 1 := by
  have h := size_altDom_le (M := allTrueAlt) n
  simp only [allTrueAlt] at h
  norm_num at h
  exact h

/-! ### Every refinement is a complete binary tree -/

/-- **A refinement of the configuration task with `k` bits left has exactly `2 ^ k - 1`
actions.**  There is no choice: the only method for a configuration is the universal one, and its
body contains one guard and both successors. -/
theorem length_yieldSeq_altDom_allTrueAlt (n : ℕ) : ∀ (k : ℕ) (as : List ℕ),
    (altDom allTrueAlt n).toDomain.YieldSeq [Sum.inr (altName allTrueAlt n k 0)] as →
      as.length + 1 = 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro as hy
    cases hy with
    | comp hm h =>
      rcases seqBody_altDom_iff.1 hm with ⟨j, -, hj, -⟩ | ⟨j, -, hj, -⟩ | ⟨-, -, rfl⟩
      · exact absurd hj (by simp)
      · exact absurd hj (by simp)
      · rw [List.nil_append] at h
        cases h with
        | nil => simp
  | succ k ih =>
    intro as hy
    cases hy with
    | comp hm h =>
      rcases seqBody_altDom_iff.1 hm with ⟨j, -, -, b, q', htr, rfl⟩ |
        ⟨j, -, hjeq, b, q₁, q₂, hun, rfl⟩ | ⟨hk, -, -⟩
      · exact absurd htr (by simp [allTrueAlt])
      · have hjk : j = k := by omega
        have hq : q₁ = 0 ∧ q₂ = 0 := by
          have hu := hun
          simp only [allTrueAlt, List.mem_singleton, Prod.mk.injEq] at hu
          tauto
        obtain ⟨hq₁, hq₂⟩ := hq
        subst hq₁
        subst hq₂
        rw [List.cons_append, List.cons_append, List.nil_append] at h
        cases h with
        | prim h =>
          cases h with
          | comp hm' h' =>
            obtain ⟨-, -, rfl⟩ := seqBody_altDom_br_iff.1 hm'
            rw [List.append_nil] at h'
            obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := Domain.YieldSeq.split
              (xs := [Sum.inr (altName allTrueAlt n j 0)])
              (ys := [Sum.inr (altName allTrueAlt n j 0)]) h'
            rw [hjk] at h₁ h₂
            have e₁ := ih as₁ h₁
            have e₂ := ih as₂ h₂
            simp only [List.length_cons, List.length_append]
            rw [pow_succ]
            omega
      · exact absurd hk (by simp)

/-- **Every refinement of the root task has `2 ^ n - 1` actions.** -/
theorem length_yieldSeq_altDom_allTrueAlt_root (n : ℕ) (as : List ℕ)
    (h : (altDom allTrueAlt n).toDomain.YieldSeq [Sum.inr 0] as) : as.length + 1 = 2 ^ n := by
  have hroot : altName allTrueAlt n n 0 = 0 := altName_root (M := allTrueAlt) n
  exact length_yieldSeq_altDom_allTrueAlt n n as (by rw [hroot]; exact h)

/-! ### The instance is solvable -/

theorem lAllTrue_replicate (n : ℕ) : LAllTrue (List.replicate n true) := by
  intro b hb
  exact List.eq_of_mem_replicate hb

/-- **The encoded problem for the all-`true` word is solvable** — so the exponentially long
refinements are not vacuous. -/
theorem solvable_altDom_allTrueAlt (n : ℕ) :
    Solvable (altDom allTrueAlt n) (posEnc (List.replicate n true)) := by
  have hlen : (List.replicate n true).length = n := List.length_replicate
  have h := (solvable_altDom_iff (M := allTrueAlt) (List.replicate n true)).2
    ((allTrueAlt_accepts_iff _).2 (lAllTrue_replicate n))
  rwa [hlen] at h

/-- **A domain description of linear size all of whose plans are exponentially long.** -/
theorem altDom_allTrueAlt_exponential (n : ℕ) :
    (altDom allTrueAlt n).size ≤ 16 * n + 1 ∧
      Solvable (altDom allTrueAlt n) (posEnc (List.replicate n true)) ∧
      ∀ as : List ℕ, (altDom allTrueAlt n).toDomain.YieldSeq [Sum.inr 0] as →
        as.length + 1 = 2 ^ n :=
  ⟨size_altDom_allTrueAlt_le n, solvable_altDom_allTrueAlt n,
    length_yieldSeq_altDom_allTrueAlt_root n⟩

end Syn

end HTN
