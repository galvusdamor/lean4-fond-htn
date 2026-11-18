import HtnComplexity.Undec.Encoding
/-!
# What the two chains of the encoding refine into

The initial task network of the encoding is a grid of two chains, one per stack, and every
method body is again a chain.  The refinements of such a network are described syntactically by
`HTN.Domain.ChainYield` and `HTN.Domain.GridYield`
(`HtnPlanning/Interleave/GridYield.lean`).  This file computes them for the encoding:

* `HTN.Undec.Yields M b s as` — the inductive relation "the stack `b`, holding `s`, can be run
  down by the sequence `as` of transitions": either `s` is empty and `as` is empty, or the first
  transition of `as` pops the top of `s`, pushes its word, and the rest of `as` runs the
  resulting stack down;
* `HTN.Undec.chainYield_iff` — the chain of a stack refines exactly into the sequences `as` with
  `Yields M b s as`;
* `HTN.Undec.gridYield_iff` — the initial network refines exactly into the interleavings of a
  run-down of the first stack with a run-down of the second.

Nothing here mentions the state of the planning problem: these are the *hierarchical*
constraints on a plan.  The state constraints are dealt with in
`HtnComplexity/Undec/Run.lean`.
-/

namespace HTN

namespace Undec

open Syn TaskNetwork Domain

/-- **The transition sequences that run a stack down.**  `Yields M b s as` holds when the stack
`b`, holding `s`, is emptied by performing the transitions `as` in this order. -/
inductive Yields (M : TSM) (b : Bool) : List ℕ → List ℕ → Prop
  /-- An empty stack is run down by no transition. -/
  | nil : Yields M b [] []
  /-- A transition pops the top symbol and pushes its word. -/
  | step {n : ℕ} {rest as : List ℕ} (hn : n < M.trans.length) (hb : (M.trAt n).stk = b)
      (hy : Yields M b ((M.trAt n).push ++ rest) as) :
      Yields M b ((M.trAt n).pop :: rest) (n :: as)

variable {M : TSM} {b : Bool} {s : List ℕ} {as : List ℕ}

/-- A stack that is run down by no transition is empty. -/
theorem Yields.eq_nil (h : Yields M b s []) : s = [] := by
  cases h; rfl

/-- Inversion of a nonempty run-down. -/
theorem Yields.cons_inv {n : ℕ} {as : List ℕ} (h : Yields M b s (n :: as)) :
    ∃ rest, n < M.trans.length ∧ (M.trAt n).stk = b ∧ s = (M.trAt n).pop :: rest ∧
      Yields M b ((M.trAt n).push ++ rest) as := by
  cases h with
  | step hn hb hy => exact ⟨_, hn, hb, rfl, hy⟩

/-- Running two stacked contents down one after the other. -/
theorem Yields.append {s s' : List ℕ} {as as' : List ℕ} (h : Yields M b s as)
    (h' : Yields M b s' as') : Yields M b (s ++ s') (as ++ as') := by
  induction h with
  | nil => simpa using h'
  | step hn hb _ ih =>
    rw [List.cons_append, List.cons_append]
    exact Yields.step hn hb (by rw [← List.append_assoc]; exact ih)

/-- Two presentations of the same grid have the same refinements. -/
theorem gridYield_congr {M : TSM} {ls ls' : List (List (ℕ ⊕ ℕ))} {as : List ℕ}
    (h : TaskNetwork.grid ls = TaskNetwork.grid ls') :
    (semDom M).GridYield ls as ↔ (semDom M).GridYield ls' as :=
  exists_congr fun _ => gridYieldN_congr (semDom_grid M) h

/-- The refinements of the body of a transition: the action of the transition, then a
refinement of the chain of the pushed word. -/
theorem gridYield_bodyOf_iff {M : TSM} {n : ℕ} {ls : List (List (ℕ ⊕ ℕ))} {bs : List ℕ}
    (hgrid : TaskNetwork.grid ls = TaskNetwork.grid (bodyOf n (M.trAt n))) :
    (semDom M).GridYield ls bs ↔
      ∃ u, bs = n :: u ∧ (semDom M).ChainYield (stackChain (M.trAt n).stk (M.trAt n).push) u := by
  rw [gridYield_congr hgrid, bodyOf, gridYield_singleton_iff, chainYield_cons_inl_iff]

/-- **The chain of a stack refines exactly into the sequences that run the stack down.** -/
theorem chainYield_iff {M : TSM} {b : Bool} {s as : List ℕ} :
    (semDom M).ChainYield (stackChain b s) as ↔ Yields M b s as := by
  constructor
  · -- the hard direction: induction on the length of the action sequence
    suffices h : ∀ k : ℕ, ∀ (s as : List ℕ), as.length ≤ k →
        (semDom M).ChainYield (stackChain b s) as → Yields M b s as from
      fun hy => h as.length s as le_rfl hy
    intro k
    induction k with
    | zero =>
      intro s as hlen hy
      have has : as = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
      subst has
      -- an empty action sequence forces an empty stack
      cases s with
      | nil => exact Yields.nil
      | cons a s' =>
        rw [stackChain_cons, chainYield_cons_inr_iff] at hy
        obtain ⟨ls, bs, as', hbody, hgy, -, hnil⟩ := hy
        obtain ⟨n, -, -, hgrid⟩ := gridBody_semDom hbody
        obtain ⟨u, rfl, -⟩ := (gridYield_bodyOf_iff hgrid).1 hgy
        simp at hnil
    | succ k ih =>
      intro s as hlen hy
      cases as with
      | nil =>
        -- as above
        cases s with
        | nil => exact Yields.nil
        | cons a s' =>
          rw [stackChain_cons, chainYield_cons_inr_iff] at hy
          obtain ⟨ls, bs, as', hbody, hgy, -, hnil⟩ := hy
          obtain ⟨n, -, -, hgrid⟩ := gridBody_semDom hbody
          obtain ⟨u, rfl, -⟩ := (gridYield_bodyOf_iff hgrid).1 hgy
          simp at hnil
      | cons n₀ as'' =>
        cases s with
        | nil =>
          rw [stackChain_nil, chainYield_nil_iff] at hy
          exact absurd hy (by simp)
        | cons a s' =>
          rw [stackChain_cons, chainYield_cons_inr_iff] at hy
          obtain ⟨ls, bs, as', hbody, hgy, hrest, hcs⟩ := hy
          obtain ⟨n, hn, hname, hgrid⟩ := gridBody_semDom hbody
          obtain ⟨hstk, hpop⟩ := tskName_injective hname
          obtain ⟨u, rfl, hu⟩ := (gridYield_bodyOf_iff hgrid).1 hgy
          rw [List.cons_append, List.cons.injEq] at hcs
          obtain ⟨rfl, rfl⟩ := hcs
          subst hpop
          have hchain : (semDom M).ChainYield
              (stackChain b ((M.trAt n₀).push ++ s')) (u ++ as') := by
            rw [stackChain_append]
            refine chainYield_append_iff.2 ⟨u, as', rfl, ?_, hrest⟩
            rw [hstk]
            exact hu
          have hlen' : (u ++ as').length ≤ k := by
            simp only [List.length_cons, List.length_append] at hlen ⊢
            omega
          exact Yields.step hn hstk.symm (ih _ _ hlen' hchain)
  · intro hy
    induction hy with
    | nil => simp
    | @step n rest as hn hb hyr ih =>
      rw [stackChain_cons, chainYield_cons_inr_iff]
      rw [stackChain_append] at ih
      obtain ⟨u, v, rfl, hu, hv⟩ := chainYield_append_iff.1 ih
      refine ⟨bodyOf n (M.trAt n), n :: u, v, ?_, ?_, hv, rfl⟩
      · rw [← hb]
        exact gridBody_semDom_of_lt hn
      · rw [gridYield_bodyOf_iff rfl]
        exact ⟨u, rfl, by rw [hb]; exact hu⟩

/-- **The initial network refines exactly into the interleavings of two run-downs.** -/
theorem gridYield_iff {M : TSM} {s1 s2 : List ℕ} {as : List ℕ} :
    (semDom M).GridYield [stackChain false s1, stackChain true s2] as ↔
      ∃ y1 y2, Yields M false s1 y1 ∧ Yields M true s2 y2 ∧ Interleave y1 y2 as := by
  rw [gridYield_cons_iff]
  constructor
  · rintro ⟨y1, y2, h1, h2, hint⟩
    exact ⟨y1, y2, chainYield_iff.1 h1, chainYield_iff.1 (gridYield_singleton_iff.1 h2), hint⟩
  · rintro ⟨y1, y2, h1, h2, hint⟩
    exact ⟨y1, y2, chainYield_iff.2 h1, gridYield_singleton_iff.2 (chainYield_iff.2 h2), hint⟩

end Undec

end HTN
