import HtnComplexity.Complexity.ChainDesc
import HtnComplexity.Undec.Correct
/-!
# The two-stack machine encoding with identifiers a recursion can write

`HtnComplexity/Undec/Encoding.lean` encodes a two-stack machine `M` as a *fixed* domain
description `HTN.Undec.tsmDom M` together with an instance description
`HTN.Undec.tsmInst M s₁ s₂` carrying the two initial stacks, and
`HTN.Undec.solvable_tsm_iff` proves that the described problem is solvable exactly when `M`
halts.  This is the shape of the hardness families of the literature: the machine sits in the
domain, the input sits in the instance.

The instance description of that encoding cannot be written down in polynomial time, though:
it names the `j`-th task of the chain of a stack `Nat.pair 0 j`, and the binary numeral of
`Nat.pair 0 j` is `j²`, whose computation needs binary multiplication — see the discussion in
`HtnComplexity/Complexity/ChainDesc.lean`.

This file replaces those identifiers by ones a counting recursion produces: the `j`-th task of a
chain of `k` tasks is named `k - 1 - j`, the number of tasks that *follow* it.  A recursion on
the input word has that number in its hand at every step — it is the length of the remaining
word — so the description becomes writable in Cobham's class
(`HtnCompilability/Complexity/MachineFamily.lean`).

* `HTN.Syn.chainDown` — the chain description with the downward naming;
* `HTN.Syn.chainDown_iso_gridDesc` — it denotes the same network as the grid description of the
  same row, up to isomorphism;
* `HTN.Undec.stackInst` — the instance description of the encoding with the downward naming,
  for a first stack and an empty second one, and
  `HTN.Undec.solvable_stackInst_iff` — it is solvable exactly when `M` halts on that stack.
-/

namespace HTN

namespace Syn

/-! ### The chain with the downward naming -/

/-- **The chain description with the downward naming**: the `j`-th of the `k` tasks is named
`k - 1 - j`, the number of tasks that follow it. -/
def chainDown (row : List (Bool × ℕ)) : TnDesc := chainOn (fun j => row.length - 1 - j) row

/-- The renaming that turns the downward naming into the naming of a grid description. -/
def downToPair (k : ℕ) : ℕ → ℕ := fun j => Nat.pair 0 (k - 1 - j)

theorem chainDown_mapIds (row : List (Bool × ℕ)) :
    (chainDown row).mapIds (downToPair row.length) = chainOn (Nat.pair 0) row := by
  rw [chainDown, chainOn_mapIds]
  refine chainOn_congr fun j hj => ?_
  simp only [Function.comp_apply, downToPair]
  congr 1
  omega

theorem injOn_downToPair (row : List (Bool × ℕ)) :
    Set.InjOn (downToPair row.length) {x | x ∈ (chainDown row).ids} := by
  intro x hx y hy hxy
  simp only [chainDown, chainOn_ids, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  simp only [downToPair] at hxy
  have := (Nat.pair_eq_pair.1 hxy).2
  omega

/-- **The downward naming denotes the same task network as the naming of a grid**, up to
isomorphism. -/
theorem chainDown_iso_chainOn_pair (row : List (Bool × ℕ)) :
    (chainDown row).toTaskNetwork.Iso (chainOn (Nat.pair 0) row).toTaskNetwork := by
  have h := TnDesc.mapIds_iso (f := downToPair row.length) (t := chainDown row)
    (by simpa [chainDown] using chainOn_ordList_mem (g := fun j => row.length - 1 - j) (row := row))
    (by simpa [chainDown] using chainOn_lbl_mem (g := fun j => row.length - 1 - j) (row := row))
    (injOn_downToPair row)
  rwa [chainDown_mapIds] at h

/-- The same, against the grid description of a row followed by an empty row. -/
theorem chainDown_iso_gridDesc (row : List (Bool × ℕ)) :
    (chainDown row).toTaskNetwork.Iso (gridDesc [row, []]).toTaskNetwork := by
  rw [gridDesc_pair_nil_eq_chainOn]
  exact chainDown_iso_chainOn_pair row

/-! ### A chain preceded by an isolated task, named downwards -/

/-- **The isolated task together with the chain, named downwards**: the `j`-th of the `k` tasks
of the chain is named `k - 1 - j` and the isolated task is named `k`, a name no task of the
chain carries. -/
def chainDownWith (t : Bool × ℕ) (row : List (Bool × ℕ)) : TnDesc :=
  chainWith row.length t (fun j => row.length - 1 - j) row

/-- The renaming that turns the downward naming of `HTN.Syn.chainDownWith` into the naming of a
grid description. -/
def downToPairWith (k : ℕ) : ℕ → ℕ :=
  fun j => if j = k then Nat.pair 0 0 else Nat.pair 1 (k - 1 - j)

theorem chainDownWith_mapIds (t : Bool × ℕ) (row : List (Bool × ℕ)) :
    (chainDownWith t row).mapIds (downToPairWith row.length)
      = chainWith (Nat.pair 0 0) t (Nat.pair 1) row := by
  rw [chainDownWith, chainWith_mapIds]
  have hh : downToPairWith row.length row.length = Nat.pair 0 0 := by
    simp [downToPairWith]
  rw [hh]
  refine chainWith_congr fun j hj => ?_
  have hne : row.length - 1 - j ≠ row.length := by omega
  simp only [Function.comp_apply, downToPairWith, if_neg hne]
  congr 1
  omega

theorem injOn_downToPairWith (t : Bool × ℕ) (row : List (Bool × ℕ)) :
    Set.InjOn (downToPairWith row.length) {x | x ∈ (chainDownWith t row).ids} := by
  have hmem : ∀ x ∈ (chainDownWith t row).ids, x = row.length ∨ x < row.length := by
    intro x hx
    simp only [chainDownWith, chainWith_ids, List.mem_cons, List.mem_map, List.mem_range] at hx
    rcases hx with rfl | ⟨j, hj, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (by omega)
  have hne : ∀ m : ℕ, Nat.pair 1 m ≠ Nat.pair 0 0 := by
    intro m h
    exact absurd (Nat.pair_eq_pair.1 h).1 (by omega)
  intro x hx y hy hxy
  rcases hmem x hx with rfl | hx' <;> rcases hmem y hy with rfl | hy'
  · rfl
  · rw [downToPairWith, downToPairWith, if_pos rfl, if_neg (by omega)] at hxy
    exact absurd hxy.symm (hne _)
  · rw [downToPairWith, downToPairWith, if_neg (by omega), if_pos rfl] at hxy
    exact absurd hxy (hne _)
  · rw [downToPairWith, downToPairWith, if_neg (by omega), if_neg (by omega)] at hxy
    have := (Nat.pair_eq_pair.1 hxy).2
    omega

/-- **The downward naming denotes the same network as the naming of a grid**, up to
isomorphism. -/
theorem chainDownWith_iso_gridDesc (t : Bool × ℕ) (row : List (Bool × ℕ)) :
    (chainDownWith t row).toTaskNetwork.Iso (gridDesc [[t], row]).toTaskNetwork := by
  have hord : ∀ p ∈ (chainDownWith t row).ordList,
      p.1 ∈ (chainDownWith t row).ids ∧ p.2 ∈ (chainDownWith t row).ids :=
    chainWith_ordList_mem
  have hlbl : ∀ l ∈ (chainDownWith t row).lbl, l.1 ∈ (chainDownWith t row).ids :=
    chainWith_lbl_mem
  have h := TnDesc.mapIds_iso (f := downToPairWith row.length) (t := chainDownWith t row)
    hord hlbl (injOn_downToPairWith t row)
  rw [chainDownWith_mapIds] at h
  rw [gridDesc_single_cons_eq_chainWith]
  exact h

end Syn

namespace Undec

open Syn

/-! ### The instance of the two-stack encoding, renamed -/

/-- The row of labels of the chain of the first stack: the compound task of each symbol. -/
def stackRow (s : List ℕ) : List (Bool × ℕ) := s.map fun a => (true, tskName false a)

theorem gridDescOf_stack_eq (s : List ℕ) :
    gridDescOf id id [stackChain false s, stackChain true []] = gridDesc [stackRow s, []] := by
  simp [gridDescOf, stackChain, stackRow, encLabel, List.map_map, Function.comp_def]

/-- The row of labels of the chain of the second stack: the compound task of each symbol. -/
def stackRow2 (s : List ℕ) : List (Bool × ℕ) := s.map fun a => (true, tskName true a)

theorem gridDescOf_stack2_eq (z : ℕ) (s : List ℕ) :
    gridDescOf id id [stackChain false [z], stackChain true s]
      = gridDesc [[(true, tskName false z)], stackRow2 s] := by
  simp [gridDescOf, stackChain, stackRow2, encLabel, List.map_map, Function.comp_def]

/-- **The instance description of the two-stack encoding with the downward naming**, for a
one-symbol first stack and the word on the second: the first stack is the single symbol `z`, the
second is `s`.  A nonempty first stack is what makes the device two-stack — a machine started
with an empty stack can never push onto it, so it is only a pushdown automaton. -/
def stackInstTwo (M : TSM) (z : ℕ) (s : List ℕ) : InstDesc :=
  ([M.start], [M.acc], chainDownWith (true, tskName false z) (stackRow2 s))

/-- **The renamed two-stack instance describes the same problem**: it is solvable exactly when
the machine halts from the stacks `[z]` and `s`. -/
theorem solvable_stackInstTwo_iff (M : TSM) (z : ℕ) (s : List ℕ) :
    Syn.Solvable (tsmDom M) (stackInstTwo M z s) ↔ M.Halts [z] s := by
  have hiso : (chainDownWith (true, tskName false z) (stackRow2 s)).toTaskNetwork.Iso
      (gridDescOf id id [stackChain false [z], stackChain true s]).toTaskNetwork := by
    rw [gridDescOf_stack2_eq]
    exact chainDownWith_iso_gridDesc _ _
  have h := Syn.solvable_congr_tnI_iso (tsmDom M) [M.start] [M.acc]
    (chainDownWith (true, tskName false z) (stackRow2 s))
    (gridDescOf id id [stackChain false [z], stackChain true s]) hiso
  rw [stackInstTwo, h]
  exact solvable_tsm_iff M [z] s

/-- **The instance description of the two-stack encoding with the downward naming**: the first
stack is `s`, the second is empty. -/
def stackInst (M : TSM) (s : List ℕ) : InstDesc := ([M.start], [M.acc], chainDown (stackRow s))

/-- **The renamed instance describes the same problem**: it is solvable exactly when the machine
halts on the stack `s` with an empty second stack. -/
theorem solvable_stackInst_iff (M : TSM) (s : List ℕ) :
    Syn.Solvable (tsmDom M) (stackInst M s) ↔ M.Halts s [] := by
  have hiso : (chainDown (stackRow s)).toTaskNetwork.Iso
      (gridDescOf id id [stackChain false s, stackChain true []]).toTaskNetwork := by
    rw [gridDescOf_stack_eq]
    exact chainDown_iso_gridDesc (stackRow s)
  have h := Syn.solvable_congr_tnI_iso (tsmDom M) [M.start] [M.acc]
    (chainDown (stackRow s)) (gridDescOf id id [stackChain false s, stackChain true []]) hiso
  rw [stackInst]
  rw [h]
  exact solvable_tsm_iff M s []

end Undec

end HTN
