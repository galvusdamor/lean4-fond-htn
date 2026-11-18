import ComplexityTheory.Undec.Sim.Defs
/-!
# The transitions of the simulating machine, indexed by their source state

The transition list of `HTN.Undec.Sim.simTSM` is assembled from the per-state lists
`HTN.Undec.Sim.trsOf`.  Every transition of `trsOf s` has source `stCode S s`, and `stCode` is
injective on the states that really occur (`HTN.Undec.Sim.allSt`).  Hence a transition of the
machine whose source is `stCode S s` belongs to `trsOf s` — which is what turns a step of the
machine into a case distinction over the finitely many transitions of one state.
-/

namespace HTN

namespace Undec

namespace Sim

open Turing

open scoped Classical

variable {Γ : Type*} [Inhabited Γ] [Fintype Γ] {Λ : Type*} [Inhabited Λ]
variable {N : TM0.Machine Γ Λ} {S : Finset Λ} {q0 : Λ}

/-- The states that occur in `allSt`: those whose control state is listed in `S`. -/
def StOk (S : Finset Λ) : St Γ Λ → Prop
  | .run q _ => q ∈ S
  | .pl q _ _ => q ∈ S
  | .pr q _ _ => q ∈ S
  | _ => True

theorem mem_allSt {s : St Γ Λ} (h : StOk S s) : s ∈ allSt S := by
  cases s with
  | start => simp [allSt]
  | flush1 => simp [allSt]
  | flush2 => simp [allSt]
  | acc => simp [allSt]
  | run q a =>
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      refine List.mem_flatMap.2 ⟨q, Finset.mem_toList.2 h, ?_⟩
      exact List.mem_map_of_mem (mem_symList a)
  | pl q y b =>
      refine List.mem_append_right _ ?_
      refine List.mem_flatMap.2 ⟨q, Finset.mem_toList.2 h, ?_⟩
      refine List.mem_flatMap.2 ⟨y, mem_symList y, ?_⟩
      refine List.mem_flatMap.2 ⟨b, mem_symList b, ?_⟩
      simp
  | pr q y b =>
      refine List.mem_append_right _ ?_
      refine List.mem_flatMap.2 ⟨q, Finset.mem_toList.2 h, ?_⟩
      refine List.mem_flatMap.2 ⟨y, mem_symList y, ?_⟩
      refine List.mem_flatMap.2 ⟨b, mem_symList b, ?_⟩
      simp

omit [Inhabited Γ] [Inhabited Λ] in
theorem stOk_of_mem_allSt {s : St Γ Λ} (h : s ∈ allSt S) : StOk S s := by
  simp only [allSt, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false, Finset.mem_toList] at h
  rcases h with (h | ⟨q, hq, a, -, rfl⟩) | ⟨q, hq, y, -, b, -, hs⟩
  · rcases h with rfl | rfl | rfl | rfl <;> trivial
  · exact hq
  · rcases hs with rfl | rfl <;> exact hq

/-! ### Injectivity of the state codes -/

omit [Inhabited Γ] [Inhabited Λ] in
theorem stCode_ne_of_ne {s s' : St Γ Λ} (hs : StOk S s) (hs' : StOk S s')
    (h : stCode S s = stCode S s') : s = s' := by
  cases s <;> cases s' <;>
    simp_all [stCode, Nat.pair_eq_pair, symCode_ne_zero, StOk] <;>
    first
      | omega
      | (first
          | (obtain ⟨h1, h2, h3⟩ := h
             exact ⟨stIdx_inj hs hs' h1, symCode_injective h2, symCode_injective h3⟩)
          | (obtain ⟨h1, h2⟩ := h
             exact ⟨stIdx_inj hs hs' h1, symCode_injective h2⟩))

/-! ### Sources -/

theorem src_of_mem_trsOf {s : St Γ Λ} {t : Tr} (h : t ∈ trsOf N S q0 s) :
    t.src = stCode S s := by
  cases s with
  | start =>
      simp only [trsOf, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨c, -, rfl⟩ <;> rfl
  | flush1 =>
      simp only [trsOf, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨c, -, rfl⟩ <;> rfl
  | flush2 =>
      simp only [trsOf, List.mem_cons, List.mem_map] at h
      rcases h with rfl | ⟨c, -, rfl⟩ <;> rfl
  | acc => simp [trsOf] at h
  | run q a =>
      rw [trsOf] at h
      match hN : N q a with
      | none =>
          rw [hN] at h
          obtain ⟨s, -, rfl⟩ := List.mem_map.1 h; rfl
      | some (q', TM0.Stmt.write b) =>
          rw [hN] at h
          obtain ⟨s, -, rfl⟩ := List.mem_map.1 h; rfl
      | some (q', TM0.Stmt.move Dir.right) =>
          rw [hN] at h
          simp only [List.mem_cons, List.mem_map] at h
          rcases h with rfl | ⟨c, -, rfl⟩ <;> rfl
      | some (q', TM0.Stmt.move Dir.left) =>
          rw [hN] at h
          simp only [List.mem_cons, List.mem_map] at h
          rcases h with rfl | ⟨c, -, rfl⟩ <;> rfl
  | pl q y b =>
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 h; rfl
  | pr q y b =>
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 h; rfl

/-! ### Membership in the transition list of the machine -/

theorem mem_trans {s : St Γ Λ} {t : Tr} (hs : StOk S s) (ht : t ∈ trsOf N S q0 s) :
    t ∈ (simTSM N S q0).trans :=
  List.mem_flatMap.2 ⟨s, mem_allSt hs, ht⟩

/-- **The transitions of the machine, read off by source state.** -/
theorem mem_trsOf_of_mem_trans {s : St Γ Λ} {t : Tr} (hs : StOk S s)
    (ht : t ∈ (simTSM N S q0).trans) (hsrc : t.src = stCode S s) :
    t ∈ trsOf N S q0 s := by
  obtain ⟨s', hs', ht'⟩ := List.mem_flatMap.1 ht
  have h1 : t.src = stCode S s' := src_of_mem_trsOf ht'
  have : s' = s := stCode_ne_of_ne (stOk_of_mem_allSt hs') hs (h1.symm.trans hsrc)
  exact this ▸ ht'

end Sim

end Undec

end HTN
