import HtnComplexity.UODecide.Abstract
import ComplexityTheory.UOStream.WalkDec
/-!
# Unordered runs: decompositions first, then a walk of the state automaton

For an abstract unordered problem `S` (`HTN.UOAbs.Sys`):

* `HTN.UOStream.reach_decFirst` — every run is a sequence of decompositions (which do not depend
  on the state) followed by a sequence of executions; `reach_of_decFirst` is the converse.
* `HTN.UOStream.exeReach_iff_walk` — a sequence of executions that empties the multiset of open
  tasks is a walk of the state automaton (edge `s —a→ nxt s a` if `a` is applicable in `s`) whose
  label multiset is the multiset of open actions.
* `HTN.UOStream.decReach_chain` — for one-hole problems (every method body has at most one compound
  task), the decompositions from one compound task form a walk in the *method graph* (edge
  `some c —β→ (the compound task of β)`), and the primitive tasks they add are the sum of the
  primitive parts of the bodies.
-/

namespace HTN

namespace UOStream

open UOAbs

variable {S : Sys}

/-! ### Decompositions first -/

/-- Runs of decompositions only (they do not touch the state). -/
inductive DecReach (S : Sys) : Multiset (Bool × ℕ) → Multiset (Bool × ℕ) → Prop
  | refl (M : Multiset (Bool × ℕ)) : DecReach S M M
  | step {M M' : Multiset (Bool × ℕ)} {c : ℕ} {β : Multiset (Bool × ℕ)} :
      (true, c) ∈ M → S.meth c β → DecReach S (M.erase (true, c) + β) M' → DecReach S M M'

/-- Runs of executions only. -/
inductive ExeReach (S : Sys) : Cfg → Cfg → Prop
  | refl (x : Cfg) : ExeReach S x x
  | step {s : Finset ℕ} {M : Multiset (Bool × ℕ)} {a : ℕ} {y : Cfg} :
      (false, a) ∈ M → S.app s a → ExeReach S (S.nxt s a, M.erase (false, a)) y →
        ExeReach S (s, M) y

theorem decReach_add {M M' : Multiset (Bool × ℕ)} (h : DecReach S M M') (X : Multiset (Bool × ℕ)) :
    DecReach S (M + X) (M' + X) := by
  induction h with
  | refl M => exact .refl _
  | @step M M' c β hc hm _ ih =>
    refine .step (Multiset.mem_add.2 (Or.inl hc)) hm ?_
    rw [Multiset.erase_add_left_pos _ hc, add_right_comm]
    exact ih

theorem decReach_trans {M M' M'' : Multiset (Bool × ℕ)} (h : DecReach S M M')
    (h' : DecReach S M' M'') : DecReach S M M'' := by
  induction h with
  | refl => exact h'
  | step hc hm _ ih => exact .step hc hm (ih h')

/-- **Decompositions first.** -/
theorem reach_decFirst {n : ℕ} {x y : Cfg} (h : ReachIn S n x y) :
    ∃ M', DecReach S x.2 M' ∧ ExeReach S (x.1, M') y := by
  induction h with
  | refl x => exact ⟨x.2, .refl _, .refl _⟩
  | @step n x x₁ z hs _ ih =>
    obtain ⟨M', hd, he⟩ := ih
    cases hs with
    | dec s M c β hc hm => exact ⟨M', .step hc hm hd, he⟩
    | exe s M a ha happ =>
      refine ⟨M' + {(false, a)}, ?_, ?_⟩
      · have e : M.erase (false, a) + {(false, a)} = M := by
          rw [add_comm, Multiset.singleton_add, Multiset.cons_erase ha]
        have := decReach_add hd {(false, a)}
        rwa [e] at this
      · refine .step (Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self _))) happ ?_
        rw [Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self _), Multiset.erase_singleton,
          add_zero]
        exact he

theorem reachIn_trans' {n m : ℕ} {x y z : Cfg} (h₁ : ReachIn S n x y) (h₂ : ReachIn S m y z) :
    ReachIn S (n + m) x z := by
  induction h₁ with
  | refl => simpa using h₂
  | @step n x y z hs _ ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    exact ReachIn.step hs (ih h₂)

theorem exeReach_reach {x y : Cfg} (h : ExeReach S x y) : ∃ n, ReachIn S n x y := by
  induction h with
  | refl x => exact ⟨0, .refl x⟩
  | step ha happ _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step (.exe _ _ _ ha happ) hn⟩

theorem decReach_reach {s : Finset ℕ} {M M' : Multiset (Bool × ℕ)} (h : DecReach S M M') :
    ∃ n, ReachIn S n (s, M) (s, M') := by
  induction h with
  | refl M => exact ⟨0, .refl _⟩
  | step hc hm _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step (.dec _ _ _ _ hc hm) hn⟩

/-- **The converse**: decompositions followed by executions are a run. -/
theorem reach_of_decFirst {s : Finset ℕ} {M M' : Multiset (Bool × ℕ)} {y : Cfg}
    (hd : DecReach S M M') (he : ExeReach S (s, M') y) : ∃ n, ReachIn S n (s, M) y := by
  obtain ⟨n₁, h₁⟩ := decReach_reach (s := s) hd
  obtain ⟨n₂, h₂⟩ := exeReach_reach he
  exact ⟨n₁ + n₂, reachIn_trans' h₁ h₂⟩

/-- Executions do not touch compound tasks. -/
theorem exeReach_count_comp {x y : Cfg} (h : ExeReach S x y) (c : ℕ) :
    x.2.count (true, c) = y.2.count (true, c) := by
  induction h with
  | refl => rfl
  | @step s M a y ha happ _ ih =>
    rw [← ih, Multiset.count_erase_of_ne (by simp)]

/-! ### Executions are walks of the state automaton -/

/-- The state automaton: an edge `s —a→ nxt s a` for every action `a` applicable in `s`. -/
def stR (S : Sys) (s : Finset ℕ) (a : ℕ) (s' : Finset ℕ) : Prop := S.app s a ∧ s' = S.nxt s a

/-- The open actions of a label multiset of actions. -/
def acts (P : Multiset ℕ) : Multiset (Bool × ℕ) := P.map fun a => (false, a)

theorem exeReach_walk_aux {x y : Cfg} (h : ExeReach S x y) :
    y.2 = 0 → ∃ w, IsWalk (stR S) x.1 w y.1 ∧ x.2 = acts (par w) := by
  induction h with
  | refl x => intro h0; exact ⟨[], .nil _, by simp [acts, par, h0]⟩
  | @step s M a y ha happ _ ih =>
    intro h0
    obtain ⟨w, hw, hM⟩ := ih h0
    refine ⟨(a, S.nxt s a) :: w, .cons ⟨happ, rfl⟩ hw, ?_⟩
    simp only [acts, par, List.map_cons] at hM ⊢
    rw [← Multiset.cons_coe, Multiset.map_cons, ← hM, Multiset.cons_erase ha]

theorem exeReach_iff_walk {s s' : Finset ℕ} {M : Multiset (Bool × ℕ)} :
    ExeReach S (s, M) (s', 0) ↔ ∃ w, IsWalk (stR S) s w s' ∧ M = acts (par w) := by
  constructor
  · intro h
    exact exeReach_walk_aux h rfl
  · rintro ⟨w, hw, rfl⟩
    induction hw with
    | nil => exact .refl _
    | @cons s u t a w hR _ ih =>
      obtain ⟨happ, rfl⟩ := hR
      refine .step (by simp [acts, par]) happ ?_
      have : (acts (par ((a, S.nxt s a) :: w))).erase (false, a) = acts (par w) := by
        simp [acts, par]
      rw [this]
      exact ih

/-! ### Decompositions of a one-hole problem are walks of the method graph -/

/-- The compound task of a body, if any. -/
noncomputable def holeOf (β : Multiset (Bool × ℕ)) : Option ℕ := by
  classical
  exact if h : ∃ c, (true, c) ∈ β then some (Classical.choose h) else none

/-- The primitive part of a body. -/
def primOf (β : Multiset (Bool × ℕ)) : Multiset (Bool × ℕ) := β.filter fun l => l.1 = false

/-- The method graph: an edge `some c —β→ holeOf β` for every method `c ↦ β`. -/
def methR (S : Sys) (u : Option ℕ) (β : Multiset (Bool × ℕ)) (u' : Option ℕ) : Prop :=
  ∃ c, u = some c ∧ S.meth c β ∧ u' = holeOf β

/-- A one-hole multiset: at most one compound task. -/
def OneHoleMS (β : Multiset (Bool × ℕ)) : Prop :=
  ∀ c₁ c₂, (true, c₁) ∈ β → (true, c₂) ∈ β → c₁ = c₂ ∧ β.count (true, c₁) = 1

/-- One-hole bodies. -/
def OneHole (S : Sys) : Prop := ∀ c β, S.meth c β → OneHoleMS β

/-- A multiset with exactly the compound task `u` (none if `u = none`) on top of the primitive
multiset `P`. -/
def withHole (P : Multiset (Bool × ℕ)) : Option ℕ → Multiset (Bool × ℕ)
  | none => P
  | some c => (true, c) ::ₘ P

/-- Primitive multisets. -/
def Prim (P : Multiset (Bool × ℕ)) : Prop := ∀ l ∈ P, l.1 = false

theorem ms_split {β : Multiset (Bool × ℕ)} (hβ : OneHoleMS β) :
    β = withHole (primOf β) (holeOf β) := by
  classical
  unfold holeOf
  split_ifs with h
  · have hc := Classical.choose_spec h
    set c' := Classical.choose h
    simp only [withHole, primOf]
    ext l
    obtain ⟨b, x⟩ := l
    rw [Multiset.count_cons, Multiset.count_filter]
    cases b with
    | false => simp
    | true =>
      simp only [Bool.true_eq_false, if_false, zero_add, Prod.mk.injEq, true_and]
      split_ifs with hx
      · subst hx; exact (hβ _ _ hc hc).2
      · rw [Multiset.count_eq_zero]
        intro hmem
        exact hx (hβ _ _ hmem hc).1
  · simp only [withHole, primOf]
    ext l
    obtain ⟨b, x⟩ := l
    rw [Multiset.count_filter]
    cases b with
    | false => simp
    | true =>
      simp only [Bool.true_eq_false, if_false]
      rw [Multiset.count_eq_zero]
      exact fun hmem => h ⟨x, hmem⟩

theorem prim_primOf (β : Multiset (Bool × ℕ)) : Prim (primOf β) := fun l hl =>
  (Multiset.mem_filter.1 hl).2

/-- The primitive tasks added along a walk of the method graph. -/
def addedP (w : List (Multiset (Bool × ℕ) × Option ℕ)) : Multiset (Bool × ℕ) :=
  (w.map fun p => primOf p.1).sum

theorem prim_withHole_none {P : Multiset (Bool × ℕ)} (h : Prim P) {c : ℕ} :
    (true, c) ∉ P := fun hm => by simpa using h _ hm

theorem withHole_step (hS : OneHole S) {c : ℕ} {β P : Multiset (Bool × ℕ)} (hm : S.meth c β) :
    (withHole P (some c)).erase (true, c) + β = withHole (P + primOf β) (holeOf β) := by
  have hsplit := ms_split (hS c β hm)
  simp only [withHole, Multiset.erase_cons_head]
  conv_lhs => rw [hsplit]
  cases holeOf β with
  | none => simp [withHole]
  | some c' => simp [withHole]

theorem prim_add {P Q : Multiset (Bool × ℕ)} (hP : Prim P) (hQ : Prim Q) : Prim (P + Q) :=
  fun l hl => (Multiset.mem_add.1 hl).elim (hP l) (hQ l)

theorem chain_rev (hS : OneHole S) : ∀ (w : List (Multiset (Bool × ℕ) × Option ℕ)) (u : Option ℕ)
    {P : Multiset (Bool × ℕ)}, IsWalk (methR S) u w none → Prim P →
      DecReach S (withHole P u) (P + addedP w)
  | [], u, P, hw, _ => by cases hw; simp [withHole, addedP]; exact .refl _
  | (β, u') :: w, u, P, hw, hP => by
    cases hw with
    | cons hR hrest =>
      obtain ⟨c, rfl, hm, rfl⟩ := hR
      refine .step (Multiset.mem_cons_self _ _) hm ?_
      rw [withHole_step hS hm]
      have := chain_rev hS w _ hrest (prim_add hP (prim_primOf β))
      simpa [addedP, add_assoc] using this

/-- **Decompositions of a one-hole multiset are a walk of the method graph.** -/
theorem decReach_chain (hS : OneHole S) {P M' : Multiset (Bool × ℕ)} (hP : Prim P) (u : Option ℕ)
    (hM' : Prim M') :
    DecReach S (withHole P u) M' ↔
      ∃ w, IsWalk (methR S) u w none ∧ M' = P + addedP w := by
  constructor
  · intro h
    generalize hx : withHole P u = M at h
    induction h generalizing P u with
    | refl M =>
      subst hx
      cases u with
      | none => exact ⟨[], .nil _, by simp [withHole, addedP]⟩
      | some c => exact absurd (hM' _ (Multiset.mem_cons_self _ _)) (by simp)
    | @step M M'' c β hc hm _ ih =>
      subst hx
      cases u with
      | none => exact absurd hc (prim_withHole_none hP)
      | some c₀ =>
        have hcc : c = c₀ := by
          rcases Multiset.mem_cons.1 hc with h | h
          · simpa using h
          · exact absurd h (prim_withHole_none hP)
        subst hcc
        have he := withHole_step (P := P) hS hm
        obtain ⟨w, hw, hM⟩ := ih (P := P + primOf β) (u := holeOf β)
          (fun l hl => by
            rcases Multiset.mem_add.1 hl with hl | hl
            · exact hP l hl
            · exact prim_primOf β l hl) hM' he.symm
        refine ⟨(β, holeOf β) :: w, .cons ⟨c, rfl, hm, rfl⟩ hw, ?_⟩
        rw [hM]; simp [addedP, add_assoc]
  · rintro ⟨w, hw, rfl⟩
    exact chain_rev hS w u hw hP

end UOStream

end HTN
