import ComplexityTheory.UODecide.ZeroSum
import ComplexityTheory.UODecide.Tree
/-!
# Unordered HTN planning, abstractly: a bound on the length of a shortest solution

In an unordered problem a search configuration is determined by the current state and the
*multiset* of open task labels.  This file works with that abstraction:

* `HTN.UOAbs.Sys` — an abstract unordered problem: which multisets a compound name may be
  decomposed into, and STRIPS-like transitions on finite sets of facts;
* `HTN.UOAbs.Step`, `HTN.UOAbs.ReachIn` — the progression search on configurations
  `(state, multiset of labels)` and runs of a given length;
* `HTN.UOAbs.short_run` — **the small-solution theorem**: if a goal configuration is reachable,
  it is reachable in at most `uoBound k |Acts| M` steps, where `k` bounds the number of compound
  names plus the number of states, `Acts` is the set of relevant actions and `M` bounds the
  size of a method body and of the initial network.

The proof encodes a solution as a derivation tree of a commutative grammar (a forest for the
hierarchy, a path for the execution, both under a fresh root), with leaves `prim a` (an action
the hierarchy produced) and `act a` (an action the execution consumed), balanced in the sense
that both occur equally often (`vec … = 0`).  The label-preserving decomposition of
`ComplexityTheory/UODecide/Tree.lean` writes the tree as a small base tree plus small pumps;
the zero-sum lemma of `ComplexityTheory/UODecide/ZeroSum.lean` selects a bounded number of
pumps that restores the balance; inserting them gives a small balanced tree, i.e. a short
solution.
-/

namespace HTN

namespace UOAbs

open CTree

/-- **An abstract unordered HTN problem.** -/
structure Sys where
  /-- `meth c β`: the compound name `c` may be decomposed into the multiset of labels `β`. -/
  meth : ℕ → Multiset (Bool × ℕ) → Prop
  /-- `app s a`: the action `a` is applicable in the state `s`. -/
  app : Finset ℕ → ℕ → Prop
  /-- `nxt s a`: the state after applying `a` in `s`. -/
  nxt : Finset ℕ → ℕ → Finset ℕ
  /-- `goal s`: the state `s` satisfies the goal. -/
  goal : Finset ℕ → Prop

/-- A configuration: the state and the multiset of open task labels (`(true, c)` a compound
name, `(false, a)` an action). -/
abbrev Cfg : Type := Finset ℕ × Multiset (Bool × ℕ)

/-- One step of the progression search of an unordered problem. -/
inductive Step (S : Sys) : Cfg → Cfg → Prop
  | dec (s : Finset ℕ) (M : Multiset (Bool × ℕ)) (c : ℕ) (β : Multiset (Bool × ℕ)) :
      (true, c) ∈ M → S.meth c β → Step S (s, M) (s, M.erase (true, c) + β)
  | exe (s : Finset ℕ) (M : Multiset (Bool × ℕ)) (a : ℕ) :
      (false, a) ∈ M → S.app s a → Step S (s, M) (S.nxt s a, M.erase (false, a))

/-- Goal configurations. -/
def IsGoal (S : Sys) (x : Cfg) : Prop := x.2 = 0 ∧ S.goal x.1

/-- Runs of a given length. -/
inductive ReachIn (S : Sys) : ℕ → Cfg → Cfg → Prop
  | refl (x : Cfg) : ReachIn S 0 x x
  | step {n : ℕ} {x y z : Cfg} : Step S x y → ReachIn S n y z → ReachIn S (n + 1) x z

/-! ### The grammar of solutions -/

/-- Nonterminals: the fresh root, compound names, states. -/
inductive NT where
  | top : NT
  | comp (c : ℕ) : NT
  | st (s : Finset ℕ) : NT
  deriving DecidableEq

/-- Terminals: an action produced by the hierarchy, an action consumed by the execution. -/
inductive TT where
  | prim (a : ℕ) : TT
  | act (a : ℕ) : TT
  deriving DecidableEq

/-- The name of a terminal. -/
def TT.name : TT → ℕ
  | prim a => a
  | act a => a

/-- The grammar symbol of a task label. -/
def sym : Bool × ℕ → NT ⊕ TT
  | (true, c) => Sum.inl (NT.comp c)
  | (false, a) => Sum.inr (TT.prim a)

theorem sym_injective : Function.Injective sym := by
  rintro ⟨b₁, n₁⟩ ⟨b₂, n₂⟩ h
  cases b₁ <;> cases b₂ <;> simp_all [sym]

/-- **The grammar of solutions** of the problem with initial state `s₀` and initial labels `I`:
the root derives the initial labels and the initial state; a compound name derives the bodies
of its methods; a state derives an applicable relevant action and the successor state, or
nothing if it satisfies the goal. -/
def G (S : Sys) (s₀ : Finset ℕ) (I : Multiset (Bool × ℕ)) (Acts : Finset ℕ) :
    NT → Multiset (NT ⊕ TT) → Prop
  | NT.top, β => β = I.map sym + {Sum.inl (NT.st s₀)}
  | NT.comp c, β => ∃ β', S.meth c β' ∧ β = β'.map sym
  | NT.st s, β => (∃ a ∈ Acts, S.app s a ∧
      β = {Sum.inr (TT.act a), Sum.inl (NT.st (S.nxt s a))}) ∨ (S.goal s ∧ β = 0)

/-- The balance vector: how many more times an action was produced than consumed. -/
def vec (y : Multiset TT) (a : ℕ) : ℤ := (y.count (TT.prim a) : ℤ) - y.count (TT.act a)

@[simp] theorem vec_zero : vec 0 = 0 := by funext a; simp [vec]

theorem vec_add (y z : Multiset TT) : vec (y + z) = vec y + vec z := by
  funext a
  simp only [vec, Multiset.count_add, Pi.add_apply]
  push_cast
  ring

theorem vec_list_sum {α : Type*} (f : α → Multiset TT) :
    ∀ l : List α, vec (l.map f).sum = (l.map (fun x => vec (f x))).sum
  | [] => by simp
  | x :: l => by simp [vec_add, vec_list_sum f l]

theorem vec_multiset_sum {α : Type*} (f : α → Multiset TT) (U : Multiset α) :
    vec (U.map f).sum = (U.map (fun x => vec (f x))).sum := by
  induction U using Multiset.induction_on with
  | empty => simp
  | cons x U ih => simp [vec_add, ih]

theorem abs_vec_le (y : Multiset TT) (a : ℕ) : |vec y a| ≤ (Multiset.card y : ℤ) := by
  have h1 : y.count (TT.prim a) ≤ Multiset.card y := Multiset.count_le_card _ _
  have h2 : y.count (TT.act a) ≤ Multiset.card y := Multiset.count_le_card _ _
  simp only [vec, abs_le]
  constructor <;> omega

theorem vec_eq_zero_of_names {y : Multiset TT} {Acts : Finset ℕ}
    (h : ∀ x ∈ y, x.name ∈ Acts) {a : ℕ} (ha : a ∉ Acts) : vec y a = 0 := by
  have h1 : y.count (TT.prim a) = 0 :=
    Multiset.count_eq_zero.2 (fun hm => ha (h _ hm))
  have h2 : y.count (TT.act a) = 0 :=
    Multiset.count_eq_zero.2 (fun hm => ha (h _ hm))
  simp [vec, h1, h2]

/-- Labels whose compound names lie in `Comps` and whose actions lie in `Acts`. -/
def LabOK (Comps Acts : Finset ℕ) (M : Multiset (Bool × ℕ)) : Prop :=
  ∀ x ∈ M, (x.1 = true → x.2 ∈ Comps) ∧ (x.1 = false → x.2 ∈ Acts)

/-- The finiteness data of an abstract problem. -/
structure Closed (S : Sys) (Comps Acts F : Finset ℕ) (Mb : ℕ) : Prop where
  meth_lab : ∀ c β, S.meth c β → LabOK Comps Acts β
  meth_card : ∀ c β, S.meth c β → Multiset.card β ≤ Mb
  nxt_sub : ∀ s a, s ⊆ F → S.nxt s a ⊆ F

variable {S : Sys} {s₀ : Finset ℕ} {I : Multiset (Bool × ℕ)} {Acts : Finset ℕ}

theorem labOK_erase_add {Comps : Finset ℕ} {M β : Multiset (Bool × ℕ)} {x : Bool × ℕ}
    (hM : LabOK Comps Acts M) (hβ : LabOK Comps Acts β) : LabOK Comps Acts (M.erase x + β) := by
  intro y hy
  rcases Multiset.mem_add.1 hy with h | h
  · exact hM y (Multiset.mem_of_mem_erase h)
  · exact hβ y h

theorem map_sym_cons_erase {M : Multiset (Bool × ℕ)} {x : Bool × ℕ} (hx : x ∈ M) :
    M.map sym = sym x ::ₘ (M.erase x).map sym := by
  conv_lhs => rw [← Multiset.cons_erase hx]
  simp

/-! ### From a run to a tree -/

/-- **A run yields a balanced forest.**  A run from `(s, M)` to a goal configuration gives a
forest of hierarchy trees for `M` and an execution path from `s`, together balanced. -/
theorem forest_of_reach {Comps F : Finset ℕ} {Mb : ℕ} (hC : Closed S Comps Acts F Mb) :
    ∀ {n : ℕ} {x y : Cfg}, ReachIn S n x y → IsGoal S y → LabOK Comps Acts x.2 →
      ∃ (Fo : List (DT NT TT)) (t₂ : DT NT TT), (∀ u ∈ Fo, u.Valid (G S s₀ I Acts)) ∧
        (↑(Fo.map DT.root) : Multiset (NT ⊕ TT)) = x.2.map sym ∧
        t₂.Valid (G S s₀ I Acts) ∧ t₂.root = Sum.inl (NT.st x.1) ∧
        vec ((Fo.map DT.yield).sum + t₂.yield) = 0 := by
  intro n x y h
  induction h with
  | refl x =>
    intro hg _
    obtain ⟨hM, hgoal⟩ := hg
    refine ⟨[], DT.node (NT.st x.1) [], by simp, by simp [hM], ?_, rfl, by simp⟩
    exact DT.Valid.node _ _ (Or.inr ⟨hgoal, by simp⟩) (by simp)
  | @step n x y z hs _ ih =>
    intro hg hlab
    cases hs with
    | dec s M c β hc hm =>
      obtain ⟨Fo', t₂, hFo', hroots, ht₂, hr₂, hvec⟩ :=
        ih hg (labOK_erase_add hlab (hC.meth_lab c β hm))
      rw [Multiset.map_add] at hroots
      obtain ⟨L₁, L₂, hp, h₁, h₂⟩ := exists_split DT.root Fo' _ _ hroots
      have hmem : ∀ u ∈ L₁ ++ L₂, u ∈ Fo' := fun u hu => hp.symm.subset hu
      let u : DT NT TT := DT.node (NT.comp c) L₂
      have hu : u.Valid (G S s₀ I Acts) :=
        DT.Valid.node _ _ ⟨β, hm, h₂⟩ (fun v hv => hFo' v (hmem v (List.mem_append_right _ hv)))
      refine ⟨u :: L₁, t₂, ?_, ?_, ht₂, hr₂, ?_⟩
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hu
        · exact hFo' v (hmem v (List.mem_append_left _ hv))
      · simp only [List.map_cons, ← Multiset.cons_coe, h₁]
        rw [map_sym_cons_erase hc]
        rfl
      · have hsum : (Fo'.map DT.yield).sum = ((u :: L₁).map DT.yield).sum := by
          rw [(hp.map DT.yield).sum_eq]
          simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, u,
            DT.yield_node]
          abel
        rw [← hsum]
        exact hvec
    | exe s M a ha happ =>
      obtain ⟨Fo', t₂', hFo', hroots, ht₂', hr₂', hvec⟩ :=
        ih hg (fun z hz => hlab z (Multiset.mem_of_mem_erase hz))
      have haA : a ∈ Acts := (hlab _ ha).2 rfl
      let t₂ : DT NT TT := DT.node (NT.st s) [DT.leaf (TT.act a), t₂']
      have ht₂ : t₂.Valid (G S s₀ I Acts) := by
        refine DT.Valid.node _ _ (Or.inl ⟨a, haA, happ, ?_⟩) ?_
        · simp only [List.map_cons, List.map_nil, DT.root_leaf, ← Multiset.cons_coe]
          rw [hr₂']
          rfl
        · intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact DT.Valid.leaf _
          · exact ht₂'
      refine ⟨DT.leaf (TT.prim a) :: Fo', t₂, ?_, ?_, ht₂, rfl, ?_⟩
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact DT.Valid.leaf _
        · exact hFo' v hv
      · simp only [List.map_cons, ← Multiset.cons_coe, hroots, DT.root_leaf]
        rw [map_sym_cons_erase ha]
        rfl
      · have : (DT.leaf (TT.prim a) :: Fo').map DT.yield = {TT.prim a} :: Fo'.map DT.yield := by
          simp
        rw [this, List.sum_cons]
        simp only [t₂, DT.yield_node, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          DT.yield_leaf, add_zero]
        have e : ({TT.prim a} + (Fo'.map DT.yield).sum + ({TT.act a} + t₂'.yield)) =
            ((Fo'.map DT.yield).sum + t₂'.yield) + ({TT.prim a} + {TT.act a}) := by abel
        rw [e, vec_add, hvec, zero_add]
        funext b
        by_cases hb : b = a
        · subst hb; simp [vec]
        · simp [vec, hb]

/-! ### From a tree to a run -/

/-- An execution path produces only consumed actions. -/
theorem yield_act_of_st {t : DT NT TT} (ht : t.Valid (G S s₀ I Acts)) :
    ∀ s, t.root = Sum.inl (NT.st s) → ∀ x ∈ t.yield, ∃ a, x = TT.act a := by
  induction ht with
  | leaf b => intro s h; simp at h
  | node X ts hR _ ih =>
    intro s hX x hx
    simp only [DT.root_node, Sum.inl.injEq] at hX
    subst hX
    simp only [DT.yield_node] at hx
    obtain ⟨y, hy, hxy⟩ := (mem_list_sum _).1 hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
    have hroot : u.root ∈ (↑(ts.map DT.root) : Multiset (NT ⊕ TT)) :=
      Multiset.mem_coe.2 (List.mem_map_of_mem hu)
    rcases hR with ⟨a, -, -, hβ⟩ | ⟨-, hβ⟩
    · rw [hβ] at hroot
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hroot
      rcases hroot with h | h
      · cases u with
        | leaf b =>
          simp only [DT.root_leaf, Sum.inr.injEq] at h
          subst h
          simp only [DT.yield_leaf, Multiset.mem_singleton] at hxy
          exact ⟨a, hxy⟩
        | node => simp at h
      · exact ih u hu _ h x hxy
    · rw [hβ] at hroot
      simp at hroot

theorem eq_singleton_of_map {α β : Type*} {f : α → β} {L : List α} {b : β}
    (h : (↑(L.map f) : Multiset β) = {b}) : ∃ u, L = [u] ∧ f u = b := by
  have hlen : L.length = 1 := by
    have := congrArg Multiset.card h
    simpa using this
  match L, hlen with
  | [u], _ =>
    refine ⟨u, rfl, ?_⟩
    simpa using h

/-- **A balanced forest yields a run.**  A forest of hierarchy trees for `M` and an execution
path from `s`, together balanced, give a run from `(s, M)` to a goal configuration whose length
is at most the number of nodes. -/
theorem reach_of_forest : ∀ (n : ℕ) (Fo : List (DT NT TT)) (t₂ : DT NT TT) (s : Finset ℕ)
    (M : Multiset (Bool × ℕ)), (Fo.map DT.size).sum + t₂.size = n →
    (∀ u ∈ Fo, u.Valid (G S s₀ I Acts)) →
    (↑(Fo.map DT.root) : Multiset (NT ⊕ TT)) = M.map sym →
    t₂.Valid (G S s₀ I Acts) → t₂.root = Sum.inl (NT.st s) →
    vec ((Fo.map DT.yield).sum + t₂.yield) = 0 →
    ∃ m ≤ n, ∃ y, ReachIn S m (s, M) y ∧ IsGoal S y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Fo t₂ s M hn hFo hroots ht₂ hr₂ hvec
  by_cases hnode : ∃ u ∈ Fo, ∃ X ch, u = DT.node X ch
  · -- decompose the compound task at the root of an inner node of the forest
    obtain ⟨u, hu, X, ch, rfl⟩ := hnode
    have hpu : Fo.Perm (DT.node X ch :: Fo.erase (DT.node X ch)) := List.perm_cons_erase hu
    have hXmem : Sum.inl X ∈ M.map sym := by
      rw [← hroots]
      exact Multiset.mem_coe.2 (List.mem_map_of_mem (f := DT.root) hu)
    obtain ⟨⟨b, c⟩, hbc, hsym⟩ := Multiset.mem_map.1 hXmem
    cases b with
    | false => simp [sym] at hsym
    | true =>
    simp only [sym, Sum.inl.injEq] at hsym
    subst hsym
    obtain ⟨hR, hch⟩ := DT.Valid.children (hFo _ hu)
    obtain ⟨β, hm, hβ⟩ := hR
    let rest := Fo.erase (DT.node (NT.comp c) ch)
    let Fo₂ := rest ++ ch
    have hsize : (Fo₂.map DT.size).sum + t₂.size + 1 = n := by
      rw [← hn, (hpu.map DT.size).sum_eq]
      simp only [Fo₂, List.map_cons, List.sum_cons, DT.size_node, List.map_append,
        List.sum_append]
      ring
    have hrest : (↑(rest.map DT.root) : Multiset (NT ⊕ TT)) = (M.erase (true, c)).map sym := by
      have h1 := hroots
      rw [Multiset.coe_eq_coe.2 (hpu.map DT.root), map_sym_cons_erase hbc] at h1
      simp only [List.map_cons, ← Multiset.cons_coe, DT.root_node] at h1
      exact (Multiset.cons_inj_right _).1 h1
    have hroots₂ : (↑(Fo₂.map DT.root) : Multiset (NT ⊕ TT)) =
        (M.erase (true, c) + β).map sym := by
      simp only [Fo₂, List.map_append, ← Multiset.coe_add, hrest, hβ, Multiset.map_add]
    have hyield : (Fo.map DT.yield).sum = (Fo₂.map DT.yield).sum := by
      rw [(hpu.map DT.yield).sum_eq]
      simp only [Fo₂, List.map_cons, List.sum_cons, DT.yield_node, List.map_append,
        List.sum_append]
      abel
    have hFo₂ : ∀ v ∈ Fo₂, v.Valid (G S s₀ I Acts) := by
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hFo v (List.mem_of_mem_erase hv)
      · exact hch v hv
    obtain ⟨m, hm', y, hy, hg⟩ := ih _ (by omega) Fo₂ t₂ s _ rfl hFo₂ hroots₂ ht₂ hr₂
      (hyield ▸ hvec)
    exact ⟨m + 1, by omega, y, ReachIn.step (Step.dec s M c β hbc hm) hy, hg⟩
  · push_neg at hnode
    -- every tree of the forest is a leaf, labelled with an action
    have hleaf : ∀ u ∈ Fo, ∃ b, u = DT.leaf (TT.prim b) ∧ (false, b) ∈ M := by
      intro u hu
      cases u with
      | node X ch => exact absurd rfl (hnode _ hu X ch)
      | leaf x =>
        have hxmem : Sum.inr x ∈ M.map sym := by
          rw [← hroots]
          exact Multiset.mem_coe.2 (List.mem_map_of_mem (f := DT.root) hu)
        obtain ⟨⟨b, a⟩, hba, hsym⟩ := Multiset.mem_map.1 hxmem
        cases b with
        | true => simp [sym] at hsym
        | false =>
          simp only [sym, Sum.inr.injEq] at hsym
          exact ⟨a, by rw [hsym], hba⟩
    have hFoprim : ∀ x ∈ (Fo.map DT.yield).sum, ∃ b, x = TT.prim b := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := (mem_list_sum _).1 hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
      obtain ⟨b, rfl, -⟩ := hleaf u hu
      simp only [DT.yield_leaf, Multiset.mem_singleton] at hxy
      exact ⟨b, hxy⟩
    cases t₂ with
    | leaf x => simp at hr₂
    | node Z ch =>
    simp only [DT.root_node, Sum.inl.injEq] at hr₂
    subst hr₂
    obtain ⟨hR, hch⟩ := DT.Valid.children ht₂
    rcases hR with ⟨a, haA, happ, hβ⟩ | ⟨hgoal, hβ⟩
    · -- execute the action the path starts with
      rw [Multiset.insert_eq_cons, ← Multiset.singleton_add] at hβ
      obtain ⟨L₁, L₂, hp, h₁, h₂⟩ := exists_split DT.root ch _ _ hβ
      obtain ⟨u₁, rfl, hu₁⟩ := eq_singleton_of_map h₁
      obtain ⟨u₂, rfl, hu₂⟩ := eq_singleton_of_map h₂
      cases u₁ with
      | node => simp at hu₁
      | leaf x₁ =>
      simp only [DT.root_leaf, Sum.inr.injEq] at hu₁
      subst hu₁
      have hu₂v : u₂.Valid (G S s₀ I Acts) := hch u₂ (hp.symm.subset (by simp))
      have hsz : (ch.map DT.size).sum = 1 + u₂.size := by
        rw [(hp.map DT.size).sum_eq]
        simp
      have hyl : (ch.map DT.yield).sum = {TT.act a} + u₂.yield := by
        rw [(hp.map DT.yield).sum_eq]
        simp
      -- the action was produced by the hierarchy
      have hcount : 0 < (Fo.map DT.yield).sum.count (TT.prim a) := by
        have hva := congrFun hvec a
        simp only [DT.yield_node, hyl, vec, Multiset.count_add, Pi.zero_apply] at hva
        have hnp : u₂.yield.count (TT.prim a) = 0 := by
          refine Multiset.count_eq_zero.2 (fun hm => ?_)
          obtain ⟨b, hb⟩ := yield_act_of_st hu₂v _ hu₂ _ hm
          cases hb
        have : ({TT.act a} : Multiset TT).count (TT.act a) = 1 := by simp
        have h0 : ({TT.act a} : Multiset TT).count (TT.prim a) = 0 := by simp
        push_cast at hva
        omega
      obtain ⟨y₀, hy₀, hay⟩ := (mem_list_sum _).1 (Multiset.count_pos.1 hcount)
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy₀
      obtain ⟨b, rfl, hbM⟩ := hleaf u hu
      simp only [DT.yield_leaf, Multiset.mem_singleton, TT.prim.injEq] at hay
      subst hay
      have hpu : Fo.Perm (DT.leaf (TT.prim a) :: Fo.erase (DT.leaf (TT.prim a))) :=
        List.perm_cons_erase hu
      let Fo₂ := Fo.erase (DT.leaf (TT.prim a))
      have hroots₂ : (↑(Fo₂.map DT.root) : Multiset (NT ⊕ TT)) =
          (M.erase (false, a)).map sym := by
        have h1 := hroots
        rw [Multiset.coe_eq_coe.2 (hpu.map DT.root), map_sym_cons_erase hbM] at h1
        simp only [List.map_cons, ← Multiset.cons_coe, DT.root_leaf] at h1
        exact (Multiset.cons_inj_right _).1 h1
      have hyield : (Fo.map DT.yield).sum = {TT.prim a} + (Fo₂.map DT.yield).sum := by
        rw [(hpu.map DT.yield).sum_eq]
        simp [Fo₂]
      have hvec₂ : vec ((Fo₂.map DT.yield).sum + u₂.yield) = 0 := by
        have e : (Fo.map DT.yield).sum + (DT.node (NT.st s) ch).yield =
            ((Fo₂.map DT.yield).sum + u₂.yield) + ({TT.prim a} + {TT.act a}) := by
          rw [hyield, DT.yield_node, hyl]
          abel
        rw [e, vec_add] at hvec
        have h2 : vec ({TT.prim a} + {TT.act a}) = 0 := by
          funext b'
          by_cases hb : b' = a
          · subst hb; simp [vec]
          · simp [vec, hb]
        rw [h2, add_zero] at hvec
        exact hvec
      have hsize : (Fo₂.map DT.size).sum + u₂.size + 3 = n := by
        rw [← hn, (hpu.map DT.size).sum_eq, DT.size_node, hsz]
        simp only [List.map_cons, List.sum_cons, DT.size_leaf, Fo₂]
        ring
      obtain ⟨m, hm', y, hy, hg⟩ := ih _ (by omega) Fo₂ u₂ (S.nxt s a) _ rfl
        (fun v hv => hFo v (List.mem_of_mem_erase hv)) hroots₂ hu₂v hu₂ hvec₂
      exact ⟨m + 1, by omega, y, ReachIn.step (Step.exe s M a hbM happ) hy, hg⟩
    · -- the goal holds and nothing is left to do
      have hch0 : ch = [] := by
        have : ch.map DT.root = [] := by simpa using hβ
        simpa using this
      subst hch0
      have hFo0 : Fo = [] := by
        rcases Fo with _ | ⟨u, Fo'⟩
        · rfl
        · exfalso
          obtain ⟨b, rfl, -⟩ := hleaf _ List.mem_cons_self
          have hva := congrFun hvec b
          have hact : (Multiset.count (TT.act b) (((DT.leaf (TT.prim b) :: Fo').map
              DT.yield).sum)) = 0 :=
            Multiset.count_eq_zero.2 (fun hm => by
              obtain ⟨b', hb'⟩ := hFoprim _ hm
              cases hb')
          have hprim : 0 < (Multiset.count (TT.prim b) (((DT.leaf (TT.prim b) :: Fo').map
              DT.yield).sum)) := by
            simp
          simp only [DT.yield_node, List.map_nil, List.sum_nil, add_zero, vec,
            Pi.zero_apply] at hva
          omega
      subst hFo0
      have hM0 : M = 0 := by
        have : M.map sym = 0 := by simpa using hroots.symm
        exact Multiset.map_eq_zero.1 this
      exact ⟨0, by omega, (s, M), ReachIn.refl _, hM0, hgoal⟩

/-! ### The small-solution theorem -/

/-- **The bound of the small-solution theorem**: `k` bounds the number of nonterminals (compound
names, states and the root), `nA` is the number of relevant actions, `M` bounds the length of
a rule body. -/
def uoBound (k nA M : ℕ) : ℕ :=
  (M + 1) ^ (k * 2 ^ k + 1) +
    ZeroSum.zsB nA ((M + 1) ^ (k * 2 ^ k + 2)) * (M + 1) ^ (k * 2 ^ k + 2)

/-- The nonterminals that can occur in a tree of solutions. -/
def KSet (Comps F : Finset ℕ) : Finset NT :=
  insert NT.top (Comps.image NT.comp ∪ F.powerset.image NT.st)

theorem card_KSet (Comps F : Finset ℕ) : (KSet Comps F).card ≤ 1 + Comps.card + 2 ^ F.card := by
  unfold KSet
  calc (insert NT.top (Comps.image NT.comp ∪ F.powerset.image NT.st)).card
      ≤ (Comps.image NT.comp ∪ F.powerset.image NT.st).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Comps.image NT.comp).card + (F.powerset.image NT.st).card + 1 := by
        have := Finset.card_union_le (Comps.image NT.comp) (F.powerset.image NT.st)
        omega
    _ ≤ Comps.card + F.powerset.card + 1 := by
        have h1 := Finset.card_image_le (s := Comps) (f := NT.comp)
        have h2 := Finset.card_image_le (s := F.powerset) (f := NT.st)
        omega
    _ = 1 + Comps.card + 2 ^ F.card := by rw [Finset.card_powerset]; ring

theorem exists_map_some {α : Type*} :
    ∀ (U : Multiset (Option α)) (V : Multiset α), U ≤ V.map some → ∃ W ≤ V, U = W.map some := by
  intro U V hUV
  have hsome : ∀ x ∈ U, x ≠ none := by
    intro x hx hxn
    subst hxn
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hUV hx)
    cases ha
  have key : ∀ U : Multiset (Option α), (∀ x ∈ U, x ≠ none) → (U.filterMap id).map some = U := by
    intro U
    induction U using Multiset.induction_on with
    | empty => simp
    | cons x U ih =>
      intro h
      obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.1 (h x (Multiset.mem_cons_self _ _))
      rw [Multiset.filterMap_cons_some id a U rfl, Multiset.map_cons,
        ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))]
  refine ⟨U.filterMap id, ?_, (key U hsome).symm⟩
  rw [← Multiset.map_le_map_iff (Option.some_injective α), key U hsome]
  exact hUV

/-- **The small-solution theorem for abstract unordered problems.** -/
theorem short_run {Comps F : Finset ℕ} {Mb k : ℕ} (hC : Closed S Comps Acts F Mb)
    (hs₀ : s₀ ⊆ F) (hI : LabOK Comps Acts I) (hk : 1 + Comps.card + 2 ^ F.card ≤ k)
    {n : ℕ} {y : Cfg} (h : ReachIn S n (s₀, I) y) (hy : IsGoal S y) :
    ∃ m ≤ uoBound k Acts.card (Multiset.card I + Mb + 2), ∃ y', ReachIn S m (s₀, I) y' ∧
      IsGoal S y' := by
  classical
  set Mx := Multiset.card I + Mb + 2 with hMx
  set D := k * 2 ^ k with hD
  obtain ⟨Fo, t₂, hFo, hroots, ht₂, hr₂, hvec⟩ :=
    forest_of_reach (s₀ := s₀) (I := I) hC h hy hI
  -- the tree of the solution
  let t : DT NT TT := DT.node NT.top (Fo ++ [t₂])
  have ht : t.Valid (G S s₀ I Acts) := by
    refine DT.Valid.node _ _ ?_ ?_
    · show _ = _
      simp only [List.map_append, List.map_cons, List.map_nil, ← Multiset.coe_add, hroots, hr₂]
      rfl
    · intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hFo v hv
      · rw [List.mem_singleton] at hv
        exact hv ▸ ht₂
  have hvt : vec t.yield = 0 := by
    simpa [t, List.map_append, List.sum_append] using hvec
  -- the rules
  have hclosed : ∀ X β, X ∈ KSet Comps F → G S s₀ I Acts X β →
      ∀ Y, Sum.inl Y ∈ β → Y ∈ KSet Comps F := by
    intro X β hX hR Y hY
    cases X with
    | top =>
      simp only [G] at hR
      subst hR
      rcases Multiset.mem_add.1 hY with hY | hY
      · obtain ⟨⟨b, c⟩, hbc, hsym⟩ := Multiset.mem_map.1 hY
        cases b with
        | false => simp [sym] at hsym
        | true =>
          simp only [sym, Sum.inl.injEq] at hsym
          subst hsym
          simp [KSet, (hI _ hbc).1 rfl]
      · simp only [Multiset.mem_singleton, Sum.inl.injEq] at hY
        subst hY
        simp [KSet, hs₀]
    | comp c =>
      obtain ⟨β', hm, rfl⟩ := hR
      obtain ⟨⟨b, c'⟩, hbc, hsym⟩ := Multiset.mem_map.1 hY
      cases b with
      | false => simp [sym] at hsym
      | true =>
        simp only [sym, Sum.inl.injEq] at hsym
        subst hsym
        simp [KSet, (hC.meth_lab c β' hm _ hbc).1 rfl]
    | st s =>
      have hsF : s ⊆ F := by
        simp only [KSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          Finset.mem_powerset] at hX
        rcases hX with h | ⟨_, _, h⟩ | ⟨s', hs', h⟩
        · cases h
        · cases h
        · cases h
          exact hs'
      rcases hR with ⟨a, -, -, rfl⟩ | ⟨-, rfl⟩
      · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
          reduceCtorEq, false_or, Sum.inl.injEq] at hY
        subst hY
        simp [KSet, hC.nxt_sub s a hsF]
      · simp at hY
  have hMrule : ∀ X β, G S s₀ I Acts X β → Multiset.card β ≤ Mx := by
    intro X β hR
    cases X with
    | top =>
      simp only [G] at hR
      subst hR
      simp only [Multiset.card_add, Multiset.card_map, Multiset.card_singleton]
      omega
    | comp c =>
      obtain ⟨β', hm, rfl⟩ := hR
      have := hC.meth_card c β' hm
      simp only [Multiset.card_map]
      omega
    | st s =>
      rcases hR with ⟨a, -, -, rfl⟩ | ⟨-, rfl⟩
      · simp [hMx]
      · simp
  have hQ : ∀ X β, G S s₀ I Acts X β → ∀ x, Sum.inr x ∈ β → x.name ∈ Acts := by
    intro X β hR x hx
    cases X with
    | top =>
      simp only [G] at hR
      subst hR
      rcases Multiset.mem_add.1 hx with hx | hx
      · obtain ⟨⟨b, a⟩, hba, hsym⟩ := Multiset.mem_map.1 hx
        cases b with
        | true => simp [sym] at hsym
        | false =>
          simp only [sym, Sum.inr.injEq] at hsym
          subst hsym
          exact (hI _ hba).2 rfl
      · simp at hx
    | comp c =>
      obtain ⟨β', hm, rfl⟩ := hR
      obtain ⟨⟨b, a⟩, hba, hsym⟩ := Multiset.mem_map.1 hx
      cases b with
      | true => simp [sym] at hsym
      | false =>
        simp only [sym, Sum.inr.injEq] at hsym
        subst hsym
        exact (hC.meth_lab c β' hm _ hba).2 rfl
    | st s =>
      rcases hR with ⟨a, ha, -, rfl⟩ | ⟨-, rfl⟩
      · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Sum.inr.injEq,
          Multiset.mem_singleton, reduceCtorEq, or_false] at hx
        subst hx
        exact ha
      · simp at hx
  have hK : t.labels ⊆ KSet Comps F :=
    DT.labels_subset_of_closed hclosed ht NT.top rfl (by simp [KSet])
  -- decompose
  obtain ⟨t₀, ps, h₀, hr₀, -, hh₀, hps, hy₀⟩ := decomp (KSet Comps F) hMrule t.size t rfl ht hK
  have hKk : (KSet Comps F).card ≤ k := (card_KSet Comps F).trans hk
  have hDle : (KSet Comps F).card * 2 ^ (KSet Comps F).card ≤ D :=
    Nat.mul_le_mul hKk (Nat.pow_le_pow_right (by norm_num) hKk)
  set ab := (Mx + 1) ^ (D + 2) with hab
  have hsz₀ : t₀.size ≤ (Mx + 1) ^ (D + 1) :=
    (DT.size_le_pow hMrule h₀).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hsz₀' : t₀.size ≤ ab :=
    hsz₀.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hszp : ∀ p ∈ ps, p.2.size ≤ ab := fun p hp =>
    (hps p hp).2.2.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hnames₀ : ∀ x ∈ t₀.yield, x.name ∈ Acts :=
    DT.yield_mem_of_rules hQ h₀ (fun x hx => by rw [hr₀] at hx; cases hx)
  have hnamesp : ∀ p ∈ ps, ∀ x ∈ p.2.yieldC, x.name ∈ Acts := fun p hp =>
    Ctx.yieldC_mem_of_rules hQ (hps p hp).1.1
  -- select pumps restoring the balance
  let g : Option (NT × Ctx NT TT) → ℕ → ℤ := fun o =>
    match o with
    | none => vec t₀.yield
    | some p => vec p.2.yieldC
  let S0 : Multiset (Option (NT × Ctx NT TT)) := none ::ₘ (↑ps : Multiset _).map some
  have hsum : (S0.map g).sum = 0 := by
    have e : (S0.map g).sum = vec t₀.yield + (ps.map (fun p => vec p.2.yieldC)).sum := by
      simp only [S0, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_coe, Multiset.sum_coe]
      rw [List.map_map]
      rfl
    rw [e, ← vec_list_sum, ← vec_add, ← hy₀]
    exact hvt
  have hsupp : ∀ x ∈ S0, ∀ i, i ∉ Acts → g x i = 0 := by
    intro x hx i hi
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact vec_eq_zero_of_names hnames₀ hi
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      exact vec_eq_zero_of_names (hnamesp p (Multiset.mem_coe.1 hp)) hi
  have hbnd : ∀ x ∈ S0, ∀ i, |g x i| ≤ (ab : ℤ) := by
    intro x hx i
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · refine (abs_vec_le _ _).trans ?_
      exact_mod_cast (DT.card_yield_le _ t₀ rfl).trans hsz₀'
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      refine (abs_vec_le _ _).trans ?_
      exact_mod_cast (Ctx.card_yieldC_le p.2).trans (hszp p (Multiset.mem_coe.1 hp))
  obtain ⟨T, hTS, hnone, hcardT, hTsum⟩ := ZeroSum.exists_small_zero_sum_mem Acts ab g none _
    S0 rfl (Multiset.mem_cons_self _ _) hsupp hbnd hsum
  have hTe : T.erase none ≤ (↑ps : Multiset _).map some := by
    have := Multiset.erase_le_erase none hTS
    simpa [S0] using this
  obtain ⟨W, hW, hTW⟩ := exists_map_some _ _ hTe
  let qs := W.toList
  have hqs_mem : ∀ q ∈ qs, q ∈ ps := fun q hq =>
    Multiset.mem_coe.1 (Multiset.mem_of_le hW (Multiset.mem_toList.1 hq))
  have hqs_len : qs.length ≤ ZeroSum.zsB Acts.card ab := by
    have h1 : qs.length = Multiset.card (T.erase none) := by
      rw [Multiset.length_toList, hTW, Multiset.card_map]
    rw [h1, Multiset.card_erase_of_mem hnone]
    exact (Nat.pred_le _).trans hcardT
  have hqs_sum : vec t₀.yield + (qs.map (fun q => vec q.2.yieldC)).sum = 0 := by
    have e : (T.map g).sum = vec t₀.yield + (qs.map (fun q => vec q.2.yieldC)).sum := by
      rw [← Multiset.cons_erase hnone, Multiset.map_cons, Multiset.sum_cons, hTW,
        Multiset.map_map]
      have : W = (↑qs : Multiset _) := (Multiset.coe_toList W).symm
      rw [this, Multiset.map_coe, Multiset.sum_coe]
      rfl
    rw [← e]
    exact hTsum
  -- insert them
  obtain ⟨t', ht', hr', hy', hs'⟩ := insert_pumps qs h₀
    (fun q hq => ⟨(hps q (hqs_mem q hq)).1, (hps q (hqs_mem q hq)).2.1⟩)
  have hvt' : vec t'.yield = 0 := by
    rw [hy', vec_add, vec_list_sum]
    exact hqs_sum
  have hst' : t'.size ≤ uoBound k Acts.card Mx := by
    rw [hs']
    have h1 : (qs.map (fun p => p.2.size)).sum ≤ qs.length * ab :=
      sum_le_length_mul _ _ qs (fun q hq => hszp q (hqs_mem q hq))
    have h2 : qs.length * ab ≤ ZeroSum.zsB Acts.card ab * ab := Nat.mul_le_mul_right _ hqs_len
    have e : uoBound k Acts.card Mx = (Mx + 1) ^ (D + 1) + ZeroSum.zsB Acts.card ab * ab := rfl
    rw [e]
    omega
  -- read off a run
  have hrt' : t'.root = Sum.inl NT.top := by rw [hr', hr₀]; rfl
  cases t' with
  | leaf x => simp at hrt'
  | node X ch =>
  simp only [DT.root_node, Sum.inl.injEq] at hrt'
  subst hrt'
  obtain ⟨hR, hch⟩ := DT.Valid.children ht'
  simp only [G] at hR
  obtain ⟨L₁, L₂, hp, h₁, h₂⟩ := exists_split DT.root ch _ _ hR
  obtain ⟨u₂, rfl, hu₂⟩ := eq_singleton_of_map h₂
  have hmem : ∀ v, v ∈ L₁ ++ [u₂] → v ∈ ch := fun v hv => hp.symm.subset hv
  have hyl : (ch.map DT.yield).sum = (L₁.map DT.yield).sum + u₂.yield := by
    rw [(hp.map DT.yield).sum_eq]
    simp
  have hsz : (ch.map DT.size).sum = (L₁.map DT.size).sum + u₂.size := by
    rw [(hp.map DT.size).sum_eq]
    simp
  obtain ⟨m, hm, y', hy', hg'⟩ := reach_of_forest (S := S) (s₀ := s₀) (I := I) (Acts := Acts) _
    L₁ u₂ s₀ I rfl (fun v hv => hch v (hmem v (List.mem_append_left _ hv))) h₁
    (hch u₂ (hmem u₂ (by simp))) hu₂ (by rw [← hyl]; simpa using hvt')
  refine ⟨m, ?_, y', hy', hg'⟩
  simp only [DT.size_node] at hst'
  omega

end UOAbs

end HTN
