import HtnPlanning.Regular.RegularStructure
import HtnPlanning.Core.Macro
/-!
# A normal form for totally ordered regular HTN problems

A *regular* task network contains at most one compound task, which is ordered after all other
tasks (Def. 3.3); if in addition all methods are totally ordered, every task network reachable
from a single initial compound task is a **chain**: a totally ordered sequence of primitive
tasks followed by at most one compound task.

This file introduces the corresponding predicate `TaskNetwork.IsChain tn l os tail` and proves

* `TaskNetwork.exists_isChain` — every well-formed, regular and totally ordered task network
  *is* such a chain;
* `TaskNetwork.isChain_decomposeWith` — decomposing the trailing compound task of a chain with
  (a fresh copy of) a chain-shaped method body yields again a chain, whose action sequence is
  the concatenation of the two;
* `TaskNetwork.IsChain.actionSeq_unique` — a closed chain (no compound task) has exactly one
  action sequence, namely `os`.

These are the ingredients of the **normal form theorem** `Problem.solvable_iff_derives`: a
totally ordered regular problem with initial compound task `c₀` is solvable iff there is a
*derivation* `Derives c₀ as` (a sequence of methods, each continuing the compound task left
over by the previous one) whose action sequence `as` is executable and reaches the goal.

This is the HTN-side ingredient of the compilation of regular HTN problems into STRIPS
(`HtnComplexity/Regular/RegularToStrips.lean`).
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace TaskNetwork

section Chain

variable [DecidableEq I]

/-- Two members of a list with the same index are equal. -/
lemma idxOf_inj_of_mem {m : List I} {x y : I} (hx : x ∈ m) (hy : y ∈ m)
    (h : m.idxOf x = m.idxOf y) : x = y := by
  have h1 : m[m.idxOf x]'(List.idxOf_lt_length_of_mem hx) = x := List.getElem_idxOf _
  have h2 : m[m.idxOf y]'(List.idxOf_lt_length_of_mem hy) = y := List.getElem_idxOf _
  rw [← h1, ← h2]
  simp only [h]

/-- The task ids of a chain network, in their linear order: the primitive ones followed by the
optional trailing compound task. -/
def chainIds (l : List I) (tail : Option (I × C)) : List I :=
  match tail with
  | none => l
  | some p => l ++ [p.1]

omit [DecidableEq I] in
@[simp] lemma chainIds_none (l : List I) : chainIds (C := C) l none = l := rfl

omit [DecidableEq I] in
@[simp] lemma chainIds_some (l : List I) (p : I × C) : chainIds l (some p) = l ++ [p.1] := rfl

omit [DecidableEq I] in
lemma chainIds_append (l l' : List I) (tail : Option (I × C)) :
    chainIds (l ++ l') tail = l ++ chainIds l' tail := by
  cases tail <;> simp

/-- **Chain networks.**  `IsChain tn l os tail` states that the task network `tn` consists of
the primitive tasks `l` (labelled by the action sequence `os`), followed by the optional
compound task `tail = some (t, c)`, and that its ordering is the linear order of this
sequence. -/
structure IsChain (tn : TaskNetwork I A C) (l : List I) (os : List A)
    (tail : Option (I × C)) : Prop where
  /-- The task ids are pairwise distinct. -/
  nodup : (chainIds l tail).Nodup
  /-- The task ids of the network are exactly those of the chain. -/
  memT : ∀ x, x ∈ tn.T ↔ x ∈ chainIds l tail
  /-- The tasks of `l` are labelled by the actions `os`. -/
  labels : l.map tn.α = os.map Sum.inl
  /-- The trailing task, if any, is labelled by its compound task name. -/
  tailLabel : ∀ p : I × C, tail = some p → tn.α p.1 = Sum.inr p.2
  /-- The ordering is the linear order of the chain. -/
  ord : ∀ x y, tn.ord x y ↔ (x ∈ chainIds l tail ∧ y ∈ chainIds l tail ∧
    (chainIds l tail).idxOf x < (chainIds l tail).idxOf y)

namespace IsChain

variable {tn : TaskNetwork I A C} {l : List I} {os : List A} {tail : Option (I × C)}

lemma mem_of_mem_l (h : IsChain tn l os tail) {x : I} (hx : x ∈ l) : x ∈ tn.T := by
  refine (h.memT x).2 ?_
  cases tail <;> simp [hx]

lemma mem_tail (h : IsChain tn l os tail) {p : I × C} (hp : tail = some p) : p.1 ∈ tn.T := by
  refine (h.memT p.1).2 ?_
  simp [hp]

/-- A chain network is well formed. -/
lemma wf (h : IsChain tn l os tail) : tn.WF where
  mem_left := by
    intro a b hab
    exact (h.memT a).2 ((h.ord a b).1 hab).1
  mem_right := by
    intro a b hab
    exact (h.memT b).2 ((h.ord a b).1 hab).2.1
  irrefl := by
    intro a hcon
    exact absurd ((h.ord a a).1 hcon).2.2 (lt_irrefl _)
  trans := by
    intro a b c hab hbc
    obtain ⟨ha, -, hab'⟩ := (h.ord a b).1 hab
    obtain ⟨-, hc, hbc'⟩ := (h.ord b c).1 hbc
    exact (h.ord a c).2 ⟨ha, hc, lt_trans hab' hbc'⟩

/-- The chain enumeration is a linearization of the network. -/
lemma isLinearization (h : IsChain tn l os tail) : tn.IsLinearization (chainIds l tail) := by
  refine ⟨h.nodup, fun t => (h.memT t).symm, ?_⟩
  have hpair : (chainIds l tail).Pairwise
      (fun a b => (chainIds l tail).idxOf a < (chainIds l tail).idxOf b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.Nodup.idxOf_getElem h.nodup, List.Nodup.idxOf_getElem h.nodup]
    exact hij
  refine List.Pairwise.imp ?_ hpair
  intro a b hab hcon
  exact absurd ((h.ord b a).1 hcon).2.2 (by omega)

/-- The action sequence induced by the primitive part of a chain. -/
lemma isActionSeq (h : IsChain tn l os tail) : tn.IsActionSeq l os := h.labels

/-- A chain without a trailing compound task is a primitive task network. -/
lemma isPrimitive (h : IsChain tn l os none) : tn.IsPrimitive := by
  intro t ht
  have htl : t ∈ l := (h.memT t).1 ht
  have hmem : tn.α t ∈ l.map tn.α := List.mem_map_of_mem htl
  rw [h.labels] at hmem
  obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
  exact ⟨a, ha.symm⟩

/-- **The linearization of a chain is unique.** -/
lemma linearization_eq (h : IsChain tn l os tail) {m : List I} (hlin : tn.IsLinearization m) :
    m = chainIds l tail := by
  classical
  set M : List I := chainIds l tail with hM
  have hsorted : ∀ u : List I, u.Nodup → (∀ t, t ∈ u ↔ t ∈ tn.T) →
      u.Pairwise (fun a b => ¬ tn.ord b a) →
      u.Pairwise (fun a b => M.idxOf a < M.idxOf b) := by
    intro u hnodup hmem hpair
    have hcomb : u.Pairwise (fun a b => (¬ tn.ord b a) ∧ a ≠ b) :=
      List.Pairwise.and hpair hnodup
    refine List.Pairwise.imp_of_mem ?_ hcomb
    rintro a b ha hb ⟨hnord, hne⟩
    have haT : a ∈ M := (h.memT a).1 ((hmem a).1 ha)
    have hbT : b ∈ M := (h.memT b).1 ((hmem b).1 hb)
    have hidx : M.idxOf a ≠ M.idxOf b := fun hcon => hne (idxOf_inj_of_mem haT hbT hcon)
    rcases lt_or_gt_of_ne hidx with hlt | hgt
    · exact hlt
    · exact absurd ((h.ord b a).2 ⟨hbT, haT, hgt⟩) hnord
  have hperm : m.Perm M := by
    refine (List.perm_ext_iff_of_nodup hlin.1 h.nodup).2 ?_
    intro t
    rw [hlin.2.1 t, h.memT t]
  have h₁ : m.Pairwise (fun a b => M.idxOf a < M.idxOf b) := hsorted m hlin.1 hlin.2.1 hlin.2.2
  have h₂ : M.Pairwise (fun a b => M.idxOf a < M.idxOf b) :=
    hsorted M h.nodup (fun t => (h.memT t).symm) h.isLinearization.2.2
  refine List.Perm.eq_of_pairwise ?_ h₁ h₂ hperm
  intro a b _ _ hab hba
  exact absurd (lt_trans hab hba) (lt_irrefl _)

/-- A closed chain has *exactly one* action sequence: every linearization induces `os`. -/
lemma actionSeq_unique (h : IsChain tn l os none) {l' : List I} {as : List A}
    (hlin : tn.IsLinearization l') (hseq : tn.IsActionSeq l' as) : as = os := by
  have hll : l' = l := by simpa using h.linearization_eq hlin
  subst hll
  exact isActionSeq_unique hseq h.isActionSeq

end IsChain

/-! ### Every regular, totally ordered task network is a chain -/

/-- In a totally ordered well-formed network, the ordering is the index order of any
linearization. -/
lemma ord_iff_idxOf_lt {tn : TaskNetwork I A C} (hwf : tn.WF) (hTO : tn.IsTotallyOrdered)
    {m : List I} (hlin : tn.IsLinearization m) (x y : I) :
    tn.ord x y ↔ (x ∈ m ∧ y ∈ m ∧ m.idxOf x < m.idxOf y) := by
  classical
  obtain ⟨hnodup, hmem, hpair⟩ := hlin
  have hforbid : ∀ a b : I, a ∈ m → b ∈ m → m.idxOf a < m.idxOf b → ¬ tn.ord b a := by
    intro a b ha hb hlt
    have hpair' := hpair
    rw [List.pairwise_iff_getElem] at hpair'
    have halt : m.idxOf a < m.length := List.idxOf_lt_length_of_mem ha
    have hblt : m.idxOf b < m.length := List.idxOf_lt_length_of_mem hb
    have hga : m[m.idxOf a]'halt = a := List.getElem_idxOf _
    have hgb : m[m.idxOf b]'hblt = b := List.getElem_idxOf _
    have := hpair' (m.idxOf a) (m.idxOf b) halt hblt hlt
    rw [hga, hgb] at this
    exact this
  constructor
  · intro hord
    have hx : x ∈ m := (hmem x).2 (hwf.mem_left hord)
    have hy : y ∈ m := (hmem y).2 (hwf.mem_right hord)
    refine ⟨hx, hy, ?_⟩
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · have : y = x := idxOf_inj_of_mem hy hx heq
      exact hwf.irrefl x (this ▸ hord)
    · exact hforbid y x hy hx hlt hord
  · rintro ⟨hx, hy, hlt⟩
    have hne : x ≠ y := fun hcon => absurd hlt (by rw [hcon]; exact lt_irrefl _)
    rcases hTO x ((hmem x).1 hx) y ((hmem y).1 hy) hne with h | h
    · exact h
    · exact absurd h (hforbid x y hx hy hlt)

/-- **Every well-formed, regular and totally ordered task network is a chain.** -/
theorem exists_isChain {tn : TaskNetwork I A C} (hwf : tn.WF) (hreg : tn.IsRegular)
    (hTO : tn.IsTotallyOrdered) :
    ∃ (l : List I) (os : List A) (tail : Option (I × C)), IsChain tn l os tail := by
  classical
  obtain ⟨m, hlin⟩ := exists_linearization hwf
  have hord := ord_iff_idxOf_lt hwf hTO hlin
  by_cases habs : ∃ t ∈ m, tn.IsAbstractId t
  · obtain ⟨t, htm, c, hc⟩ := habs
    have htT : t ∈ tn.T := (hlin.2.1 t).1 htm
    -- `t` is the last element of the linearization
    have hlast : ∀ x ∈ m, x ≠ t → m.idxOf x < m.idxOf t := by
      intro x hx hxt
      have := hreg.2 t htT ⟨c, hc⟩ x ((hlin.2.1 x).1 hx) hxt
      exact ((hord x t).1 this).2.2
    have htlt : m.idxOf t < m.length := List.idxOf_lt_length_of_mem htm
    have hidx : m.idxOf t = m.length - 1 := by
      by_contra hcon
      have hlt : m.idxOf t + 1 < m.length := by omega
      have hmem : m[m.idxOf t + 1]'hlt ∈ m := List.getElem_mem _
      have hidx' : m.idxOf (m[m.idxOf t + 1]'hlt) = m.idxOf t + 1 :=
        List.Nodup.idxOf_getElem hlin.1 _ hlt
      have hne : m[m.idxOf t + 1]'hlt ≠ t := by
        intro heq
        rw [heq] at hidx'
        omega
      have := hlast _ hmem hne
      rw [hidx'] at this
      omega
    obtain ⟨l, hml⟩ : ∃ l : List I, m = l ++ [t] := by
      refine ⟨m.dropLast, ?_⟩
      have hne : m ≠ [] := by
        intro hcon
        rw [hcon] at htm
        simp at htm
      have hlen : m.length - 1 < m.length := by
        have := List.length_pos_of_ne_nil hne
        omega
      have hgl : m.getLast hne = t := by
        have hget : m.getLast hne = m[m.length - 1]'hlen := by rw [List.getLast_eq_getElem]
        rw [hget]
        have hidx' : m.idxOf (m[m.length - 1]'hlen) = m.length - 1 :=
          List.Nodup.idxOf_getElem hlin.1 _ hlen
        exact idxOf_inj_of_mem (List.getElem_mem hlen) htm (by rw [hidx', hidx])
      conv_lhs => rw [← List.dropLast_append_getLast hne, hgl]
    subst hml
    have hprimAll : ∀ x ∈ l, tn.IsPrimitiveId x := by
      intro x hx
      have hxm : x ∈ l ++ [t] := List.mem_append_left _ hx
      have hxT : x ∈ tn.T := (hlin.2.1 x).1 hxm
      have hxt : x ≠ t := by
        intro hcon
        subst hcon
        have hnd := hlin.1
        rw [List.nodup_append] at hnd
        exact hnd.2.2 x hx x (by simp) rfl
      by_contra hprim
      refine hxt (hreg.1 x hxT t htT ?_ ⟨c, hc⟩)
      rcases hcase : tn.α x with a | c'
      · exact absurd ⟨a, hcase⟩ hprim
      · exact ⟨c', hcase⟩
    obtain ⟨os, hos⟩ := exists_actionSeq hprimAll
    refine ⟨l, os, some (t, c), hlin.1, ?_, hos, ?_, ?_⟩
    · intro x
      rw [← hlin.2.1 x]
      simp
    · intro p hp
      simp only [Option.some.injEq] at hp
      subst hp
      exact hc
    · intro x y
      simpa using hord x y
  · push_neg at habs
    have hprimAll : ∀ x ∈ m, tn.IsPrimitiveId x := by
      intro x hx
      by_contra hprim
      refine habs x hx ?_
      rcases hcase : tn.α x with a | c'
      · exact absurd ⟨a, hcase⟩ hprim
      · exact ⟨c', hcase⟩
    obtain ⟨os, hos⟩ := exists_actionSeq hprimAll
    refine ⟨m, os, none, hlin.1, ?_, hos, ?_, ?_⟩
    · intro x
      rw [← hlin.2.1 x]
      simp
    · rintro p ⟨⟩
    · intro x y
      simpa using hord x y


/-! ### Decomposition of the trailing compound task of a chain -/

/-- **Decomposing the trailing compound task of a chain with a chain-shaped method body yields
again a chain**, whose primitive tasks are those of the two chains, one after the other. -/
theorem isChain_decomposeWith {tn tn' : TaskNetwork I A C} {l l' : List I} {os os' : List A}
    {t : I} {c : C} {tail' : Option (I × C)}
    (hc : IsChain tn l os (some (t, c))) (hc' : IsChain tn' l' os' tail')
    (hdisj : Disjoint tn.T tn'.T) :
    IsChain (decomposeWith tn t tn') (l ++ l') (os ++ os') tail' := by
  classical
  obtain ⟨hnodup', hmem', hlabels', htail', hord'⟩ := hc'
  obtain ⟨hnodupu, hmemu, hlabels, htail, hordu⟩ := hc
  simp only [chainIds_some] at hnodupu hmemu hordu
  set v : List I := chainIds l' tail' with hv
  have hnew : chainIds (l ++ l') tail' = l ++ v := chainIds_append l l' tail'
  have hnodupl : l.Nodup := (List.nodup_append.1 hnodupu).1
  have htl : t ∉ l := fun hcon =>
    (List.nodup_append.1 hnodupu).2.2 t hcon t (by simp) rfl
  have hnotmem : ∀ x, x ∈ l ++ [t] → x ∉ v := by
    intro x hx hxv
    exact (Finset.disjoint_left.1 hdisj ((hmemu x).2 hx)) ((hmem' x).2 hxv)
  have hlv : ∀ x, x ∈ l → x ∉ v := fun x hx => hnotmem x (List.mem_append_left _ hx)
  have hlT' : ∀ x, x ∈ l → x ∉ tn'.T := fun x hx hcon => hlv x hx ((hmem' x).1 hcon)
  -- index computations
  have hidxl : ∀ x, x ∈ l → (l ++ v).idxOf x = l.idxOf x := by
    intro x hx; simp [List.idxOf_append, hx]
  have hidxv : ∀ x, x ∈ v → (l ++ v).idxOf x = v.idxOf x + l.length := by
    intro x hx
    have hxl : x ∉ l := fun hcon => hlv x hcon hx
    simp [List.idxOf_append, hxl]
  have hidxlu : ∀ x, x ∈ l → (l ++ [t]).idxOf x = l.idxOf x := by
    intro x hx; simp [List.idxOf_append, hx]
  have hidxtu : (l ++ [t]).idxOf t = l.length := by
    simp [List.idxOf_append, htl]
  have hidxl_lt : ∀ x, x ∈ l → l.idxOf x < l.length := fun x hx =>
    List.idxOf_lt_length_of_mem hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hnew]
    exact List.Nodup.append hnodupl hnodup' (fun x hx hxv => hlv x hx hxv)
  · intro x
    rw [hnew, mem_decomposeWith_T, hmemu x, hmem' x]
    constructor
    · rintro (⟨hx, hxt⟩ | hx)
      · rcases List.mem_append.1 hx with hx' | hx'
        · exact List.mem_append_left _ hx'
        · simp only [List.mem_singleton] at hx'
          exact absurd hx' hxt
      · exact List.mem_append_right _ hx
    · intro hx
      rcases List.mem_append.1 hx with hx' | hx'
      · refine Or.inl ⟨List.mem_append_left _ hx', ?_⟩
        rintro rfl
        exact htl hx'
      · exact Or.inr hx'
  · rw [List.map_append, List.map_append]
    congr 1
    · rw [← hlabels]
      refine List.map_congr_left ?_
      intro x hx
      simp [decomposeWith_α, hlT' x hx]
    · rw [← hlabels']
      refine List.map_congr_left ?_
      intro x hx
      have hxv : x ∈ v := by
        rw [hv]
        cases tail' <;> simp [hx]
      simp [decomposeWith_α, (hmem' x).2 hxv]
  · intro p hp
    have hpv : p.1 ∈ v := by rw [hv, hp]; simp
    have hpT : p.1 ∈ tn'.T := (hmem' p.1).2 hpv
    simp only [decomposeWith_α, hpT, if_true]
    exact htail' p hp
  · intro x y
    rw [hnew, decomposeWith_ord_iff]
    constructor
    · rintro (hord | ⟨hord, hy⟩ | ⟨hord, hx⟩ | ⟨hord, hxt, hyt⟩)
      · -- both tasks come from the inserted network
        obtain ⟨hx, hy, hlt⟩ := (hord' x y).1 hord
        refine ⟨List.mem_append_right _ hx, List.mem_append_right _ hy, ?_⟩
        rw [hidxv x hx, hidxv y hy]
        omega
      · -- an old task ordered before the decomposed task, and an inserted task
        obtain ⟨hxu, -, hlt⟩ := (hordu x t).1 hord
        have hxl : x ∈ l := by
          rcases List.mem_append.1 hxu with h | h
          · exact h
          · simp only [List.mem_singleton] at h
            subst h
            exact absurd hlt (lt_irrefl _)
        have hyv : y ∈ v := (hmem' y).1 hy
        refine ⟨List.mem_append_left _ hxl, List.mem_append_right _ hyv, ?_⟩
        rw [hidxl x hxl, hidxv y hyv]
        have := hidxl_lt x hxl
        omega
      · -- the decomposed task has no successor: impossible
        exfalso
        obtain ⟨-, hyu, hlt⟩ := (hordu t y).1 hord
        have hylen : (l ++ [t]).idxOf y < (l ++ [t]).length :=
          List.idxOf_lt_length_of_mem hyu
        rw [hidxtu] at hlt
        simp only [List.length_append, List.length_cons, List.length_nil] at hylen
        omega
      · -- two old tasks
        obtain ⟨hxu, hyu, hlt⟩ := (hordu x y).1 hord
        have hxl : x ∈ l := by
          rcases List.mem_append.1 hxu with h | h
          · exact h
          · simp only [List.mem_singleton] at h
            exact absurd h hxt
        have hyl : y ∈ l := by
          rcases List.mem_append.1 hyu with h | h
          · exact h
          · simp only [List.mem_singleton] at h
            exact absurd h hyt
        refine ⟨List.mem_append_left _ hxl, List.mem_append_left _ hyl, ?_⟩
        rw [hidxl x hxl, hidxl y hyl]
        rwa [hidxlu x hxl, hidxlu y hyl] at hlt
    · rintro ⟨hx, hy, hlt⟩
      rcases List.mem_append.1 hx with hxl | hxv
      · rcases List.mem_append.1 hy with hyl | hyv
        · -- two old tasks
          refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
          · refine (hordu x y).2 ⟨List.mem_append_left _ hxl, List.mem_append_left _ hyl, ?_⟩
            rw [hidxl x hxl, hidxl y hyl] at hlt
            rwa [hidxlu x hxl, hidxlu y hyl]
          · rintro rfl; exact htl hxl
          · rintro rfl; exact htl hyl
        · -- an old task followed by an inserted task
          refine Or.inr (Or.inl ⟨?_, (hmem' y).2 hyv⟩)
          refine (hordu x t).2 ⟨List.mem_append_left _ hxl, by simp, ?_⟩
          rw [hidxlu x hxl, hidxtu]
          exact hidxl_lt x hxl
      · rcases List.mem_append.1 hy with hyl | hyv
        · -- an inserted task before an old task: impossible
          exfalso
          rw [hidxl y hyl, hidxv x hxv] at hlt
          have := hidxl_lt y hyl
          omega
        · -- two inserted tasks
          refine Or.inl ((hord' x y).2 ⟨hxv, hyv, ?_⟩)
          rw [hidxv x hxv, hidxv y hyv] at hlt
          omega


/-! ### Chains are transported along isomorphisms -/

/-- Injective renaming does not change the position of an element in a list. -/
lemma idxOf_map_of_injOn {l : List I} {σ : I → I}
    (hinj : ∀ x ∈ l, ∀ y ∈ l, σ x = σ y → x = y) {x : I} (hx : x ∈ l) :
    (l.map σ).idxOf (σ x) = l.idxOf x := by
  classical
  induction l with
  | nil => simp at hx
  | cons a l ih =>
      by_cases hxa : x = a
      · subst hxa
        simp
      · have hxl : x ∈ l := by
          rcases List.mem_cons.1 hx with h | h
          · exact absurd h hxa
          · exact h
        have hne : σ x ≠ σ a := by
          intro hcon
          exact hxa (hinj x hx a (by simp) hcon)
        have hinj' : ∀ u ∈ l, ∀ v ∈ l, σ u = σ v → u = v := by
          intro u hu v hv huv
          exact hinj u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv) huv
        simp only [List.map_cons, List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
        rw [if_neg (Ne.symm hne), if_neg (Ne.symm hxa), ih hinj' hxl]

/-- **Chains are invariant under renaming of the task identifiers.** -/
lemma IsChain.iso {tn tn' : TaskNetwork I A C} {l : List I} {os : List A}
    {tail : Option (I × C)} (h : IsChain tn l os tail) (hwf' : tn'.WF) (hiso : tn.Iso tn') :
    ∃ (l₂ : List I) (tail₂ : Option (I × C)),
      IsChain tn' l₂ os tail₂ ∧ tail₂.map Prod.snd = tail.map Prod.snd := by
  classical
  obtain ⟨σ, hbij, hord, hα⟩ := hiso
  have hmemT : ∀ x, x ∈ tn.T ↔ x ∈ chainIds l tail := h.memT
  have hmapsTo : ∀ x, x ∈ chainIds l tail → σ x ∈ tn'.T := by
    intro x hx
    simpa using hbij.mapsTo (by simpa using (hmemT x).2 hx)
  have hinj : ∀ x ∈ chainIds l tail, ∀ y ∈ chainIds l tail, σ x = σ y → x = y := by
    intro x hx y hy hxy
    exact hbij.injOn (by simpa using (hmemT x).2 hx) (by simpa using (hmemT y).2 hy) hxy
  have hchainmap : chainIds (l.map σ) (tail.map (fun p => (σ p.1, p.2))) =
      (chainIds l tail).map σ := by
    cases tail <;> simp
  have hinjl : ∀ x ∈ l, ∀ y ∈ l, σ x = σ y → x = y := by
    intro x hx y hy hxy
    refine hinj x ?_ y ?_ hxy <;> cases tail <;> simp [hx, hy]
  refine ⟨l.map σ, tail.map (fun p => (σ p.1, p.2)), ⟨?_, ?_, ?_, ?_, ?_⟩, by cases tail <;> simp⟩
  · rw [hchainmap]
    exact List.Nodup.map_on hinj h.nodup
  · intro x
    rw [hchainmap]
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hbij.surjOn (by simpa using hx)
      exact List.mem_map.2 ⟨y, (hmemT y).1 (by simpa using hy), rfl⟩
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hmapsTo y hy
  · rw [List.map_map, ← h.labels]
    refine List.map_congr_left ?_
    intro x hx
    have hxT : x ∈ tn.T := h.mem_of_mem_l hx
    exact (hα x hxT).symm
  · rintro p hp
    cases tail with
    | none => simp at hp
    | some q =>
        simp only [Option.map_some] at hp
        have hq : q.1 ∈ tn.T := h.mem_tail rfl
        have := h.tailLabel q rfl
        rw [hα q.1 hq] at this
        simp only [Option.some.injEq] at hp
        subst hp
        exact this
  · intro x y
    rw [hchainmap]
    constructor
    · intro hxy
      have hxT : x ∈ tn'.T := hwf'.mem_left hxy
      have hyT : y ∈ tn'.T := hwf'.mem_right hxy
      obtain ⟨a, ha, rfl⟩ := hbij.surjOn (by simpa using hxT)
      obtain ⟨b, hb, rfl⟩ := hbij.surjOn (by simpa using hyT)
      have haT : a ∈ tn.T := by simpa using ha
      have hbT : b ∈ tn.T := by simpa using hb
      have hab : tn.ord a b := (hord a haT b hbT).2 hxy
      obtain ⟨ha', hb', hlt⟩ := (h.ord a b).1 hab
      refine ⟨List.mem_map_of_mem ha', List.mem_map_of_mem hb', ?_⟩
      rw [idxOf_map_of_injOn hinj ha', idxOf_map_of_injOn hinj hb']
      exact hlt
    · rintro ⟨hx, hy, hlt⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      rw [idxOf_map_of_injOn hinj ha, idxOf_map_of_injOn hinj hb] at hlt
      have hab : tn.ord a b := (h.ord a b).2 ⟨ha, hb, hlt⟩
      exact (hord a ((hmemT a).2 ha) b ((hmemT b).2 hb)).1 hab

end Chain

end TaskNetwork

/-! ### Method bodies and derivations -/

namespace Method

variable [DecidableEq I]

/-- The *body* of a method of a totally ordered regular problem: the method decomposes its
compound task into the sequence `os` of primitive tasks followed by the optional compound task
`next`. -/
def HasBody (m : Method I A C) (os : List A) (next : Option C) : Prop :=
  ∃ (l : List I) (tail : Option (I × C)),
    m.subtasks.IsChain l os tail ∧ tail.map Prod.snd = next

/-- **The body of a method is unique.**  A method whose subtask network is a chain has exactly
one body: the actions of its primitive tasks, in their (unique) order, and the compound task it
leaves open. -/
lemma HasBody.unique {m : Method I A C} {os os' : List A} {next next' : Option C}
    (h : m.HasBody os next) (h' : m.HasBody os' next') : os = os' ∧ next = next' := by
  obtain ⟨l, tail, hchain, htail⟩ := h
  obtain ⟨l', tail', hchain', htail'⟩ := h'
  have hM : TaskNetwork.chainIds l tail = TaskNetwork.chainIds l' tail' :=
    hchain'.linearization_eq hchain.isLinearization
  have hmapinj : ∀ {u v : List A}, u.map (Sum.inl (β := C)) = v.map Sum.inl → u = v :=
    fun {u v} huv => List.map_injective_iff.2 (fun _ _ hxy => Sum.inl_injective hxy) huv
  have habs : ∀ (p : I × C), tail = some p → tail' = none → False := by
    intro p hp hp'
    subst hp'
    have hmem : p.1 ∈ l' := by
      have hmem0 : p.1 ∈ TaskNetwork.chainIds l tail := by rw [hp]; simp
      rw [hM] at hmem0
      simpa using hmem0
    have hprim : m.subtasks.IsPrimitiveId p.1 := by
      have hmemmap : m.subtasks.α p.1 ∈ l'.map m.subtasks.α := List.mem_map_of_mem hmem
      rw [hchain'.labels] at hmemmap
      obtain ⟨a, -, ha⟩ := List.mem_map.1 hmemmap
      exact ⟨a, ha.symm⟩
    obtain ⟨a, ha⟩ := hprim
    have hlab := hchain.tailLabel p hp
    rw [ha] at hlab
    exact absurd hlab (by simp)
  have habs' : ∀ (p : I × C), tail' = some p → tail = none → False := by
    intro p hp hp'
    subst hp'
    have hmem : p.1 ∈ l := by
      have hmem0 : p.1 ∈ TaskNetwork.chainIds l' tail' := by rw [hp]; simp
      rw [← hM] at hmem0
      simpa using hmem0
    have hprim : m.subtasks.IsPrimitiveId p.1 := by
      have hmemmap : m.subtasks.α p.1 ∈ l.map m.subtasks.α := List.mem_map_of_mem hmem
      rw [hchain.labels] at hmemmap
      obtain ⟨a, -, ha⟩ := List.mem_map.1 hmemmap
      exact ⟨a, ha.symm⟩
    obtain ⟨a, ha⟩ := hprim
    have hlab := hchain'.tailLabel p hp
    rw [ha] at hlab
    exact absurd hlab (by simp)
  cases htaileq : tail with
  | none =>
      cases htaileq' : tail' with
      | none =>
          subst htaileq; subst htaileq'
          simp only [TaskNetwork.chainIds_none] at hM
          subst hM
          have : os.map (Sum.inl (β := C)) = os'.map Sum.inl := by
            rw [← hchain.labels, ← hchain'.labels]
          exact ⟨hmapinj this, by rw [← htail, ← htail']⟩
      | some q =>
          exact absurd (habs' q htaileq' htaileq) (by simp)
  | some p =>
      cases htaileq' : tail' with
      | none => exact absurd (habs p htaileq htaileq') (by simp)
      | some q =>
          subst htaileq; subst htaileq'
          simp only [TaskNetwork.chainIds_some] at hM
          obtain ⟨hll, hpq⟩ : l = l' ∧ [p.1] = [q.1] :=
            List.append_inj' hM (by simp)
          have hp1 : p.1 = q.1 := by simpa using hpq
          subst hll
          have hlabels : os.map (Sum.inl (β := C)) = os'.map Sum.inl := by
            rw [← hchain.labels, ← hchain'.labels]
          have hp2 : p.2 = q.2 := by
            have h1 := hchain.tailLabel p rfl
            have h2 := hchain'.tailLabel q rfl
            rw [← hp1] at h2
            rw [h1] at h2
            simpa using h2
          refine ⟨hmapinj hlabels, ?_⟩
          rw [← htail, ← htail']
          simp [hp2]

/-- Every well-formed, regular and totally ordered method has a body. -/
lemma exists_hasBody {m : Method I A C} (hwf : m.subtasks.WF) (hreg : m.subtasks.IsRegular)
    (hTO : m.subtasks.IsTotallyOrdered) : ∃ os next, m.HasBody os next := by
  obtain ⟨l, os, tail, hchain⟩ := TaskNetwork.exists_isChain hwf hreg hTO
  exact ⟨os, tail.map Prod.snd, l, tail, hchain, rfl⟩

end Method

namespace Problem

variable [DecidableEq I]

/-- **Derivations of a regular problem.**  `P.Derives c as` states that the compound task `c`
can be decomposed — by a chain of methods, each continuing the compound task left over by the
previous one — into the primitive action sequence `as`. -/
inductive Derives (P : Problem F A C I) : C → List A → Prop
  /-- The last method of the derivation leaves no compound task. -/
  | last {c : C} {os : List A} {m : Method I A C} (hm : m ∈ P.methods)
      (hc : m.abstractTask = c) (hb : m.HasBody os none) : P.Derives c os
  /-- A method leaving the compound task `c'`, which is derived in turn. -/
  | cons {c c' : C} {os rest : List A} {m : Method I A C} (hm : m ∈ P.methods)
      (hc : m.abstractTask = c) (hb : m.HasBody os (some c')) (h : P.Derives c' rest) :
      P.Derives c (os ++ rest)

/-- The continuation invariant of the normal form proof: the actions `os` produced so far,
together with a derivation of the compound task still open (if any), yield a derivation of the
initial compound task. -/
def ContDerives (P : Problem F A C I) (c₀ : C) (os : List A) (tail : Option (I × C)) : Prop :=
  match tail with
  | none => P.Derives c₀ os
  | some p => ∀ rest, P.Derives p.2 rest → P.Derives c₀ (os ++ rest)

end Problem

namespace Problem

/-! ### The normal form theorem -/

section NormalForm

variable [DecidableEq I] {P : Problem F A C I}

open TaskNetwork

/-- A problem whose initial task network is the single compound task `c₀` starts from the empty
chain. -/
lemma isChain_tnI (hwf : P.tnI.WF) {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀})
    (hα : P.tnI.α t₀ = Sum.inr c₀) : P.tnI.IsChain [] [] (some (t₀, c₀)) := by
  refine ⟨by simp, ?_, rfl, ?_, ?_⟩
  · intro x; rw [hT]; simp
  · intro p hp
    simp only [Option.some.injEq] at hp
    subst hp
    exact hα
  · intro x y
    constructor
    · intro hord
      exfalso
      have hx : x ∈ P.tnI.T := hwf.mem_left hord
      have hy : y ∈ P.tnI.T := hwf.mem_right hord
      rw [hT] at hx hy
      simp only [Finset.mem_singleton] at hx hy
      subst hx; subst hy
      exact hwf.irrefl _ hord
    · rintro ⟨hx, hy, hlt⟩
      simp only [chainIds_some, List.nil_append, List.mem_singleton] at hx hy
      subst hx; subst hy
      exact absurd hlt (lt_irrefl _)

/-- In a chain, the only task that can be decomposed is the trailing compound task. -/
lemma decompStep_tail_eq {tn₁ tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    {l : List I} {os : List A} {tail : Option (I × C)}
    (hchain : tn₁.IsChain l os tail) (hstep : DecompStep P.methods tn₁ t m tn₂) :
    tail = some (t, m.abstractTask) := by
  obtain ⟨-, htT, hαt, -⟩ := hstep
  have hmem : t ∈ chainIds l tail := (hchain.memT t).1 htT
  cases htail : tail with
  | none =>
      exfalso
      subst htail
      obtain ⟨a, ha⟩ := hchain.isPrimitive t htT
      rw [ha] at hαt
      exact absurd hαt (by simp)
  | some p =>
      rw [htail] at hmem
      simp only [chainIds_some, List.mem_append, List.mem_singleton] at hmem
      have hpl : tn₁.α p.1 = Sum.inr p.2 := hchain.tailLabel p htail
      have htp : t = p.1 := by
        rcases hmem with hml | hmr
        · exfalso
          have hprim : tn₁.IsPrimitiveId t := by
            have hmemmap : tn₁.α t ∈ l.map tn₁.α := List.mem_map_of_mem hml
            rw [hchain.labels] at hmemmap
            obtain ⟨a, -, ha⟩ := List.mem_map.1 hmemmap
            exact ⟨a, ha.symm⟩
          obtain ⟨a, ha⟩ := hprim
          rw [ha] at hαt
          exact absurd hαt (by simp)
        · exact hmr
      subst htp
      rw [hpl] at hαt
      simp only [Sum.inr.injEq] at hαt
      rw [← hαt]

/-- **One decomposition step of a chain.**  Decomposing the trailing compound task of a chain
with a well-formed, regular and totally ordered method yields a chain whose action sequence
extends the previous one by the body of the method. -/
lemma isChain_of_decompStep {tn₁ tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    {l : List I} {os : List A} {c : C}
    (hwfm : m.subtasks.WF) (hregm : m.subtasks.IsRegular) (hTOm : m.subtasks.IsTotallyOrdered)
    (hchain : tn₁.IsChain l os (some (t, c))) (hstep : DecompStep P.methods tn₁ t m tn₂) :
    ∃ (l' : List I) (os' : List A) (tail' : Option (I × C)),
      tn₂.IsChain (l ++ l') (os ++ os') tail' ∧ m.HasBody os' (tail'.map Prod.snd) := by
  obtain ⟨-, htT, -, tn', hwf', hiso', hdisj, rfl⟩ := hstep
  haveI : Nonempty I := ⟨t⟩
  obtain ⟨lm, osm, tailm, hchainm⟩ := TaskNetwork.exists_isChain hwfm hregm hTOm
  obtain ⟨l₂, tail₂, hchain₂, htail₂⟩ := hchainm.iso hwf' hiso'.symm
  refine ⟨l₂, osm, tail₂, isChain_decomposeWith hchain hchain₂ hdisj, ?_⟩
  exact ⟨lm, tailm, hchainm, htail₂.symm⟩

/-- **Every reachable task network of a totally ordered regular problem is a chain**, and the
actions produced so far together with the open compound task derive the initial task. -/
theorem exists_chain_contDerives (hwf : P.WF) (hreg : P.IsRegularM) (hto : P.IsTO_M)
    {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀)
    {tn : TaskNetwork I A C} (hreach : P.Reachable tn) :
    ∃ (l : List I) (os : List A) (tail : Option (I × C)),
      tn.IsChain l os tail ∧ P.ContDerives c₀ os tail := by
  induction hreach with
  | refl =>
      refine ⟨[], [], some (t₀, c₀), isChain_tnI hwf.tnI hT hα, ?_⟩
      intro rest hrest
      simpa using hrest
  | tail hprefix hstep ih =>
      obtain ⟨l, os, tail, hchain, hcont⟩ := ih
      obtain ⟨t, m, hs⟩ := hstep
      have hmr : P.ReachableMethod m := Problem.reachableMethod_of_decomposesTo hprefix hs
      have htail : tail = some (t, m.abstractTask) := decompStep_tail_eq hchain hs
      subst htail
      obtain ⟨l', os', tail', hchain', hbody⟩ :=
        isChain_of_decompStep (hwf.methods m hmr.1) (hreg m hmr) (hto m hmr) hchain hs
      refine ⟨l ++ l', os ++ os', tail', hchain', ?_⟩
      cases htail' : tail' with
      | none =>
          show P.Derives c₀ (os ++ os')
          refine hcont os' ?_
          exact Derives.last hmr.1 rfl (by rw [htail'] at hbody; simpa using hbody)
      | some p =>
          show ∀ rest, P.Derives p.2 rest → P.Derives c₀ ((os ++ os') ++ rest)
          intro rest hrest
          rw [List.append_assoc]
          refine hcont (os' ++ rest) ?_
          exact Derives.cons hmr.1 rfl (by rw [htail'] at hbody; simpa using hbody) hrest

/-- **Every solution plan of a totally ordered regular problem is a derivation.** -/
theorem derives_of_isSolutionPlan (hwf : P.WF) (hreg : P.IsRegularM) (hto : P.IsTO_M)
    {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀)
    {as : List A} (hsol : P.IsSolutionPlan as) : P.Derives c₀ as := by
  obtain ⟨tn, lin, hreach, hprim, hlin, hseq, -, -⟩ := hsol
  obtain ⟨l, os, tail, hchain, hcont⟩ := exists_chain_contDerives hwf hreg hto hT hα hreach
  cases htail : tail with
  | none =>
      subst htail
      have : as = os := hchain.actionSeq_unique hlin hseq
      subst this
      exact hcont
  | some p =>
      exfalso
      subst htail
      have hpT : p.1 ∈ tn.T := hchain.mem_tail rfl
      obtain ⟨a, ha⟩ := hprim p.1 hpT
      have := hchain.tailLabel p rfl
      rw [ha] at this
      exact absurd this (by simp)

/-- **Every derivation of the open compound task of a reachable chain yields a solution.** -/
theorem exists_closed_chain_of_derives [Infinite I] (hwf : P.WF)
    {rest : List A} {c : C} (hd : P.Derives c rest) :
    ∀ {tn : TaskNetwork I A C} {l : List I} {pre : List A} {t : I},
      tn.IsChain l pre (some (t, c)) → P.Reachable tn →
      ∃ (tn₂ : TaskNetwork I A C) (l₂ : List I),
        P.Reachable tn₂ ∧ tn₂.IsChain l₂ (pre ++ rest) none := by
  induction hd with
  | @last c os m hm hc hb =>
      intro tn l pre t hchain hreach
      obtain ⟨lm, tailm, hchainm, htailm⟩ := hb
      have htailm' : tailm = none := by
        cases tailm with
        | none => rfl
        | some q => simp at htailm
      subst htailm'
      obtain ⟨tn', hwf', hiso', hdisj⟩ :=
        TaskNetwork.exists_fresh_iso_copy m.subtasks (hwf.methods m hm) tn.T
      haveI : Nonempty I := ⟨t⟩
      obtain ⟨l₂, tail₂, hchain₂, htail₂⟩ := hchainm.iso hwf' hiso'.symm
      have htail₂' : tail₂ = none := by
        cases tail₂ with
        | none => rfl
        | some q => simp at htail₂
      subst htail₂'
      have hstep : DecompStep P.methods tn t m (decomposeWith tn t tn') := by
        refine ⟨hm, hchain.mem_tail rfl, ?_, tn', hwf', hiso', hdisj, rfl⟩
        have := hchain.tailLabel (t, c) rfl
        simpa [hc] using this
      exact ⟨decomposeWith tn t tn', l ++ l₂,
        Relation.ReflTransGen.tail hreach ⟨t, m, hstep⟩,
        isChain_decomposeWith hchain hchain₂ hdisj⟩
  | @cons c c' os rest m hm hc hb h ih =>
      intro tn l pre t hchain hreach
      obtain ⟨lm, tailm, hchainm, htailm⟩ := hb
      obtain ⟨q, htailmq⟩ : ∃ q : I × C, tailm = some q := by
        cases tailm with
        | none => simp at htailm
        | some q => exact ⟨q, rfl⟩
      subst htailmq
      obtain ⟨tn', hwf', hiso', hdisj⟩ :=
        TaskNetwork.exists_fresh_iso_copy m.subtasks (hwf.methods m hm) tn.T
      haveI : Nonempty I := ⟨t⟩
      obtain ⟨l₂, tail₂, hchain₂, htail₂⟩ := hchainm.iso hwf' hiso'.symm
      obtain ⟨q₂, htail₂q⟩ : ∃ q₂ : I × C, tail₂ = some q₂ := by
        cases tail₂ with
        | none => simp at htail₂
        | some q₂ => exact ⟨q₂, rfl⟩
      subst htail₂q
      have hq₂ : q₂.2 = c' := by
        have h1 : q₂.2 = q.2 := by simpa using htail₂
        have h2 : q.2 = c' := by simpa using htailm
        rw [h1, h2]
      have hstep : DecompStep P.methods tn t m (decomposeWith tn t tn') := by
        refine ⟨hm, hchain.mem_tail rfl, ?_, tn', hwf', hiso', hdisj, rfl⟩
        have := hchain.tailLabel (t, c) rfl
        simpa [hc] using this
      have hchain' : (decomposeWith tn t tn').IsChain (l ++ l₂) (pre ++ os) (some (q₂.1, c')) := by
        have := isChain_decomposeWith hchain hchain₂ hdisj
        rwa [show (some q₂ : Option (I × C)) = some (q₂.1, c') by rw [← hq₂]] at this
      obtain ⟨tn₃, l₃, hreach₃, hchain₃⟩ := ih hchain'
        (Relation.ReflTransGen.tail hreach ⟨t, m, hstep⟩)
      exact ⟨tn₃, l₃, hreach₃, by rwa [List.append_assoc] at hchain₃⟩

/-- **Normal form theorem for totally ordered regular problems.**  A well-formed, regular,
totally ordered HTN planning problem whose initial task network is a single compound task `c₀`
is solvable exactly when there is a derivation of `c₀` whose action sequence is executable in
the initial state and reaches the goal. -/
theorem solvable_iff_derives [Infinite I] (hwf : P.WF) (hreg : P.IsRegularM) (hto : P.IsTO_M)
    {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀) :
    P.Solvable ↔ ∃ as : List A, P.Derives c₀ as ∧ P.SeqApplicable as P.init ∧
      P.GoalState (P.transitionSeq as P.init) := by
  constructor
  · intro h
    obtain ⟨as, hplan⟩ := solvable_iff_exists_solutionPlan.1 h
    have hplan' := hplan
    obtain ⟨-, -, -, -, -, -, happ, hgoal⟩ := hplan'
    exact ⟨as, derives_of_isSolutionPlan hwf hreg hto hT hα hplan, happ, hgoal⟩
  · rintro ⟨as, hd, happ, hgoal⟩
    obtain ⟨tn₂, l₂, hreach₂, hchain₂⟩ :=
      exists_closed_chain_of_derives hwf hd (isChain_tnI hwf.tnI hT hα)
        Relation.ReflTransGen.refl
    refine ⟨tn₂, hreach₂, hchain₂.isPrimitive, l₂, as, ?_, ?_, happ, hgoal⟩
    · simpa using hchain₂.isLinearization
    · simpa using hchain₂.isActionSeq

end NormalForm

end Problem

end HTN
