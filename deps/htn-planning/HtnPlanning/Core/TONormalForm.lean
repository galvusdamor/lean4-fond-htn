import HtnPlanning.Core.ProofTuples
import HtnPlanning.Regular.RegularNormalForm
/-!
# A normal form for totally ordered HTN problems

A *totally ordered* task network is nothing but a sequence of task names: its task ids can be
enumerated in one linear order `l`, and the labels `xs = l.map α` determine the network up to
renaming of the ids.  Decomposing the `i`-th task of such a network with a (totally ordered)
method body `bs` replaces the `i`-th entry of `xs` by `bs`.  Totally ordered HTN planning is
therefore exactly *derivation in a context-free grammar* whose non-terminals are the compound
task names and whose terminals are the actions.

This file makes that precise:

* `TaskNetwork.IsSeqNet tn l xs` — the network `tn` is the sequence of tasks `l` labelled `xs`,
  ordered linearly along `l`;
* `TaskNetwork.exists_isSeqNet` — every well-formed totally ordered network is of this shape;
* `TaskNetwork.isSeqNet_decomposeWith` — decomposing a task of a sequence network by a
  sequence network replaces the corresponding entry of the label list (the *context-free
  substitution*);
* `HTN.Domain.YieldSeq xs as` — the leftmost-derivation relation: the task sequence `xs` can be
  refined into the action sequence `as`;
* `Problem.solvable_iff_yieldSeq` — **the normal form theorem**: a well-formed totally ordered
  problem is solvable iff its initial task sequence yields an executable action sequence
  reaching the goal.

Together with `HTN.Domain.provable_iff_yield` of `HtnPlanning/Core/ProofTuples.lean` this
gives the characterisation of solvability of a totally ordered problem by the proof tuples
`(s, T, s')` of Erol, Hendler and Nau (`Problem.solvable_iff_provable`), which is the source
side of the compilation of totally ordered problems into acyclic ones
(`HtnComplexity/ToHtnAc/ToHtnAc.lean`).

The counterpart of this file for *regular* problems is
`HtnPlanning/Regular/RegularNormalForm.lean`; there a reachable network is a chain with at most
one open compound task at its end, here it is an arbitrary sequence of open compound tasks.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace TaskNetwork

section Seq

variable [DecidableEq I]

/-- If a list is pairwise `R` then earlier elements are `R`-related to later ones. -/
lemma rel_of_idxOf_lt {R : I → I → Prop} {l : List I} (hp : l.Pairwise R) {x y : I}
    (hx : x ∈ l) (hy : y ∈ l) (h : l.idxOf x < l.idxOf y) : R x y := by
  rw [List.pairwise_iff_getElem] at hp
  have hxl : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have hyl : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hy
  have := hp (l.idxOf x) (l.idxOf y) hxl hyl h
  rwa [List.getElem_idxOf, List.getElem_idxOf] at this

/-- **Sequence networks.**  `IsSeqNet tn l xs` states that the task network `tn` consists of
the tasks `l`, labelled by the task names `xs`, and that its ordering is the linear order of
the enumeration `l`. -/
structure IsSeqNet (tn : TaskNetwork I A C) (l : List I) (xs : List (A ⊕ C)) : Prop where
  /-- The task ids are pairwise distinct. -/
  nodup : l.Nodup
  /-- The task ids of the network are exactly those of the sequence. -/
  memT : ∀ x, x ∈ tn.T ↔ x ∈ l
  /-- The tasks are labelled by `xs`. -/
  labels : l.map tn.α = xs
  /-- The ordering is the linear order of the sequence. -/
  ord : ∀ x y, tn.ord x y ↔ (x ∈ l ∧ y ∈ l ∧ l.idxOf x < l.idxOf y)

namespace IsSeqNet

variable {tn : TaskNetwork I A C} {l : List I} {xs : List (A ⊕ C)}

lemma mem_of_mem (h : IsSeqNet tn l xs) {y : I} (hy : y ∈ l) : y ∈ tn.T := (h.memT y).2 hy

lemma length_eq (h : IsSeqNet tn l xs) : l.length = xs.length := by
  rw [← h.labels, List.length_map]

/-- A sequence network is well formed. -/
lemma wf (h : IsSeqNet tn l xs) : tn.WF where
  mem_left := fun hab => (h.memT _).2 ((h.ord _ _).1 hab).1
  mem_right := fun hab => (h.memT _).2 ((h.ord _ _).1 hab).2.1
  irrefl := fun a hcon => absurd ((h.ord a a).1 hcon).2.2 (lt_irrefl _)
  trans := by
    intro a b c hab hbc
    obtain ⟨ha, -, hab'⟩ := (h.ord a b).1 hab
    obtain ⟨-, hc, hbc'⟩ := (h.ord b c).1 hbc
    exact (h.ord a c).2 ⟨ha, hc, lt_trans hab' hbc'⟩

/-- A sequence network is totally ordered. -/
lemma isTotallyOrdered (h : IsSeqNet tn l xs) : tn.IsTotallyOrdered := by
  intro s hs t ht hst
  have hs' : s ∈ l := (h.memT s).1 hs
  have ht' : t ∈ l := (h.memT t).1 ht
  have hne : l.idxOf s ≠ l.idxOf t := fun hcon => hst (idxOf_inj_of_mem hs' ht' hcon)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl ((h.ord s t).2 ⟨hs', ht', hlt⟩)
  · exact Or.inr ((h.ord t s).2 ⟨ht', hs', hgt⟩)

/-- The enumeration of a sequence network is a linearization of it. -/
lemma isLinearization (h : IsSeqNet tn l xs) : tn.IsLinearization l := by
  refine ⟨h.nodup, fun t => (h.memT t).symm, ?_⟩
  have hpair : l.Pairwise (fun a b => l.idxOf a < l.idxOf b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.Nodup.idxOf_getElem h.nodup, List.Nodup.idxOf_getElem h.nodup]
    exact hij
  refine List.Pairwise.imp ?_ hpair
  intro a b hab hcon
  exact absurd ((h.ord b a).1 hcon).2.2 (by omega)

/-- The tasks of a sequence network are pairwise ordered along the enumeration. -/
lemma pairwise_ord (h : IsSeqNet tn l xs) : l.Pairwise tn.ord := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  refine (h.ord _ _).2 ⟨List.getElem_mem _, List.getElem_mem _, ?_⟩
  rw [List.Nodup.idxOf_getElem h.nodup, List.Nodup.idxOf_getElem h.nodup]
  exact hij

/-- **The linearization of a sequence network is unique.** -/
lemma linearization_eq (h : IsSeqNet tn l xs) {m : List I} (hlin : tn.IsLinearization m) :
    m = l := by
  classical
  have hsorted : ∀ u : List I, u.Nodup → (∀ t, t ∈ u ↔ t ∈ tn.T) →
      u.Pairwise (fun a b => ¬ tn.ord b a) → u.Pairwise (fun a b => l.idxOf a < l.idxOf b) := by
    intro u hnodup hmem hpair
    have hcomb : u.Pairwise (fun a b => (¬ tn.ord b a) ∧ a ≠ b) :=
      List.Pairwise.and hpair hnodup
    refine List.Pairwise.imp_of_mem ?_ hcomb
    rintro a b ha hb ⟨hnord, hne⟩
    have haT : a ∈ l := (h.memT a).1 ((hmem a).1 ha)
    have hbT : b ∈ l := (h.memT b).1 ((hmem b).1 hb)
    have hidx : l.idxOf a ≠ l.idxOf b := fun hcon => hne (idxOf_inj_of_mem haT hbT hcon)
    rcases lt_or_gt_of_ne hidx with hlt | hgt
    · exact hlt
    · exact absurd ((h.ord b a).2 ⟨hbT, haT, hgt⟩) hnord
  have hperm : m.Perm l := by
    refine (List.perm_ext_iff_of_nodup hlin.1 h.nodup).2 ?_
    intro t
    rw [hlin.2.1 t, h.memT t]
  have h₁ : m.Pairwise (fun a b => l.idxOf a < l.idxOf b) := hsorted m hlin.1 hlin.2.1 hlin.2.2
  have h₂ : l.Pairwise (fun a b => l.idxOf a < l.idxOf b) :=
    hsorted l h.nodup (fun t => (h.memT t).symm) h.isLinearization.2.2
  refine List.Perm.eq_of_pairwise ?_ h₁ h₂ hperm
  intro a b _ _ hab hba
  exact absurd (lt_trans hab hba) (lt_irrefl _)

/-- A sequence network all of whose labels are actions is primitive. -/
lemma isPrimitive_of_labels {as : List A} (h : IsSeqNet tn l (as.map Sum.inl)) :
    tn.IsPrimitive := by
  intro t ht
  have htl : t ∈ l := (h.memT t).1 ht
  have hmem : tn.α t ∈ l.map tn.α := List.mem_map_of_mem htl
  rw [h.labels] at hmem
  obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
  exact ⟨a, ha.symm⟩

/-- The action sequence of a primitive sequence network. -/
lemma isActionSeq_of_labels {as : List A} (h : IsSeqNet tn l (as.map Sum.inl)) :
    tn.IsActionSeq l as := h.labels

/-- **The action sequence of a primitive sequence network is its label list.**  Every
linearization of it induces the same action sequence. -/
lemma actionSeq_eq {as bs : List A} (h : IsSeqNet tn l (as.map Sum.inl)) {m : List I}
    (hlin : tn.IsLinearization m) (hseq : tn.IsActionSeq m bs) : bs = as := by
  have hml : m = l := h.linearization_eq hlin
  subst hml
  exact isActionSeq_unique hseq h.isActionSeq_of_labels

end IsSeqNet

/-- **A well-formed network whose tasks can be enumerated in a linear order is a sequence
network.** -/
lemma isSeqNet_of_pairwise_ord {tn : TaskNetwork I A C} {l : List I} (hwf : tn.WF)
    (hnd : l.Nodup) (hmem : ∀ t, t ∈ tn.T ↔ t ∈ l) (hpair : l.Pairwise tn.ord) :
    tn.IsSeqNet l (l.map tn.α) := by
  refine ⟨hnd, hmem, rfl, fun a b => ?_⟩
  constructor
  · intro hab
    have ha : a ∈ l := (hmem a).1 (hwf.mem_left hab)
    have hb : b ∈ l := (hmem b).1 (hwf.mem_right hab)
    refine ⟨ha, hb, ?_⟩
    rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with hlt | heq | hgt
    · exact hlt
    · exact absurd (idxOf_inj_of_mem ha hb heq ▸ hab) (hwf.irrefl a)
    · exact absurd (rel_of_idxOf_lt hpair hb ha hgt) (fun h' => hwf.asymm hab h')
  · rintro ⟨ha, hb, hlt⟩
    exact rel_of_idxOf_lt hpair ha hb hlt

/-- **Every well-formed, totally ordered task network is a sequence network.** -/
theorem exists_isSeqNet {tn : TaskNetwork I A C} (hwf : tn.WF) (hTO : tn.IsTotallyOrdered) :
    ∃ (l : List I) (xs : List (A ⊕ C)), tn.IsSeqNet l xs := by
  classical
  obtain ⟨m, hlin⟩ := exists_linearization hwf
  exact ⟨m, m.map tn.α, hlin.1, fun t => (hlin.2.1 t).symm, rfl,
    ord_iff_idxOf_lt hwf hTO hlin⟩

/-- **Sequence networks are invariant under renaming of the task identifiers.** -/
lemma IsSeqNet.iso {tn tn' : TaskNetwork I A C} {l : List I} {xs : List (A ⊕ C)}
    (h : IsSeqNet tn l xs) (hwf' : tn'.WF) (hiso : tn.Iso tn') :
    ∃ l₂ : List I, IsSeqNet tn' l₂ xs := by
  classical
  obtain ⟨σ, hbij, hord, hα⟩ := hiso
  have hinj : ∀ x ∈ l, ∀ y ∈ l, σ x = σ y → x = y := by
    intro x hx y hy hxy
    exact hbij.injOn (by simpa using h.mem_of_mem hx) (by simpa using h.mem_of_mem hy) hxy
  have hmapsTo : ∀ x, x ∈ l → σ x ∈ tn'.T := by
    intro x hx
    simpa using hbij.mapsTo (by simpa using h.mem_of_mem hx)
  refine ⟨l.map σ, List.Nodup.map_on hinj h.nodup, ?_, ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := hbij.surjOn (by simpa using hy)
      exact List.mem_map.2 ⟨z, (h.memT z).1 (by simpa using hz), rfl⟩
    · rintro hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact hmapsTo z hz
  · rw [List.map_map, ← h.labels]
    refine List.map_congr_left ?_
    intro y hy
    exact (hα y (h.mem_of_mem hy)).symm
  · intro y z
    constructor
    · intro hyz
      obtain ⟨a, ha, rfl⟩ := hbij.surjOn (by simpa using hwf'.mem_left hyz)
      obtain ⟨b, hb, rfl⟩ := hbij.surjOn (by simpa using hwf'.mem_right hyz)
      have haT : a ∈ tn.T := by simpa using ha
      have hbT : b ∈ tn.T := by simpa using hb
      obtain ⟨ha', hb', hlt⟩ := (h.ord a b).1 ((hord a haT b hbT).2 hyz)
      refine ⟨List.mem_map_of_mem ha', List.mem_map_of_mem hb', ?_⟩
      rw [idxOf_map_of_injOn hinj ha', idxOf_map_of_injOn hinj hb']
      exact hlt
    · rintro ⟨hy, hz, hlt⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hz
      rw [idxOf_map_of_injOn hinj ha, idxOf_map_of_injOn hinj hb] at hlt
      exact (hord a ((h.memT a).2 ha) b ((h.memT b).2 hb)).1 ((h.ord a b).2 ⟨ha, hb, hlt⟩)

/-- **Decomposition of a sequence network is substitution in the label list.**  Decomposing the
task `t` of the sequence `l₁ ++ t :: l₂` by a (fresh) sequence network with labels `bs`
produces the sequence network whose labels are `xs₁ ++ bs ++ xs₂`. -/
theorem isSeqNet_decomposeWith {tn tn' : TaskNetwork I A C} {l₁ l₂ lm : List I}
    {xs₁ xs₂ bs : List (A ⊕ C)} {y : A ⊕ C} {t : I}
    (h : tn.IsSeqNet (l₁ ++ t :: l₂) (xs₁ ++ y :: xs₂)) (hlen : l₁.length = xs₁.length)
    (h' : tn'.IsSeqNet lm bs) (hdisj : Disjoint tn.T tn'.T) :
    (decomposeWith tn t tn').IsSeqNet (l₁ ++ lm ++ l₂) (xs₁ ++ bs ++ xs₂) := by
  classical
  obtain ⟨hnodup, hmemT, hlabels, hord⟩ := h
  obtain ⟨hnodup', hmemT', hlabels', hord'⟩ := h'
  -- the three segments are pairwise disjoint
  rw [List.nodup_append] at hnodup
  obtain ⟨hnd1, hndt2, hdis12⟩ := hnodup
  rw [List.nodup_cons] at hndt2
  obtain ⟨ht2, hnd2⟩ := hndt2
  have ht1 : t ∉ l₁ := fun hc => hdis12 t hc t (by simp) rfl
  have h12 : ∀ x ∈ l₁, x ∉ l₂ := fun x hx hx2 => hdis12 x hx x (by simp [hx2]) rfl
  have hmem1T : ∀ x ∈ l₁, x ∈ tn.T := fun x hx => (hmemT x).2 (by simp [hx])
  have hmem2T : ∀ x ∈ l₂, x ∈ tn.T := fun x hx => (hmemT x).2 (by simp [hx])
  have htT : t ∈ tn.T := (hmemT t).2 (by simp)
  have hmemmT : ∀ x ∈ lm, x ∈ tn'.T := fun x hx => (hmemT' x).2 hx
  have hnotm : ∀ x ∈ lm, x ∉ tn.T := fun x hx hc =>
    (Finset.disjoint_left.1 hdisj hc) (hmemmT x hx)
  have hm1 : ∀ x ∈ l₁, x ∉ lm := fun x hx hc => hnotm x hc (hmem1T x hx)
  have hm2 : ∀ x ∈ l₂, x ∉ lm := fun x hx hc => hnotm x hc (hmem2T x hx)
  have hmt : t ∉ lm := fun hc => hnotm t hc htT
  have hnotT' : ∀ x ∈ l₁ ++ t :: l₂, x ∉ tn'.T := by
    intro x hx hc
    exact (Finset.disjoint_left.1 hdisj ((hmemT x).2 hx)) hc
  -- index computations in the new sequence
  have hidxL1 : ∀ x ∈ l₁, (l₁ ++ lm ++ l₂).idxOf x = l₁.idxOf x := by
    intro x hx; simp [List.append_assoc, List.idxOf_append, hx]
  have hidxLm : ∀ x ∈ lm, (l₁ ++ lm ++ l₂).idxOf x = lm.idxOf x + l₁.length := by
    intro x hx
    have hx1 : x ∉ l₁ := fun hc => hm1 x hc hx
    simp [List.append_assoc, List.idxOf_append, hx, hx1]
  have hidxL2 : ∀ x ∈ l₂,
      (l₁ ++ lm ++ l₂).idxOf x = l₂.idxOf x + lm.length + l₁.length := by
    intro x hx
    have hx1 : x ∉ l₁ := fun hc => h12 x hc hx
    have hxm : x ∉ lm := hm2 x hx
    simp [List.append_assoc, List.idxOf_append, hx1, hxm]
  -- index computations in the old sequence
  have hidxM1 : ∀ x ∈ l₁, (l₁ ++ t :: l₂).idxOf x = l₁.idxOf x := by
    intro x hx; simp [List.idxOf_append, hx]
  have hidxMt : (l₁ ++ t :: l₂).idxOf t = l₁.length := by
    simp [List.idxOf_append, ht1]
  have hidxM2 : ∀ x ∈ l₂, (l₁ ++ t :: l₂).idxOf x = l₂.idxOf x + 1 + l₁.length := by
    intro x hx
    have hx1 : x ∉ l₁ := fun hc => h12 x hc hx
    have hxt : x ≠ t := fun hc => ht2 (hc ▸ hx)
    simp [List.idxOf_append, hx1, Ne.symm hxt]
  have hlt1 : ∀ x ∈ l₁, l₁.idxOf x < l₁.length := fun x hx => List.idxOf_lt_length_of_mem hx
  have hltm : ∀ x ∈ lm, lm.idxOf x < lm.length := fun x hx => List.idxOf_lt_length_of_mem hx
  -- membership in the new network
  have hmemnew : ∀ x, x ∈ (decomposeWith tn t tn').T ↔ x ∈ l₁ ++ lm ++ l₂ := by
    intro x
    rw [mem_decomposeWith_T, hmemT x]
    constructor
    · rintro (⟨hx, hxt⟩ | hx)
      · rcases List.mem_append.1 hx with hx' | hx'
        · simp [hx']
        · rcases List.mem_cons.1 hx' with rfl | hx''
          · exact absurd rfl hxt
          · simp [hx'']
      · have := (hmemT' x).1 hx
        simp [this]
    · intro hx
      rcases List.mem_append.1 hx with hx' | hx'
      · rcases List.mem_append.1 hx' with hx'' | hx''
        · exact Or.inl ⟨by simp [hx''], fun hc => ht1 (hc ▸ hx'')⟩
        · exact Or.inr (hmemmT x hx'')
      · exact Or.inl ⟨by simp [hx'], fun hc => ht2 (hc ▸ hx')⟩
  -- the labels of the three segments
  have hsplit : l₁.map tn.α = xs₁ ∧ (t :: l₂).map tn.α = y :: xs₂ := by
    refine List.append_inj (by simpa using hlabels) ?_
    simpa using hlen
  have hlab1 : l₁.map tn.α = xs₁ := hsplit.1
  have hlab2 : l₂.map tn.α = xs₂ := by
    have := hsplit.2
    simpa using congrArg List.tail this
  refine ⟨?_, hmemnew, ?_, ?_⟩
  · -- the identifiers of the new sequence are pairwise distinct
    refine List.Nodup.append (List.Nodup.append hnd1 hnodup' ?_) hnd2 ?_
    · intro x hx hxm; exact hm1 x hx hxm
    · intro x hx hx2
      rcases List.mem_append.1 hx with hx' | hx'
      · exact h12 x hx' hx2
      · exact hm2 x hx2 hx'
  · -- the labels
    rw [List.map_append, List.map_append]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
    · rw [← hlab1]
      refine List.map_congr_left ?_
      intro x hx
      have : x ∉ tn'.T := hnotT' x (by simp [hx])
      simp [decomposeWith_α, this]
    · rw [← hlabels']
      refine List.map_congr_left ?_
      intro x hx
      simp [decomposeWith_α, hmemmT x hx]
    · rw [← hlab2]
      refine List.map_congr_left ?_
      intro x hx
      have : x ∉ tn'.T := hnotT' x (by simp [hx])
      simp [decomposeWith_α, this]
  · -- the ordering
    intro a b
    rw [decomposeWith_ord_iff]
    constructor
    · rintro (hab | ⟨hab, hb⟩ | ⟨hab, ha⟩ | ⟨hab, hat, hbt⟩)
      · obtain ⟨ham, hbm, hlt⟩ := (hord' a b).1 hab
        refine ⟨by simp [ham], by simp [hbm], ?_⟩
        rw [hidxLm a ham, hidxLm b hbm]; omega
      · obtain ⟨haM, -, hlt⟩ := (hord a t).1 hab
        have hbm : b ∈ lm := (hmemT' b).1 hb
        have ha1 : a ∈ l₁ := by
          rcases List.mem_append.1 haM with h' | h'
          · exact h'
          · rcases List.mem_cons.1 h' with rfl | h''
            · exact absurd hlt (by rw [hidxMt]; omega)
            · exact absurd hlt (by rw [hidxM2 a h'', hidxMt]; omega)
        refine ⟨by simp [ha1], by simp [hbm], ?_⟩
        rw [hidxL1 a ha1, hidxLm b hbm]
        have := hlt1 a ha1; omega
      · obtain ⟨-, hbM, hlt⟩ := (hord t b).1 hab
        have ham : a ∈ lm := (hmemT' a).1 ha
        have hb2 : b ∈ l₂ := by
          rcases List.mem_append.1 hbM with h' | h'
          · exact absurd hlt (by rw [hidxM1 b h', hidxMt]; have := hlt1 b h'; omega)
          · rcases List.mem_cons.1 h' with rfl | h''
            · exact absurd hlt (by rw [hidxMt]; omega)
            · exact h''
        refine ⟨by simp [ham], by simp [hb2], ?_⟩
        rw [hidxLm a ham, hidxL2 b hb2]
        have := hltm a ham; omega
      · obtain ⟨haM, hbM, hlt⟩ := (hord a b).1 hab
        have hacase : a ∈ l₁ ∨ a ∈ l₂ := by
          rcases List.mem_append.1 haM with h' | h'
          · exact Or.inl h'
          · rcases List.mem_cons.1 h' with rfl | h''
            · exact absurd rfl hat
            · exact Or.inr h''
        have hbcase : b ∈ l₁ ∨ b ∈ l₂ := by
          rcases List.mem_append.1 hbM with h' | h'
          · exact Or.inl h'
          · rcases List.mem_cons.1 h' with rfl | h''
            · exact absurd rfl hbt
            · exact Or.inr h''
        rcases hacase with ha' | ha' <;> rcases hbcase with hb' | hb'
        · refine ⟨by simp [ha'], by simp [hb'], ?_⟩
          rw [hidxL1 a ha', hidxL1 b hb']
          rwa [hidxM1 a ha', hidxM1 b hb'] at hlt
        · refine ⟨by simp [ha'], by simp [hb'], ?_⟩
          rw [hidxL1 a ha', hidxL2 b hb']
          have := hlt1 a ha'; omega
        · exfalso
          rw [hidxM2 a ha', hidxM1 b hb'] at hlt
          have := hlt1 b hb'; omega
        · refine ⟨by simp [ha'], by simp [hb'], ?_⟩
          rw [hidxL2 a ha', hidxL2 b hb']
          rw [hidxM2 a ha', hidxM2 b hb'] at hlt
          omega
    · rintro ⟨ha, hb, hlt⟩
      have hacase : a ∈ l₁ ∨ a ∈ lm ∨ a ∈ l₂ := by
        rcases List.mem_append.1 ha with h' | h'
        · rcases List.mem_append.1 h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl h'')
        · exact Or.inr (Or.inr h')
      have hbcase : b ∈ l₁ ∨ b ∈ lm ∨ b ∈ l₂ := by
        rcases List.mem_append.1 hb with h' | h'
        · rcases List.mem_append.1 h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl h'')
        · exact Or.inr (Or.inr h')
      rcases hacase with ha' | ha' | ha' <;> rcases hbcase with hb' | hb' | hb'
      · -- both in the prefix
        refine Or.inr (Or.inr (Or.inr ⟨?_, fun hc => ht1 (hc ▸ ha'), fun hc => ht1 (hc ▸ hb')⟩))
        refine (hord a b).2 ⟨by simp [ha'], by simp [hb'], ?_⟩
        rw [hidxM1 a ha', hidxM1 b hb']
        rwa [hidxL1 a ha', hidxL1 b hb'] at hlt
      · -- prefix before inserted network
        refine Or.inr (Or.inl ⟨?_, hmemmT b hb'⟩)
        refine (hord a t).2 ⟨by simp [ha'], by simp, ?_⟩
        rw [hidxM1 a ha', hidxMt]
        exact hlt1 a ha'
      · -- prefix before suffix
        refine Or.inr (Or.inr (Or.inr ⟨?_, fun hc => ht1 (hc ▸ ha'), fun hc => ht2 (hc ▸ hb')⟩))
        refine (hord a b).2 ⟨by simp [ha'], by simp [hb'], ?_⟩
        rw [hidxM1 a ha', hidxM2 b hb']
        have := hlt1 a ha'; omega
      · -- inserted network before prefix: impossible
        exfalso
        rw [hidxLm a ha', hidxL1 b hb'] at hlt
        have := hlt1 b hb'; omega
      · -- both inserted
        refine Or.inl ((hord' a b).2 ⟨ha', hb', ?_⟩)
        rw [hidxLm a ha', hidxLm b hb'] at hlt
        omega
      · -- inserted before suffix
        refine Or.inr (Or.inr (Or.inl ⟨?_, hmemmT a ha'⟩))
        refine (hord t b).2 ⟨by simp, by simp [hb'], ?_⟩
        rw [hidxMt, hidxM2 b hb']
        omega
      · -- suffix before prefix: impossible
        exfalso
        rw [hidxL2 a ha', hidxL1 b hb'] at hlt
        have := hlt1 b hb'; omega
      · -- suffix before inserted network: impossible
        exfalso
        rw [hidxL2 a ha', hidxLm b hb'] at hlt
        have := hltm b hb'; omega
      · -- both in the suffix
        refine Or.inr (Or.inr (Or.inr ⟨?_, fun hc => ht2 (hc ▸ ha'), fun hc => ht2 (hc ▸ hb')⟩))
        refine (hord a b).2 ⟨by simp [ha'], by simp [hb'], ?_⟩
        rw [hidxM2 a ha', hidxM2 b hb']
        rw [hidxL2 a ha', hidxL2 b hb'] at hlt
        omega

end Seq

end TaskNetwork

/-! ### Method bodies -/

namespace Method

variable [DecidableEq I]

/-- A sequence network presenting the subtask network of a method is a *body* of it. -/
lemma hasSeqBody_of_isSeqNet {m : Method I A C} {l : List I} {bs : List (A ⊕ C)}
    (h : m.subtasks.IsSeqNet l bs) : m.HasSeqBody bs :=
  ⟨l, h.isLinearization, h.labels, h.pairwise_ord⟩

/-- Conversely, a (totally ordered) body of a well-formed method presents its subtask network
as a sequence network. -/
lemma exists_isSeqNet_of_hasSeqBody {m : Method I A C} {bs : List (A ⊕ C)}
    (hwf : m.subtasks.WF) (h : m.HasSeqBody bs) : ∃ l, m.subtasks.IsSeqNet l bs := by
  obtain ⟨l, hlin, hlabels, hpair⟩ := h
  refine ⟨l, ?_⟩
  have := TaskNetwork.isSeqNet_of_pairwise_ord hwf hlin.1 (fun t => (hlin.2.1 t).symm) hpair
  rwa [hlabels] at this

/-- **The body of a totally ordered method is unique.** -/
lemma hasSeqBody_iff_of_isSeqNet {m : Method I A C} {l : List I} {xs bs : List (A ⊕ C)}
    (h : m.subtasks.IsSeqNet l xs) : m.HasSeqBody bs ↔ bs = xs := by
  constructor
  · rintro ⟨l', hlin, hlabels, -⟩
    rw [h.linearization_eq hlin] at hlabels
    exact hlabels.symm.trans h.labels
  · rintro rfl
    exact hasSeqBody_of_isSeqNet h

/-- A well-formed, totally ordered method has a body. -/
lemma exists_hasSeqBody {m : Method I A C} (hwf : m.subtasks.WF)
    (hTO : m.subtasks.IsTotallyOrdered) : ∃ bs, m.HasSeqBody bs := by
  obtain ⟨l, bs, h⟩ := TaskNetwork.exists_isSeqNet hwf hTO
  exact ⟨bs, hasSeqBody_of_isSeqNet h⟩

end Method

/-! ### Refinement of task sequences -/

namespace Domain

variable (D : Domain F A C I)

/-- **Refinement of a task sequence.**  `D.YieldSeq xs as` states that the sequence of tasks
`xs` can be refined into the action sequence `as`: this is the leftmost derivation relation of
the context-free grammar whose non-terminals are the compound task names, whose terminals are
the actions and whose productions are the (totally ordered) methods of `D`. -/
inductive YieldSeq : List (A ⊕ C) → List A → Prop
  /-- The empty task sequence yields the empty action sequence. -/
  | nil : YieldSeq [] []
  /-- A leading primitive task is executed. -/
  | prim {a : A} {xs : List (A ⊕ C)} {as : List A} (h : YieldSeq xs as) :
      YieldSeq (Sum.inl a :: xs) (a :: as)
  /-- A leading compound task is replaced by the body of one of its methods. -/
  | comp {c : C} {bs xs : List (A ⊕ C)} {as : List A} (hm : D.SeqBody c bs)
      (h : YieldSeq (bs ++ xs) as) : YieldSeq (Sum.inr c :: xs) as

variable {D}

/-- A sequence of primitive tasks yields exactly its own action sequence. -/
lemma yieldSeq_map_inl (as : List A) : D.YieldSeq (as.map Sum.inl) as := by
  induction as with
  | nil => exact YieldSeq.nil
  | cons a as ih => exact YieldSeq.prim ih

/-- Refinements of two task sequences compose to a refinement of their concatenation. -/
lemma YieldSeq.append {xs ys : List (A ⊕ C)} {as bs : List A} (hx : D.YieldSeq xs as)
    (hy : D.YieldSeq ys bs) : D.YieldSeq (xs ++ ys) (as ++ bs) := by
  induction hx with
  | nil => simpa using hy
  | prim _ ih => exact YieldSeq.prim ih
  | @comp c cs zs _ hm _ ih =>
      refine YieldSeq.comp hm ?_
      rwa [List.append_assoc] at ih

/-- **Refinements of a concatenation split.**  A refinement of `xs ++ ys` consists of a
refinement of `xs` followed by one of `ys`. -/
lemma YieldSeq.split {xs ys : List (A ⊕ C)} {as : List A} (h : D.YieldSeq (xs ++ ys) as) :
    ∃ as₁ as₂, as = as₁ ++ as₂ ∧ D.YieldSeq xs as₁ ∧ D.YieldSeq ys as₂ := by
  have H : ∀ {zs : List (A ⊕ C)} {cs : List A}, D.YieldSeq zs cs → ∀ xs ys, zs = xs ++ ys →
      ∃ as₁ as₂, cs = as₁ ++ as₂ ∧ D.YieldSeq xs as₁ ∧ D.YieldSeq ys as₂ := by
    intro zs cs hzs
    induction hzs with
    | nil =>
        intro xs ys hxy
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hxy.symm
        exact ⟨[], [], rfl, YieldSeq.nil, YieldSeq.nil⟩
    | @prim a zs bs hy ih =>
        intro xs ys hxy
        cases xs with
        | nil =>
            refine ⟨[], a :: bs, rfl, YieldSeq.nil, ?_⟩
            simp only [List.nil_append] at hxy
            exact hxy ▸ YieldSeq.prim hy
        | cons x xs =>
            rw [List.cons_append] at hxy
            injection hxy with h1 h2
            subst h1
            obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := ih xs ys h2
            exact ⟨a :: as₁, as₂, rfl, YieldSeq.prim h₁, h₂⟩
    | @comp c cs zs bs hm hy ih =>
        intro xs ys hxy
        cases xs with
        | nil =>
            refine ⟨[], bs, rfl, YieldSeq.nil, ?_⟩
            simp only [List.nil_append] at hxy
            exact hxy ▸ YieldSeq.comp hm hy
        | cons x xs =>
            rw [List.cons_append] at hxy
            injection hxy with h1 h2
            subst h1
            obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := ih (cs ++ xs) ys (by rw [h2, List.append_assoc])
            exact ⟨as₁, as₂, rfl, YieldSeq.comp hm h₁, h₂⟩
  exact H h xs ys rfl

/-- **Decomposition steps preserve refinements**: whatever the result of substituting a method
body yields, the original task sequence yields as well. -/
lemma yieldSeq_of_subst {xs₁ xs₂ bs : List (A ⊕ C)} {c : C} {as : List A}
    (hm : D.SeqBody c bs) (h : D.YieldSeq (xs₁ ++ bs ++ xs₂) as) :
    D.YieldSeq (xs₁ ++ Sum.inr c :: xs₂) as := by
  rw [List.append_assoc] at h
  obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h.split
  obtain ⟨bs₁, bs₂, rfl, hb₁, hb₂⟩ := h₂.split
  exact h₁.append (YieldSeq.comp hm (hb₁.append hb₂))

/-! #### Comparison with the binary refinement relation of `ProofTuples.lean` -/

variable (D)

/-- The tasks of `xs` are refined one by one (in the sense of `Domain.Yield`, i.e. using
methods with at most two subtasks) and their action sequences are concatenated. -/
inductive YieldAll : List (A ⊕ C) → List A → Prop
  /-- The empty task sequence. -/
  | nil : YieldAll [] []
  /-- The first task is refined, then the remaining ones. -/
  | cons {x : A ⊕ C} {xs : List (A ⊕ C)} {as bs : List A} (h : D.Yield x as)
      (ht : YieldAll xs bs) : YieldAll (x :: xs) (as ++ bs)

variable {D}

lemma YieldAll.append {xs ys : List (A ⊕ C)} {as bs : List A} (hx : D.YieldAll xs as)
    (hy : D.YieldAll ys bs) : D.YieldAll (xs ++ ys) (as ++ bs) := by
  induction hx with
  | nil => simpa using hy
  | @cons x zs cs ds h _ ih =>
      have := YieldAll.cons h ih
      rwa [← List.append_assoc] at this

lemma YieldAll.split {xs ys : List (A ⊕ C)} {as : List A} (h : D.YieldAll (xs ++ ys) as) :
    ∃ as₁ as₂, as = as₁ ++ as₂ ∧ D.YieldAll xs as₁ ∧ D.YieldAll ys as₂ := by
  induction xs generalizing as with
  | nil => exact ⟨[], as, rfl, YieldAll.nil, by simpa using h⟩
  | cons x xs ih =>
      rw [List.cons_append] at h
      cases h with
      | cons hy ht =>
          obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := ih ht
          exact ⟨_ ++ as₁, as₂, by rw [List.append_assoc], YieldAll.cons hy h₁, h₂⟩

lemma YieldAll.eq_nil {as : List A} (h : D.YieldAll [] as) : as = [] := by
  cases h; rfl

lemma YieldAll.yield_of_singleton {x : A ⊕ C} {as : List A} (h : D.YieldAll [x] as) :
    D.Yield x as := by
  cases h with
  | cons hy ht => rw [ht.eq_nil]; simpa using hy

lemma YieldAll.of_pair {x y : A ⊕ C} {as : List A} (h : D.YieldAll [x, y] as) :
    ∃ u v, as = u ++ v ∧ D.Yield x u ∧ D.Yield y v := by
  cases h with
  | cons hy ht => exact ⟨_, _, rfl, hy, ht.yield_of_singleton⟩

/-- A refinement in the sense of `Domain.Yield` refines the corresponding singleton
sequence. -/
lemma yieldSeq_singleton_of_yield {x : A ⊕ C} {as : List A} (h : D.Yield x as) :
    D.YieldSeq [x] as := by
  induction h with
  | prim a => exact YieldSeq.prim YieldSeq.nil
  | zero hb => exact YieldSeq.comp hb (by simpa using YieldSeq.nil)
  | one hb _ ih => exact YieldSeq.comp hb (by simpa using ih)
  | two hb _ _ ihx ihy => exact YieldSeq.comp hb (by simpa using ihx.append ihy)

/-- If all method bodies have at most two subtasks, a refinement of a task sequence refines
its tasks one by one in the sense of `Domain.Yield`. -/
lemma yieldAll_of_yieldSeq (hbody : ∀ c bs, D.SeqBody c bs → bs.length ≤ 2)
    {xs : List (A ⊕ C)} {as : List A} (h : D.YieldSeq xs as) : D.YieldAll xs as := by
  induction h with
  | nil => exact YieldAll.nil
  | prim _ ih => simpa using YieldAll.cons (Yield.prim _) ih
  | @comp c bs zs cs hm _ ih =>
      obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := ih.split
      refine YieldAll.cons ?_ h₂
      have hlen := hbody c bs hm
      match bs, hlen with
      | [], _ => rw [h₁.eq_nil]; exact Yield.zero hm
      | [x], _ => exact Yield.one hm h₁.yield_of_singleton
      | [x, y], _ =>
          obtain ⟨u, v, rfl, hu, hv⟩ := h₁.of_pair
          exact Yield.two hm hu hv

/-- **The two refinement relations agree** for domains all of whose method bodies have at most
two subtasks: the binary relation `Domain.Yield` of the proof-tuple characterisation and the
leftmost derivation relation `Domain.YieldSeq`. -/
lemma yield_iff_yieldSeq_singleton (hbody : ∀ c bs, D.SeqBody c bs → bs.length ≤ 2)
    {x : A ⊕ C} {as : List A} : D.Yield x as ↔ D.YieldSeq [x] as :=
  ⟨yieldSeq_singleton_of_yield, fun h => (yieldAll_of_yieldSeq hbody h).yield_of_singleton⟩

end Domain

/-! ### The normal form theorem -/

namespace Problem

open TaskNetwork

section NormalForm

variable [DecidableEq I] {P : Problem F A C I}

/-- A position in the label list of a sequence network is realised by a task identifier. -/
lemma _root_.HTN.TaskNetwork.IsSeqNet.split_labels
    {tn : TaskNetwork I A C} {l : List I} {xs xs₁ xs₂ : List (A ⊕ C)} {y : A ⊕ C}
    (h : tn.IsSeqNet l xs) (hxs : xs = xs₁ ++ y :: xs₂) :
    ∃ l₁ t l₂, l = l₁ ++ t :: l₂ ∧ l₁.length = xs₁.length ∧ tn.α t = y ∧
      l₁.map tn.α = xs₁ ∧ l₂.map tn.α = xs₂ := by
  have hl : l.map tn.α = xs₁ ++ y :: xs₂ := by rw [h.labels, hxs]
  obtain ⟨l₁, l', rfl, hl₁, hl'⟩ := List.map_eq_append_iff.1 hl
  obtain ⟨t, l₂, rfl, ht, hl₂⟩ := List.map_eq_cons_iff.1 hl'
  exact ⟨l₁, t, l₂, rfl, by rw [← hl₁, List.length_map], ht, hl₁, hl₂⟩

/-- **Every reachable task network of a totally ordered problem is a sequence network**, and
whatever its task sequence refines to, the initial task sequence refines to as well. -/
theorem exists_isSeqNet_of_reachable (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I}
    {xs₀ : List (A ⊕ C)} (h₀ : P.tnI.IsSeqNet l₀ xs₀) {tn : TaskNetwork I A C}
    (hreach : P.Reachable tn) :
    ∃ (l : List I) (xs : List (A ⊕ C)), tn.IsSeqNet l xs ∧
      ∀ as, P.domain.YieldSeq xs as → P.domain.YieldSeq xs₀ as := by
  induction hreach with
  | refl => exact ⟨l₀, xs₀, h₀, fun _ h => h⟩
  | @tail tn₁ tn₂ hprefix hstep ih =>
      obtain ⟨l, xs, hseq, hcont⟩ := ih
      obtain ⟨t, m, hs⟩ := hstep
      have hmr : P.ReachableMethod m := Problem.reachableMethod_of_decomposesTo hprefix hs
      obtain ⟨hm, htT, hαt, tn', hwf', hiso', hdisj, hEq⟩ := hs
      subst hEq
      haveI : Nonempty I := ⟨t⟩
      -- split the sequence at the decomposed task
      obtain ⟨l₁, l₂, rfl⟩ : ∃ l₁ l₂, l = l₁ ++ t :: l₂ := by
        obtain ⟨s, u, hsu⟩ := List.append_of_mem ((hseq.memT t).1 htT)
        exact ⟨s, u, hsu⟩
      have hxs : xs = l₁.map tn₁.α ++ tn₁.α t :: l₂.map tn₁.α := by
        rw [← hseq.labels]; simp
      have hseq' : tn₁.IsSeqNet (l₁ ++ t :: l₂)
          (l₁.map tn₁.α ++ tn₁.α t :: l₂.map tn₁.α) := by
        rw [← hxs]; exact hseq
      -- the method body is a sequence
      obtain ⟨lm, bs, hbody⟩ :=
        TaskNetwork.exists_isSeqNet (hwf.methods m hmr.1) (hto m hmr)
      obtain ⟨lm', hbody'⟩ := hbody.iso hwf' (hiso'.symm)
      have hsub := TaskNetwork.isSeqNet_decomposeWith hseq' (by simp) hbody' hdisj
      refine ⟨l₁ ++ lm' ++ l₂, l₁.map tn₁.α ++ bs ++ l₂.map tn₁.α, hsub, ?_⟩
      intro as hy
      refine hcont as ?_
      rw [hxs, hαt]
      refine Domain.yieldSeq_of_subst ?_ hy
      exact ⟨m, hm, rfl, Method.hasSeqBody_of_isSeqNet hbody⟩

/-- **Every solution plan of a totally ordered problem refines the initial task sequence.** -/
theorem yieldSeq_of_isSolutionPlan (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I}
    {xs₀ : List (A ⊕ C)} (h₀ : P.tnI.IsSeqNet l₀ xs₀) {as : List A}
    (hsol : P.IsSolutionPlan as) : P.domain.YieldSeq xs₀ as := by
  obtain ⟨tn, lin, hreach, -, hlin, hseqa, -, -⟩ := hsol
  obtain ⟨l, xs, hseq, hcont⟩ := exists_isSeqNet_of_reachable hwf hto h₀ hreach
  have hll : lin = l := hseq.linearization_eq hlin
  subst hll
  have hxs : xs = as.map Sum.inl := by rw [← hseq.labels]; exact hseqa
  subst hxs
  exact hcont as (Domain.yieldSeq_map_inl as)

/-- **Every refinement of the task sequence of a reachable network can be carried out by
decomposition.**  If the sequence `xs` refines to the actions `as`, then a reachable network
whose labels are `done` (already primitive), followed by `xs`, followed by `rest`, decomposes
into a reachable network with labels `done ++ as` followed by `rest`. -/
theorem exists_reachable_isSeqNet_of_yieldSeq [Infinite I] (hwf : P.WF)
    {xs : List (A ⊕ C)} {as : List A} (hy : P.domain.YieldSeq xs as) :
    ∀ {tn : TaskNetwork I A C} {l : List I} {done : List A} {rest : List (A ⊕ C)},
      tn.IsSeqNet l (done.map Sum.inl ++ xs ++ rest) → P.Reachable tn →
      ∃ (tn₂ : TaskNetwork I A C) (l₂ : List I),
        P.Reachable tn₂ ∧ tn₂.IsSeqNet l₂ ((done ++ as).map Sum.inl ++ rest) := by
  induction hy with
  | nil =>
      intro tn l done rest hseq hreach
      exact ⟨tn, l, hreach, by simpa using hseq⟩
  | @prim a zs bs _ ih =>
      intro tn l done rest hseq hreach
      obtain ⟨tn₂, l₂, hreach₂, hseq₂⟩ :=
        ih (done := done ++ [a]) (rest := rest) (by simpa using hseq) hreach
      exact ⟨tn₂, l₂, hreach₂, by simpa using hseq₂⟩
  | @comp c cs zs bs hm _ ih =>
      intro tn l done rest hseq hreach
      obtain ⟨mth, hmth, hmc, hmbody⟩ := hm
      -- locate the compound task in the network
      obtain ⟨l₁, t, l₂, rfl, hlen, hαt, -, -⟩ :=
        hseq.split_labels (xs₁ := done.map Sum.inl) (y := Sum.inr c)
          (xs₂ := zs ++ rest) (by simp)
      haveI : Nonempty I := ⟨t⟩
      -- a fresh copy of the method body
      obtain ⟨lm, hlm⟩ :=
        Method.exists_isSeqNet_of_hasSeqBody (hwf.methods mth hmth) hmbody
      obtain ⟨tn', hwf', hiso', hdisj⟩ :=
        TaskNetwork.exists_fresh_iso_copy mth.subtasks (hwf.methods mth hmth) tn.T
      obtain ⟨lm', hlm'⟩ := hlm.iso hwf' hiso'.symm
      have hstep : DecompStep P.methods tn t mth (decomposeWith tn t tn') := by
        refine ⟨hmth, (hseq.memT t).2 (by simp), ?_, tn', hwf', hiso', hdisj, rfl⟩
        rw [hαt, hmc]
      have hsub := TaskNetwork.isSeqNet_decomposeWith
        (xs₁ := done.map Sum.inl) (xs₂ := zs ++ rest) (y := Sum.inr c)
        (by simpa using hseq) hlen hlm' hdisj
      refine ih (l := l₁ ++ lm' ++ l₂) (done := done) (rest := rest) ?_
        (Relation.ReflTransGen.tail hreach ⟨t, mth, hstep⟩)
      simpa [List.append_assoc] using hsub

/-- **Every executable refinement of the initial task sequence that reaches the goal is a
solution plan** — the converse of `HTN.Problem.yieldSeq_of_isSolutionPlan`. -/
theorem isSolutionPlan_of_yieldSeq [Infinite I] (hwf : P.WF) {l₀ : List I}
    {xs₀ : List (A ⊕ C)} (h₀ : P.tnI.IsSeqNet l₀ xs₀) {as : List A}
    (hy : P.domain.YieldSeq xs₀ as) (happ : P.SeqApplicable as P.init)
    (hgoal : P.GoalState (P.transitionSeq as P.init)) : P.IsSolutionPlan as := by
  obtain ⟨tn₂, l₂, hreach₂, hseq₂⟩ :=
    exists_reachable_isSeqNet_of_yieldSeq (done := []) (rest := []) hwf hy
      (by simpa using h₀) Relation.ReflTransGen.refl
  rw [List.nil_append, List.append_nil] at hseq₂
  exact ⟨tn₂, l₂, hreach₂, hseq₂.isPrimitive_of_labels, hseq₂.isLinearization,
    hseq₂.isActionSeq_of_labels, happ, hgoal⟩

/-- **Normal form theorem for totally ordered HTN problems.**  A well-formed problem whose
methods are totally ordered and whose initial task network is the task sequence `xs₀` is
solvable exactly when `xs₀` can be refined into an action sequence that is executable in the
initial state and reaches the goal. -/
theorem solvable_iff_yieldSeq [Infinite I] (hwf : P.WF) (hto : P.IsTO_M) {l₀ : List I}
    {xs₀ : List (A ⊕ C)} (h₀ : P.tnI.IsSeqNet l₀ xs₀) :
    P.Solvable ↔ ∃ as : List A, P.domain.YieldSeq xs₀ as ∧ P.SeqApplicable as P.init ∧
      P.GoalState (P.transitionSeq as P.init) := by
  constructor
  · intro h
    obtain ⟨as, hplan⟩ := solvable_iff_exists_solutionPlan.1 h
    obtain ⟨-, -, -, -, -, -, happ, hgoal⟩ := id hplan
    exact ⟨as, yieldSeq_of_isSolutionPlan hwf hto h₀ hplan, happ, hgoal⟩
  · rintro ⟨as, hy, happ, hgoal⟩
    exact solvable_iff_exists_solutionPlan.2
      ⟨as, isSolutionPlan_of_yieldSeq hwf h₀ hy happ hgoal⟩

/-- The normal form theorem for a totally ordered problem, with the initial task sequence
obtained from total orderedness of the initial task network. -/
theorem solvable_iff_exists_yieldSeq [Infinite I] (hwf : P.WF) (hTO : P.IsTO) :
    P.Solvable ↔ ∃ (xs₀ : List (A ⊕ C)) (l₀ : List I), P.tnI.IsSeqNet l₀ xs₀ ∧
      ∃ as : List A, P.domain.YieldSeq xs₀ as ∧ P.SeqApplicable as P.init ∧
        P.GoalState (P.transitionSeq as P.init) := by
  obtain ⟨l₀, xs₀, h₀⟩ := TaskNetwork.exists_isSeqNet hwf.tnI hTO.1
  constructor
  · intro h
    exact ⟨xs₀, l₀, h₀, (solvable_iff_yieldSeq hwf hTO.2 h₀).1 h⟩
  · rintro ⟨xs, l, hseq, hrest⟩
    exact (solvable_iff_yieldSeq hwf hTO.2 hseq).2 hrest

/-- A task network with a single task is the corresponding one-element sequence network. -/
lemma _root_.HTN.TaskNetwork.isSeqNet_singleton {tn : TaskNetwork I A C} (hwf : tn.WF)
    {t₀ : I} (hT : tn.T = {t₀}) : tn.IsSeqNet [t₀] [tn.α t₀] := by
  refine ⟨by simp, ?_, rfl, ?_⟩
  · intro s; rw [hT]; simp
  · intro s u
    constructor
    · intro hord
      exfalso
      have hs : s ∈ tn.T := hwf.mem_left hord
      have hu : u ∈ tn.T := hwf.mem_right hord
      rw [hT] at hs hu
      simp only [Finset.mem_singleton] at hs hu
      subst hs; subst hu
      exact hwf.irrefl _ hord
    · rintro ⟨hs, hu, hlt⟩
      simp only [List.mem_singleton] at hs hu
      subst hs; subst hu
      exact absurd hlt (lt_irrefl _)

/-- **Solvability of a totally ordered problem is decided by the proof tuples of Erol, Hendler
and Nau.**  For a well-formed, totally ordered problem whose methods have at most two subtasks
and whose initial task network is the single compound task `c₀`, the problem is solvable iff
the triple `(s₀, c₀, s')` is derivable for some goal state `s'`.

This is the source side of the compilation of totally ordered problems into acyclic ones
(`HtnComplexity/ToHtnAc/ToHtnAc.lean`): it combines the normal form theorem
`Problem.solvable_iff_yieldSeq` with the correctness `HTN.Domain.provable_iff_yield` of the
proof-tuple characterisation. -/
theorem solvable_iff_provable [Infinite I] (hwf : P.WF) (hto : P.IsTO_M)
    (hbody : ∀ c bs, P.domain.SeqBody c bs → bs.length ≤ 2)
    {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀) :
    P.Solvable ↔ ∃ s' : Set F, P.domain.Provable P.init (Sum.inr c₀) s' ∧ P.GoalState s' := by
  have h₀ : P.tnI.IsSeqNet [t₀] [Sum.inr c₀] := by
    have h := TaskNetwork.isSeqNet_singleton hwf.tnI hT
    rwa [hα] at h
  rw [solvable_iff_yieldSeq hwf hto h₀]
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    refine ⟨P.transitionSeq as P.init, ?_, hgoal⟩
    exact (Domain.provable_iff_yield _ _ _).2
      ⟨as, (Domain.yield_iff_yieldSeq_singleton hbody).2 hy, happ, rfl⟩
  · rintro ⟨s', hprov, hgoal⟩
    obtain ⟨as, hy, happ, rfl⟩ := (Domain.provable_iff_yield _ _ _).1 hprov
    exact ⟨as, (Domain.yield_iff_yieldSeq_singleton hbody).1 hy, happ, hgoal⟩

end NormalForm

end Problem

end HTN
