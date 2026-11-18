import HtnComplexity.Computable.TrRank
import HtnComplexity.Regular.TailRecBound
/-!
# The invariant of the progression search of a tail-recursive domain description

This is for `HTN-TR` what `HtnComplexity/Computable/RegInv.lean` is for `HTN-REG`: the
search of `HtnComplexity/Computable/PoSearch.lean` keeps the reachable configurations
small, here because the denoted task network satisfies the **address invariant** of
`HtnComplexity/Regular/TailRecBound.lean` — the live tasks form a forest of processes of depth at
most the maximal rank, and a compound task is ordered after everything else at its address.

* `HTN.Syn.trK`, `HTN.Syn.trR`, `HTN.Syn.trBnd` — the branching, the depth and the resulting
  bound on the number of open tasks, all computable and all arithmetic in the two vocabularies
  of the description;
* `HTN.Syn.TrInv` — the invariant, `HTN.Syn.trInv_initConfig` and `HTN.Syn.TrInv.step`;
* `HTN.Syn.TrInv.length_ids_le` and `HTN.Syn.TrInv.toCfgInv` — a reachable search network has
  at most `HTN.Syn.trBnd d q` tasks left, so the generic invariant of
  `HtnComplexity/Computable/RegInv.lean` holds with that bound.

The rank is the computed one of `HtnComplexity/Computable/TrRank.lean`; it is bounded by
the number of labels the description mentions, which is what makes the depth `HTN.Syn.trR`
computable.
-/

namespace HTN

namespace Syn

/-! ### The parameters of the invariant -/

/-- The branching of the forest of addresses: enough for the initial tasks and for the subtasks
of a method. -/
def trK (d : DomDesc) (q : InstDesc) : ℕ := max (slotSize d) (slotCount q)

/-- The depth of the forest of addresses: one more than the largest rank. -/
def trR (d : DomDesc) (q : InstDesc) : ℕ := (allLbls d q).length + 1

/-- **The bound on the number of tasks** of a search network reachable in a tail-recursive
description. -/
def trBnd (d : DomDesc) (q : InstDesc) : ℕ := slotSize d * (trK d q + 1) ^ trR d q

/-! ### The computed rank is bounded by the vocabulary -/

theorem mem_allLbls_of_mem_compTargets {d : DomDesc} {q : InstDesc} {z : ℕ}
    (h : z ∈ compTargets d) : (true, z) ∈ allLbls d q := by
  obtain ⟨a, ha⟩ := mem_compTargets.1 h
  obtain ⟨e, he, -, x, hx, hlab⟩ := mem_compEdges.1 ha
  have hpair : e.2.lblPair x = (true, z) :=
    TnDesc.ofPair_eq_inr_iff.1 (by rw [TnDesc.ofPair_lblPair, hlab])
  have := lblPair_method_mem_allLbls (q := q) he x
  rwa [hpair] at this

/-- **The computed rank never exceeds the number of labels** the description mentions. -/
theorem rkT_le_length_allLbls (d : DomDesc) (q : InstDesc) (c : ℕ) :
    rkT d c ≤ (allLbls d q).length := by
  classical
  have hnd : ((compTargets d).dedup.filter fun z => sBelowB d c z).Nodup :=
    (List.nodup_dedup _).filter _
  have hsub : ∀ z ∈ (compTargets d).dedup.filter fun z => sBelowB d c z,
      z ∈ (allLbls d q).map fun p => p.2 := by
    intro z hz
    have hz' : z ∈ compTargets d := List.mem_dedup.1 (List.mem_of_mem_filter hz)
    exact List.mem_map.2 ⟨(true, z), mem_allLbls_of_mem_compTargets hz', rfl⟩
  have := nodup_length_le hnd hsub
  rwa [List.length_map] at this

/-! ### The invariant -/

/-- **The invariant of the search for a tail-recursive domain description.** -/
structure TrInv (d : DomDesc) (q : InstDesc) (c : PConfig) : Prop where
  /-- The search network is well formed. -/
  ok : PNet.Ok c.2
  /-- Every fact of the state is one of the facts the description mentions. -/
  facts : ∀ f ∈ c.1, f ∈ allFacts d q
  /-- Every label still to be processed is one of the labels the description mentions. -/
  lbls : ∀ x ∈ c.2, x.2.2.1 = true → x.2.1 ∈ allLbls d q
  /-- The denoted task network satisfies the address invariant. -/
  addr : (PNet.toTN c.2).AddrBounded (rkT d) (trK d q) (trR d q) (slotSize d)

/-- **A search network with the invariant has at most `trBnd d q` tasks left.** -/
theorem TrInv.length_ids_le {d : DomDesc} {q : InstDesc} {c : PConfig} (h : TrInv d q c) :
    c.2.ids.length ≤ trBnd d q := by
  have hnd : c.2.ids.Nodup := h.ok.nodup_ids
  have hcard : c.2.ids.toFinset.card = c.2.ids.length := List.toFinset_card_of_nodup hnd
  have := h.addr.card_le
  rw [PNet.toTN_T, hcard] at this
  exact this

/-- The invariant of a tail-recursive description is an instance of the generic one. -/
theorem TrInv.toCfgInv {d : DomDesc} {q : InstDesc} {c : PConfig} (h : TrInv d q c) :
    CfgInv d q (trBnd d q) c :=
  ⟨h.ok, h.facts, h.lbls, h.length_ids_le⟩

/-! ### The invariant holds initially -/

theorem trInv_initConfig (d : DomDesc) (q : InstDesc) : TrInv d q (initConfig q) := by
  classical
  have hT : (PNet.toTN (initConfig q).2).T = q.tnI.ids.toFinset := by
    rw [toTN_initConfig]
    rfl
  refine ⟨ok_initConfig q, ?_, ?_, ?_⟩
  · intro f hf
    simp only [allFacts, List.mem_append]
    exact Or.inl hf
  · intro z hz _
    simp only [initConfig, PNet.ofTnDesc, List.mem_map] at hz
    obtain ⟨y, -, rfl⟩ := hz
    exact lblPair_tnI_mem_allLbls d q y
  · refine ⟨fun i => [q.tnI.ids.idxOf i], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t _
      simp only [List.length_cons, List.length_nil, trR]
      omega
    · intro t ht i hi
      rw [hT, List.mem_toFinset] at ht
      have hi' : i = q.tnI.ids.idxOf t := by simpa using hi
      have : q.tnI.ids.idxOf t < slotCount q := List.idxOf_lt_length_of_mem ht
      have hle : slotCount q ≤ trK d q := le_max_right _ _
      omega
    · intro a
      refine le_trans (Finset.card_le_one.2 ?_) (one_le_slotSize d)
      intro u hu v hv
      simp only [Finset.mem_filter, hT, List.mem_toFinset] at hu hv
      have : q.tnI.ids.idxOf u = q.tnI.ids.idxOf v := by
        have h1 : [q.tnI.ids.idxOf u] = a := hu.2
        have h2 : [q.tnI.ids.idxOf v] = a := hv.2
        simpa using h1.trans h2.symm
      exact (List.idxOf_inj hu.1).1 this
    · intro cc hc _ y hy hne hown
      exfalso
      simp only [hT, List.mem_toFinset] at hc hy
      exact hne ((List.idxOf_inj hy).1 (by simpa using hown))
    · intro cc _ _ y _ hpre hne
      exfalso
      exact hne (hpre.eq_of_length (by simp)).symm
    · intro cc _ n _
      have := rkT_le_length_allLbls d q n
      simp only [List.length_cons, List.length_nil, trR]
      omega

/-! ### The invariant is preserved -/

theorem TrInv.step {d : DomDesc} {q : InstDesc} {c c' : PConfig} (hd : d.IsTailRec)
    (h : TrInv d q c) (hstep : PStep d c c') : TrInv d q c' := by
  obtain ⟨x, hx, hcase⟩ := mem_succsOf_iff.1 hstep
  obtain ⟨hxm, hpres, hdeps⟩ := mem_readyItems.1 hx
  have hids : x.1 ∈ c.2.ids := PNet.mem_ids.2 ⟨x, hxm, rfl, hpres⟩
  have hdepsnil : c.2.deps x.1 = [] := by rw [PNet.deps_eq_of_mem hxm h.ok.nodup, hdeps]
  obtain ⟨own, hown⟩ := h.addr
  rcases hcase with ⟨e, he, hk, hename, rfl⟩ | ⟨hk, -, rfl⟩
  · -- decomposition
    refine ⟨PNet.expand_ok h.ok hids e, h.facts, ?_, ?_⟩
    · intro z hz hlive
      rcases List.mem_append.1 hz with hz' | hz'
      · simp only [PNet.oldItems, List.mem_map] at hz'
        obtain ⟨y, hy, rfl⟩ := hz'
        by_cases hyi : y.1 = x.1
        · rw [if_pos hyi] at hlive
          exact absurd hlive (by simp)
        · rw [if_neg hyi] at hlive ⊢
          exact h.lbls y hy hlive
      · simp only [PNet.newItems, List.mem_map] at hz'
        obtain ⟨y, -, rfl⟩ := hz'
        exact lblPair_method_mem_allLbls he y
    · rw [PNet.toTN_expand h.ok hids e]
      have hu : (PNet.toTN c.2).Unconstrained x.1 := unconstrained_of_ready h.ok hx
      have hlbl : (PNet.toTN c.2).α x.1 = TnDesc.ofPair x.2.1 :=
        PNet.label_eq_of_head hxm rfl h.ok.nodup
      have hα : (PNet.toTN c.2).α x.1 = Sum.inr x.2.1.2 := by
        rw [hlbl]
        exact TnDesc.ofPair_eq_inr_iff.2 (by rw [← hk])
      have hcard : ((TnDesc.shift c.2.freshOff e.2).toTaskNetwork).T.card ≤ slotSize d := by
        have h1 : ((TnDesc.shift c.2.freshOff e.2).toTaskNetwork).T
            = (e.2.ids.map (fun y => c.2.freshOff + y)).toFinset := rfl
        have h2 : (e.2.ids.map (fun y => c.2.freshOff + y)).toFinset.card
            ≤ e.2.ids.dedup.length := by
          have himg : (e.2.ids.map (fun y => c.2.freshOff + y)).toFinset
              = e.2.ids.toFinset.image (fun y => c.2.freshOff + y) := by ext z; simp
          rw [himg]
          refine le_trans Finset.card_image_le ?_
          rw [show e.2.ids.toFinset = e.2.ids.dedup.toFinset by ext z; simp]
          exact List.toFinset_card_le _
        have h4 : e.2.ids.dedup.length ≤ maxBody d :=
          le_foldr_max (List.mem_map_of_mem he)
        rw [h1]
        exact le_trans h2 (le_trans h4 (le_max_left _ _))
      have hbody : ∀ y ∈ ((TnDesc.shift c.2.freshOff e.2).toTaskNetwork).T, ∀ n : ℕ,
          ((TnDesc.shift c.2.freshOff e.2).toTaskNetwork).α y = Sum.inr n →
          (((TnDesc.shift c.2.freshOff e.2).toTaskNetwork).IsLastId y →
              rkT d n ≤ rkT d x.2.1.2) ∧
            (¬ ((TnDesc.shift c.2.freshOff e.2).toTaskNetwork).IsLastId y →
              rkT d n < rkT d x.2.1.2) := by
        refine TaskNetwork.Iso.tailRecBody (TnDesc.shift_iso _ _) ?_
        intro y hy n hn
        have := tailRecBy_rkT hd e he y hy n hn
        rwa [hename] at this
      exact h.addr.decompose hu hα (PNet.disjoint_shift c.2 e) hcard (one_le_slotSize d)
        (le_max_left _ _) hbody
  · -- progression
    refine ⟨PNet.finish_ok h.ok x.1, ?_, ?_, ?_⟩
    · intro f hf
      rcases List.mem_append.1 hf with hf' | hf'
      · exact h.facts f (List.mem_of_mem_filter hf')
      · exact mem_allFacts_of_mem_add hf'
    · intro z hz hlive
      simp only [PNet.finish, List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      by_cases hyi : y.1 = x.1
      · rw [if_pos hyi] at hlive
        exact absurd hlive (by simp)
      · rw [if_neg hyi] at hlive ⊢
        exact h.lbls y hy hlive
    · rw [PNet.toTN_finish hdepsnil]
      exact ⟨own, hown.progress _⟩

theorem TrInv.reach {d : DomDesc} {q : InstDesc} {c c' : PConfig} (hd : d.IsTailRec)
    (h : TrInv d q c) (hreach : PReach d c c') : TrInv d q c' := by
  induction hreach with
  | refl => exact h
  | tail _ hstep ih => exact ih.step hd hstep

end Syn

end HTN
