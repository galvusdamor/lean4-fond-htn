import HtnComplexity.Computable.PoRank
import HtnComplexity.Regular.RegularBound
/-!
# The invariant of the progression search of a regular domain description

The search of `HtnComplexity/Computable/PoSearch.lean` explores configurations
`(state, search network)`.  For a **regular** domain description the reachable configurations
stay small, and this file proves it, by carrying along the search the invariant

* the search network satisfies `HTN.Syn.PNet.Ok`;
* every fact of the state occurs in `HTN.Syn.allFacts d q` — the initial facts and the facts
  some action adds;
* every label of a task still to be processed occurs in `HTN.Syn.allLbls d q` — the labels of
  the initial task network and of the listed methods;
* the denoted task network satisfies the **slot invariant** of
  `HtnComplexity/Regular/RegularBound.lean` with `HTN.Syn.slotCount q` slots of
  `HTN.Syn.slotSize d` tasks.

The last item is the substantial one; it gives the bound `HTN.Syn.RegInv.length_ids_le`: a
reachable search network has at most `HTN.Syn.bnd d q` tasks left to process.  The slot
invariant is preserved because a decomposition replaces a task by the body of a regular method,
which is inserted into the slot the decomposed task had to itself.
-/

namespace HTN

namespace Syn

/-- The facts a reachable state can contain: the initial facts and the facts an action adds. -/
def allFacts (d : DomDesc) (q : InstDesc) : List ℕ :=
  q.initList ++ d.actions.flatMap (fun e => e.2.2.1)

/-- The labels a reachable task can carry: the labels of the initial task network, the labels of
the listed methods, and the default label `(false, 0)`. -/
def allLbls (d : DomDesc) (q : InstDesc) : List (Bool × ℕ) :=
  (false, 0) :: (q.tnI.lbl.map (fun p => p.2) ++
    d.methods.flatMap (fun e => e.2.lbl.map (fun p => p.2)))

/-- The number of slots: one for every task of the initial task network. -/
def slotCount (q : InstDesc) : ℕ := q.tnI.ids.length

/-- The size of a slot: the number of subtasks of the largest listed method (but at least one,
for the tasks of the initial network). -/
def slotSize (d : DomDesc) : ℕ := max (maxBody d) 1

/-- The bound on the number of tasks of a reachable search network. -/
def bnd (d : DomDesc) (q : InstDesc) : ℕ := slotSize d * slotCount q

/-- **The generic invariant the bounded search relies on**: the search network is well formed,
the state and the labels come from the two vocabularies of the description, and at most `B`
tasks are left to process.  It is all that
`HtnComplexity/Computable/RegNorm.lean` and `HtnComplexity/Computable/RegDecide.lean`
use; which class of descriptions supplies the bound `B` is immaterial there. -/
structure CfgInv (d : DomDesc) (q : InstDesc) (B : ℕ) (c : PConfig) : Prop where
  /-- The search network is well formed. -/
  ok : PNet.Ok c.2
  /-- Every fact of the state is one of the facts the description mentions. -/
  facts : ∀ f ∈ c.1, f ∈ allFacts d q
  /-- Every label still to be processed is one of the labels the description mentions. -/
  lbls : ∀ x ∈ c.2, x.2.2.1 = true → x.2.1 ∈ allLbls d q
  /-- At most `B` tasks are left to process. -/
  small : c.2.ids.length ≤ B

/-- **The invariant of the search for a regular domain description.** -/
structure RegInv (d : DomDesc) (q : InstDesc) (c : PConfig) : Prop where
  /-- The search network is well formed. -/
  ok : PNet.Ok c.2
  /-- Every fact of the state is one of the facts the description mentions. -/
  facts : ∀ f ∈ c.1, f ∈ allFacts d q
  /-- Every label still to be processed is one of the labels the description mentions. -/
  lbls : ∀ x ∈ c.2, x.2.2.1 = true → x.2.1 ∈ allLbls d q
  /-- The denoted task network satisfies the slot invariant. -/
  slot : (PNet.toTN c.2).SlotBounded (slotCount q) (slotSize d)

/-- The identifiers still to be processed are pairwise distinct. -/
theorem PNet.Ok.nodup_ids {p : PNet} (h : PNet.Ok p) : p.ids.Nodup := by
  have hsub : List.Sublist ((p.filter (fun x => x.2.2.1)).map (fun x => x.1))
      (p.map (fun x => x.1)) := List.filter_sublist.map _
  exact List.Nodup.sublist hsub h.nodup

/-- **A search network with the invariant has at most `bnd d q` tasks left.** -/
theorem RegInv.length_ids_le {d : DomDesc} {q : InstDesc} {c : PConfig} (h : RegInv d q c) :
    c.2.ids.length ≤ bnd d q := by
  have hnd : c.2.ids.Nodup := h.ok.nodup_ids
  have hcard : c.2.ids.toFinset.card = c.2.ids.length := List.toFinset_card_of_nodup hnd
  have := h.slot.card_le
  rw [PNet.toTN_T, hcard] at this
  exact this

/-! ### A counting helper -/

/-- A list without duplicates is no longer than any list containing it. -/
theorem nodup_length_le {α : Type} [DecidableEq α] {l m : List α} (h : l.Nodup)
    (hs : ∀ x ∈ l, x ∈ m) : l.length ≤ m.length :=
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup h).symm
    _ ≤ m.toFinset.card := Finset.card_le_card (by
        intro x hx
        simp only [List.mem_toFinset] at hx ⊢
        exact hs x hx)
    _ ≤ m.length := List.toFinset_card_le _

/-! ### The two lists are large enough -/

/-- The label of an identifier is either the default or one of the listed labels. -/
theorem lblPair_cases (t : TnDesc) (i : ℕ) :
    t.lblPair i = (false, 0) ∨ t.lblPair i ∈ t.lbl.map (fun p => p.2) := by
  rcases hl : t.lbl.lookup i with _ | ⟨b, n⟩
  · exact Or.inl (by simp [TnDesc.lblPair, hl])
  · refine Or.inr ?_
    have hmem : (i, b, n) ∈ t.lbl := mem_of_lookup_eq_some hl
    have : t.lblPair i = (b, n) := by simp [TnDesc.lblPair, hl]
    rw [this]
    exact List.mem_map_of_mem hmem

theorem lblPair_tnI_mem_allLbls (d : DomDesc) (q : InstDesc) (i : ℕ) :
    q.tnI.lblPair i ∈ allLbls d q := by
  rcases lblPair_cases q.tnI i with h | h
  · simp [allLbls, h]
  · simp only [allLbls, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl h)

theorem lblPair_method_mem_allLbls {d : DomDesc} {q : InstDesc} {e : MethodDesc}
    (he : e ∈ d.methods) (i : ℕ) : e.2.lblPair i ∈ allLbls d q := by
  rcases lblPair_cases e.2 i with h | h
  · simp [allLbls, h]
  · simp only [allLbls, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (List.mem_flatMap.2 ⟨e, he, h⟩))

theorem mem_allFacts_of_mem_add {d : DomDesc} {q : InstDesc} {a f : ℕ}
    (hf : f ∈ (actOf d a).2.1) : f ∈ allFacts d q := by
  simp only [allFacts, List.mem_append]
  refine Or.inr (List.mem_flatMap.2 ?_)
  rw [actOf_eq] at hf
  rcases hl : d.actions.lookup a with _ | v
  · rw [hl] at hf
    simp at hf
  · rw [hl] at hf
    exact ⟨(a, v), mem_of_lookup_eq_some hl, hf⟩

theorem one_le_slotSize (d : DomDesc) : 1 ≤ slotSize d := le_max_right _ _

/-! ### The invariant holds initially -/

theorem regInv_initConfig (d : DomDesc) (q : InstDesc) : RegInv d q (initConfig q) := by
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
  · refine ⟨fun i => q.tnI.ids.idxOf i, ?_, ?_, ?_⟩
    · intro t ht
      rw [hT, List.mem_toFinset] at ht
      exact List.idxOf_lt_length_of_mem ht
    · intro s
      refine le_trans (Finset.card_le_one.2 ?_) (one_le_slotSize d)
      intro a ha b hb
      simp only [Finset.mem_filter, hT, List.mem_toFinset] at ha hb
      exact (List.idxOf_inj ha.1).1 (ha.2.trans hb.2.symm)
    · intro c hc _ x hx hxc hown
      exfalso
      simp only [hT, List.mem_toFinset] at hc hx
      exact hxc ((List.idxOf_inj hx).1 hown)

/-- The invariant of a regular description is an instance of the generic one. -/
theorem RegInv.toCfgInv {d : DomDesc} {q : InstDesc} {c : PConfig} (h : RegInv d q c) :
    CfgInv d q (bnd d q) c :=
  ⟨h.ok, h.facts, h.lbls, h.length_ids_le⟩

/-! ### The invariant is preserved -/

theorem RegInv.step {d : DomDesc} {q : InstDesc} {c c' : PConfig} (hd : d.MethodsReg)
    (h : RegInv d q c) (hstep : PStep d c c') : RegInv d q c' := by
  obtain ⟨x, hx, hcase⟩ := mem_succsOf_iff.1 hstep
  obtain ⟨hxm, hpres, hdeps⟩ := mem_readyItems.1 hx
  have hids : x.1 ∈ c.2.ids := PNet.mem_ids.2 ⟨x, hxm, rfl, hpres⟩
  have hdepsnil : c.2.deps x.1 = [] := by rw [PNet.deps_eq_of_mem hxm h.ok.nodup, hdeps]
  obtain ⟨own, hown⟩ := h.slot
  rcases hcase with ⟨e, he, hk, -, rfl⟩ | ⟨hk, -, rfl⟩
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
      have habs : (PNet.toTN c.2).IsAbstractId x.1 := by
        refine ⟨x.2.1.2, ?_⟩
        rw [hlbl]
        exact TnDesc.ofPair_eq_inr_iff.2 (by rw [← hk])
      have hreg : ((TnDesc.shift c.2.freshOff e.2).toTaskNetwork).IsRegular :=
        TaskNetwork.Iso.isRegular (TnDesc.shift_iso _ _) (hd e he)
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
      exact ⟨_, hown.decompose hu habs hreg hcard⟩
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

theorem RegInv.reach {d : DomDesc} {q : InstDesc} {c c' : PConfig} (hd : d.MethodsReg)
    (h : RegInv d q c) (hreach : PReach d c c') : RegInv d q c' := by
  induction hreach with
  | refl => exact h
  | tail _ hstep ih => exact ih.step hd hstep

end Syn

end HTN
