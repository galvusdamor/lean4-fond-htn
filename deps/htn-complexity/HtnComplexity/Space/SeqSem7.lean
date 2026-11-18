import HtnComplexity.Space.SeqSem6
import HtnComplexity.Space.TblMachine
/-!
# The accepting test, the marker rows and the canonical configuration

* `HTN.Space.SeqM.seqAccB_iff` — the accepting test reads the flag bit of the advice and checks
  that the configuration contains the compiled goal `seqGoal d q`;
* `HTN.Space.SeqM.solvableTbl_markRows` — the two marker rows (no add or delete effects) do not
  change solvability;
* `HTN.Space.SeqM.canon_seqInitB` — the canonical configuration (the compiled initial state of
  the gadget instance for the canonical witness) passes the initial test; its length is linear in
  the length of the code of the instance.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### The accepting test -/

theorem mem_seqGoal {d : DomDesc} {q : InstDesc} {f : ℕ} :
    f ∈ seqGoal d q ↔ (∃ v ∈ q.goalList, f = cfI v) ∨ f = cfG .fin ∨ f = 0 := by
  simp only [seqGoal, List.map_append, List.map_map, List.mem_append, List.mem_map,
    Function.comp_apply, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((⟨v, hv, rfl⟩ | rfl) | rfl)
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (⟨v, hv, rfl⟩ | rfl | rfl)
    · exact Or.inl (Or.inl ⟨v, hv, rfl⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl

theorem entFin_eq : entFin = entN (cfG .fin) := by rw [entFin, entN, bitsOfNat_cfG]

theorem nilEnt_eq' : nilEnt = entN 0 := by simp [nilEnt, entN]

/-- **The accepting test.** -/
theorem seqAccB_iff {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (d : DomDesc)
    (q : InstDesc) (b : Bool) (tbl : List Row) :
    seqAccB (blist S) (instSer q) (tblAdv b tbl) = true ↔
      (b = true ∧ ∀ f ∈ seqGoal d q, f ∈ decSt S) := by
  have hrev : ((tblAdv b tbl).reverse.headD false) = b := by simp [tblAdv]
  rw [seqAccB, hrev, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, goal_iff,
    entFin_eq, occB_S hS, nilEnt_eq', occB_S hS]
  have hI : ∀ v, tagI3 ++ bitsOfNat v ∈ S ↔ cfI v ∈ decSt S := fun v => by
    rw [mem_S_iff hS, bitsOfNat_cfI]
  simp only [hI]
  constructor
  · rintro ⟨⟨⟨hb, hg⟩, hfin⟩, h0⟩
    refine ⟨hb, fun f hf => ?_⟩
    rcases mem_seqGoal.1 hf with ⟨v, hv, rfl⟩ | rfl | rfl
    · exact hg v hv
    · exact hfin
    · exact h0
  · rintro ⟨hb, h⟩
    exact ⟨⟨⟨hb, fun v hv => h _ (mem_seqGoal.2 (Or.inl ⟨v, hv, rfl⟩))⟩,
      h _ (mem_seqGoal.2 (Or.inr (Or.inl rfl)))⟩, h _ (mem_seqGoal.2 (Or.inr (Or.inr rfl)))⟩

/-! ### The marker rows -/

theorem reachTbl_markRows {d : DomDesc} {T : List Row} {u v : List ℕ}
    (h : ReachTbl (markRows d K ++ T) u v) : ∃ w, ReachTbl T u w ∧ ∀ f, f ∈ w ↔ f ∈ v := by
  induction h with
  | refl => exact ⟨u, Relation.ReflTransGen.refl, fun _ => Iff.rfl⟩
  | @tail v v' _ hstep ih =>
    obtain ⟨w, hw, hwv⟩ := ih
    obtain ⟨row, hrow, hprec, hpost⟩ := hstep
    rcases List.mem_append.1 hrow with hm | hm
    · have hnil : row.2.1 = [] ∧ row.2.2 = [] := by
        simp only [markRows, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> exact ⟨rfl, rfl⟩
      refine ⟨w, hw, fun f => ?_⟩
      rw [hwv, hpost, hnil.1, hnil.2]
      simp
    · obtain ⟨t, ht, htv⟩ := exists_run_of_congr
        (Relation.ReflTransGen.single (show StepTbl T v v' from ⟨row, hm, hprec, hpost⟩))
        (u' := w) hwv
      exact ⟨t, hw.trans ht, htv⟩

/-- **The marker rows do not change solvability.** -/
theorem solvableTbl_markRows {d : DomDesc} {T : List Row} {u g : List ℕ} :
    SolvableTbl (markRows d K ++ T) u g ↔ SolvableTbl T u g := by
  constructor
  · rintro ⟨s, hs, hg⟩
    obtain ⟨w, hw, hws⟩ := reachTbl_markRows hs
    exact ⟨w, hw, fun f hf => (hws f).2 (hg f hf)⟩
  · rintro ⟨s, hs, hg⟩
    refine ⟨s, Relation.ReflTransGen.mono (fun a b hab => ?_) hs, hg⟩
    obtain ⟨row, hrow, hprec, hpost⟩ := hab
    exact ⟨row, List.mem_append_right _ hrow, hprec, hpost⟩

/-- The root numeral is written into the advice. -/
theorem length_bitsOfNat_cRoot_le (d : DomDesc) (K : ℕ) (b : Bool) (T : List Row) :
    (bitsOfNat (cRoot d)).length ≤ (tblAdv b (markRows d K ++ T)).length := by
  have hmem : factEnt 0 tagPrec (cRoot d) ∈ factEnts (markRows d K ++ T) := by
    rw [mem_factEnts_prec (by simp [markRows])]
    simp [rowOf, markRows]
  have h1 := le_length_blist_of_mem hmem
  have h2 : (bitsOfNat (cRoot d)).length ≤ (factEnt 0 tagPrec (cRoot d)).length := by
    simp only [factEnt, List.length_append, length_rowId]
    omega
  have h3 : (blist (factEnts (markRows d K ++ T))).length ≤ (tblAdv b (markRows d K ++ T)).length := by
    simp [tblAdv]
    omega
  omega

/-! ### The canonical configuration -/

section Canon

variable {d : DomDesc} {K : ℕ} {q : InstDesc}

theorem card_eq_length_lin (hTO : q.tnI.toTaskNetwork.IsTotallyOrdered) :
    q.tnI.ids.toFinset.card = q.tnI.lin.length := by
  rw [← List.toFinset_card_of_nodup (TnDesc.isLinearization_lin hTO).1]
  congr 1
  ext i
  simp only [List.mem_toFinset]
  exact (mem_lin_iff hTO).symm

open Classical in
theorem rval_le_card (hTO : q.tnI.toTaskNetwork.IsTotallyOrdered) (a : ℕ) :
    rval q.tnI a ≤ q.tnI.ids.toFinset.card := by
  refine Finset.sup_le fun j hj => ?_
  rw [Finset.mem_filter, List.mem_toFinset] at hj
  have h1 : lpos q.tnI j < q.tnI.lin.length :=
    List.idxOf_lt_length_of_mem ((mem_lin_iff hTO).2 hj.1)
  rw [card_eq_length_lin hTO]
  exact h1.le

/-- The canonical configuration: the compiled initial state of the gadget instance for the
canonical witness, without repetitions. -/
noncomputable def canonCfg (d : DomDesc) (q : InstDesc) (xs : List (ℕ ⊕ ℕ)) : List ℕ :=
  (regInitR (seqInst (code d) d q xs (canonWit q.tnI))).dedup

theorem initOk_canonCfg (hq : q.IsTO) {xs : List (ℕ ⊕ ℕ)} (hx : WitSeq q.tnI (canonWit q.tnI) xs) :
    InitOk d q (canonCfg d q xs) :=
  initOk_of_eqv (witOk_canonWit hq) hx fun _ => List.mem_dedup

theorem wit_canonCfg (hq : q.IsTO) {xs : List (ℕ ⊕ ℕ)} {p a : ℕ}
    (h : cfG (.wit p a) ∈ canonCfg d q xs) : a ∈ wnodes q.tnI ∧ p ≤ q.tnI.ids.toFinset.card := by
  rw [canonCfg, List.mem_dedup, cfG_mem_regInitR, wit_mem_stat_iff] at h
  rcases h with h | h
  · cases h
  · obtain ⟨ha, rfl⟩ := mem_canonWit.1 h
    exact ⟨ha, rval_le_card hq a⟩

/-- **The canonical configuration passes the initial test.** -/
theorem canon_seqInitB (hq : q.IsTO) {xs : List (ℕ ⊕ ℕ)} (hx : WitSeq q.tnI (canonWit q.tnI) xs)
    (hK : (instSer q).length ≤ K) (b : Bool) (T : List Row) :
    seqInitB (blist ((canonCfg d q xs).map bitsOfNat)) (instSer q)
      (tblAdv b (markRows d K ++ T)) = true := by
  have hS := canon_map_bitsOfNat (canonCfg d q xs)
  refine seqInitB_of_initOk hS hK ?_ ?_
  · rw [decSt_map_bitsOfNat]; exact initOk_canonCfg hq hx
  · intro p a h
    rw [decSt_map_bitsOfNat] at h
    exact wit_canonCfg hq h

theorem length_wnodes_le (q : InstDesc) : (wnodes q.tnI).length ≤ 2 * (instSer q).length := by
  have hx := congrArg List.length (instSer_split q)
  simp only [List.length_append] at hx
  have h1 := length_succ_le_length_blist (q.tnI.ids.map bitsOfNat)
  have h2 := length_succ_le_length_blist (q.tnI.ordList.map serPair)
  simp only [List.length_map] at h1 h2
  have h3 : ∀ l : List (ℕ × ℕ), (l.flatMap fun e => [e.1, e.2]).length = 2 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons e l ih => simp [List.flatMap_cons, ih]; ring
  rw [wnodes, List.length_append, h3]
  omega

/-- **The canonical configuration is short.** -/
theorem length_canonCfg_le {xs : List (ℕ ⊕ ℕ)} (hx : WitSeq q.tnI (canonWit q.tnI) xs) :
    (canonCfg d q xs).length ≤ 5 * (instSer q).length + 3 := by
  have h1 : (canonCfg d q xs).length ≤ (regInitR (seqInst (code d) d q xs (canonWit q.tnI))).length :=
    List.Sublist.length_le (List.dedup_sublist _)
  have hxs : xs.length ≤ (instSer q).length := hx.1 ▸ card_ids_le q
  have hw := length_wnodes_le q
  have hinit : q.initList.length + 1 ≤ (instSer q).length := by
    have := length_succ_le_length_blist (q.initList.map bitsOfNat)
    have hx' := congrArg List.length (instSer_split q)
    simp only [List.length_append, List.length_map] at hx' this
    omega
  have hf : ((List.range xs.length).filter
      (fun p => unknownPrimB d (xs.getD p (Sum.inl 0)))).length ≤ xs.length := by
    have := List.length_filter_le (fun p => unknownPrimB d (xs.getD p (Sum.inl 0)))
      (List.range xs.length)
    simpa using this
  simp only [regInitR, seqInst, gadInit, gadStatic, canonWit, InstDesc.initList, List.length_append,
    List.length_map, List.length_cons, List.length_range, List.length_nil] at h1
  have hg : q.1.length = q.initList.length := rfl
  omega

end Canon

end SeqM

end Space

end HTN
