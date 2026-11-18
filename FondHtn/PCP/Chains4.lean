import FondHtn.PCP.Decomp
import FondHtn.FixedMethodsLemmas
/-!
# Strong OD solvability of chain problems with four roots

**`FOND.PCP.strongOD_iff_cwin`**: for a chain problem with four roots, strong OD solvability is:
some complete derivation from each root, such that the chain game
(`FOND.AcycHard.CWin`) on the four label words — the first as control chain, the others as
pool — is won from the initial state.
-/

namespace FOND

namespace PCP

open HTN FOND.AcycHard

variable {F : Type} {P : Problem F ℕ ℕ ℕ}

/-- The primitive label of a task (`0` for compound tasks). -/
def lbl (tn : TaskNetwork ℕ ℕ ℕ) (t : ℕ) : ℕ := Sum.elim id (fun _ => 0) (tn.α t)

theorem isChains_of_inv {tn : TaskNetwork ℕ ℕ ℕ} {root : ℕ → ℕ} {ids : ℕ → List ℕ}
    {pend : ℕ → Option ℕ} {st : ℕ → List ℕ × Option ℕ} (h : Inv P tn 4 root ids pend st)
    (hprim : tn.IsPrimitive) :
    IsChains tn (ids 0) ([ids 1, ids 2, ids 3] : Multiset (List ℕ)) (lbl tn) ∧
      ∀ i < 4, (ids i).map (lbl tn) = (st i).1 ∧ (st i).2 = none := by
  have hpn : ∀ i < 4, pend i = none := fun i hi => (h.pend_none hprim hi).1
  have hseq : ∀ i < 4, ids i ++ (pend i).toList = ids i := fun i hi => by simp [hpn i hi]
  have h4 : ∀ (Q : ℕ → Prop), (∃ i < 4, Q i) ↔ Q 0 ∨ Q 1 ∨ Q 2 ∨ Q 3 := by
    intro Q
    constructor
    · rintro ⟨i, hi, hq⟩
      interval_cases i <;> simp_all
    · rintro (h | h | h | h) <;> exact ⟨_, by omega, h⟩
  have hpool : ∀ (Q : List ℕ → Prop), (∃ c ∈ ([ids 1, ids 2, ids 3] : Multiset (List ℕ)), Q c) ↔
      Q (ids 1) ∨ Q (ids 2) ∨ Q (ids 3) := by
    intro Q; simp
  have hdisj : ∀ i j, i < 4 → j < 4 → i ≠ j → ∀ x ∈ ids i, x ∉ ids j := by
    intro i j hi hj hij x hx hx'
    exact h.disj i j hi hj hij x (by rw [hseq i hi]; exact hx) (by rw [hseq j hj]; exact hx')
  refine ⟨⟨fun x => ?_, fun a b => ?_, fun t ht => ?_, ?_, ?_, ?_, ?_⟩, fun i hi => ⟨?_, ?_⟩⟩
  · rw [h.mem, h4 (fun i => x ∈ ids i ++ (pend i).toList), hpool]
    simp only [hseq 0 (by omega), hseq 1 (by omega), hseq 2 (by omega), hseq 3 (by omega)]
  · rw [h.ord, h4 (fun i => Before (ids i ++ (pend i).toList) a b), hpool]
    simp only [hseq 0 (by omega), hseq 1 (by omega), hseq 2 (by omega), hseq 3 (by omega)]
  · obtain ⟨a, ha⟩ := hprim t ht
    simp [lbl, ha]
  · simpa [hseq 0 (by omega)] using h.nodup 0 (by omega)
  · intro c hc
    simp only [Multiset.mem_coe, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simpa [hseq 1 (by omega)] using h.nodup 1 (by omega)
    · simpa [hseq 2 (by omega)] using h.nodup 2 (by omega)
    · simpa [hseq 3 (by omega)] using h.nodup 3 (by omega)
  · intro c hc t ht
    simp only [Multiset.mem_coe, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hdisj 1 0 (by omega) (by omega) (by omega) t ht
    · exact hdisj 2 0 (by omega) (by omega) (by omega) t ht
    · exact hdisj 3 0 (by omega) (by omega) (by omega) t ht
  · intro c hc t ht c' hc'
    have hidx : ∀ d ∈ ([ids 1, ids 2, ids 3] : Multiset (List ℕ)),
        ∃ k, (k = 1 ∨ k = 2 ∨ k = 3) ∧ d = ids k := by
      intro d hd
      simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, rfl⟩
      · exact ⟨3, by omega, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hidx c hc
    intro htc'
    by_cases hcc : c' = ids j
    · subst hcc
      have h2 : 2 ≤ Multiset.count (ids j) ([ids 1, ids 2, ids 3] : Multiset (List ℕ)) := by
        have := Multiset.count_pos.2 hc'; rw [Multiset.count_erase_self] at this; omega
      simp only [Multiset.coe_count, List.count_cons, List.count_nil, beq_iff_eq] at h2
      have two : ∀ a b, a ≠ b → (a = 1 ∨ a = 2 ∨ a = 3) → (b = 1 ∨ b = 2 ∨ b = 3) →
          ids a = ids j → ids b = ids j → False := by
        intro a b hab ha hb hea heb
        exact hdisj a b (by omega) (by omega) hab t (hea ▸ ht) (heb ▸ ht)
      by_cases e1 : ids 1 = ids j <;> by_cases e2 : ids 2 = ids j <;>
        by_cases e3 : ids 3 = ids j <;> simp only [e1, e2, e3, if_true, if_false] at h2 <;> first
        | omega
        | exact two 1 2 (by omega) (by omega) (by omega) e1 e2
        | exact two 1 3 (by omega) (by omega) (by omega) e1 e3
        | exact two 2 3 (by omega) (by omega) (by omega) e2 e3
    · obtain ⟨k, hk, rfl⟩ := hidx c' (Multiset.mem_of_mem_erase hc')
      exact hdisj j k (by omega) (by omega) (fun e => hcc (e ▸ rfl)) t ht htc'
  · have hl := h.lab i hi
    apply List.map_injective_iff.2 Sum.inl_injective
    rw [← hl, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨a, ha⟩ := hprim x (mem_of_seq h hi (List.mem_append_left _ hx))
    simp [lbl, ha]
  · exact (h.pend_none hprim hi).2

/-- **Strong OD solvability of a chain problem with four roots.** -/
theorem strongOD_iff_cwin (hM : ChainMethods P) (hMwf : ∀ m ∈ P.methods, m.subtasks.WF)
    {root : ℕ → ℕ} (hI : IsRoots P.tnI 4 root) :
    P.StrongODSolvable ↔ ∃ w : ℕ → List ℕ,
      (∀ i < 4, Relation.ReflTransGen (PStep P) ([], some (root i)) (w i, none)) ∧
      CWin P.δ P.δ (w 0) ([w 1, w 2, w 3] : Multiset (List ℕ)) P.init := by
  rw [Problem.strongODSolvable_iff_fmSolvableDB]
  constructor
  · rintro ⟨tn, ⟨hd, hprim⟩, hb⟩
    obtain ⟨ids, pend, st, hinv⟩ := inv_of_decomposesTo hM hI hd
    obtain ⟨hch, hlab⟩ := isChains_of_inv hinv hprim
    refine ⟨fun i => (st i).1, fun i hi => ?_, ?_⟩
    · have := hinv.der i hi
      rwa [show st i = ((st i).1, none) by ext <;> simp [(hlab i hi).2]] at this
    · have := (beliefSolvable_iff_cwin P hch P.init).1 hb
      simpa [(hlab 0 (by omega)).1, (hlab 1 (by omega)).1, (hlab 2 (by omega)).1,
        (hlab 3 (by omega)).1] using this
  · rintro ⟨w, hw, hc⟩
    have h0 := inv_roots (P := P) hI
    -- run the four derivations one after the other
    have run : ∀ i (hi : i < 4) {tn ids pend st}, Inv P tn 4 root ids pend st →
        st i = ([], some (root i)) →
        ∃ tn' ids' pend', P.DecomposesTo tn tn' ∧
          Inv P tn' 4 root ids' pend' (Function.update st i (w i, none)) := by
      intro i hi tn ids pend st h hst
      obtain ⟨tn', ids', pend', hd, h', -⟩ := Inv.exists_run hMwf hi (hw i hi) h hst
      exact ⟨tn', ids', pend', hd, h'⟩
    obtain ⟨t1, i1, p1, d1, h1⟩ := run 0 (by omega) h0 rfl
    obtain ⟨t2, i2, p2, d2, h2⟩ := run 1 (by omega) h1 (by simp)
    obtain ⟨t3, i3, p3, d3, h3⟩ := run 2 (by omega) h2 (by simp)
    obtain ⟨t4, i4, p4, d4, h4⟩ := run 3 (by omega) h3 (by simp)
    set stF := Function.update (Function.update (Function.update (Function.update
      (fun i => (([] : List ℕ), some (root i))) 0 (w 0, none)) 1 (w 1, none)) 2 (w 2, none)) 3
        (w 3, none) with hstF
    have hstw : ∀ i < 4, stF i = (w i, none) := by
      intro i hi
      interval_cases i <;> simp [stF]
    have hprim : t4.IsPrimitive := by
      intro t ht
      obtain ⟨i, hi, hx⟩ := (h4.mem t).1 ht
      have hpn : p4 i = none := by
        have := h4.pendSome i hi; rw [hstw i hi] at this
        exact Option.not_isSome_iff_eq_none.1 (by simpa using this)
      rw [hpn] at hx
      simp only [Option.toList_none, List.append_nil] at hx
      have := h4.lab i hi
      have hmem : t4.α t ∈ (stF i).1.map Sum.inl := by rw [← this]; exact List.mem_map_of_mem hx
      obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
      exact ⟨a, ha.symm⟩
    refine ⟨t4, ⟨(d1.trans d2).trans (d3.trans d4), hprim⟩, ?_⟩
    obtain ⟨hch, hlab⟩ := isChains_of_inv h4 hprim
    rw [beliefSolvable_iff_cwin P hch]
    have hl : ∀ i < 4, (i4 i).map (lbl t4) = w i := fun i hi => by
      rw [(hlab i hi).1, hstw i hi]
    simpa [hl 0 (by omega), hl 1 (by omega), hl 2 (by omega), hl 3 (by omega)] using hc

end PCP

end FOND
