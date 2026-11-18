import HtnComplexity.Space.ThrTestsSem1
/-!
# Soundness of the initial test of the thread machine: the kinds of entries

`HTN.Space.Thr.classifyR`: every fact of a configuration of canonical numerals that passes the
entry test of `HTN.Space.Thr.thrInitB` is one of the admitted kinds — a fact of the instance,
`cur 0`, a witness entry of a node, a label, `nop` or `len` entry as in P-TR, an `edge` entry
justified by a listed pair, a `cl` entry, or an `nc` entry without a `cl` entry of the same pair.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

section Classify

variable {d : DomDesc} {K : ℕ} {q : InstDesc} {b : Bool} {T : List Row} {S : List (List Bool)}

/-- Every entry of the configuration is of an admitted kind (the entry test of `thrInitB`). -/
def AllOkR (d : DomDesc) (K : ℕ) (q : InstDesc) (b : Bool) (T : List Row)
    (S : List (List Bool)) : Prop :=
  ∀ f ∈ decSt S, entryOkR (entN f) (blist S) (instSer q) (tblAdv b (markRows d K ++ T)) = true

theorem entry_labR (hS : ∀ w ∈ S, IsCanon w) (hall : AllOkR d K q b T S) {f : ℕ}
    (hf : f ∈ decSt S) (hpre : kp tLab <+: entN f) :
    ∃ p i, i ∈ q.tnI.ids ∧ cfG (.wit p i) ∈ decSt S ∧ f = cfG (.lab p (q.tnI.label i)) := by
  have h := hall f hf
  simp only [entryOkR, Bool.or_eq_true] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · obtain ⟨v, -, hE⟩ := (kInst_iff _ q).1 h
    rw [hE] at hpre; exact absurd hpre (kp_not_inst _ _)
  · rw [kCur, decide_eq_true_eq] at h
    rw [h, entCur0, kp_prefix_iff] at hpre; obtain ⟨s, hs⟩ := hpre
    simp [gT, tLab, gbits, unary] at hs
  · obtain ⟨a, -, hn⟩ := (witAny_iff _ q).1 h
    simp only [witNode, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact absurd (kp_eq_of_prefix rfl rfl hpre hn.1.1) (by decide)
  · exact kLab_sound hS h
  · simp only [kNop, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd (kp_eq_of_prefix rfl rfl hpre h.1.1) (by decide)
  · simp only [kLen, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd (kp_eq_of_prefix rfl rfl hpre h.1.1.1) (by decide)
  · simp only [kEdge, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd (kp_eq_of_prefix rfl rfl hpre h.1.1) (by decide)
  · simp only [kCl, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd (kp_eq_of_prefix rfl rfl hpre h.1) (by decide)
  · simp only [kNc, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd (kp_eq_of_prefix rfl rfl hpre h.1.1) (by decide)

theorem kEdge_sound (hS : ∀ w ∈ S, IsCanon w) {f : ℕ}
    (h : kEdge (entN f) (blist S) (instSer q) = true) :
    ∃ x y, (∃ e ∈ q.tnI.ordList, cfG (.wit x e.1) ∈ decSt S ∧ cfG (.wit y e.2) ∈ decSt S) ∧
      f = cfN (.edge x y) := by
  simp only [kEdge, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpre, hend⟩, h⟩ := h
  obtain ⟨x, y, rfl⟩ := entry_edge hpre hend
  refine ⟨x, y, ?_, rfl⟩
  obtain ⟨e, he, h⟩ := (atL_ord_any _ q _ _ _).1 h
  rw [kEdgeBody] at h
  obtain ⟨f1, hf1, h⟩ := (anyE_S hS _ _ _ _).1 h
  simp only [kEdgeW1, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [witFst_iff, witNode_entN] at h1
  obtain ⟨p, rfl⟩ := h1
  rw [samePos_iff (drop_entG_wit p e.1) (drop_edge x y)] at h2
  subst h2
  obtain ⟨f2, hf2, h3⟩ := (anyE_S hS _ _ _ _).1 h3
  simp only [kEdgeW2, Bool.and_eq_true] at h3
  obtain ⟨h4, h5⟩ := h3
  rw [witSnd_iff, witNode_entN] at h4
  obtain ⟨p', rfl⟩ := h4
  rw [pos21_iff (drop_edge p y) (drop_entG_wit p' e.2)] at h5
  subst h5
  exact ⟨e, he, hf1, hf2⟩

theorem kNc_sound (hS : ∀ w ∈ S, IsCanon w) {f : ℕ} (h : kNc (entN f) (blist S) = true) :
    ∃ x y, cfN (.cl x y) ∉ decSt S ∧ f = cfN (.nc x y) := by
  simp only [kNc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpre, hend⟩, h⟩ := h
  obtain ⟨x, y, rfl⟩ := entry_nc hpre hend
  refine ⟨x, y, fun hc => ?_, rfl⟩
  have := (allE_S hS _ _ _ _).1 h _ hc
  have hk : kp tC3 <+: entN (cfN (.cl x y)) := kp_entN_cfN (.cl x y)
  rw [kNcBody, decide_eq_true hk,
    (samePair_iff (drop_nc x y) (drop_cl x y)).2 ⟨rfl, rfl⟩] at this
  exact absurd this (by decide)

/-- **The classification of the facts of a configuration that passes the entry test.** -/
theorem classifyR (hS : ∀ w ∈ S, IsCanon w) (hK : (instSer q).length ≤ K)
    (hall : AllOkR d K q b T S) {f : ℕ} (hf : f ∈ decSt S) :
    (∃ v ∈ q.initList, f = cfI v) ∨ f = cfG (.cur 0) ∨
      (∃ p a, a ∈ wnodes q.tnI ∧ f = cfG (.wit p a)) ∨
      (∃ p i, i ∈ q.tnI.ids ∧ cfG (.wit p i) ∈ decSt S ∧ f = cfG (.lab p (q.tnI.label i))) ∨
      (∃ p a0, cfG (.lab p (Sum.inl a0)) ∈ decSt S ∧ a0 ∉ vocA d ∧ f = cfG (.nop p)) ∨
      (∃ k, (∀ p y, cfG (.lab p y) ∈ decSt S → p ≠ k) ∧
        (k = 0 ∨ ∃ y, cfG (.lab (k - 1) y) ∈ decSt S) ∧ f = cfG (.len k)) ∨
      (∃ x y, (∃ e ∈ q.tnI.ordList, cfG (.wit x e.1) ∈ decSt S ∧ cfG (.wit y e.2) ∈ decSt S) ∧
        f = cfN (.edge x y)) ∨
      (∃ x y, f = cfN (.cl x y)) ∨
      (∃ x y, cfN (.cl x y) ∉ decSt S ∧ f = cfN (.nc x y)) := by
  have h := hall f hf
  simp only [entryOkR, Bool.or_eq_true] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · obtain ⟨v, hv, hE⟩ := (kInst_iff _ q).1 h
    refine Or.inl ⟨v, hv, ?_⟩
    rw [← bitsOfNat_cfI] at hE
    exact entN_injective hE
  · rw [kCur, decide_eq_true_eq, entCur0, ← bitsOfNat_cfG] at h
    exact Or.inr (Or.inl (entN_injective h))
  · obtain ⟨a, ha, hn⟩ := (witAny_iff _ q).1 h
    obtain ⟨p, rfl⟩ := (witNode_entN f a).1 hn
    exact Or.inr (Or.inr (Or.inl ⟨p, a, ha, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (kLab_sound hS h))))
  · simp only [kNop, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpre, hend⟩, h⟩ := h
    obtain ⟨p, hp⟩ := posEnd_split rfl hpre hend
    have hfp : f = cfG (.nop p) := entN_injective (hp.trans (entG_nop p).symm)
    subst hfp
    obtain ⟨f', hf', h⟩ := (anyE_S hS _ _ _ _).1 h
    simp only [kNopBody, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpre', hsame⟩, hunk⟩ := h
    obtain ⟨p', i, -, -, rfl⟩ := entry_labR hS hall hf' hpre'
    rw [samePos_iff (drop_entG_nop p) (drop_entG_lab p' _)] at hsame
    subst hsame
    obtain ⟨a0, ha0, hna⟩ := (unknownD_iff d K b T p _).1 hunk
    have hna' : a0 ∉ vocA d := fun hm => hna ⟨hm, (bits_le_of_label ha0).trans hK⟩
    rw [ha0] at hf'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, a0, hf', hna', rfl⟩))))
  · simp only [kLen, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hpre, hend⟩, hall1⟩, hz⟩ := h
    obtain ⟨k, hk⟩ := posEnd_split rfl hpre hend
    have hfk : f = cfG (.len k) := entN_injective (hk.trans (entG_len k).symm)
    subst hfk
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, ?_, ?_, rfl⟩)))))
    · intro p y hpy hpk
      subst hpk
      have := (allE_S hS _ _ _ _).1 hall1 _ hpy
      simp only [kLenBody1, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at this
      rcases this with h1 | h1
      · exact h1 (kp_entG_lab _ _)
      · have h2 := (samePos_iff (drop_entG_len p) (drop_entG_lab p y)).2 rfl
        rw [h1] at h2; exact Bool.false_ne_true h2
    · rcases hz with hz | hz
      · exact Or.inl ((posZero_iff (drop_entG_len k)).1 hz)
      · obtain ⟨f', hf', h⟩ := (anyE_S hS _ _ _ _).1 hz
        simp only [kLenBody2, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨p', i, -, -, rfl⟩ := entry_labR hS hall hf' h.1
        rw [succPos_iff (drop_entG_lab p' _) (drop_entG_len k)] at h
        refine Or.inr ⟨q.tnI.label i, ?_⟩
        rw [h.2, Nat.add_sub_cancel]; exact hf'
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (kEdge_sound hS h)))))))
  · simp only [kCl, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (entry_cl h.1 h.2))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (kNc_sound hS h))))))))

end Classify

end Thr

end Space

end HTN
