import HtnComplexity.Space.ThrTestsSem4
/-!
# The thread machine: bounded facts, the accepting test, the canonical configuration

* `HTN.Space.Thr.bits_le_of_thrInitOk` — every numeral of a configuration satisfying the local
  conditions `ThrInitOk` has at most `thrBnd q = 4·|code| + 10` bits;
* `HTN.Space.Thr.thrAccB_iff` — the accepting test checks that the configuration contains the
  numbered goal of the thread table, `(goalF q.goalList).map enc`;
* `HTN.Space.Thr.canon_thrInitB` — the canonical configuration `canonS d q` passes the initial
  test.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

/-- The bound on the bit length of the facts of a configuration passing the initial test. -/
def thrBnd (q : InstDesc) : ℕ := 4 * (instSer q).length + 10

theorem length_bitsOfNat_cfN (e : NF) :
    (bitsOfNat (cfN e)).length = npos1 e + npos2 e + 8 := by
  rw [bitsOfNat_cfN]
  cases e <;> simp [gT, nbits, npos1, npos2, unary] <;> omega

section Bound

variable {d : DomDesc} {q : InstDesc} {S : List ℕ}

theorem ThrInitOk.pos_lt (h : ThrInitOk d q S) {p a : ℕ} (hw : cfG (.wit p a) ∈ S) :
    p < 2 * (instSer q).length := by
  have h1 := h.wit.lt_nodes (mem_witList.2 hw)
  have h2 := List.toFinset_card_le (wnodes q.tnI)
  have h3 := length_wnodes_le q
  omega

/-- **The facts of a configuration satisfying the local conditions have at most `thrBnd q`
bits.** -/
theorem bits_le_of_thrInitOk (h : ThrInitOk d q S) :
    ∀ f ∈ S, (bitsOfNat f).length ≤ thrBnd q := by
  intro f hf
  unfold thrBnd
  rcases h.shape f hf with ⟨v, rfl⟩ | ⟨g, rfl⟩ | ⟨e, rfl⟩
  · have := length_bitsOfNat_add_two_le_of_mem_initList ((h.inst v).1 hf)
    rw [bitsOfNat_cfI]; simp [tagI3]; omega
  · rw [length_bitsOfNat_cfG]
    cases g with
    | cur p =>
      obtain rfl := (h.cur p).1 hf
      simp [gbits, unary]
    | fin => exact absurd hf h.fin
    | wit p a =>
      have h1 := h.pos_lt hf
      have h2 := length_serNat_le_of_mem_wnodes (h.wit.node p a (mem_witList.2 hf))
      simp [gbits, unary]; omega
    | lab p x =>
      obtain ⟨i, -, hw, rfl⟩ := (h.lab p x).1 hf
      have h1 := h.pos_lt hw
      have h2 := length_lblBits_label_le (q := q) i
      simp [gbits, unary]; omega
    | nop p =>
      obtain ⟨i, -, hw, -⟩ := (h.nop p).1 hf
      have h1 := h.pos_lt hw
      simp [gbits, unary]; omega
    | len k =>
      have h1 := (h.len_iff k).1 hf
      have h2 := card_ids_le q
      simp only [nIds] at h1
      simp [gbits, unary]; omega
  · rw [length_bitsOfNat_cfN]
    have key : ∀ x y, (∃ a, cfG (.wit x a) ∈ S) → (∃ a, cfG (.wit y a) ∈ S) →
        x + y + 8 ≤ 4 * (instSer q).length + 10 := by
      rintro x y ⟨a, ha⟩ ⟨b, hb⟩
      have := h.pos_lt ha
      have := h.pos_lt hb
      omega
    cases e with
    | edge x y =>
      obtain ⟨o, -, h1, h2⟩ := (h.edge x y).1 hf
      exact key x y ⟨_, h1⟩ ⟨_, h2⟩
    | cl x y => exact key x y (h.clpos x y hf).1 (h.clpos x y hf).2
    | nc x y => exact key x y (h.ncpos x y hf).1 (h.ncpos x y hf).2

end Bound

/-! ### The accepting test -/

theorem mem_goalF_enc {g : List ℕ} {f : ℕ} :
    f ∈ (goalF g).map enc ↔ (∃ v ∈ g, f = cfI v) ∨ f = cfG .fin := by
  simp only [goalF, List.map_append, List.map_map, List.mem_append, List.mem_map,
    Function.comp_apply, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨v, hv, rfl⟩ | rfl)
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨v, hv, rfl⟩ | rfl)
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr rfl

/-- **The accepting test**: the configuration contains the numbered goal of the thread table. -/
theorem thrAccB_iff {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (q : InstDesc) :
    thrAccB (blist S) (instSer q) = true ↔ ∀ f ∈ (goalF q.goalList).map enc, f ∈ decSt S := by
  rw [thrAccB, Bool.and_eq_true, goal_iff, entFin_eq, occB_S hS]
  have hI : ∀ v, tagI3 ++ bitsOfNat v ∈ S ↔ cfI v ∈ decSt S := fun v => by
    rw [mem_S_iff hS, bitsOfNat_cfI]
  simp only [hI]
  constructor
  · rintro ⟨hg, hfin⟩ f hf
    rcases mem_goalF_enc.1 hf with ⟨v, hv, rfl⟩ | rfl
    · exact hg v hv
    · exact hfin
  · intro h
    exact ⟨fun v hv => h _ (mem_goalF_enc.2 (Or.inl ⟨v, hv, rfl⟩)),
      h _ (mem_goalF_enc.2 (Or.inr rfl))⟩

/-! ### The canonical configuration -/

/-- **The canonical configuration passes the initial test.** -/
theorem canon_thrInitB {d : DomDesc} {q : InstDesc} {K : ℕ} (hK : (instSer q).length ≤ K)
    (b : Bool) (T : List Row) :
    thrInitB (blist ((canonS d q).map bitsOfNat)) (instSer q)
      (tblAdv b (markRows d K ++ T)) = true := by
  have hS := canon_map_bitsOfNat (canonS d q)
  refine thrInitB_of_thrInitOk hS hK ?_
  rw [decSt_map_bitsOfNat]
  exact initOk_canonS

end Thr

end Space

end HTN
