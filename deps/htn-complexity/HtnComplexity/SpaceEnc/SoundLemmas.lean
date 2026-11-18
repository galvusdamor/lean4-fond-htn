import HtnComplexity.SpaceEnc.SoundInv
/-!
# Soundness of the encoding: word and multiset lemmas

The heads of the words of the encoding, and the bookkeeping of the multisets of remaining words
used by the phase invariants of `HtnComplexity/SpaceEnc/SoundInv.lean`.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type}

/-! ### Heads of words -/

theorem chainW_eq (m : ℕ) (p : Bool) (cd : CD Q Γ) :
    chainW m p cd = .ws p :: wipW m p 0 cd := by
  simp [chainW, bitL, wipW]

theorem wipW_lt {m k : ℕ} (p : Bool) (cd : CD Q Γ) (hk : k < m) :
    wipW m p k cd = .wb p k (cd.x k) (cd.e k) :: wipW m p (k + 1) cd := by
  unfold wipW
  rw [show m - k = (m - (k + 1)) + 1 by omega, wbsL_succ]
  rfl

theorem wipW_self (m : ℕ) (p : Bool) (cd : CD Q Γ) :
    wipW m p m cd = cd.rd ++ cd.core :: cd.incw :: .rv p cd.val :: rbsL p 0 m cd.x := by
  simp [wipW, wbsL, midL]

theorem tl_eq (m : ℕ) (q : Bool) (c : ℕ) (g : Γ) :
    (tl m q c g : List (Act Q Γ)) = .rv q g :: rbsL q 0 m (bitsOf c) := rfl

theorem rbsL_zero_succ (q : Bool) (j : ℕ) (x : ℕ → Bool) :
    (rbsL q 0 (j + 1) x : List (Act Q Γ)) = .rb q j (x j) :: rbsL q 0 j x := by
  simp [rbsL, List.range'_concat]

theorem rbsL_congr (q : Bool) (j : ℕ) {x y : ℕ → Bool} (h : ∀ i < j, x i = y i) :
    (rbsL q 0 j x : List (Act Q Γ)) = rbsL q 0 j y := by
  unfold rbsL
  congr 1
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range'_1] at hi
  rw [h i (by omega)]

theorem rbsL_zero_zero (q : Bool) (x : ℕ → Bool) : (rbsL q 0 0 x : List (Act Q Γ)) = [] := rfl

theorem wipW_ne_nil (m : ℕ) (p : Bool) (k : ℕ) (cd : CD Q Γ) : (wipW m p k cd : List (Act Q Γ)) ≠ [] := by
  simp [wipW, midL]

/-! ### Multisets of words -/

section Ms

variable {α : Type*} [DecidableEq α]

theorem multiset_map_erase_of_mem {β : Type*} [DecidableEq β] (f : β → α) {s : Multiset β} {b : β}
    (hb : b ∈ s) : (s.map f).erase (f b) = (s.erase b).map f := by
  conv_lhs => rw [← Multiset.cons_erase hb]
  rw [Multiset.map_cons, Multiset.erase_cons_head]

omit [DecidableEq α] in
theorem mem_msOf_of_get {bl : List (List α)} {i : ℕ} {v : List α} (h : bl[i]? = some v)
    (hv : v ≠ []) : v ∈ msOf bl :=
  mem_msOf.2 ⟨List.mem_of_getElem? h, hv⟩

/-- Advancing a word whose multiset position is known. -/
theorem msOf_set_of_eq {bl : List (List α)} {i : ℕ} {v t : List α} {S : Multiset (List α)}
    (hi : bl[i]? = some v) (hv : v ≠ []) (h : msOf bl = S + {v}) :
    msOf (bl.set i t) = S + Multiset.filter (· ≠ []) {t} := by
  rw [msOf_set hi hv, h, add_comm S, Multiset.singleton_add, Multiset.erase_cons_head]

omit [DecidableEq α] in
theorem msOf_ne_zero_not_allEmpty {bl : List (List α)} (h : msOf bl ≠ 0) : ¬ AllEmpty bl :=
  fun hA => h (allEmpty_iff_msOf.1 hA)

omit [DecidableEq α] in
theorem filter_singleton_of_ne {t : List α} (ht : t ≠ []) :
    Multiset.filter (· ≠ []) ({t} : Multiset (List α)) = {t} := by
  simp [ht]

omit [DecidableEq α] in
theorem filter_singleton_nil :
    Multiset.filter (· ≠ []) ({[]} : Multiset (List α)) = 0 := by
  simp

end Ms

/-! ### Tails -/

section Tails

theorem tails_range_succ (m : ℕ) (p : Bool) (f : ℕ → Γ) (c : ℕ) :
    (tails m p f (List.range (c + 1)) : Multiset (List (Act Q Γ))) =
      tails m p f (List.range c) + {tl m p c (f c)} := by
  simp only [tails, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    ← Multiset.coe_add, Multiset.coe_singleton]

theorem tails_range'_cons (m : ℕ) (p : Bool) (f : ℕ → Γ) {c W : ℕ} (hc : c < W) :
    (tails m p f (List.range' c (W - c)) : Multiset (List (Act Q Γ))) =
      {tl m p c (f c)} + tails m p f (List.range' (c + 1) (W - (c + 1))) := by
  rw [show W - c = (W - (c + 1)) + 1 by omega, List.range'_succ]
  simp [tails]

theorem mem_tails {m : ℕ} {p : Bool} {f : ℕ → Γ} {s : List ℕ} {v : List (Act Q Γ)}
    (h : v ∈ tails m p f s) : ∃ c ∈ s, v = tl m p c (f c) := by
  simp only [tails, Multiset.mem_coe, List.mem_map] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, hc, rfl⟩

theorem tails_congr {m : ℕ} {p : Bool} {f f' : ℕ → Γ} {s : List ℕ} (h : ∀ c ∈ s, f c = f' c) :
    (tails m p f s : Multiset (List (Act Q Γ))) = tails m p f' s := by
  unfold tails
  congr 1
  exact List.map_congr_left fun c hc => by rw [h c hc]

end Tails

/-! ### Blocks -/

section Blocks

variable [Fintype Q] [Fintype Γ] {m n' : ℕ} {N : NTM Q Γ}

theorem WCur.ms_ne_zero {p : Bool} {c : ℕ} {nv : ℕ → Γ} {X : Multiset (List (Act Q Γ))}
    {cur : List (List (Act Q Γ))} (h : WCur m n' N p c nv X cur) : msOf cur ≠ 0 := by
  obtain ⟨Fr, a, -, -, -, hms⟩ := h
  rw [hms]
  simp

omit [Fintype Q] [Fintype Γ] in
/-- The multiset of the words of a fresh block. -/
theorem msOf_fresh {p : Bool} {cds : List (CD Q Γ)} {a : Act Q Γ} :
    msOf (cds.map (chainW m p) ++ [[a]]) =
      (cds : Multiset (CD Q Γ)).map (chainW m p) + {[a]} := by
  unfold msOf
  rw [← Multiset.coe_add, Multiset.filter_add]
  congr 1
  · rw [Multiset.filter_eq_self.2]
    · simp
    · intro v hv
      simp only [Multiset.mem_coe, List.mem_map] at hv
      obtain ⟨cd, -, rfl⟩ := hv
      exact chainW_ne_nil m p cd
/-- **A fresh block is the writer's current block at position `0`.** -/
theorem FreshBlock.wcur {p : Bool} {bl : List (List (Act Q Γ))} (h : FreshBlock m n' N p bl)
    (nv : ℕ → Γ) : WCur m n' N p 0 nv 0 bl := by
  obtain ⟨cds, a, hv, hn, ha, rfl⟩ := h
  refine ⟨cds, a, fun cd hcd => hv cd hcd, by simp [hn], ha, ?_⟩
  rw [msOf_fresh]
  simp [tails]

end Blocks

end SpaceEnc

end HTN
