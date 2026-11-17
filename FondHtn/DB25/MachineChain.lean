import FondHtn.DB25.MachineSem
/-!
# The chain of machine blocks

* `FOND.DB.pre_sem` — the initial block: for every cell `c` chosen by nature, the content
  register holds the input symbol at `c`;
* `FOND.DB.chain_iff_runC` — **the chain of blocks is won iff for every cell `c` the cell run
  `FOND.DB.RunC` succeeds**.
-/

namespace FOND

namespace DB

/-! ## The initial block -/

/-- The input symbol at cell `c`. -/
def inp (w : List Sym) (blank : Sym) (c : ℕ) : Sym := w.getD c blank

theorem sat_phiInit (n : ℕ) (w : List Sym) (blank : Sym) (ρ : ℕ → Bool) :
    (∀ C ∈ phiInit n w blank, SatC ρ C) ↔
      (∀ i < w.length, i < 2 ^ n → ρ (gB i) = true → ∀ b < n, ρ (cB b) = i.testBit b) ∧
      (∀ i < w.length, 2 ^ n ≤ i → ρ (gB i) = false) ∧
      (∀ i < w.length, i < 2 ^ n → (∀ b < n, ρ (cB b) = i.testBit b) →
        ∀ j < 2, ρ (sB j) = ebit (w.getI i) j) ∧
      (∀ j < 2, (∃ i < w.length, ρ (gB i) = true) ∨ ρ (sB j) = ebit blank j) := by
  simp only [phiInit, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · intro h
    refine ⟨fun i hi hin hg b hb => ?_, fun i hi hin => ?_, fun i hi hin hc j hj => ?_,
      fun j hj => ?_⟩
    · have := h [(gB i, false), (cB b, i.testBit b)]
        (Or.inl (Or.inl ⟨i, hi, by rw [if_pos hin]; exact List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩))
      simp only [satC_cons, satC_nil, or_false] at this
      rcases this with h1 | h1
      · rw [hg] at h1; simp at h1
      · exact h1
    · have := h [(gB i, false)] (Or.inl (Or.inl ⟨i, hi, by rw [if_neg (by omega)]; simp⟩))
      simpa [satC_cons, satC_nil] using this
    · have := h ((List.range n).map (fun b => (cB b, !i.testBit b)) ++ [(sB j, ebit (w.getI i) j)])
        (Or.inl (Or.inr ⟨i, hi, by rw [if_pos hin]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩))
      rw [satC_append, satC_map_range] at this
      rcases this with ⟨b, hb, h1⟩ | h1
      · have := hc b hb; simp only at h1; rw [this] at h1; cases i.testBit b <;> simp at h1
      · simpa [satC_cons, satC_nil] using h1
    · have := h _ (Or.inr ⟨j, hj, rfl⟩)
      rw [satC_append, satC_map_range] at this
      simpa [satC_cons, satC_nil] using this
  · rintro ⟨hG, hG', hE, hB⟩ C hC
    rcases hC with (⟨i, hi, hC⟩ | ⟨i, hi, hC⟩) | ⟨j, hj, rfl⟩
    · split_ifs at hC with hin
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hC
        simp only [satC_cons, satC_nil, or_false]
        cases hg : ρ (gB i)
        · exact Or.inl rfl
        · exact Or.inr (hG i hi hin hg b (List.mem_range.1 hb))
      · simp only [List.mem_singleton] at hC; subst hC
        simp [satC_cons, hG' i hi (by omega)]
    · split_ifs at hC with hin
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hC
        rw [satC_append, satC_map_range]
        by_cases hc : ∀ b < n, ρ (cB b) = i.testBit b
        · exact Or.inr (by simp [satC_cons, hE i hi hin hc j (List.mem_range.1 hj)])
        · push_neg at hc
          obtain ⟨b, hb, hne⟩ := hc
          exact Or.inl ⟨b, hb, by simp only; cases h : i.testBit b <;> simp_all⟩
      · simp at hC
    · rw [satC_append, satC_map_range]
      rcases hB j hj with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [satC_cons, h])

theorem cbits_eq_iff {n i : ℕ} (hi : i < 2 ^ n) (γ : ℕ → Bool) :
    (∀ b < n, γ b = i.testBit b) ↔ bval n γ = i := by
  constructor
  · intro h; rw [← bval_testBit hi]; exact bval_congr n h
  · intro h; exact bval_inj n (h.trans (bval_testBit hi).symm)

/-- The registers after the initial block. -/
def initRho (n : ℕ) (w : List Sym) (blank : Sym) (γ ρ : ℕ → Bool) : ℕ → Bool := fun x =>
  if x = sB 0 then ebit (inp w blank (bval n γ)) 0
  else if x = sB 1 then ebit (inp w blank (bval n γ)) 1
  else if (Nat.unpair x).1 = 0 then γ (Nat.unpair x).2 else ρ x

theorem initRho_cB (n : ℕ) (w : List Sym) (blank : Sym) (γ ρ : ℕ → Bool) (b : ℕ) :
    initRho n w blank γ ρ (cB b) = γ b := by
  simp only [initRho, cB_ne_sB, if_false]; simp [cB]

theorem initRho_hB (n : ℕ) (w : List Sym) (blank : Sym) (γ ρ : ℕ → Bool) (b : ℕ) :
    initRho n w blank γ ρ (hB b) = ρ (hB b) := by
  simp only [initRho, hB_ne_sB, if_false]; simp [hB]

theorem initRho_sB (n : ℕ) (w : List Sym) (blank : Sym) (γ ρ : ℕ → Bool) (j : ℕ) (hj : j < 2) :
    initRho n w blank γ ρ (sB j) = ebit (inp w blank (bval n γ)) j := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [initRho]

theorem inp_of_lt {w : List Sym} {blank : Sym} {c : ℕ} (h : c < w.length) :
    inp w blank c = w.getI c := by
  rw [inp, List.getD_eq_getElem _ _ h, List.getI_eq_getElem _ h]

theorem inp_of_ge {w : List Sym} {blank : Sym} {c : ℕ} (h : w.length ≤ c) : inp w blank c = blank := by
  rw [inp, List.getD_eq_default _ _ h]

theorem phiInit_content {n : ℕ} {w : List Sym} {blank : Sym} {ρ : ℕ → Bool} {γ : ℕ → Bool}
    (hγ : ∀ b < n, ρ (cB b) = γ b) (hΦ : ∀ C ∈ phiInit n w blank, SatC ρ C) :
    ∀ j < 2, ρ (sB j) = ebit (inp w blank (bval n γ)) j := by
  rw [sat_phiInit] at hΦ
  obtain ⟨hG, hG', hE, hB⟩ := hΦ
  intro j hj
  by_cases hc : bval n γ < w.length
  · rw [inp_of_lt hc]
    refine hE _ hc (bval_lt n γ) (fun b hb => ?_) j hj
    rw [hγ b hb]
    exact (cbits_eq_iff (bval_lt n γ) γ).2 rfl b hb
  · rw [inp_of_ge (by omega)]
    refine (hB j hj).resolve_left ?_
    rintro ⟨i, hi, hg⟩
    by_cases hin : i < 2 ^ n
    · have := (cbits_eq_iff hin γ).1 fun b hb => (hγ b hb).symm.trans (hG i hi hin hg b hb)
      omega
    · rw [hG' i hi (by omega)] at hg; simp at hg

/-- **The initial block.** -/
theorem pre_sem {n : ℕ} {w : List Sym} {blank : Sym} {K : (ℕ → Bool) → ℕ → Prop} (hK : Good n K)
    (ρ : ℕ → Bool) (q : ℕ) :
    blockSem (preOps n w blank) K ρ q ↔ ∀ γ, K (initRho n w blank γ ρ) q := by
  have hpre : preOps n w blank = ((List.range n).map cB).map Op.nature ++
      ((initChoices w).map Op.choice ++ [.check (phiInit n w blank)]) := by
    simp [preOps, List.map_map, Function.comp_def]
  rw [hpre, blockSem_natures]
  have key : ∀ τ : ℕ → Bool,
      blockSem ((initChoices w).map Op.choice ++ [.check (phiInit n w blank)]) K
        (updOn ((List.range n).map cB) τ ρ) q ↔
      K (initRho n w blank (fun b => τ (cB b)) ρ) q := by
    intro τ
    set ρ1 := updOn ((List.range n).map cB) τ ρ
    rw [blockSem_choices]
    simp only [blockSem, List.foldr_cons, List.foldr_nil, opSem]
    have hc1 : ∀ b < n, ρ1 (cB b) = τ (cB b) := fun b hb => by
      simp [ρ1, updOn, hb]
    have hh1 : ∀ b, ρ1 (hB b) = ρ (hB b) := fun b => by simp [ρ1, updOn]
    have hnot : ∀ x, (∀ i, x ≠ gB i) → x ≠ sB 0 → x ≠ sB 1 → x ∉ initChoices w := by
      intro x hx h0 h1 hm
      simp only [initChoices, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_map, List.mem_range] at hm
      rcases hm with (h | h) | ⟨i, -, rfl⟩
      · exact h0 h
      · exact h1 h
      · exact hx i rfl
    have hagree : ∀ τ', (∀ j < 2, updOn (initChoices w) τ' ρ1 (sB j) =
        ebit (inp w blank (bval n fun b => τ (cB b))) j) →
        Agree n (updOn (initChoices w) τ' ρ1) (initRho n w blank (fun b => τ (cB b)) ρ) := by
      intro τ' hs
      refine ⟨fun b hb => ?_, fun b hb => ?_, ?_, ?_⟩
      · rw [initRho_cB, updOn, if_neg (hnot _ (fun i => cB_ne_gB _ _) (cB_ne_sB _ _)
          (cB_ne_sB _ _)), hc1 b hb]
      · rw [initRho_hB, updOn, if_neg (hnot _ (fun i => hB_ne_gB _ _) (hB_ne_sB _ _)
          (hB_ne_sB _ _)), hh1]
      · rw [hs 0 (by omega), initRho_sB _ _ _ _ _ _ (by omega)]
      · rw [hs 1 (by omega), initRho_sB _ _ _ _ _ _ (by omega)]
    have hcb : ∀ τ', ∀ b < n, updOn (initChoices w) τ' ρ1 (cB b) = τ (cB b) := fun τ' b hb => by
      rw [updOn, if_neg (hnot _ (fun i => cB_ne_gB _ _) (cB_ne_sB _ _) (cB_ne_sB _ _)), hc1 b hb]
    constructor
    · rintro ⟨τ', hΦ, hKK⟩
      exact (hK _ _ _ (hagree τ' (phiInit_content (hcb τ') hΦ))).1 hKK
    · intro hKs
      set c := bval n fun b => τ (cB b)
      let τ' : ℕ → Bool := fun x => if x = sB 0 then ebit (inp w blank c) 0 else
        if x = sB 1 then ebit (inp w blank c) 1 else decide (∃ i < w.length, x = gB i ∧ i = c)
      have hs : ∀ j < 2, updOn (initChoices w) τ' ρ1 (sB j) = ebit (inp w blank c) j := by
        intro j hj
        have hm : sB j ∈ initChoices w := by
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [initChoices]
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [updOn, hm, τ']
      have hg : ∀ i < w.length, updOn (initChoices w) τ' ρ1 (gB i) = decide (i = c) := by
        intro i hi
        have hm : gB i ∈ initChoices w := by simp [initChoices, hi]
        simp only [updOn, hm, if_true, τ', gB_ne_sB, if_false]
        congr 1
        exact propext ⟨fun ⟨i', _, he, h⟩ => by rw [gB_inj] at he; subst he; exact h,
          fun h => ⟨i, hi, rfl, h⟩⟩
      refine ⟨τ', ?_, (hK _ _ _ (hagree τ' hs)).2 hKs⟩
      rw [sat_phiInit]
      refine ⟨fun i hi hin hgi b hb => ?_, fun i hi hin => ?_, fun i hi hin hcb' j hj => ?_,
        fun j hj => ?_⟩
      · rw [hg i hi] at hgi
        have hic : i = c := by simpa using hgi
        rw [hcb τ' b hb]
        exact (cbits_eq_iff hin _).2 hic.symm b hb
      · rw [hg i hi]; simp only [decide_eq_false_iff_not]
        intro hic; have := bval_lt n (fun b => τ (cB b)); omega
      · have hic : c = i := (cbits_eq_iff hin _).1 fun b hb => by rw [← hcb τ' b hb]; exact hcb' b hb
        rw [hs j hj, hic, inp_of_lt hi]
      · by_cases hc : c < w.length
        · exact Or.inl ⟨c, hc, by rw [hg c hc]; simp⟩
        · exact Or.inr (by rw [hs j hj, inp_of_ge (by omega)])
  simp only [key]
  constructor
  · intro h γ
    have := h fun x => γ (Nat.unpair x).2
    simpa [cB] using this
  · intro h τ; exact h _

/-! ## The chain -/

/-- Setting bits. -/
def setBits (β : ℕ → Bool) (post : List (ℕ × Bool)) : ℕ → Bool := fun i =>
  if (i, true) ∈ post then true else if (i, false) ∈ post then false else β i

/-- **The run of the blocks for the cell `c` (bits `γ`)**: the head bits `β`, the state `q` and
the content `σ` of the cell. -/
def RunC (n : ℕ) (LD : List (TrD × HU)) (acc : ℕ) (γ : ℕ → Bool) :
    List ℕ → (ℕ → Bool) → ℕ → Sym → Prop
  | [], _, q, _ => q = acc
  | w :: ws, β, q, σ =>
    q = (LD.getI w).1.1 ∧ (∀ l ∈ (LD.getI w).2.1, β l.1 = l.2) ∧
      ((∀ b < n, γ b = β b) → σ = (LD.getI w).1.2.1) ∧
      RunC n LD acc γ ws (setBits β (LD.getI w).2.2) (LD.getI w).1.2.2.1
        (if ∀ b < n, γ b = β b then (LD.getI w).1.2.2.2 else σ)

/-- Head literals are on the first `n` bits. -/
def HUok (n : ℕ) (d : TrD × HU) : Prop := ∀ l ∈ d.2.1 ++ d.2.2, l.1 < n

theorem agree_stepRho {n : ℕ} {d : TrD × HU} {ρ ρ' : ℕ → Bool} (h : Agree n ρ ρ') :
    Agree n (stepRho n d ρ) (stepRho n d ρ') := by
  have hE : EqCH n ρ ↔ EqCH n ρ' := by
    simp only [EqCH]
    exact forall₂_congr fun b hb => by rw [h.1 b hb, h.2.1 b hb]
  have hn : ∀ j < 2, nextSym n d ρ j = nextSym n d ρ' j := by
    intro j hj
    simp only [nextSym, hE]
    split_ifs
    · rfl
    · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact h.2.2.1
      · exact h.2.2.2
  refine agree_setAll _ ⟨fun b hb => ?_, fun b hb => ?_, ?_, ?_⟩
  · simp [h.1 b hb]
  · simp [h.2.1 b hb]
  · simp [hn 0 (by omega)]
  · simp [hn 1 (by omega)]

theorem good_loop {n : ℕ} {d : TrD × HU} (hd : HUok n d) {K : (ℕ → Bool) → ℕ → Prop}
    (hK : Good n K) : Good n (blockSem (loopOps n d) K) := by
  intro ρ ρ' q h
  rw [loop_sem hK, loop_sem hK]
  have hE : EqCH n ρ ↔ EqCH n ρ' := by
    simp only [EqCH]
    exact forall₂_congr fun b hb => by rw [h.1 b hb, h.2.1 b hb]
  have hp : (∀ l ∈ d.2.1, ρ (hB l.1) = l.2) ↔ (∀ l ∈ d.2.1, ρ' (hB l.1) = l.2) :=
    forall₂_congr fun l hl => by rw [h.2.1 l.1 (hd l (List.mem_append_left _ hl))]
  rw [hp, hE, h.2.2.1, h.2.2.2, hK _ _ _ (agree_stepRho h)]

theorem good_final (acc : ℕ) {n : ℕ} {K : (ℕ → Bool) → ℕ → Prop} (hK : Good n K) :
    Good n (blockSem (finalOps acc) K) := by
  intro ρ ρ' q h
  rw [final_sem, final_sem, hK _ _ _ h]

theorem good_true (n : ℕ) : Good n (fun _ _ => True) := fun _ _ _ _ => Iff.rfl

/-- The blocks of a word and a final block. -/
def blocksOf (n : ℕ) (LD : List (TrD × HU)) (acc : ℕ) (ws : List ℕ) : List (List Op) :=
  ws.map (fun w => loopOps n (LD.getI w)) ++ [finalOps acc]

theorem good_chain {n : ℕ} {LD : List (TrD × HU)} (hLD : ∀ d ∈ LD, HUok n d) (acc : ℕ) :
    ∀ ws : List ℕ, Good n (chainB (blocksOf n LD acc ws) fun _ _ => True)
  | [] => good_final acc (good_true n)
  | w :: ws => by
    have hd : HUok n (LD.getI w) := by
      by_cases hw : w < LD.length
      · rw [List.getI_eq_getElem _ hw]; exact hLD _ (List.getElem_mem hw)
      · rw [List.getI_eq_default _ (by omega)]; intro l hl; simp [default] at hl
    exact good_loop hd (good_chain hLD acc ws)

theorem stepRho_cB (n : ℕ) (d : TrD × HU) (ρ : ℕ → Bool) (b : ℕ) :
    stepRho n d ρ (cB b) = ρ (cB b) := by
  simp [stepRho, setAll_of_not_key (not_key_hl (fun i => cB_ne_hB _ _) _)]

theorem stepRho_hB (n : ℕ) (d : TrD × HU) (ρ : ℕ → Bool) (b : ℕ) :
    stepRho n d ρ (hB b) = setBits (fun i => ρ (hB i)) d.2.2 b := by
  simp only [stepRho, setAll, setBits, List.mem_map, hl, Prod.mk.injEq, hB_inj]
  split_ifs <;> simp_all

theorem stepRho_sB (n : ℕ) (d : TrD × HU) (ρ : ℕ → Bool) (j : ℕ) (hj : j < 2) :
    stepRho n d ρ (sB j) = nextSym n d ρ j := by
  rw [stepRho, setAll_of_not_key (not_key_hl (fun i => sB_ne_hB _ _) _)]
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp

/-- **The chain of loop and final blocks is the cell run.** -/
theorem chain_runC {n : ℕ} {LD : List (TrD × HU)} (hLD : ∀ d ∈ LD, HUok n d) (acc : ℕ)
    (γ : ℕ → Bool) : ∀ (ws : List ℕ) (ρ β : ℕ → Bool) (q : ℕ) (σ : Sym),
    (∀ b < n, ρ (cB b) = γ b) → (∀ b, ρ (hB b) = β b) → (∀ j < 2, ρ (sB j) = ebit σ j) →
    (chainB (blocksOf n LD acc ws) (fun _ _ => True) ρ q ↔ RunC n LD acc γ ws β q σ)
  | [], ρ, β, q, σ, _, _, _ => by
    simp [blocksOf, chainB, final_sem, RunC]
  | w :: ws, ρ, β, q, σ, hc, hh, hs => by
    show blockSem (loopOps n (LD.getI w)) (chainB (blocksOf n LD acc ws) fun _ _ => True) ρ q ↔ _
    rw [loop_sem (good_chain hLD acc ws)]
    simp only [RunC]
    have hE : EqCH n ρ ↔ ∀ b < n, γ b = β b := by
      simp only [EqCH]; exact forall₂_congr fun b hb => by rw [hc b hb, hh b]
    have hpre : (∀ l ∈ (LD.getI w).2.1, ρ (hB l.1) = l.2) ↔ ∀ l ∈ (LD.getI w).2.1, β l.1 = l.2 :=
      forall₂_congr fun l _ => by rw [hh]
    have hread : (ρ (sB 0) = ebit (LD.getI w).1.2.1 0 ∧ ρ (sB 1) = ebit (LD.getI w).1.2.1 1) ↔
        σ = (LD.getI w).1.2.1 := by
      rw [hs 0 (by omega), hs 1 (by omega)]
      exact ⟨fun h => ebit_inj h.1 h.2, fun h => by rw [h]; exact ⟨rfl, rfl⟩⟩
    rw [hpre, hE, hread]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
    refine chain_runC hLD acc γ ws _ _ _ _ (fun b hb => by rw [stepRho_cB, hc b hb])
      (fun b => by rw [stepRho_hB]; simp only [hh]) (fun j hj => ?_)
    rw [stepRho_sB _ _ _ _ hj, nextSym]
    by_cases heq : ∀ b < n, γ b = β b
    · rw [if_pos (hE.2 heq), if_pos heq]
    · rw [if_neg (fun h => heq (hE.1 h)), if_neg heq, hs j hj]

/-- **Theorem A**: the whole chain is won iff the cell run succeeds for every cell. -/
theorem chain_iff {n : ℕ} {w : List Sym} {blank : Sym} {LD : List (TrD × HU)}
    (hLD : ∀ d ∈ LD, HUok n d) (acc : ℕ) (ws : List ℕ) (ρ₀ : ℕ → Bool) (q₀ : ℕ) :
    chainB (preOps n w blank :: blocksOf n LD acc ws) (fun _ _ => True) ρ₀ q₀ ↔
      ∀ γ : ℕ → Bool, RunC n LD acc γ ws (fun b => ρ₀ (hB b)) q₀ (inp w blank (bval n γ)) := by
  rw [chainB, pre_sem (good_chain hLD acc ws)]
  refine forall_congr' fun γ => chain_runC hLD acc γ ws _ _ q₀ _ (fun b _ => initRho_cB ..)
    (fun b => initRho_hB ..) (fun j hj => initRho_sB _ _ _ _ _ _ hj)

end DB



end FOND
