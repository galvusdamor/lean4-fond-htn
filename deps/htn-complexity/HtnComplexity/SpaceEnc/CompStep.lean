import HtnComplexity.SpaceEnc.CompInv
import HtnComplexity.SpaceEnc.Sound
/-!
# Completeness of the encoding: the steps of the planned run (writer address checks, reads)

Each phase of the planned run (`HtnComplexity/SpaceEnc/CompInv.lean`) allows one
executable step into the next phase.  This file: the common bookkeeping and the phases `CP0`,
`CPW`, `CPR`.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type}

/-! ### Bookkeeping -/

section Book

variable [DecidableEq Q] [DecidableEq Γ]

/-- **Advancing one word of the first unfinished block of a loop.** -/
theorem wstep_word {δ : ActionModel (Fct Q Γ) (Act Q Γ)} {wd : World (Fct Q Γ) (Act Q Γ)}
    {q : Bool} {E rest : List (List (List (Act Q Γ)))} {cur : List (List (Act Q Γ))}
    {M : Multiset (List (Act Q Γ))} {a : Act Q Γ} {t : List (Act Q Γ)}
    (hbq : wd.bs q = E ++ cur :: rest) (hE : AllE E) (hms : msOf cur = M + {a :: t})
    (happ : δ.Applicable a wd.s) :
    ∃ cur', msOf cur' = M + Multiset.filter (· ≠ []) {t} ∧
      WStep δ wd ⟨δ.transition a wd.s, Function.update wd.bs q (cur' :: rest), wd.φ⟩ := by
  have hmem : a :: t ∈ msOf cur := by rw [hms]; simp
  obtain ⟨i, hi⟩ := exists_get_of_mem_msOf hmem
  exact ⟨cur.set i t, msOf_set_of_eq hi (List.cons_ne_nil _ _) hms, wstep_loop hbq hE hi happ⟩

end Book

section Plan

variable {N : NTM Q Γ} {S : ℕ} {c₀ : Config Q Γ} (R : RunSeq N S c₀)
  (m n' : ℕ) (w : List Bool)

theorem Mfr_cons {k c : ℕ} (hc : c < 2 ^ m) :
    Mfr R m n' w k c = {chainW m (parR k) (cdOf R m n' w k c)} + Mfr R m n' w k (c + 1) := by
  unfold Mfr
  rw [show 2 ^ m - c = (2 ^ m - (c + 1)) + 1 by omega, List.range'_succ]
  simp

theorem Mfr_top (k : ℕ) : Mfr R m n' w k (2 ^ m) = 0 := by
  simp [Mfr]

end Plan

theorem decide_lt_succ (P : ℕ → Prop) [DecidablePred P] (j : ℕ) :
    (decide (∀ i < j, P i) && decide (P j)) = decide (∀ i < j + 1, P i) := by
  by_cases h : P j
  · simp only [h, decide_true, Bool.and_true]
    congr 1
    refine propext ⟨fun H i hi => ?_, fun H i hi => H i (by omega)⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact H i hi
    · exact h
  · simp only [h, decide_false, Bool.and_false]
    symm
    simp only [decide_eq_false_iff_not, not_forall]
    exact ⟨j, by omega, h⟩

theorem coreW_ne_nil (cd : CD Q Γ) (p : Bool) (m : ℕ) : coreW cd p m ≠ [] := by
  simp [coreW]

theorem beq_eq_decide' (a b : Bool) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

theorem initConfig_tape {N : NTM Q Γ} {ι : Bool → Γ} {w : List Bool} (c : ℕ) :
    (N.initConfig (w.map ι)).tape c = if c < w.length then ι (w.getD c false) else N.blank := by
  simp only [NTM.initConfig, List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · simp [List.getElem?_eq_getElem h]
  · simp [List.getElem?_eq_none (by omega : w.length ≤ c)]

theorem RB_zero {N : NTM Q Γ} {S : ℕ} {c₀ : Config Q Γ} {R : RunSeq N S c₀} {m n' : ℕ}
    {w : List Bool} {X Y : Multiset (List (Act Q Γ))} {bsq : List (List (List (Act Q Γ)))}
    (h : RB R m n' w 0 X bsq) : RB R m n' w 0 Y bsq := by
  obtain ⟨E, L, h1, h2, h3, -⟩ := h
  exact ⟨E, L, h1, h2, h3, fun h => absurd rfl h⟩

/-! ### The steps -/

variable [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {N : NTM Q Γ} {m n' : ℕ}
  {ι : Bool → Γ} {w : List Bool} (R : RunSeq N (2 ^ m) (N.initConfig (w.map ι)))

/-- `CP0 → CPW 0`: the start `ws` of the chain word. -/
theorem step_CP0 {k c : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CP0 R m n' w k c wd) :
    ∃ wd', WStep (am m n' ι N) wd wd' ∧ CPW R m n' w k c 0 wd' := by
  obtain ⟨hk, hc, fs, hs, hcfs, heqv, hu, ⟨E, cur, hbs, hE, hms⟩, hrb, hφ⟩ := h
  have hms' : msOf cur = (Mfr R m n' w k (c + 1) + {[hOf R k]} +
      tails m (parR k) (R.cf (k + 1)).tape (List.range c)) +
      {.ws (parR k) :: wipW m (parR k) 0 (cdOf R m n' w k c)} := by
    rw [hms, Mfr_cons R m n' w hc, ← chainW_eq]
    abel
  have happ : (am m n' ι N).Applicable (.ws (parR k)) wd.s := by
    rw [hs, app_ws]; exact ⟨hcfs.1, hcfs.2.2.2.1⟩
  obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  refine ⟨_, hst, hk, hc, Nat.zero_le _, { fs with pc := 1 }, ?_, ⟨rfl, h2, h3, h4, h5, h6, h7⟩,
    by simp [heqv], hu, ⟨[], cur', by simp, by simp [AllE], ?_⟩, ?_, hφ⟩
  · show (am m n' ι N).transition _ wd.s = _
    rw [hs, trans_ws m n' ι N w fs _ h1]
  · rw [hcur', filter_singleton_of_ne (wipW_ne_nil _ _ _ _)]
  · show RB R m n' w k (RT R m k c) (Function.update wd.bs (parR k) _ (!parR k))
    rw [update_not]; exact hrb

/-- `CPW j → CPW (j + 1)`: an address check of the writer. -/
theorem step_CPW_lt {k c j : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CPW R m n' w k c j wd)
    (hj : j < m) : ∃ wd', WStep (am m n' ι N) wd wd' ∧ CPW R m n' w k c (j + 1) wd' := by
  obtain ⟨hk, hc, hjm, fs, hs, hcfs, heqv, hu, ⟨E, cur, hbs, hE, hms⟩, hrb, hφ⟩ := h
  set cd := cdOf R m n' w k c with hcd
  have hms' : msOf cur = (Mfr R m n' w k (c + 1) + {[hOf R k]} +
      tails m (parR k) (R.cf (k + 1)).tape (List.range c)) +
      {.wb (parR k) j (cd.x j) (cd.e j) :: wipW m (parR k) (j + 1) cd} := by
    rw [hms, wipW_lt _ _ hj]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  have hx : cd.x j = c.testBit j := rfl
  have he : cd.e j = (c.testBit j == (R.cf k).head.testBit j) := rfl
  have happ : (am m n' ι N).Applicable (.wb (parR k) j (cd.x j) (cd.e j)) wd.s := by
    rw [hs, app_wb]
    refine ⟨h1, hj, by rw [hx, h2], ?_, h4⟩
    rw [hx, he, h3]
    cases c.testBit j <;> cases (R.cf k).head.testBit j <;> rfl
  obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
  refine ⟨_, hst, hk, hc, hj, { fs with pc := j + 2, eqv := fs.eqv && cd.e j }, ?_,
    ⟨rfl, h2, h3, h4, h5, h6, h7⟩, ?_, hu, ⟨[], cur', by simp, by simp [AllE], ?_⟩, ?_, hφ⟩
  · show (am m n' ι N).transition _ wd.s = _
    rw [hs, trans_wb m n' ι N w fs _ _ _ _ h1]
  · show (fs.eqv && cd.e j) = _
    rw [heqv, he, beq_eq_decide', decide_lt_succ (fun i => c.testBit i = (R.cf k).head.testBit i)]
  · rw [hcur', filter_singleton_of_ne (wipW_ne_nil _ _ _ _)]
  · show RB R m n' w k (RT R m k c) (Function.update wd.bs (parR k) _ (!parR k))
    rw [update_not]; exact hrb

/-- `CPW m → CPC` in round `0`: the input read `ri`/`rblank`. -/
theorem step_CPW_rd (hn' : n' = w.length) {c : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)}
    (h : CPW R m n' w 0 c m wd) : ∃ wd', WStep (am m n' ι N) wd wd' ∧ CPC R m n' w 0 c wd' := by
  obtain ⟨hk, hc, -, fs, hs, hcfs, heqv, hu, ⟨E, cur, hbs, hE, hms⟩, hrb, hφ⟩ := h
  have hu' := hu rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  have hwip : wipW m (parR 0) m (cdOf R m n' w 0 c) = (cdOf R m n' w 0 c).rd ++
      coreW (cdOf R m n' w 0 c) (parR 0) m := wipW_self _ _ _
  have htape := initConfig_tape (N := N) (ι := ι) (w := w) c
  rw [← R.cf_zero] at htape
  by_cases hcn : c < n'
  · have hrd : (cdOf R m n' w 0 c).rd = [.ri c (w.getD c false)] := by simp [cdOf, hcn]
    have hms' : msOf cur = (Mfr R m n' w 0 (c + 1) + {[hOf R 0]} +
        tails m (parR 0) (R.cf (0 + 1)).tape (List.range c)) +
        {.ri c (w.getD c false) :: coreW (cdOf R m n' w 0 c) (parR 0) m} := by
      rw [hms, hwip, hrd]; rfl
    have hu2 : fs.u = c := by rw [hu']; omega
    have happ : (am m n' ι N).Applicable (.ri c (w.getD c false)) wd.s := by
      rw [hs, app_ri]
      exact ⟨h1, by rw [h5]; rfl, hu2, by omega, rfl⟩
    obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
    refine ⟨_, hst, hk, hc, { fs with pc := 2 * m + 2, u := c + 1, sym := some (ι (w.getD c false)) },
      ?_, ⟨rfl, h2, h3, h4, h5, h6, h7⟩, heqv, ?_, fun _ => ?_, ⟨[], cur', by simp, by simp [AllE], ?_⟩,
      ?_, hφ⟩
    · show (am m n' ι N).transition _ wd.s = _
      rw [hs, trans_ri m n' ι N w fs _ _ h1 hu2]
    · show some _ = some _
      rw [htape, if_pos (by omega)]
    · show c + 1 = _; omega
    · rw [hcur', filter_singleton_of_ne (coreW_ne_nil _ _ _)]
    · dsimp only
      rw [update_not]; exact RB_zero hrb
  · have hrd : (cdOf R m n' w 0 c).rd = [.rblank] := by simp [cdOf, hcn]
    have hms' : msOf cur = (Mfr R m n' w 0 (c + 1) + {[hOf R 0]} +
        tails m (parR 0) (R.cf (0 + 1)).tape (List.range c)) +
        {.rblank :: coreW (cdOf R m n' w 0 c) (parR 0) m} := by
      rw [hms, hwip, hrd]; rfl
    have hu2 : fs.u = n' := by rw [hu']; omega
    have happ : (am m n' ι N).Applicable .rblank wd.s := by
      rw [hs, app_rblank]
      exact ⟨h1, by rw [h5]; rfl, hu2⟩
    obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
    refine ⟨_, hst, hk, hc, { fs with pc := 2 * m + 2, sym := some N.blank },
      ?_, ⟨rfl, h2, h3, h4, h5, h6, h7⟩, heqv, ?_, fun _ => ?_, ⟨[], cur', by simp, by simp [AllE], ?_⟩,
      ?_, hφ⟩
    · show (am m n' ι N).transition _ wd.s = _
      rw [hs, trans_rblank m n' ι N w fs h1]
    · show some _ = some _
      rw [htape, if_neg (by omega)]
    · show fs.u = _; rw [hu2]; omega
    · rw [hcur', filter_singleton_of_ne (coreW_ne_nil _ _ _)]
    · dsimp only
      rw [update_not]; exact RB_zero hrb

/-- `CPW m → CPR 0` in the later rounds: the start `rv` of the stored tail. -/
theorem step_CPW_rv {k c : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CPW R m n' w k c m wd)
    (hk0 : k ≠ 0) : ∃ wd', WStep (am m n' ι N) wd wd' ∧ CPR R m n' w k c 0 wd' := by
  obtain ⟨hk, hc, -, fs, hs, hcfs, heqv, hu, hwb, ⟨E, L, hbs, hE, -, hL⟩, hφ⟩ := h
  obtain ⟨cur, rfl, hms⟩ := hL hk0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  have hms' : msOf cur = RT R m k (c + 1) +
      {.rv (!parR k) ((R.cf k).tape c) :: rbsL (!parR k) 0 m (bitsOf c)} := by
    rw [hms, RT, RT, tails_range'_cons _ _ _ hc, add_comm]; rfl
  have happ : (am m n' ι N).Applicable (.rv (!parR k) ((R.cf k).tape c)) wd.s := by
    rw [hs, app_rv]; exact ⟨h1, by rw [h4, Bool.not_not]⟩
  obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
  refine ⟨_, hst, hk, hk0, hc, Nat.zero_le _, { fs with pc := m + 2, sym := some ((R.cf k).tape c) },
    ?_, ⟨rfl, h2, h3, h4, h5, h6, h7⟩, heqv, rfl, ?_, ⟨[], _, by simp, by simp [AllE],
      fun h => absurd h hk0, fun _ => ⟨cur', rfl, by rw [hcur']; simp⟩⟩, hφ⟩
  · show (am m n' ι N).transition _ wd.s = _
    rw [hs, trans_rv m n' ι N w fs _ _ h1]
  · show WB R m n' w k (c + 1) c _ (Function.update wd.bs (!parR k) _ (parR k))
    rw [update_not']; exact hwb

/-- `CPR j → CPR (j + 1)`: an address check of the stored tail. -/
theorem step_CPR_lt {k c j : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CPR R m n' w k c j wd)
    (hj : j < m) : ∃ wd', WStep (am m n' ι N) wd wd' ∧ CPR R m n' w k c (j + 1) wd' := by
  obtain ⟨hk, hk0, hc, -, fs, hs, hcfs, heqv, hsym, hwb, ⟨E, L, hbs, hE, -, hL⟩, hφ⟩ := h
  obtain ⟨cur, rfl, hms⟩ := hL hk0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  have hms' : msOf cur = RT R m k (c + 1) +
      {.rb (!parR k) (m - (j + 1)) (bitsOf c (m - (j + 1))) ::
        rbsL (!parR k) 0 (m - (j + 1)) (bitsOf c)} := by
    rw [hms, show m - j = (m - (j + 1)) + 1 by omega, rbsL_zero_succ,
      filter_singleton_of_ne (List.cons_ne_nil _ _)]
  have happ : (am m n' ι N).Applicable
      (.rb (!parR k) (m - (j + 1)) (bitsOf c (m - (j + 1)))) wd.s := by
    rw [hs, app_rb]; exact ⟨by rw [h1]; omega, by omega, by rw [h2]; rfl⟩
  obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
  refine ⟨_, hst, hk, hk0, hc, hj, { fs with pc := 2 * m + 2 - (m - (j + 1)) },
    ?_, ⟨by dsimp only; omega, h2, h3, h4, h5, h6, h7⟩, heqv, hsym, ?_,
      ⟨[], _, by simp, by simp [AllE], fun h => absurd h hk0, fun _ => ⟨cur', rfl, hcur'⟩⟩, hφ⟩
  · show (am m n' ι N).transition _ wd.s = _
    rw [hs, trans_rb m n' ι N w fs _ _ _ (by rw [h1]; omega) (by omega)]
  · show WB R m n' w k (c + 1) c _ (Function.update wd.bs (!parR k) _ (parR k))
    rw [update_not']; exact hwb

omit [Fintype Q] [DecidableEq Q] [DecidableEq Γ] in
/-- `CPR m` is `CPC`: the stored tail has been read. -/
theorem cpc_of_cpr {k c : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CPR R m n' w k c m wd) :
    CPC R m n' w k c wd := by
  obtain ⟨hk, hk0, hc, -, fs, hs, hcfs, heqv, hsym, ⟨E, cur, hbs, hE, hms⟩, hrb, hφ⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  refine ⟨hk, hc, fs, hs, ⟨by omega, h2, h3, h4, h5, h6, h7⟩, heqv, hsym, fun h => absurd h hk0,
    ⟨E, cur, hbs, hE, ?_⟩, ?_, hφ⟩
  · rw [hms, wipW_self]
    simp [cdOf, hk0, coreW]
  · rwa [Nat.sub_self, rbsL_zero_zero, filter_singleton_nil, add_zero] at hrb

end SpaceEnc

end HTN
