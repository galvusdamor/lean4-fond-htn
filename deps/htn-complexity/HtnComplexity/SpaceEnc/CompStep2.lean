import HtnComplexity.SpaceEnc.CompStep
/-!
# Completeness of the encoding: the steps of the planned run (core, increment, head move)

The phases `CPC` (core action), `CPI` (increment) and `CPE` (head move) of the planned run.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type}

section Plan

variable {N : NTM Q Γ} {S : ℕ} {c₀ : Config Q Γ} (R : RunSeq N S c₀) (m n' : ℕ) (w : List Bool)

/-- The stored symbol of position `c` in round `k` is the symbol of the next configuration. -/
theorem val_cdOf {k : ℕ} (hk : k < R.r) (c : ℕ) :
    (cdOf R m n' w k c).val = (R.cf (k + 1)).tape c := by
  rw [R.cf_succ k hk]
  simp only [cdOf, applyTr, Function.update_apply]

theorem msOf_blk' (k : ℕ) (f : ℕ → Γ) :
    msOf (blk R m n' w k) = Mfr R m n' w k 0 + {[hOf R k]} + tails m (parR k) f (List.range 0) +
      0 := by
  rw [msOf_blk]
  simp [Mfr, tails]

end Plan

variable [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {N : NTM Q Γ} {m n' : ℕ}
  {ι : Bool → Γ} {w : List Bool} (R : RunSeq N (2 ^ m) (N.initConfig (w.map ι)))

/-- `CPC → CPI`: the core action (`tr` at the head, `cp` elsewhere). -/
theorem step_CPC {k c : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CPC R m n' w k c wd) :
    ∃ wd', WStep (am m n' ι N) wd wd' ∧ CPI R m n' w k c wd' := by
  obtain ⟨hk, hc, fs, hs, hcfs, heqv, hsym, hu, ⟨E, cur, hbs, hE, hms⟩, hrb, hφ⟩ := h
  set cd := cdOf R m n' w k c with hcd
  have hms' : msOf cur = (Mfr R m n' w k (c + 1) + {[hOf R k]} +
      tails m (parR k) (R.cf (k + 1)).tape (List.range c)) +
      {cd.core :: (coreW cd (parR k) m).drop 1} := by
    rw [hms]; rfl
  have hX : (coreW cd (parR k) m).drop 1 ≠ [] := by simp [coreW]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  have hhd : (R.cf k).head < 2 ^ m := R.head_lt k hk.le
  by_cases hch : c = (R.cf k).head
  · have hcore : cd.core = .tr (parR k) (R.cf k).state ((R.cf k).tape c) (R.tr k).1 (R.tr k).2.1
        (R.tr k).2.2 := by simp [hcd, cdOf, hch]
    have hnd : ¬ (R.cf k).head < c := by omega
    have happ : (am m n' ι N).Applicable cd.core wd.s := by
      rw [hcore, hs, app_tr]
      exact ⟨h1, by rw [heqv, hch]; simp, hsym, (h7 hnd).1, h4⟩
    obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
    refine ⟨_, hst, hk, hc, { fs with pc := 2 * m + 3, st := (R.tr k).1, mv := some (R.tr k).2.2 },
      ?_, ⟨rfl, h2, h3, h4, h5, fun _ => ⟨rfl, rfl⟩, fun h => absurd (by omega) h⟩, hu,
      ⟨[], cur', by simp, by simp [AllE], by rw [hcur', filter_singleton_of_ne hX]⟩, ?_, hφ⟩
    · show (am m n' ι N).transition _ wd.s = _
      rw [hs, hcore, trans_tr m n' ι N w fs _ _ _ _ _ _ h1 (h7 hnd).1 (h7 hnd).2]
    · dsimp only
      rw [update_not]; exact hrb
  · have hcore : cd.core = .cp (parR k) ((R.cf k).tape c) := by simp [hcd, cdOf, hch]
    have happ : (am m n' ι N).Applicable cd.core wd.s := by
      rw [hcore, hs, app_cp]
      refine ⟨h1, ?_, hsym, h4⟩
      rw [heqv, decide_eq_false_iff_not]
      exact fun H => hch (eq_of_testBit_lt hc hhd H)
    obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
    refine ⟨_, hst, hk, hc, { fs with pc := 2 * m + 3 },
      ?_, ⟨rfl, h2, h3, h4, h5, fun h => h6 (by omega), fun h => h7 (by omega)⟩, hu,
      ⟨[], cur', by simp, by simp [AllE], by rw [hcur', filter_singleton_of_ne hX]⟩, ?_, hφ⟩
    · show (am m n' ι N).transition _ wd.s = _
      rw [hs, hcore, trans_cp m n' ι N w fs _ _ h1]
    · dsimp only
      rw [update_not]; exact hrb

/-- `CPI → CP0 (c + 1)`: the increment `inc` of the counter. -/
theorem step_CPI_inc {k c : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CPI R m n' w k c wd)
    (hcW : c + 1 ≠ 2 ^ m) : ∃ wd', WStep (am m n' ι N) wd wd' ∧ CP0 R m n' w k (c + 1) wd' := by
  obtain ⟨hk, hc, fs, hs, hcfs, hu, ⟨E, cur, hbs, hE, hms⟩, hrb, hφ⟩ := h
  set cd := cdOf R m n' w k c with hcd
  have hinc : cd.incw = .inc (parR k) (lzb c) := by simp [hcd, cdOf, hcW]
  have hms' : msOf cur = (Mfr R m n' w k (c + 1) + {[hOf R k]} +
      tails m (parR k) (R.cf (k + 1)).tape (List.range c)) +
      {.inc (parR k) (lzb c) :: tl m (parR k) c ((R.cf (k + 1)).tape c)} := by
    rw [hms, ← hinc, ← val_cdOf R m n' w hk c]; rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  have hlt := lzb_lt hc hcW
  have happ : (am m n' ι N).Applicable (.inc (parR k) (lzb c)) wd.s := by
    rw [hs, app_inc]
    exact ⟨h1, h4, hlt, by rw [h2]; exact lzb_spec c, fun j hj => by rw [h2]; exact lzb_min hj⟩
  obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
  refine ⟨_, hst, hk, by omega, { fs with pc := 0, cnt := fs.cnt + 1, eqv := true }, ?_,
    ⟨rfl, by dsimp only; rw [h2], h3, h4, h5, h6, h7⟩, rfl, hu,
    ⟨[], cur', by simp, by simp [AllE], ?_⟩, ?_, hφ⟩
  · show (am m n' ι N).transition _ wd.s = _
    rw [hs, trans_inc m n' ι N w fs _ _ h1 hlt
      (by rw [h2]; exact lzb_spec c) (fun j hj => by rw [h2]; exact lzb_min hj)]
  · rw [hcur', filter_singleton_of_ne (tl_ne_nil _ _ _ _), tails_range_succ, add_zero]
    abel
  · dsimp only
    rw [update_not]; exact hrb

/-- `CPI → CPE`: the wrap-around `wrap` of the counter at the end of the round. -/
theorem step_CPI_wrap {k c : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CPI R m n' w k c wd)
    (hcW : c + 1 = 2 ^ m) : ∃ wd', WStep (am m n' ι N) wd wd' ∧ CPE R m n' w k wd' := by
  obtain ⟨hk, hc, fs, hs, hcfs, hu, ⟨E, cur, hbs, hE, hms⟩, hrb, hφ⟩ := h
  set cd := cdOf R m n' w k c with hcd
  have hwr : cd.incw = .wrap (parR k) := by simp [hcd, cdOf, hcW]
  have hms' : msOf cur = (Mfr R m n' w k (c + 1) + {[hOf R k]} +
      tails m (parR k) (R.cf (k + 1)).tape (List.range c)) +
      {.wrap (parR k) :: tl m (parR k) c ((R.cf (k + 1)).tape c)} := by
    rw [hms, ← hwr, ← val_cdOf R m n' w hk c]; rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hcfs
  have hall : ∀ j < m, fs.cnt.testBit j = true := by
    intro j hj
    rw [h2, show c = 2 ^ m - 1 by omega, Nat.testBit_two_pow_sub_one]
    simp [hj]
  have happ : (am m n' ι N).Applicable (.wrap (parR k)) wd.s := by
    rw [hs, app_wrap]; exact ⟨h1, h4, hall⟩
  have hhd : (R.cf k).head < c + 1 := by have := R.head_lt k hk.le; omega
  obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' happ
  refine ⟨_, hst, hk, { fs with pc := 2 * m + 4, cnt := 0, eqv := true }, ?_,
    ⟨rfl, rfl, h3, h4, h5, fun _ => h6 hhd, fun h => absurd trivial h⟩, rfl,
    ⟨[], cur', by simp, by simp [AllE], ?_⟩, ?_, hφ⟩
  · show (am m n' ι N).transition _ wd.s = _
    rw [hs, trans_wrap m n' ι N w fs _ h1 hall]
  · have hM : Mfr R m n' w k (c + 1) = 0 := by rw [hcW]; exact Mfr_top R m n' w k
    have hT := tails_range_succ (Q := Q) m (parR k) (R.cf (k + 1)).tape c
    rw [hcW] at hT
    rw [hcur', filter_singleton_of_ne (tl_ne_nil _ _ _ _), hT, hM, Mfr_top, add_zero]
    abel
  · dsimp only
    rw [update_not]
    have : RT R m k (c + 1) = 0 := by
      unfold RT; rw [show 2 ^ m - (c + 1) = 0 by omega]; rfl
    rw [this] at hrb; exact hrb

end SpaceEnc

end HTN
