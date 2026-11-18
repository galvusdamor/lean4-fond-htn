import HtnComplexity.SpaceEnc.CompStep2
/-!
# Completeness of the encoding: the steps of the planned run (head move)

The phase `CPE` of the planned run: the head move closes the round; the next round starts
(`CP0 (k + 1) 0`) or the accepting configuration has been reached (`CFin`).
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {N : NTM Q Γ}
  {m n' : ℕ} {ι : Bool → Γ} {w : List Bool} (R : RunSeq N (2 ^ m) (N.initConfig (w.map ι)))

omit [Fintype Q] [DecidableEq Q] [DecidableEq Γ] in
/-- **The planned head move** is applicable at the end of the round and moves the head as the
machine does. -/
theorem hOf_step {k : ℕ} (hk : k < R.r) {fs : FS Q Γ} (h1 : fs.pc = 2 * m + 4)
    (h3 : fs.hd = (R.cf k).head) (h4 : fs.par = parR k) (hmv : fs.mv = some (R.tr k).2.2) :
    (am m n' ι N).Applicable (hOf R k) (enc m w fs) ∧
      (am m n' ι N).transition (hOf R k) (enc m w fs) =
        enc m w { fs with pc := 0, par := !parR k, mv := none, first := false,
                          hd := (R.cf (k + 1)).head } := by
  have hnext : (R.cf (k + 1)).head = (R.tr k).2.2.apply (R.cf k).head := by
    rw [R.cf_succ k hk]; rfl
  have hlt1 := R.head_lt (k + 1) hk
  have hlt0 := R.head_lt k hk.le
  unfold hOf
  cases hμ : (R.tr k).2.2 with
  | left =>
    rw [hμ] at hmv hnext
    simp only [Move.apply] at hnext
    dsimp only
    split_ifs with h0
    · have hh : (R.cf (k + 1)).head = fs.hd := by rw [hnext, h3, h0]
      rw [hh]
      refine ⟨(app_hdec0 m n' ι N w fs).2 ⟨h1, h4, hmv, fun j _ => by rw [h3, h0]; simp⟩, ?_⟩
      rw [trans_hdec0 m n' ι N w fs _ h1 h4 hmv]
    · refine ⟨(app_hdec m n' ι N w fs).2 ⟨h1, h4, hmv, lob_lt hlt0 h0,
        by rw [h3]; exact lob_spec h0, fun j hj => by rw [h3]; exact lob_min h0 hj⟩, ?_⟩
      rw [trans_hdec m n' ι N w fs _ _ h1 h4 hmv (lob_lt hlt0 h0)
        (by rw [h3]; exact lob_spec h0) (fun j hj => by rw [h3]; exact lob_min h0 hj), hnext, h3]
  | stay =>
    rw [hμ] at hmv hnext
    simp only [Move.apply] at hnext
    dsimp only
    have hh : (R.cf (k + 1)).head = fs.hd := by rw [hnext, h3]
    rw [hh]
    exact ⟨(app_hstay m n' ι N w fs).2 ⟨h1, h4, hmv⟩, trans_hstay m n' ι N w fs _ h1 h4 hmv⟩
  | right =>
    rw [hμ] at hmv hnext
    simp only [Move.apply] at hnext
    dsimp only
    have hl := lzb_lt hlt0 (by omega : (R.cf k).head + 1 ≠ 2 ^ m)
    refine ⟨(app_hinc m n' ι N w fs).2 ⟨h1, h4, hmv, hl, by rw [h3]; exact lzb_spec _,
      fun j hj => by rw [h3]; exact lzb_min hj⟩, ?_⟩
    rw [trans_hinc m n' ι N w fs _ _ h1 h4 hmv hl (by rw [h3]; exact lzb_spec _)
      (fun j hj => by rw [h3]; exact lzb_min hj), hnext, h3]

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] in
/-- At the end of round `k` the reader's blocks are consumed up to its future blocks. -/
theorem reader_rest {k : ℕ} {bsq : List (List (List (Act Q Γ)))}
    (h : RB R m n' w k 0 bsq) :
    ∃ E, AllE E ∧ bsq = E ++ futB R m n' w (!parR k) (k + 1) := by
  obtain ⟨E, L, hbs, hE, hL0, hL1⟩ := h
  by_cases hk0 : k = 0
  · exact ⟨E, hE, by rw [hbs, hL0 hk0]⟩
  · obtain ⟨cur, hL, hms⟩ := hL1 hk0
    refine ⟨E ++ [cur], allE_append hE ?_, by rw [hbs, hL]; simp⟩
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact allEmpty_iff_msOf.2 hms

/-- `CPE → CP0 (k + 1) 0` or `CFin`: the head move at the end of round `k`. -/
theorem step_CPE {k : ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CPE R m n' w k wd) :
    ∃ wd', WStep (am m n' ι N) wd wd' ∧ (CP0 R m n' w (k + 1) 0 wd' ∨ CFin R m w wd') := by
  obtain ⟨hk, fs, hs, hcfs, heqv, ⟨E, cur, hbs, hE, hms⟩, hrb, hφ⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hcfs
  obtain ⟨hst6, hmv⟩ := h6 trivial
  obtain ⟨happ, htr⟩ := hOf_step (n' := n') (ι := ι) R hk h1 h3 h4 hmv
  have hms' : msOf cur = tails m (parR k) (R.cf (k + 1)).tape (List.range (2 ^ m)) +
      {hOf R k :: []} := by
    rw [hms, Mfr_top]; abel
  obtain ⟨cur', hcur', hst⟩ := wstep_word hbs hE hms' (by rw [hs]; exact happ)
  rw [filter_singleton_nil, add_zero] at hcur'
  obtain ⟨E3, hE3, hE3eq⟩ := reader_rest R hrb
  have hp1 : parR (k + 1) = !parR k := parR_succ k
  have hne : parR (k + 1) ≠ parR k := by rw [hp1]; cases parR k <;> simp
  have hst' : (R.cf (k + 1)).state = (R.tr k).1 := by rw [R.cf_succ k hk]; rfl
  set fs' : FS Q Γ := { fs with pc := 0, par := !parR k, mv := none, first := false,
                                hd := (R.cf (k + 1)).head } with hfs'
  refine ⟨_, hst, ?_⟩
  by_cases hk1 : k + 1 < R.r
  · refine Or.inl ⟨hk1, Nat.two_pow_pos m, fs', by rw [hs]; exact htr,
      ⟨rfl, h2, rfl, by rw [hp1], by simp [hfs'], fun h => absurd h (Nat.not_lt_zero _),
        fun _ => ⟨by rw [hst', ← hst6], rfl⟩⟩, heqv, fun h => absurd h (Nat.succ_ne_zero k),
      ?_, ?_, hφ⟩
    · show WB R m n' w (k + 1) 0 0 0 (Function.update wd.bs (parR k) _ (parR (k + 1)))
      rw [hp1, update_not, hE3eq]
      refine ⟨E3, blk R m n' w (k + 1), ?_, hE3, msOf_blk' R m n' w (k + 1) _⟩
      rw [← hp1, futB_self R m n' w hk1]
    · show RB R m n' w (k + 1) _ (Function.update wd.bs (parR k) _ (!parR (k + 1)))
      rw [hp1, Bool.not_not, update_self']
      refine ⟨[], cur' :: futB R m n' w (parR k) (k + 1), rfl, by simp [AllE],
        fun h => absurd h (Nat.succ_ne_zero k),
        fun _ => ⟨cur', ?_, ?_⟩⟩
      · rw [futB_other R m n' w hne, hp1, Bool.not_not]
      · rw [hcur', RT, hp1, Bool.not_not, Nat.sub_zero, List.range_eq_range']
  · have hr : R.r = k + 1 := by omega
    refine Or.inr ⟨fs', by rw [hs]; exact htr, rfl, h2, by rw [hr, hst', ← hst6], ?_,
      fun h => absurd h (by omega), fun _ => ⟨[], cur', ?_, by simp [AllE], ?_⟩, hφ⟩
    · show AllE (Function.update wd.bs (parR k) _ (parR R.r))
      rw [hr, hp1, update_not, hE3eq, futB_of_ge R m n' w (by omega), List.append_nil]
      exact hE3
    · show Function.update wd.bs (parR k) _ (!parR R.r) = _
      rw [hr, hp1, Bool.not_not, update_self', futB_of_ge R m n' w (by omega)]
      rfl
    · rw [hcur', hr, hp1, Bool.not_not, List.range_eq_range']

end SpaceEnc

end HTN
