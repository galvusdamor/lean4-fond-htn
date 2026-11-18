import HtnComplexity.SpaceEnc.SoundPick
/-!
# Soundness of the encoding: the steps of phase `P0` and of phase `PW`

* `HTN.SpaceEnc.step_P0` — at program counter `0` the plan either accepts (`fin`, only at the
  start of a round) or starts an unstarted chain word of the writer;
* `HTN.SpaceEnc.step_PW` — at program counter `k + 1 ≤ m` the word in progress checks its
  address bit `k`.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {m n' : ℕ}
  {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool}

omit [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] in
theorem accL_mem {q : Q} (h : q ∈ accL N) : q ∈ N.accept := by
  simpa [accL] using h

/-- Starting a chain word: the writer's current block after the step. -/
theorem wcur_start {p : Bool} {c : ℕ} {nv : ℕ → Γ} {Fr : Multiset (CD Q Γ)} {h : Act Q Γ}
    {bl : List (List (Act Q Γ))} {i : ℕ} {cd : CD Q Γ} (hFr : ∀ cd ∈ Fr, ValidCD m n' N p cd)
    (hcard : Multiset.card Fr + c + Multiset.card (0 : Multiset (List (Act Q Γ))) = 2 ^ m)
    (hh : IsHActP p h)
    (hms : msOf bl = Fr.map (chainW m p) + {[h]} + tails m p nv (List.range c) + 0)
    (hcd : cd ∈ Fr) (hi : bl[i]? = some (chainW m p cd)) :
    WCur m n' N p c nv {wipW m p 0 cd} (bl.set i (wipW m p 0 cd)) := by
  classical
  refine ⟨Fr.erase cd, h, fun cd' hcd' => hFr cd' (Multiset.mem_of_mem_erase hcd'), ?_, hh, ?_⟩
  · have := Multiset.card_erase_of_mem hcd
    rw [Nat.pred_eq_sub_one] at this
    have h1 : 0 < Multiset.card Fr := Multiset.card_pos_iff_exists_mem.2 ⟨cd, hcd⟩
    simp only [Multiset.card_zero, add_zero] at hcard
    simp only [Multiset.card_singleton]
    omega
  · rw [msOf_set hi (chainW_ne_nil m p cd), hms, add_zero,
      filter_singleton_of_ne (wipW_ne_nil m p 0 cd)]
    have hmem : chainW m p cd ∈ Fr.map (chainW m p) := Multiset.mem_map_of_mem _ hcd
    rw [Multiset.erase_add_left_pos _ (Multiset.mem_add.2 (Or.inl hmem)),
      Multiset.erase_add_left_pos _ hmem, multiset_map_erase_of_mem _ hcd]

/-- **The step of phase `P0`.** -/
theorem step_P0 {p : Bool} {cfg : Config Q Γ} {first : Bool} {c : ℕ} {nv : ℕ → Γ}
    {fs : FS Q Γ} {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)}
    {a : Act Q Γ} {z : List (Act Q Γ)}
    (hI : InvP0 m n' ι N w p cfg first c nv fs bs φ) (hG : G bs φ (a :: z))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) :
    N.AcceptsInSpace (w.map ι) (2 ^ m) ∨
      ∃ bs', (am m n' ι N).transition a (enc m w fs) = enc m w { fs with pc := 1 } ∧
        G bs' φ z ∧ InvPW m n' ι N w p cfg first c 0 nv { fs with pc := 1 } bs' φ := by
  obtain ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, hpc, heqv, hc, hu, hnv, hst, hφ, hW0, hW1, hR⟩ := hI
  rcases g_step hG with ⟨q, E, bl, rest, i, t, hbq, hE, hi, hG'⟩ | ⟨φ', hφ', hG'⟩
  · by_cases hq : q = p
    · subst hq
      have hcur : WCur m n' N q c nv 0 bl ∧ ∀ b ∈ rest, FreshBlock m n' N q b := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · obtain ⟨hF, hrest⟩ := pickF (hW0 h0) hbq hE hi (List.cons_ne_nil _ _)
          subst h0
          exact ⟨hF.wcur nv, hrest⟩
        · exact pickW (hW1 h0) (fun cur h => msOf_ne_zero_not_allEmpty h.ms_ne_zero) hbq hE hi
            (List.cons_ne_nil _ _)
      obtain ⟨⟨Fr, h, hFr, hcard, hh, hms⟩, hrest⟩ := hcur
      have hv := mem_msOf_of_get hi (List.cons_ne_nil _ _)
      rw [hms] at hv
      rcases writer_word hh hv happ hpar with ⟨-, rfl, cd, hcd, he⟩ | ⟨h2, -⟩ | hX
      · right
        have he' := he
        rw [chainW_eq] at he'
        obtain ⟨-, rfl⟩ := List.cons.inj he'
        rw [he] at hi
        refine ⟨Function.update bs q (bl.set i (wipW m q 0 cd) :: rest),
          trans_ws m n' ι N w fs q hpc, hG', hRun, ⟨hpar, hhd, hfirst, hcnt⟩, rfl, Nat.zero_le _,
          hc, hu, hnv, hst, hφ, by simp [heqv], ⟨cd, ⟨hFr cd hcd, by simp⟩, ?_⟩, ?_⟩
        · rw [update_self']
          exact blocks_set (wcur_start hFr hcard hh hms hcd hi) hrest
        · rw [update_not]
          exact hR
      · omega
      · simp at hX
    · have hq' := bool_eq_not_of_ne hq
      subst hq'
      exact (reader_no_fire hR hbq hE hi happ hpar (by omega)).elim
  · left
    obtain ⟨q, hq, rest, rfl⟩ := hφ
    obtain ⟨rfl, -⟩ := List.cons.inj hφ'
    obtain ⟨-, hst', hbits⟩ := (app_fin m n' ι N w fs).1 happ
    rw [hcnt] at hbits
    have hc0 : c = 0 := eq_zero_of_all_testBit hc hbits
    subst hc0
    have hs := (hst.2 (Nat.not_lt_zero _)).1
    obtain ⟨r, hr⟩ := hRun.1
    exact ⟨r, cfg, hr, by rw [← hs, hst']; exact accL_mem hq⟩

end SpaceEnc

end HTN

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {m n' : ℕ}
  {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool}

/-- Advancing the word in progress of the writer's current block. -/
theorem wcur_adv {p : Bool} {c : ℕ} {nv : ℕ → Γ} {v t : List (Act Q Γ)}
    {bl : List (List (Act Q Γ))} {i : ℕ} (hW : WCur m n' N p c nv {v} bl)
    (hi : bl[i]? = some v) (hv : v ≠ []) (ht : t ≠ []) :
    WCur m n' N p c nv {t} (bl.set i t) := by
  obtain ⟨Fr, h, hFr, hcard, hh, hms⟩ := hW
  refine ⟨Fr, h, hFr, by simpa using hcard, hh, ?_⟩
  rw [msOf_set_of_eq hi hv hms, filter_singleton_of_ne ht]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The word in progress of the writer is the only word of the writer's block that can fire
strictly between the program counters `0` and `2m + 4`. -/
theorem writer_wip {p : Bool} {c : ℕ} {nv : ℕ → Γ} {v : List (Act Q Γ)}
    {bl : List (List (Act Q Γ))} {i : ℕ} {a : Act Q Γ} {t : List (Act Q Γ)} {fs : FS Q Γ}
    (hW : WCur m n' N p c nv {v} bl) (hi : bl[i]? = some (a :: t))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) (hpar : fs.par = p) (hpc0 : fs.pc ≠ 0)
    (hpc4 : fs.pc ≠ 2 * m + 4) : a :: t = v := by
  obtain ⟨Fr, h, hFr, hcard, hh, hms⟩ := hW
  have hv := mem_msOf_of_get hi (List.cons_ne_nil _ _)
  rw [hms] at hv
  rcases writer_word hh hv happ hpar with ⟨h1, -⟩ | ⟨h1, -⟩ | hX
  · exact absurd h1 hpc0
  · exact absurd h1 hpc4
  · simpa using hX

/-- **The step of phase `PW k`, `k < m`**: the address check `wb p k`. -/
theorem step_PW {p : Bool} {cfg : Config Q Γ} {first : Bool} {c k : ℕ} {nv : ℕ → Γ}
    {fs : FS Q Γ} {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)}
    {a : Act Q Γ} {z : List (Act Q Γ)} (hk : k < m)
    (hI : InvPW m n' ι N w p cfg first c k nv fs bs φ) (hG : G bs φ (a :: z))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) :
    ∃ fs' bs', (am m n' ι N).transition a (enc m w fs) = enc m w fs' ∧
        G bs' φ z ∧ InvPW m n' ι N w p cfg first c (k + 1) nv fs' bs' φ := by
  obtain ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, hpc, -, hc, hu, hnv, hst, hφ, heqv,
    ⟨cd, ⟨hvalid, hcd⟩, hB⟩, hR⟩ := hI
  rcases g_step hG with ⟨q, E, bl, rest, i, t, hbq, hE, hi, hG'⟩ | ⟨φ', hφ', hG'⟩
  · by_cases hq : q = p
    · subst hq
      obtain ⟨hW, hrest⟩ := pickW hB (fun cur h => msOf_ne_zero_not_allEmpty h.ms_ne_zero)
        hbq hE hi (List.cons_ne_nil _ _)
      have he := writer_wip hW hi happ hpar (by omega) (by omega)
      rw [wipW_lt q cd hk] at he
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      obtain ⟨-, -, hx, he', -⟩ := (app_wb m n' ι N w fs).1 happ
      rw [hcnt] at hx
      rw [hhd] at he'
      have hek : cd.e k = (c.testBit k == cfg.head.testBit k) := by
        rw [hx] at he'
        revert he'
        generalize cd.e k = e
        generalize c.testBit k = b1
        generalize cfg.head.testBit k = b2
        cases e <;> cases b1 <;> cases b2 <;> simp
      refine ⟨_, Function.update bs q (bl.set i (wipW m q (k + 1) cd) :: rest),
        trans_wb m n' ι N w fs q k _ _ hpc, hG', hRun, ⟨hpar, hhd, hfirst, hcnt⟩, rfl, hk, hc,
        hu, hnv, hst, hφ, ?_, ⟨cd, ⟨hvalid, ?_⟩, ?_⟩, ?_⟩
      · simp only [heqv, hek]
        by_cases hall : ∀ i < k, c.testBit i = cfg.head.testBit i
        · have hall' : (∀ i < k + 1, c.testBit i = cfg.head.testBit i) ↔
              c.testBit k = cfg.head.testBit k := by
            constructor
            · intro h'; exact h' k (by omega)
            · intro h' i hi
              rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
              · exact hall i hi
              · exact h'
          rw [decide_eq_true hall, Bool.true_and]
          simp only [hall']
          cases c.testBit k <;> cases cfg.head.testBit k <;> rfl
        · have hall' : ¬ ∀ i < k + 1, c.testBit i = cfg.head.testBit i :=
            fun h' => hall fun i hi => h' i (by omega)
          rw [decide_eq_false hall, decide_eq_false hall']
          rfl
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hcd i hi
        · exact ⟨hx, hek⟩
      · rw [update_self']
        exact blocks_set (wcur_adv hW (by rw [wipW_lt q cd hk]; exact hi) (wipW_ne_nil _ _ _ _)
          (wipW_ne_nil _ _ _ _)) hrest
      · rw [update_not]
        exact hR
    · have hq' := bool_eq_not_of_ne hq
      subst hq'
      exact (reader_no_fire hR hbq hE hi happ hpar (by omega)).elim
  · obtain ⟨q, -, rest, rfl⟩ := hφ
    obtain ⟨rfl, -⟩ := List.cons.inj hφ'
    have := ((app_fin m n' ι N w fs).1 happ).1
    omega

end SpaceEnc

end HTN
