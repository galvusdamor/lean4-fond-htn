import HtnComplexity.SpaceEnc.SoundRead
/-!
# Soundness of the encoding: writing a symbol, incrementing, moving the head

* `HTN.SpaceEnc.step_PC` — the core action of the word in progress: `cp` away from the head
  (the stored symbol is the one read), `tr` at the head (a transition of the machine);
* `HTN.SpaceEnc.step_PI` — the increment `inc` (next position, phase `P0`) or `wrap` (end of the
  round, phase `PE`);
* `HTN.SpaceEnc.step_PE` — the head move: one step of the machine, the next round begins with
  the loops exchanged.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {m n' : ℕ}
  {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool}

omit [DecidableEq Q] [DecidableEq Γ] in
theorem mem_step_of_transL {d : Q × Γ × Q × Γ × Move} (h : d ∈ transL N) :
    (d.2.2.1, d.2.2.2.1, d.2.2.2.2) ∈ N.step d.1 d.2.1 := by
  classical
  unfold transL at h
  have := (List.mem_filter.1 h).2
  simpa using this

omit [DecidableEq Q] [DecidableEq Γ] in
theorem WCur.congr {p : Bool} {c : ℕ} {nv nv' : ℕ → Γ} {X X' : Multiset (List (Act Q Γ))}
    {cur : List (List (Act Q Γ))} (h : WCur m n' N p c nv X cur) (hnv : ∀ c' < c, nv c' = nv' c')
    (hX : X = X') : WCur m n' N p c nv' X' cur := by
  subst hX
  obtain ⟨Fr, a, hFr, hcard, ha, hms⟩ := h
  refine ⟨Fr, a, hFr, hcard, ha, ?_⟩
  rw [hms, tails_congr fun c' hc' => hnv c' (List.mem_range.1 hc')]

/-- **The step of phase `PC`**: the core action. -/
theorem step_PC {p : Bool} {cfg : Config Q Γ} {first : Bool} {c : ℕ} {nv : ℕ → Γ}
    {fs : FS Q Γ} {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)}
    {a : Act Q Γ} {z : List (Act Q Γ)}
    (hI : InvPC m n' ι N w p cfg first c nv fs bs φ) (hG : G bs φ (a :: z))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) :
    ∃ fs' bs' nv', (am m n' ι N).transition a (enc m w fs) = enc m w fs' ∧ G bs' φ z ∧
      InvPI m n' ι N w p cfg first c nv' fs' bs' φ := by
  obtain ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, hpc, hc, hu, hnv, hst, hφ, hsym, heqv,
    ⟨cd, rd, hvalid, hxc, hrd, hB⟩, hR⟩ := hI
  have hhw : cfg.head < 2 ^ m := by
    obtain ⟨r, hr⟩ := hRun.1; exact reachesSpace_head_lt hr
  rcases g_step hG with ⟨q, E, bl, rest, i, t, hbq, hE, hi, hG'⟩ | ⟨φ', hφ', hG'⟩
  · by_cases hq : q = p
    · subst hq
      obtain ⟨hW, hrest⟩ := pickW hB (fun cur h => msOf_ne_zero_not_allEmpty h.ms_ne_zero)
        hbq hE hi (List.cons_ne_nil _ _)
      have he := writer_wip hW hi happ hpar (by omega) (by omega)
      have hrd0 : rd = [] := by
        rcases hrd with h0 | h0 | ⟨i', b', h0⟩
        · exact h0
        · rw [h0] at he
          obtain ⟨rfl, -⟩ := List.cons.inj he
          have := pc_of_app happ
          simp only [pcNeed] at this
          omega
        · rw [h0] at he
          obtain ⟨rfl, -⟩ := List.cons.inj he
          have := pc_of_app happ
          simp only [pcNeed] at this
          omega
      subst hrd0
      simp only [List.nil_append, List.cons_append] at he
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      have hrbs : (rbsL q 0 m cd.x : List (Act Q Γ)) = rbsL q 0 m (bitsOf c) :=
        rbsL_congr q m fun i hi => hxc i hi
      have hW' := wcur_adv hW (t := cd.incw :: .rv q cd.val :: rbsL q 0 m cd.x)
        (by simpa using hi) (by simp) (by simp)
      have hinc : (∃ k < m, cd.incw = .inc q k) ∨ cd.incw = .wrap q := hvalid.2.2
      rcases hvalid.2.1 with ⟨g, hg, hval⟩ | ⟨d, hd, hcore, hval⟩
      · -- copy
        rw [hg] at happ
        obtain ⟨-, heq, hsg, -⟩ := (app_cp m n' ι N w fs).1 happ
        rw [hsym] at hsg
        have hgc : g = cfg.tape c := (Option.some.inj hsg).symm
        have hch : c ≠ cfg.head := by
          intro h'
          rw [heqv, h'] at heq
          simp at heq
        refine ⟨{ fs with pc := 2 * m + 3 }, Function.update bs q (bl.set i (cd.incw :: .rv q cd.val ::
            rbsL q 0 m cd.x) :: rest), Function.update nv c cd.val,
          by rw [hg]; exact trans_cp m n' ι N w fs q g hpc, hG', hRun,
          ⟨hpar, hhd, hfirst, hcnt⟩, rfl, hc, hu, ?_, ?_, hφ, ⟨cd.incw, hinc, ?_⟩, ?_⟩
        · intro c' hc' hne
          by_cases h' : c' = c
          · subst h'; rw [Function.update_self, hval, hgc]
          · rw [Function.update_of_ne h']; exact hnv c' (by omega) hne
        · refine ⟨fun hlt => ?_, fun hlt => hst.2 (by omega)⟩
          obtain ⟨μ, hμ, hstep⟩ := hst.1 (by omega)
          exact ⟨μ, hμ, by rwa [Function.update_of_ne (Ne.symm hch)]⟩
        · rw [update_self']
          refine blocks_set (hW'.congr (fun c' hc' => ?_) ?_) hrest
          · rw [Function.update_of_ne (by omega)]
          · rw [Function.update_self, hrbs]
        · rw [update_not]; exact hR
      · -- transition
        rw [hcore] at happ
        obtain ⟨-, heq, hsg, hsq, -⟩ := (app_tr m n' ι N w fs).1 happ
        rw [hsym] at hsg
        have hch : c = cfg.head := by
          rw [heqv] at heq
          exact eq_of_testBit_lt hc hhw (of_decide_eq_true heq)
        have hpre := hst.2 (by omega)
        have hstep := mem_step_of_transL hd
        refine ⟨{ fs with pc := 2 * m + 3, st := d.2.2.1, mv := some d.2.2.2.2 },
          Function.update bs q (bl.set i (cd.incw :: .rv q cd.val ::
            rbsL q 0 m cd.x) :: rest), Function.update nv c cd.val,
          by rw [hcore]; exact trans_tr m n' ι N w fs q _ _ _ _ _ hpc hsq hpre.2, hG', hRun,
          ⟨hpar, hhd, hfirst, hcnt⟩, rfl, hc, hu, ?_, ?_, hφ, ⟨cd.incw, hinc, ?_⟩, ?_⟩
        · intro c' hc' hne
          have h' : c' ≠ c := by omega
          rw [Function.update_of_ne h']; exact hnv c' (by omega) hne
        · refine ⟨fun _ => ⟨d.2.2.2.2, rfl, ?_⟩, fun h' => absurd (by omega) h'⟩
          rw [← hch, Function.update_self, hval, ← hpre.1, hsq, Option.some.inj hsg]
          exact hstep
        · rw [update_self']
          refine blocks_set (hW'.congr (fun c' hc' => ?_) ?_) hrest
          · rw [Function.update_of_ne (by omega)]
          · rw [Function.update_self, hrbs]
        · rw [update_not]; exact hR
    · have hq' := bool_eq_not_of_ne hq
      subst hq'
      exact (reader_no_fire hR hbq hE hi happ hpar (by omega)).elim
  · obtain ⟨q, -, rest, rfl⟩ := hφ
    obtain ⟨rfl, -⟩ := List.cons.inj hφ'
    have := ((app_fin m n' ι N w fs).1 happ).1
    omega

end SpaceEnc

end HTN

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {m n' : ℕ}
  {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool}

/-- Finishing the word in progress: its tail is stored. -/
theorem wcur_store {p : Bool} {c : ℕ} {nv : ℕ → Γ} {a : Act Q Γ}
    {bl : List (List (Act Q Γ))} {i : ℕ}
    (hW : WCur m n' N p c nv {a :: .rv p (nv c) :: rbsL p 0 m (bitsOf c)} bl)
    (hi : bl[i]? = some (a :: .rv p (nv c) :: rbsL p 0 m (bitsOf c))) :
    WCur m n' N p (c + 1) nv 0 (bl.set i (tl m p c (nv c))) := by
  obtain ⟨Fr, h, hFr, hcard, hh, hms⟩ := hW
  refine ⟨Fr, h, hFr, by simp at hcard ⊢; omega, hh, ?_⟩
  rw [msOf_set_of_eq hi (List.cons_ne_nil _ _) hms, filter_singleton_of_ne (tl_ne_nil _ _ _ _),
    tails_range_succ, add_zero, add_assoc]

/-- **The step of phase `PI`**: the increment. -/
theorem step_PI {p : Bool} {cfg : Config Q Γ} {first : Bool} {c : ℕ} {nv : ℕ → Γ}
    {fs : FS Q Γ} {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)}
    {a : Act Q Γ} {z : List (Act Q Γ)}
    (hI : InvPI m n' ι N w p cfg first c nv fs bs φ) (hG : G bs φ (a :: z))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) :
    ∃ fs' bs', (am m n' ι N).transition a (enc m w fs) = enc m w fs' ∧ G bs' φ z ∧
      (InvP0 m n' ι N w p cfg first (c + 1) nv fs' bs' φ ∨
        InvPE m n' ι N w p cfg first nv fs' bs' φ) := by
  obtain ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, hpc, hc, hu, hnv, hst, hφ,
    ⟨incw, hinc, hB⟩, hR⟩ := hI
  have hhw : cfg.head < 2 ^ m := by
    obtain ⟨r, hr⟩ := hRun.1; exact reachesSpace_head_lt hr
  rcases g_step hG with ⟨q, E, bl, rest, i, t, hbq, hE, hi, hG'⟩ | ⟨φ', hφ', hG'⟩
  · by_cases hq : q = p
    · subst hq
      obtain ⟨hW, hrest⟩ := pickW hB (fun cur h => msOf_ne_zero_not_allEmpty h.ms_ne_zero)
        hbq hE hi (List.cons_ne_nil _ _)
      have he := writer_wip hW hi happ hpar (by omega) (by omega)
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      have hW' := wcur_store hW hi
      rcases hinc with ⟨k, hk, rfl⟩ | rfl
      · obtain ⟨-, -, -, hbk, hlow⟩ := (app_inc m n' ι N w fs).1 happ
        rw [hcnt] at hbk hlow
        have hc1 := succ_lt_of_testBit hc hk hbk hlow
        refine ⟨_, Function.update bs q (bl.set i (tl m q c (nv c)) :: rest),
          trans_inc m n' ι N w fs q k hpc hk (by rw [hcnt]; exact hbk) (by rw [hcnt]; exact hlow),
          hG', Or.inl ⟨hRun, ⟨hpar, hhd, hfirst, by simp [hcnt]⟩, rfl, rfl, hc1, hu, hnv, hst, hφ,
          fun h => by omega, fun _ => ?_, ?_⟩⟩
        · rw [update_self']
          exact blocks_set hW' hrest
        · rw [update_not]; exact hR
      · obtain ⟨-, -, hall⟩ := (app_wrap m n' ι N w fs).1 happ
        rw [hcnt] at hall
        have hcW := eq_of_all_testBit hc hall
        have hc1 : c + 1 = 2 ^ m := by have := Nat.one_le_two_pow (n := m); omega
        refine ⟨_, Function.update bs q (bl.set i (tl m q c (nv c)) :: rest),
          trans_wrap m n' ι N w fs q hpc (by rw [hcnt]; exact hall),
          hG', Or.inr ⟨hRun, ⟨hpar, hhd, hfirst, rfl⟩, rfl, rfl, hc1 ▸ hnv,
          ⟨fun _ => hst.1 (by omega), fun h => absurd trivial h⟩, hφ, ?_, ?_⟩⟩
        · rw [update_self', ← hc1]
          exact blocks_set hW' hrest
        · rw [update_not, ← hc1]; exact hR
    · have hq' := bool_eq_not_of_ne hq
      subst hq'
      exact (reader_no_fire hR hbq hE hi happ hpar (by omega)).elim
  · obtain ⟨q, -, rest, rfl⟩ := hφ
    obtain ⟨rfl, -⟩ := List.cons.inj hφ'
    have := ((app_fin m n' ι N w fs).1 happ).1
    omega

end SpaceEnc

end HTN

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {m n' : ℕ}
  {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool}

omit [Fintype Q] [DecidableEq Q] [DecidableEq Γ] in
/-- **A head move** realises the pending move `μ` of the machine, inside the space bound. -/
theorem head_move {p : Bool} {h : Act Q Γ} {fs : FS Q Γ} {μ : Move} (hh : IsHActP p h)
    (happ : (am m n' ι N).Applicable h (enc m w fs)) (hmv : fs.mv = some μ)
    (hpc : fs.pc = 2 * m + 4) (hpar : fs.par = p) (hhw : fs.hd < 2 ^ m) :
    (am m n' ι N).transition h (enc m w fs) =
        enc m w { fs with pc := 0, par := !p, mv := none, first := false, hd := μ.apply fs.hd } ∧
      μ.apply fs.hd < 2 ^ m := by
  rcases hh with ⟨k, rfl⟩ | ⟨k, rfl⟩ | rfl | rfl
  · obtain ⟨-, -, hmv', hk, hb, hlow⟩ := (app_hinc m n' ι N w fs).1 happ
    rw [hmv] at hmv'
    obtain rfl := Option.some.inj hmv'
    exact ⟨trans_hinc m n' ι N w fs p k hpc hpar hmv hk hb hlow, succ_lt_of_testBit hhw hk hb hlow⟩
  · obtain ⟨-, -, hmv', hk, hb, hlow⟩ := (app_hdec m n' ι N w fs).1 happ
    rw [hmv] at hmv'
    obtain rfl := Option.some.inj hmv'
    exact ⟨trans_hdec m n' ι N w fs p k hpc hpar hmv hk hb hlow,
      lt_of_le_of_lt (Nat.sub_le _ _) hhw⟩
  · obtain ⟨-, -, hmv', hall⟩ := (app_hdec0 m n' ι N w fs).1 happ
    rw [hmv] at hmv'
    obtain rfl := Option.some.inj hmv'
    have h0 : fs.hd = 0 := eq_zero_of_all_testBit hhw hall
    refine ⟨?_, by simp [Move.apply, h0]⟩
    rw [trans_hdec0 m n' ι N w fs p hpc hpar hmv]
    simp [Move.apply, h0]
  · obtain ⟨-, -, hmv'⟩ := (app_hstay m n' ι N w fs).1 happ
    rw [hmv] at hmv'
    obtain rfl := Option.some.inj hmv'
    exact ⟨trans_hstay m n' ι N w fs p hpc hpar hmv, hhw⟩

/-- **The step of phase `PE`**: the head move, one step of the machine; the next round begins
with the loops exchanged. -/
theorem step_PE {p : Bool} {cfg : Config Q Γ} {first : Bool} {nv : ℕ → Γ}
    {fs : FS Q Γ} {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)}
    {a : Act Q Γ} {z : List (Act Q Γ)}
    (hI : InvPE m n' ι N w p cfg first nv fs bs φ) (hG : G bs φ (a :: z))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) :
    ∃ fs' bs' cfg', (am m n' ι N).transition a (enc m w fs) = enc m w fs' ∧ G bs' φ z ∧
      InvP0 m n' ι N w (!p) cfg' false 0 cfg'.tape fs' bs' φ := by
  obtain ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, hpc, heqv, hnv, hst, hφ, hB, hR⟩ := hI
  obtain ⟨r, hr⟩ := hRun.1
  have hhw : cfg.head < 2 ^ m := reachesSpace_head_lt hr
  obtain ⟨μ, hmv, hstep⟩ := hst.1 trivial
  rcases g_step hG with ⟨q, E, bl, rest, i, t, hbq, hE, hi, hG'⟩ | ⟨φ', hφ', hG'⟩
  · by_cases hq : q = p
    · subst hq
      obtain ⟨⟨Fr, h, hFr, hcard, hh, hms⟩, hrest⟩ := pickW hB
        (fun cur h => msOf_ne_zero_not_allEmpty h.ms_ne_zero) hbq hE hi (List.cons_ne_nil _ _)
      have hv := mem_msOf_of_get hi (List.cons_ne_nil _ _)
      rw [hms] at hv
      rcases writer_word hh hv happ hpar with ⟨h1, -⟩ | ⟨-, rfl, rfl⟩ | hX
      · omega
      · obtain ⟨htr, hlt⟩ := head_move hh happ hmv hpc hpar (hhd ▸ hhw)
        have hFr0 : Fr = 0 :=
          Multiset.card_eq_zero.1 (by simp only [Multiset.card_zero, add_zero] at hcard; omega)
        subst hFr0
        let cfg' : Config Q Γ :=
          ⟨fs.st, μ.apply cfg.head, Function.update cfg.tape cfg.head (nv cfg.head)⟩
        have hstep' : N.Step cfg cfg' := ⟨fs.st, nv cfg.head, μ, hstep, rfl⟩
        refine ⟨_, Function.update bs q (bl.set i [] :: rest), cfg', htr, hG',
          ⟨⟨r + 1, reachesSpace_snoc hr hstep' (by simpa [cfg', hhd] using hlt)⟩,
            fun h => by simp at h⟩, ⟨rfl, by simp [cfg', hhd], rfl, hcnt⟩, rfl, heqv,
          Nat.two_pow_pos m, fun h => by simp at h, fun c' hc' => by omega,
          ⟨fun h' => by omega, fun _ => ⟨rfl, rfl⟩⟩, hφ, fun _ => ?_, fun h' => by omega,
          fun h' => by simp at h', fun _ => ?_⟩
        · rw [update_not]
          cases first
          · obtain ⟨E', cur, F, h1, hE', hms', hF⟩ := hR.2 rfl
            have hA : AllEmpty cur := by
              rw [allEmpty_iff_msOf, hms', Nat.sub_self]; rfl
            exact ⟨E' ++ [cur], F, by simp [h1], allE_append hE' (by simpa [AllE] using hA), hF⟩
          · exact ⟨[], bs (!q), rfl, by simp [AllE], hR.1 rfl⟩
        · rw [Bool.not_not, update_self']
          refine blocks_set ?_ hrest
          rw [msOf_set hi (List.cons_ne_nil _ _), hms, filter_singleton_nil, add_zero, add_zero,
            Multiset.map_zero, zero_add, Multiset.singleton_add, Multiset.erase_cons_head,
            Nat.sub_zero, ← List.range_eq_range']
          refine tails_congr fun c' hc' => ?_
          rw [List.mem_range] at hc'
          by_cases h' : c' = cfg.head
          · subst h'; simp [cfg']
          · simp only [cfg', Function.update_of_ne h']
            exact hnv c' hc' h'
      · simp at hX
    · have hq' := bool_eq_not_of_ne hq
      subst hq'
      exact (reader_no_fire hR hbq hE hi happ hpar (by omega)).elim
  · obtain ⟨q, -, rest, rfl⟩ := hφ
    obtain ⟨rfl, -⟩ := List.cons.inj hφ'
    have := ((app_fin m n' ι N w fs).1 happ).1
    omega

end SpaceEnc

end HTN
