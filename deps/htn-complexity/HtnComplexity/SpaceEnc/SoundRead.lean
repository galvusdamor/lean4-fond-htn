import HtnComplexity.SpaceEnc.SoundP0
/-!
# Soundness of the encoding: reading a symbol

* `HTN.SpaceEnc.step_PWm` — at program counter `m + 1` the symbol of position `c` is read: in
  round `0` from the input (`ri`, `rblank`, phase `PC` next), later by starting to read a stored
  tail of the other loop (`rv`, phase `PR 0` next);
* `HTN.SpaceEnc.step_PR` — the address checks `rb` of the tail being read;
* `HTN.SpaceEnc.invPC_of_invPR` — once all `m` checks are done, the tail read is the one of
  position `c`.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {m n' : ℕ}
  {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool}

theorem update_not' {α : Type*} (bs : Bool → α) (q : Bool) (x : α) :
    Function.update bs (!q) x q = bs q :=
  Function.update_of_ne (by cases q <;> simp) x bs

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] in
theorem erase_add_add_singleton {α : Type*} [DecidableEq α] {s F : Multiset α} {x : α}
    (hx : x ∈ s) : s.erase x + F + {x} = s + F := by
  rw [add_right_comm, add_comm (s.erase x) {x}, Multiset.singleton_add, Multiset.cons_erase hx]

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] in
theorem erase_add_singleton_of {α : Type*} [DecidableEq α] {s T : Multiset α} {x v : α}
    (hv : v ∈ s) (h : s + {x} = T + {v}) : s.erase v + {x} = T := by
  have h1 : s.erase v + {x} = (s + {x}).erase v := (Multiset.erase_add_left_pos _ hv).symm
  rw [h1, h, add_comm, Multiset.singleton_add, Multiset.erase_cons_head]

omit [DecidableEq Q] [DecidableEq Γ] in
theorem core_pc {p : Bool} {cd : CD Q Γ} {fs : FS Q Γ} (hv : ValidCD m n' N p cd)
    (happ : (am m n' ι N).Applicable cd.core (enc m w fs)) : fs.pc = 2 * m + 2 := by
  rcases hv.2.1 with ⟨g, hg, -⟩ | ⟨d, -, hd, -⟩
  · rw [hg] at happ; exact pc_of_app happ
  · rw [hd] at happ; exact pc_of_app happ

/-- **The step of phase `PW m`**: reading the symbol of position `c`. -/
theorem step_PWm (hn' : n' = w.length) {p : Bool} {cfg : Config Q Γ} {first : Bool} {c : ℕ}
    {nv : ℕ → Γ} {fs : FS Q Γ} {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)}
    {a : Act Q Γ} {z : List (Act Q Γ)}
    (hI : InvPW m n' ι N w p cfg first c m nv fs bs φ) (hG : G bs φ (a :: z))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) :
    ∃ fs' bs', (am m n' ι N).transition a (enc m w fs) = enc m w fs' ∧ G bs' φ z ∧
      ((first = false ∧ InvPR m n' ι N w p cfg c 0 nv fs' bs' φ) ∨
        InvPC m n' ι N w p cfg first c nv fs' bs' φ) := by
  obtain ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, hpc, -, hc, hu, hnv, hst, hφ, heqv,
    ⟨cd, ⟨hvalid, hcd⟩, hB⟩, hR⟩ := hI
  rcases g_step hG with ⟨q, E, bl, rest, i, t, hbq, hE, hi, hG'⟩ | ⟨φ', hφ', hG'⟩
  · by_cases hq : q = p
    · subst hq
      obtain ⟨hW, hrest⟩ := pickW hB (fun cur h => msOf_ne_zero_not_allEmpty h.ms_ne_zero)
        hbq hE hi (List.cons_ne_nil _ _)
      have he := writer_wip hW hi happ hpar (by omega) (by omega)
      rw [wipW_self] at he
      have hxc : ∀ i < m, cd.x i = c.testBit i := fun i hi => (hcd i hi).1
      rcases hvalid.1 with h0 | ⟨hqt, h0 | ⟨i', b', -, h0⟩⟩
      · rw [h0, List.nil_append] at he
        obtain ⟨rfl, -⟩ := List.cons.inj he
        have := core_pc hvalid happ
        omega
      · rw [h0] at he
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨-, hf, hu'⟩ := (app_rblank m n' ι N w fs).1 happ
        rw [hfirst] at hf
        subst hf hqt
        obtain ⟨hcfg, -⟩ := hRun.2 rfl
        have hu0 := hu rfl
        have hcn : n' ≤ c := by omega
        refine ⟨_, Function.update bs true (bl.set i _ :: rest), trans_rblank m n' ι N w fs hpc,
          hG', Or.inr ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, rfl, hc, fun _ => by simp; omega, hnv, hst,
          hφ, ?_, heqv, ⟨cd, [], hvalid, hxc, Or.inl rfl, ?_⟩, ⟨by rw [update_not]; exact hR.1, fun h => by simp at h⟩⟩⟩
        · rw [hcfg]
          simp [NTM.initConfig, List.getD_eq_getElem?_getD, hn' ▸ hcn]
        · rw [update_self']
          refine blocks_set (wcur_adv hW (by rw [wipW_self, h0]; exact hi)
            (wipW_ne_nil _ _ _ _) (by simp)) hrest
      · rw [h0] at he
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨-, hf, hui, hiw, hb⟩ := (app_ri m n' ι N w fs).1 happ
        rw [hfirst] at hf
        subst hf hqt
        obtain ⟨hcfg, -⟩ := hRun.2 rfl
        have hu0 := hu rfl
        have hci : c = i' := by omega
        subst hci
        refine ⟨_, Function.update bs true (bl.set i _ :: rest), trans_ri m n' ι N w fs c b' hpc hui,
          hG', Or.inr ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, rfl, hc, fun _ => by simp; omega, hnv, hst,
          hφ, ?_, heqv, ⟨cd, [], hvalid, hxc, Or.inl rfl, ?_⟩, ⟨by rw [update_not]; exact hR.1, fun h => by simp at h⟩⟩⟩
        · rw [hcfg, hb]
          simp [NTM.initConfig, List.getD_eq_getElem?_getD, hiw]
        · rw [update_self']
          refine blocks_set (wcur_adv hW (by rw [wipW_self, h0]; exact hi)
            (wipW_ne_nil _ _ _ _) (by simp)) hrest
    · have hq' := bool_eq_not_of_ne hq
      subst hq'
      obtain ⟨hf, -, hms, hrest, c', hcc', hc', rfl, rfl⟩ := reader_fire hR hbq hE hi happ hpar
      subst hf
      have hmem : tl m (!p) c' (cfg.tape c') ∈ msOf bl := by
        rw [← tl_eq] at hi
        exact mem_msOf_of_get hi (tl_ne_nil _ _ _ _)
      refine ⟨_, Function.update bs (!p) (bl.set i (rbsL (!p) 0 m (bitsOf c')) :: rest),
        trans_rv m n' ι N w fs (!p) _ hpc, hG', Or.inl ⟨rfl, hRun, ⟨hpar, hhd, hfirst, hcnt⟩,
        by simp, Nat.zero_le _, hc, hnv, hst, hφ, heqv, ⟨cd, ⟨hvalid, hcd⟩, ?_⟩,
        c', hcc', hc', fun i h1 h2 => by omega, rfl, ?_⟩⟩
      · rw [update_not']
        exact hB
      · rw [update_self']
        refine blocks_set ?_ hrest
        have hne : ((Act.rv (!p) (cfg.tape c') : Act Q Γ) :: rbsL (!p) 0 m (bitsOf c')) ≠ [] :=
          List.cons_ne_nil _ _
        rw [msOf_set hi hne, ← tl_eq, Nat.sub_zero, erase_add_add_singleton hmem, hms]
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

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The word in progress after all address checks fires only at the program counters `m + 1`
(input read) and `2m + 2` (core action). -/
theorem wip_m_pc {p : Bool} {cd : CD Q Γ} {a : Act Q Γ} {t : List (Act Q Γ)} {fs : FS Q Γ}
    (hv : ValidCD m n' N p cd) (he : a :: t = wipW m p m cd)
    (happ : (am m n' ι N).Applicable a (enc m w fs)) : fs.pc = m + 1 ∨ fs.pc = 2 * m + 2 := by
  rw [wipW_self] at he
  rcases hv.1 with h0 | ⟨-, h0 | ⟨i', b', -, h0⟩⟩
  · rw [h0, List.nil_append] at he
    obtain ⟨rfl, -⟩ := List.cons.inj he
    exact Or.inr (core_pc hv happ)
  · rw [h0] at he
    obtain ⟨rfl, -⟩ := List.cons.inj he
    exact Or.inl (pc_of_app happ)
  · rw [h0] at he
    obtain ⟨rfl, -⟩ := List.cons.inj he
    exact Or.inl (pc_of_app happ)

omit [DecidableEq Q] [DecidableEq Γ] in
theorem Blocks.mono {q : Bool} {bsq : List (List (List (Act Q Γ)))}
    {P P' : List (List (Act Q Γ)) → Prop} (hB : Blocks m n' N q bsq P)
    (h : ∀ cur, P cur → P' cur) : Blocks m n' N q bsq P' := by
  obtain ⟨E, cur, F, h1, h2, h3, h4⟩ := hB
  exact ⟨E, cur, F, h1, h2, h cur h3, h4⟩

/-- **The step of phase `PR j`, `j < m`**: an address check `rb` of the tail being read. -/
theorem step_PR {p : Bool} {cfg : Config Q Γ} {c j : ℕ} {nv : ℕ → Γ} {fs : FS Q Γ}
    {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)} {a : Act Q Γ}
    {z : List (Act Q Γ)} (hj : j < m)
    (hI : InvPR m n' ι N w p cfg c j nv fs bs φ) (hG : G bs φ (a :: z))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) :
    ∃ fs' bs', (am m n' ι N).transition a (enc m w fs) = enc m w fs' ∧ G bs' φ z ∧
      InvPR m n' ι N w p cfg c (j + 1) nv fs' bs' φ := by
  obtain ⟨hRun, ⟨hpar, hhd, hfirst, hcnt⟩, hpc, -, hc, hnv, hst, hφ, heqv, ⟨cd, hcd, hB⟩,
    c', hcc', hc', hbits, hsym, hBR⟩ := hI
  rcases g_step hG with ⟨q, E, bl, rest, i, t, hbq, hE, hi, hG'⟩ | ⟨φ', hφ', hG'⟩
  · by_cases hq : q = p
    · subst hq
      obtain ⟨hW, -⟩ := pickW hB (fun cur h => msOf_ne_zero_not_allEmpty h.ms_ne_zero)
        hbq hE hi (List.cons_ne_nil _ _)
      have he := writer_wip hW hi happ hpar (by omega) (by omega)
      have := wip_m_pc hcd.1 he happ
      omega
    · have hq' := bool_eq_not_of_ne hq
      subst hq'
      have hne : fs.par ≠ !p := by rw [hpar]; cases p <;> simp
      obtain ⟨hP, hrest⟩ := pickR hBR hbq hE hi happ hne
      have hv := mem_msOf_of_get hi (List.cons_ne_nil _ _)
      have hv' : a :: t ∈ tails m (!p) cfg.tape (List.range' c (2 ^ m - c)) +
          Multiset.filter (· ≠ []) {rbsL (!p) 0 (m - j) (bitsOf c')} := by
        rw [← hP]; exact Multiset.mem_add.2 (Or.inl hv)
      rcases Multiset.mem_add.1 hv' with ht | ht
      · obtain ⟨c'', -, he⟩ := mem_tails ht
        rw [tl_eq] at he
        obtain ⟨rfl, -⟩ := List.cons.inj he
        have := pc_of_app happ
        simp only [pcNeed] at this
        omega
      · have ht' := (Multiset.mem_filter.1 ht).1
        rw [Multiset.mem_singleton, show m - j = (m - j - 1) + 1 by omega,
          rbsL_zero_succ] at ht'
        obtain ⟨rfl, rfl⟩ := List.cons.inj ht'
        obtain ⟨-, -, hx⟩ := (app_rb m n' ι N w fs).1 happ
        rw [hcnt] at hx
        refine ⟨_, Function.update bs (!p) (bl.set i (rbsL (!p) 0 (m - j - 1) (bitsOf c')) :: rest),
          trans_rb m n' ι N w fs (!p) (m - j - 1) _ (by omega) (by omega), hG', hRun,
          ⟨hpar, hhd, hfirst, hcnt⟩, by simp only; omega, hj, hc, hnv, hst, hφ, heqv,
          ⟨cd, hcd, by rw [update_not']; exact hB⟩, c', hcc', hc', ?_, hsym, ?_⟩
        · intro i' h1 h2
          by_cases h3 : i' = m - j - 1
          · subst h3; exact hx
          · exact hbits i' (by omega) h2
        · rw [update_self']
          refine blocks_set ?_ hrest
          have hne' : (Act.rb (!p) (m - j - 1) (bitsOf c' (m - j - 1)) ::
              rbsL (!p) 0 (m - j - 1) (bitsOf c') : List (Act Q Γ)) ≠ [] := List.cons_ne_nil _ _
          have hpart : (rbsL (!p) 0 (m - j) (bitsOf c') : List (Act Q Γ)) =
              .rb (!p) (m - j - 1) (bitsOf c' (m - j - 1)) :: rbsL (!p) 0 (m - j - 1) (bitsOf c') := by
            have h' : m - j = (m - j - 1) + 1 := by omega
            conv_lhs => rw [h']
            exact rbsL_zero_succ _ _ _
          rw [msOf_set hi hne', add_right_comm, erase_add_singleton_of hv
            (by rw [hP, hpart, filter_singleton_of_ne hne']), show m - (j + 1) = m - j - 1 by omega]
  · obtain ⟨q, -, rest, rfl⟩ := hφ
    obtain ⟨rfl, -⟩ := List.cons.inj hφ'
    have := ((app_fin m n' ι N w fs).1 happ).1
    omega

omit [DecidableEq Q] [DecidableEq Γ] in
/-- **The end of phase `PR`**: after all `m` address checks the tail read is the one of
position `c`, and phase `PC` begins. -/
theorem invPC_of_invPR {p : Bool} {cfg : Config Q Γ} {c : ℕ} {nv : ℕ → Γ} {fs : FS Q Γ}
    {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)}
    (hI : InvPR m n' ι N w p cfg c m nv fs bs φ) :
    InvPC m n' ι N w p cfg false c nv fs bs φ := by
  obtain ⟨hRun, hfs, hpc, -, hc, hnv, hst, hφ, heqv, ⟨cd, hcd, hB⟩,
    c', hcc', hc', hbits, hsym, hBR⟩ := hI
  have hcc : c' = c := eq_of_testBit_lt hc' hc fun i hi => hbits i (by omega) hi
  subst hcc
  refine ⟨hRun, hfs, by omega, hc, fun h => by simp at h, hnv, hst, hφ, hsym, heqv,
    ⟨cd, cd.rd, hcd.1, fun i hi => (hcd.2 i hi).1, ?_, ?_⟩, fun h => by simp at h, fun _ => ?_⟩
  · rcases hcd.1.1 with h0 | ⟨-, h0 | ⟨i', b', -, h0⟩⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr ⟨i', b', h0⟩)
  · refine hB.mono fun cur h => ?_
    rwa [wipW_self, show cd.rd ++ cd.core :: cd.incw :: .rv p cd.val :: rbsL p 0 m cd.x =
      cd.rd ++ [cd.core, cd.incw, .rv p cd.val] ++ rbsL p 0 m cd.x by simp] at h
  · refine hBR.mono fun cur h => ?_
    rw [Nat.sub_self, rbsL_zero_zero, filter_singleton_nil, add_zero,
      tails_range'_cons m (!p) cfg.tape hc', add_comm] at h
    exact add_left_cancel h

end SpaceEnc

end HTN
