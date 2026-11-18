import FondHtn.TOHard2.Sound
/-!
# Soundness of the claims

**`FOND.TOHard2.sound`**: if the policy wins the claim `K a` from a shaped state with
postcondition `Ψ`, then `Ψ` is covered and every pinning `tg, ig` of `Ψ` gives
`tabC (ofB tg D) (ofB ig D) = a` (`D = 2 ^ b`).  Induction on the height of the list game.

* `FOND.TOHard2.step_mode` — one challenge: the claim of the predecessor and the arithmetic of
  the committed digit types (`run_inc`, `run_cpy`, `run_dec`);
* the steps (middle rule, cell `0`, last cell) and the first row (prefix, cells holding `1`,
  blank cells).
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

/-- **The meaning of a won claim.** -/
def SoundC (P : Par) (tabC : ℕ → ℕ → ℕ) (a : ℕ) (Ψ : Set Cfg) : Prop :=
  Cover P Ψ ∧ ∀ tg ig, Pin P Ψ tg ig → tabC (ofB tg (2 ^ P.b)) (ofB ig (2 ^ P.b)) = a

theorem shaped_modeSt {s : St} (hs : Shaped s) (l c r : Bool) : Shaped (modeSt s l c r) := hs

theorem cover_mono {P : Par} {Ψ Ψ' : Set Cfg} (h : Cover P Ψ) (hΨ : Ψ ⊆ Ψ') : Cover P Ψ' :=
  fun k hk => let ⟨s, hs, hk', h⟩ := h k hk; ⟨s, hs, hk', hΨ h⟩

theorem pin_mono {P : Par} {Ψ Ψ' : Set Cfg} {tg ig : ℕ → Bool} (h : Pin P Ψ' tg ig) (hΨ : Ψ ⊆ Ψ') :
    Pin P Ψ tg ig := fun s hs h' => h s hs (hΨ h')

section Sound

variable {P : Par} {d : TabData} {tabC : ℕ → ℕ → ℕ} (H : Hyp P d tabC)
include H

theorem Hyp.two_le : 2 ≤ P.cs.length := by have := H.csl; omega

/-- The induction hypothesis of the soundness proof. -/
def IHs (P : Par) (tabC : ℕ → ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ n' < n, ∀ a (s : St) (Ψ : Set Cfg), Shaped s → LGH (gram P) n' [(true, KN a)] s.cfg Ψ →
    SoundC P tabC a Ψ

/-- **One challenge**: the predecessor claim and the arithmetic of the digit types. -/
theorem step_mode {n : ℕ} (ih : IHs P tabC n) {m x : ℕ} (hm3 : m < 3)
    {postP : List (ℕ × List ASpec)} (hpost : ∀ q ∈ postP, q ∈ (gram P).insL) {s : St} (hs : Shaped s)
    {Ψ : Set Cfg} (h : LGH (gram P) n (modeBody m x ++ syms postP) s.cfg Ψ) :
    s.val (4 + m) = true ∧ Cover P (wpP (inss postP) Ψ) ∧
      ∀ tg ig, Pin P (wpP (inss postP) Ψ) tg ig → ∃ t' i', ofB tg (2 ^ P.b) = t' + 1 ∧
        (m = 0 → ofB ig (2 ^ P.b) = i' + 1) ∧ (m = 1 → ofB ig (2 ^ P.b) = i') ∧
        (m = 2 → ofB ig (2 ^ P.b) + 1 = i') ∧ i' < 2 ^ 2 ^ P.b ∧ tabC t' i' = x := by
  obtain ⟨hv, n', hn', asT, asI, hT, hI, h⟩ := mode_step P H.two_le hm3 hpost h
  obtain ⟨hcov, hsnd⟩ := ih n' hn' x s _ hs h
  have hΨ' : ∀ s', Shaped s' → s'.cfg ∈ {c | c ∈ wpP (inss (chain P.b P.cs asI ++ chain P.b P.cs asT ++
      postP)) Ψ} → s'.cfg ∈ wpP (inss (chain P.b P.cs asI ++ chain P.b P.cs asT)) (wpP (inss postP) Ψ) := by
    intro s' _ h'
    simpa only [inss_append, wpP_append] using h'
  obtain ⟨hcov', hl₁, hl₂, htr⟩ := transfer H.cs (run_reg hT) (by
      have := run_reg hI
      intro a ha; rcases this a ha with h | h
      · exact Or.inl h
      · right; rw [h]; unfold modeI; split_ifs <;> rfl) hΨ' hcov
  refine ⟨hv, hcov', fun tg ig hpin => ?_⟩
  obtain ⟨tg', ig', hpin', hrT, hrI⟩ := htr tg ig hpin
  have hx := hsnd tg' ig' hpin'
  have hT' := run_inc hT hrT
  simp only [one_ne_zero, if_false, add_zero, hl₁] at hT'
  refine ⟨ofB tg' (2 ^ P.b), ofB ig' (2 ^ P.b), hT'.2, ?_, ?_, ?_, ofB_lt _ _, hx⟩
  · rintro rfl
    have := run_inc (rg := false) (by simpa [modeI] using hI) hrI
    simp only [Comp.aut, one_ne_zero, if_false, add_zero, hl₂] at this
    exact this.2
  · rintro rfl
    have := run_cpy (by simpa [modeI] using hI) hrI
    exact ofB_congr fun r hr => this r (by omega)
  · rintro rfl
    have := run_dec (rg := false) (by simpa [modeI] using hI) hrI
    simp only [Comp.aut, one_ne_zero, if_false, add_zero, hl₂] at this
    exact this.2.symm

omit H in
/-- The mode fields after a pick. -/
theorem val_modeSt (s : St) (l c r : Bool) :
    (modeSt s l c r).val 4 = l ∧ (modeSt s l c r).val 5 = c ∧ (modeSt s l c r).val 6 = r :=
  ⟨rfl, rfl, rfl⟩

omit H in
/-- The body chosen for a challenge nonterminal. -/
theorem sub_body {k j n : ℕ} {s : St} {Ψ : Set Cfg} (h : LGH (gram P) (n + 1) [(true, subN k j)] s.cfg Ψ) :
    ∃ bs, (subN k j, bs) ∈ meths P ∧ LGH (gram P) n bs s.cfg Ψ := by
  obtain ⟨bs, hb, h⟩ := lgh_comp_iff.1 h
  rw [gram_methL] at hb
  exact ⟨bs, hb, by simpa using h⟩

end Sound

/-! ## Reached states -/

theorem pin_of {P : Par} {Ψ : Set Cfg} {R : ℕ → St → Prop}
    (h : ∀ k < 2 ^ P.b, ∃ s, Shaped s ∧ s.chkV P.b = k ∧ s.cfg ∈ Ψ ∧ R k s) :
    Cover P Ψ ∧ ∀ tg ig, Pin P Ψ tg ig → ∀ k < 2 ^ P.b, ∃ s, R k s ∧ s.tb = tg k ∧ s.ib = ig k := by
  refine ⟨fun k hk => let ⟨s, hs, hk', h, _⟩ := h k hk; ⟨s, hs, hk', h⟩, fun tg ig hpin k hk => ?_⟩
  obtain ⟨s, hs, hk', h, hR⟩ := h k hk
  obtain ⟨e1, e2⟩ := hpin s hs h
  rw [hk'] at e1 e2
  exact ⟨s, hR, e1, e2⟩

theorem ofB_eq_zero {g : ℕ → Bool} {n : ℕ} (h : ∀ k < n, g k = false) : ofB g n = 0 := by
  rw [ofB_congr (g' := fun _ => false) h, ofB_false]

theorem chkV_pick_testBit (P : Par) (s : St) {k : ℕ} (hk : k < 2 ^ P.b) :
    ({ s with chk := fun r => if r < P.b then k.testBit r else s.chk r } : St).chkV P.b = k := by
  rw [chkV_pick, ofB_testBit hk]

theorem ofB_pick_testBit (P : Par) (g : ℕ → Bool) {k : ℕ} (hk : k < 2 ^ P.b) :
    ofB (fun r => if r < P.b then k.testBit r else g r) P.b = k := by
  rw [ofB_congr (g' := k.testBit) (fun r hr => by simp [hr]), ofB_testBit hk]

section Sound2

variable {P : Par} {d : TabData} {tabC : ℕ → ℕ → ℕ} (H : Hyp P d tabC)
include H

/-- A challenge: the body chosen for the challenge nonterminal is the one of the picked mode. -/
theorem pick_mode {N : ℕ} (ih : IHs P tabC (N + 1)) {k j mm : ℕ} {X : ℕ → ℕ}
    {postP : List (ℕ × List ASpec)} (hpost : ∀ q ∈ postP, q ∈ (gram P).insL) {s : St} (hs : Shaped s)
    (hbodies : ∀ bs, (subN k j, bs) ∈ meths P → ∃ mm' < 3, bs = modeBody mm' (X mm') ++ syms postP ∧
      (s.val (4 + mm') = true → mm' = mm))
    {Ψ : Set Cfg} (h : LGH (gram P) N [(true, subN k j)] s.cfg Ψ) :
    Cover P (wpP (inss postP) Ψ) ∧
      ∀ tg ig, Pin P (wpP (inss postP) Ψ) tg ig → ∃ t' i', ofB tg (2 ^ P.b) = t' + 1 ∧
        (mm = 0 → ofB ig (2 ^ P.b) = i' + 1) ∧ (mm = 1 → ofB ig (2 ^ P.b) = i') ∧
        (mm = 2 → ofB ig (2 ^ P.b) + 1 = i') ∧ i' < 2 ^ 2 ^ P.b ∧ tabC t' i' = X mm := by
  rcases N with _ | N
  · exact absurd h not_lgh_zero
  obtain ⟨bs, hb, h⟩ := sub_body h
  obtain ⟨mm', hmm', rfl, honly⟩ := hbodies bs hb
  obtain ⟨hv, hcov, hres⟩ := step_mode H (fun n' hn' => ih n' (by omega)) hmm' hpost hs h
  obtain rfl := honly hv
  exact ⟨hcov, hres⟩

/-- Post-assertion of the cell digit. -/
theorem post_IB {β : Bool} {Ψ : Set Cfg} (hcov : Cover P (wpP (inss [assertIBI β]) Ψ)) :
    Cover P Ψ ∧ ∀ tg ig, Pin P Ψ tg ig →
      Pin P (wpP (inss [assertIBI β]) Ψ) tg ig ∧ ∀ k < 2 ^ P.b, ig k = β := by
  have hmem : ∀ s : St, s.cfg ∈ wpP (inss [assertIBI β]) Ψ → s.ib = β ∧ s.cfg ∈ Ψ := by
    intro s h
    simpa only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_assertIB] using h
  refine ⟨fun k hk => ?_, fun tg ig hpin => ⟨fun s hs h => hpin s hs (hmem s h).2, fun k hk => ?_⟩⟩
  · obtain ⟨s, hs, hk', h⟩ := hcov k hk
    exact ⟨s, hs, hk', (hmem s h).2⟩
  · obtain ⟨s, hs, hk', h⟩ := hcov k hk
    obtain ⟨e1, e2⟩ := hmem s h
    have := (hpin s hs e2).2
    rw [hk'] at this
    rw [← this, e1]

/-- **The middle rule.** -/
theorem sound_mid {N : ℕ} (ih : IHs P tabC (N + 2)) {a j : ℕ} (hj : j < P.mid.length)
    (ha : (P.mid.getI j).1 = a) {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    (h : LGH (gram P) (N + 1) [(false, pick3I.1), (true, subN 0 j)] s.cfg Ψ) : SoundC P tabC a Ψ := by
  set q := P.mid.getI j with hq
  have h1 := (lgh_ins_iff (I := pick3I.2) (gram_good P).nodup (insRaw_mem_of_mem P (q := pick3I) (by simp))).1 h
  rw [wp_pick3] at h1
  obtain ⟨hL, hC, hR⟩ := h1
  let X : ℕ → ℕ := fun mm => if mm = 0 then q.2.1 else if mm = 1 then q.2.2.1 else q.2.2.2
  have hb : ∀ (l c r : Bool) (mm : ℕ), (∀ mm' < 3, (modeSt s l c r).val (4 + mm') = true → mm' = mm) →
      ∀ bs, (subN 0 j, bs) ∈ meths P → ∃ mm' < 3, bs = modeBody mm' (X mm') ++ syms [] ∧
        ((modeSt s l c r).val (4 + mm') = true → mm' = mm) := by
    intro l c r mm honly bs hbs
    rcases meth_sub P hbs with ⟨-, -, rfl | rfl | rfl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact ⟨0, by norm_num, by simp [X, hq], honly 0 (by norm_num)⟩
    · exact ⟨1, by norm_num, by simp [X, hq], honly 1 (by norm_num)⟩
    · exact ⟨2, by norm_num, by simp [X, hq], honly 2 (by norm_num)⟩
    · omega
    · omega
  have ih' : IHs P tabC (N + 1) := fun n' hn' => ih n' (by omega)
  have rL := pick_mode H ih' (mm := 0) (postP := []) (by simp) (shaped_modeSt hs _ _ _)
    (hb true false false 0 (by intro mm' hmm' hv; interval_cases mm' <;> first | rfl | (simp [modeSt, St.val] at hv))) hL
  have rC := pick_mode H ih' (mm := 1) (postP := []) (by simp) (shaped_modeSt hs _ _ _)
    (hb false true false 1 (by intro mm' hmm' hv; interval_cases mm' <;> first | rfl | (simp [modeSt, St.val] at hv))) hC
  have rR := pick_mode H ih' (mm := 2) (postP := []) (by simp) (shaped_modeSt hs _ _ _)
    (hb false false true 2 (by intro mm' hmm' hv; interval_cases mm' <;> first | rfl | (simp [modeSt, St.val] at hv))) hR
  refine ⟨rL.1, fun tg ig hpin => ?_⟩
  obtain ⟨tL, iL, eL1, eL2, -, -, -, hxL⟩ := rL.2 tg ig hpin
  obtain ⟨tC, iC, eC1, -, eC2, -, -, hxC⟩ := rC.2 tg ig hpin
  obtain ⟨tR, iR, eR1, -, -, eR2, hiR, hxR⟩ := rR.2 tg ig hpin
  specialize eL2 rfl; specialize eC2 rfl; specialize eR2 rfl
  simp only [X, if_pos rfl, if_neg (show (1 : ℕ) ≠ 0 by norm_num),
    if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_neg (show (2 : ℕ) ≠ 1 by norm_num)] at hxL hxC hxR
  have hqm : q ∈ d.mid := by
    rw [← H.mid, hq, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hB := H.hB
  have := H.good.mid_s q hqm tC (ofB ig (2 ^ P.b)) (by omega) (by rw [hB]; omega)
    (by rw [show ofB ig (2 ^ P.b) - 1 = iL by omega, show tC = tL by omega]; exact hxL)
    (by rw [eC2]; exact hxC)
    (by rw [eR2, show tC = tR by omega]; exact hxR)
  rw [eC1, this, ← ha]

/-- **Cell `0`.** -/
theorem sound_lft {N : ℕ} (ih : IHs P tabC (N + 2)) {a j : ℕ} (hj : j < P.lft.length)
    (ha : (P.lft.getI j).1 = a) {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    (h : LGH (gram P) (N + 1) [(false, pickCRI.1), (true, subN 1 j)] s.cfg Ψ) : SoundC P tabC a Ψ := by
  set q := P.lft.getI j with hq
  have h1 := (lgh_ins_iff (I := pickCRI.2) (gram_good P).nodup (insRaw_mem_of_mem P (q := pickCRI) (by simp))).1 h
  rw [wp_pickCR] at h1
  obtain ⟨hC, hR⟩ := h1
  let X : ℕ → ℕ := fun mm => if mm = 1 then q.2.1 else q.2.2
  have hpost : ∀ q ∈ [assertIBI false], q ∈ (gram P).insL := by
    intro q hq; exact insRaw_mem_of_mem P (by simp at hq; subst hq; simp)
  have hb : ∀ (l c r : Bool) (mm : ℕ), (∀ mm' < 3, mm' ≠ 0 → (modeSt s l c r).val (4 + mm') = true → mm' = mm) →
      ∀ bs, (subN 1 j, bs) ∈ meths P → ∃ mm' < 3, bs = modeBody mm' (X mm') ++ syms [assertIBI false] ∧
        ((modeSt s l c r).val (4 + mm') = true → mm' = mm) := by
    intro l c r mm honly bs hbs
    rcases meth_sub P hbs with ⟨h0, -⟩ | ⟨-, -, rfl | rfl⟩ | ⟨h0, -⟩
    · omega
    · exact ⟨1, by norm_num, by simp [X, hq], honly 1 (by norm_num) (by norm_num)⟩
    · exact ⟨2, by norm_num, by simp [X, hq], honly 2 (by norm_num) (by norm_num)⟩
    · omega
  have ih' : IHs P tabC (N + 1) := fun n' hn' => ih n' (by omega)
  have rC := pick_mode H ih' (mm := 1) hpost (shaped_modeSt hs _ _ _)
    (hb s.ml true false 1 (by intro mm' hmm' h0 hv; interval_cases mm' <;> first | rfl | omega | (simp [modeSt, St.val] at hv))) hC
  have rR := pick_mode H ih' (mm := 2) hpost (shaped_modeSt hs _ _ _)
    (hb s.ml false true 2 (by intro mm' hmm' h0 hv; interval_cases mm' <;> first | rfl | omega | (simp [modeSt, St.val] at hv))) hR
  obtain ⟨hcov, hpost'⟩ := post_IB H rC.1
  refine ⟨hcov, fun tg ig hpin => ?_⟩
  obtain ⟨hpin', hz⟩ := hpost' tg ig hpin
  have hi0 : ofB ig (2 ^ P.b) = 0 := ofB_eq_zero hz
  obtain ⟨tC, iC, eC1, -, eC2, -, -, hxC⟩ := rC.2 tg ig hpin'
  obtain ⟨tR, iR, eR1, -, -, eR2, -, hxR⟩ := rR.2 tg ig hpin'
  specialize eC2 rfl; specialize eR2 rfl
  simp only [X, if_pos rfl, if_neg (show (2 : ℕ) ≠ 1 by norm_num)] at hxC hxR
  have hqm : q ∈ d.lft := by
    rw [← H.lft, hq, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have := H.good.lft_s q hqm tC (by rw [← hxC, ← eC2, hi0]) (by rw [← hxR, ← eR2, hi0, show tC = tR by omega])
  rw [eC1, hi0, this, ← ha]

/-- **The last cell.** -/
theorem sound_rgt {N : ℕ} (ih : IHs P tabC (N + 2)) {a j : ℕ} (hj : j < P.rgt.length)
    (ha : (P.rgt.getI j).1 = a) {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    (h : LGH (gram P) (N + 1) [(false, pickLCI.1), (true, subN 2 j)] s.cfg Ψ) : SoundC P tabC a Ψ := by
  set q := P.rgt.getI j with hq
  have h1 := (lgh_ins_iff (I := pickLCI.2) (gram_good P).nodup (insRaw_mem_of_mem P (q := pickLCI) (by simp))).1 h
  rw [wp_pickLC] at h1
  obtain ⟨hL, hC⟩ := h1
  let X : ℕ → ℕ := fun mm => if mm = 0 then q.2.1 else q.2.2
  have hpost : ∀ q ∈ [assertIBI true], q ∈ (gram P).insL := by
    intro q hq; exact insRaw_mem_of_mem P (by simp at hq; subst hq; simp)
  have hb : ∀ (l c r : Bool) (mm : ℕ), (∀ mm' < 3, mm' ≠ 2 → (modeSt s l c r).val (4 + mm') = true → mm' = mm) →
      ∀ bs, (subN 2 j, bs) ∈ meths P → ∃ mm' < 3, bs = modeBody mm' (X mm') ++ syms [assertIBI true] ∧
        ((modeSt s l c r).val (4 + mm') = true → mm' = mm) := by
    intro l c r mm honly bs hbs
    rcases meth_sub P hbs with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, rfl | rfl⟩
    · omega
    · omega
    · exact ⟨0, by norm_num, by simp [X, hq], honly 0 (by norm_num) (by norm_num)⟩
    · exact ⟨1, by norm_num, by simp [X, hq], honly 1 (by norm_num) (by norm_num)⟩
  have ih' : IHs P tabC (N + 1) := fun n' hn' => ih n' (by omega)
  have rL := pick_mode H ih' (mm := 0) hpost (shaped_modeSt hs _ _ _)
    (hb true false s.mr 0 (by intro mm' hmm' h0 hv; interval_cases mm' <;> first | rfl | omega | (simp [modeSt, St.val] at hv))) hL
  have rC := pick_mode H ih' (mm := 1) hpost (shaped_modeSt hs _ _ _)
    (hb false true s.mr 1 (by intro mm' hmm' h0 hv; interval_cases mm' <;> first | rfl | omega | (simp [modeSt, St.val] at hv))) hC
  obtain ⟨hcov, hpost'⟩ := post_IB H rC.1
  refine ⟨hcov, fun tg ig hpin => ?_⟩
  obtain ⟨hpin', hz⟩ := hpost' tg ig hpin
  have hi1 : ofB ig (2 ^ P.b) + 1 = 2 ^ 2 ^ P.b := ofB_all_true hz
  obtain ⟨tL, iL, eL1, eL2, -, -, -, hxL⟩ := rL.2 tg ig hpin'
  obtain ⟨tC, iC, eC1, -, eC2, -, -, hxC⟩ := rC.2 tg ig hpin'
  specialize eL2 rfl; specialize eC2 rfl
  simp only [X, if_pos rfl, if_neg (show (1 : ℕ) ≠ 0 by norm_num)] at hxL hxC
  have hqm : q ∈ d.rgt := by
    rw [← H.rgt, hq, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hB := H.hB
  have hmx := H.good.hmx
  have htlt := ofB_lt tg (2 ^ P.b)
  have := H.good.rgt_s q hqm tC (by rw [hB]; omega)
    (by rw [hmx, hB, show 2 ^ 2 ^ P.b - 1 - 1 = iL by omega, show tC = tL by omega]; exact hxL)
    (by rw [hmx, hB, show 2 ^ 2 ^ P.b - 1 = iC by omega]; exact hxC)
  rw [eC1, show ofB ig (2 ^ P.b) = d.mx by rw [hmx, hB]; omega, this, ← ha]

/-! ## The first row -/

/-- **A prefix cell.** -/
theorem sound_pref {N : ℕ} {a c : ℕ} (hc : c < P.baseU.length) (ha : P.baseU.getI c = a) {s : St}
    (hs : Shaped s) {Ψ : Set Cfg} (h : LGH (gram P) N (prefBody P c ++ []) s.cfg Ψ) :
    SoundC P tabC a Ψ := by
  have hok : (AT.ce (2 + c)).Ok P.cs.length := by show 2 + c < P.cs.length; rw [H.csl]; omega
  have hp : ∀ q ∈ pickChks P ++ [clrTBI, guessIBI, setEQ] ++ actP P.b P.cs (.ce (2 + c)),
      q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact pickChks_mem P q hq
    · exact insRaw_mem_of_mem P (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                                    rcases hq with rfl | rfl | rfl <;> simp)
    · exact actP_mem P hok q hq
  have hw := lgh_prog (gram_good P).nodup hp (xs := [])
    (show LGH (gram P) N (syms (pickChks P ++ [clrTBI, guessIBI, setEQ] ++ actP P.b P.cs (.ce (2 + c)))
      ++ []) s.cfg Ψ by simpa [prefBody] using h)
  replace hw := wpP_mono _ (fun c' hc' => lgh_nil_iff.1 hc') hw
  simp only [inss_append, wpP_append, wp_pickChks] at hw
  have key : ∀ k < 2 ^ P.b, ∃ s', Shaped s' ∧ s'.chkV P.b = k ∧ s'.cfg ∈ Ψ ∧
      (s'.tb = false ∧ s'.ib = kDig P.cs (2 + c) k) := by
    intro k hk
    have h1 := hw k.testBit
    simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_clrTB, wp_guessIB, wp_setEQ] at h1
    obtain ⟨v, -, h1⟩ := h1
    rw [wp_act H.cs] at h1
    simp only [if_true] at h1
    obtain ⟨v', hrho, h1⟩ := h1
    have hk' := chkV_pick_testBit P s hk
    simp only [AT.reg, St.reg, St.setReg, Bool.false_eq_true, if_false, rho_ce] at hrho h1
    simp only [St.chkV, ofB_pick_testBit P s.chk hk] at hrho
    refine ⟨_, ?_, ?_, h1, rfl, ?_⟩
    · exact hs
    · exact hk'
    · simp only [kDig]; rw [hrho.2, hrho.1]
  obtain ⟨hcov, hpin⟩ := pin_of key
  refine ⟨hcov, fun tg ig hp' => ?_⟩
  have hd := hpin tg ig hp'
  have ht : ofB tg (2 ^ P.b) = 0 := ofB_eq_zero fun k hk => by
    obtain ⟨s', ⟨e1, -⟩, e2, -⟩ := hd k hk; rw [← e2, e1]
  have hi : ofB ig (2 ^ P.b) = c := by
    rw [← H.kc c hc]
    exact ofB_congr fun k hk => by obtain ⟨s', ⟨-, e1⟩, -, e2⟩ := hd k hk; rw [← e2, e1]
  rw [ht, hi, H.good.base c (by rw [H.c₁]; exact hc), ← H.baseU, ha]

omit H in
theorem Comp.reg_of_check {A : Comp} (hA : A.Check) : A.reg = false := by
  cases A <;> simp_all [Comp.Check, Comp.reg]

/-- **The first row after the prefix**: two check chains after `BB`. -/
theorem sound_bb {N : ℕ} {A₁ A₂ : Comp} (hA₁ : A₁.Check) (hA₂ : A₂.Check) (hok₁ : A₁.Ok P.cs.length)
    (hok₂ : A₂.Ok P.cs.length) {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    (h : LGH (gram P) N [(true, chN A₁ (chN A₂ bbN))] s.cfg Ψ) :
    ∃ as₁ as₂, Run A₁.aut as₁ A₁.aut.acc ∧ Run A₂.aut as₂ A₂.aut.acc ∧ as₁.length = 2 ^ P.b ∧
      as₂.length = 2 ^ P.b ∧ Cover P Ψ ∧ ∀ tg ig, Pin P Ψ tg ig →
        ofB tg (2 ^ P.b) = 0 ∧ Rel P.cs as₁ ig ig ∧ Rel P.cs as₂ ig ig := by
  obtain ⟨as₁, as₂, hr₁, hr₂, h⟩ := lgh_ch2 P h
  rcases N with _ | N
  · exact absurd h not_lgh_zero
  obtain ⟨bs, hb, h⟩ := lgh_comp_iff.1 h
  rw [gram_methL] at hb
  rw [meth_bb P hb] at h
  have hp : ∀ q ∈ pickChks P ++ [clrTBI, guessIBI] ++ chain P.b P.cs as₂ ++ chain P.b P.cs as₁,
      q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((hq | hq) | hq) | hq
    · exact pickChks_mem P q hq
    · exact insRaw_mem_of_mem P (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                                    rcases hq with rfl | rfl <;> simp)
    · exact chain_mem P (run_ok hok₂ hr₂) q hq
    · exact chain_mem P (run_ok hok₁ hr₁) q hq
  have hw := lgh_prog (gram_good P).nodup hp (xs := [])
    (show LGH (gram P) N (syms (pickChks P ++ [clrTBI, guessIBI] ++ chain P.b P.cs as₂ ++
      chain P.b P.cs as₁) ++ []) s.cfg Ψ by simpa [bbBody, List.append_assoc] using h)
  replace hw := wpP_mono _ (fun c' hc' => lgh_nil_iff.1 hc') hw
  simp only [inss_append, wpP_append, wp_pickChks] at hw
  have hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₁ a ha with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Comp.reg_of_check hA₁))
  have hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₂ a ha with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Comp.reg_of_check hA₂))
  have key : ∀ g : ℕ → Bool, as₂.length = 2 ^ P.b ∧ as₁.length = 2 ^ P.b ∧ ∃ s', Shaped s' ∧
      s'.chkV P.b = ofB g P.b ∧ s'.cfg ∈ Ψ ∧ s'.tb = false ∧
      (as₂.getD (ofB g P.b) .id).rho P.cs (ofB g P.b) s'.ib = some s'.ib ∧
      (as₁.getD (ofB g P.b) .id).rho P.cs (ofB g P.b) s'.ib = some s'.ib := by
    intro g
    have h1 := hw g
    simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_clrTB, wp_guessIB] at h1
    obtain ⟨v, h1⟩ := h1
    rw [← wpP_append, ← inss_append] at h1
    obtain ⟨hl₂, hl₁, v₂, v₁, h2, h3, h4⟩ := (wp_chain2I H.cs hreg₁ hreg₂
      (show Shaped { s with chk := fun r => if r < P.b then g r else s.chk r, tb := false, ib := v }
        from hs)).1 h1
    have hck : ({ s with chk := fun r => if r < P.b then g r else s.chk r, tb := false, ib := v } :
        St).chkV P.b = ofB g P.b := chkV_pick P _ g
    rw [hck] at h2 h3
    have hlt : ofB g P.b < as₂.length := hl₂ ▸ ofB_lt _ _
    have hlt' : ofB g P.b < as₁.length := hl₁ ▸ ofB_lt _ _
    have e2 := run_check hA₂ hr₂ hlt h2
    subst e2
    have e1 := run_check hA₁ hr₁ hlt' h3
    subst e1
    refine ⟨hl₂, hl₁, _, shaped_fn _, ?_, h4, rfl, h2, h3⟩
    exact hck
  obtain ⟨hl₂, hl₁, -⟩ := key fun _ => false
  have key' : ∀ k < 2 ^ P.b, ∃ s', Shaped s' ∧ s'.chkV P.b = k ∧ s'.cfg ∈ Ψ ∧ (s'.tb = false ∧
      (as₂.getD k .id).rho P.cs k s'.ib = some s'.ib ∧ (as₁.getD k .id).rho P.cs k s'.ib = some s'.ib) := by
    intro k hk
    obtain ⟨-, -, s', hs', hk', h1, h2, h3, h4⟩ := key k.testBit
    rw [ofB_testBit hk] at hk' h3 h4
    exact ⟨s', hs', hk', h1, h2, h3, h4⟩
  obtain ⟨hcov, hpin⟩ := pin_of key'
  refine ⟨as₁, as₂, hr₁, hr₂, hl₁, hl₂, hcov, fun tg ig hp' => ?_⟩
  have hd := hpin tg ig hp'
  refine ⟨ofB_eq_zero fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨s', ⟨e1, -⟩, e2, -⟩ := hd k hk; rw [← e2, e1]
  · obtain ⟨s', ⟨-, -, e1⟩, -, e2⟩ := hd k (hl₁ ▸ hk); rw [← e2]; exact e1
  · obtain ⟨s', ⟨-, e1, -⟩, -, e2⟩ := hd k (hl₂ ▸ hk); rw [← e2]; exact e1

/-- **The cells holding `1`.** -/
theorem sound_true {N : ℕ} {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    (h : LGH (gram P) N [(true, chN (.cmp 0 true) (chN (.cmp 1 false) bbN))] s.cfg Ψ) :
    SoundC P tabC P.codeTrue Ψ := by
  have h2 := H.two_le
  obtain ⟨as₁, as₂, hr₁, hr₂, hl₁, hl₂, hcov, hres⟩ := sound_bb H (A₁ := .cmp 0 true) (A₂ := .cmp 1 false) trivial trivial
    (show 0 < P.cs.length by omega) (show 1 < P.cs.length by omega) hs h
  refine ⟨hcov, fun tg ig hp => ?_⟩
  obtain ⟨ht, hR₁, hR₂⟩ := hres tg ig hp
  obtain ⟨-, hσ₁, -⟩ := run_cmp hr₁ hR₁
  obtain ⟨-, hσ₂, -⟩ := run_cmp hr₂ hR₂
  simp only [Comp.aut, Bool.toNat_true, Bool.toNat_false, true_iff, zero_ne_one, false_iff,
    not_le, hl₁, hl₂, H.k0, H.k1] at hσ₁ hσ₂
  rw [ht, H.good.tru _ hσ₁ hσ₂, H.codeTrue]

/-- **The blank cells.** -/
theorem sound_none {N : ℕ} {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    (h : LGH (gram P) N [(true, chN (.cmp 1 true) (chN .cpy bbN))] s.cfg Ψ) :
    SoundC P tabC P.codeNone Ψ := by
  have h2 := H.two_le
  obtain ⟨as₁, as₂, hr₁, hr₂, hl₁, hl₂, hcov, hres⟩ := sound_bb H (A₁ := .cmp 1 true) (A₂ := .cpy) trivial trivial
    (show 1 < P.cs.length by omega) trivial hs h
  refine ⟨hcov, fun tg ig hp => ?_⟩
  obtain ⟨ht, hR₁, -⟩ := hres tg ig hp
  obtain ⟨-, hσ₁, -⟩ := run_cmp hr₁ hR₁
  simp only [Comp.aut, Bool.toNat_true, true_iff, hl₁, H.k1] at hσ₁
  have hlt := ofB_lt ig (2 ^ P.b)
  rw [ht, H.good.non _ hσ₁ (by rw [H.hB]; exact hlt), H.codeNone]

/-! ## The claims and the root -/

/-- **Soundness of the claims.** -/
theorem sound : ∀ N (a : ℕ) (s : St) (Ψ : Set Cfg), Shaped s →
    LGH (gram P) N [(true, KN a)] s.cfg Ψ → SoundC P tabC a Ψ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a s Ψ hs h
  rcases N with _ | N
  · exact absurd h not_lgh_zero
  obtain ⟨bs, hb, h⟩ := lgh_comp_iff.1 h
  rw [gram_methL] at hb
  rcases meth_K P hb with ⟨j, hj, ha, rfl⟩ | ⟨j, hj, ha, rfl⟩ | ⟨j, hj, ha, rfl⟩ | ⟨c, hc, ha, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases N with _ | N
    · exact absurd h not_lgh_zero
    exact sound_mid H (fun n' hn' => ih n' hn') hj ha hs (by simpa using h)
  · rcases N with _ | N
    · exact absurd h not_lgh_zero
    exact sound_lft H (fun n' hn' => ih n' hn') hj ha hs (by simpa using h)
  · rcases N with _ | N
    · exact absurd h not_lgh_zero
    exact sound_rgt H (fun n' hn' => ih n' hn') hj ha hs (by simpa using h)
  · exact sound_pref H hc ha hs h
  · exact sound_true H hs (by simpa using h)
  · exact sound_none H hs (by simpa using h)

omit H in
theorem shaped_s₀ : Shaped s₀ := ⟨rfl, rfl⟩

/-- **Soundness of the root**: a won root yields an accepting entry in the last row. -/
theorem root_sound (h : LG (gram P) [(true, rootN)] s₀.cfg Set.univ) :
    ∃ i < 2 ^ d.B, tabC (2 ^ d.B - 1) i ∈ d.acc := by
  obtain ⟨n, h⟩ := h
  rcases n with _ | n
  · exact absurd h not_lgh_zero
  obtain ⟨bs, hb, h⟩ := lgh_comp_iff.1 h
  rw [gram_methL] at hb
  obtain ⟨a, ha, rfl⟩ := meth_root P hb
  simp only [List.cons_append, List.nil_append] at h
  obtain ⟨as₁, as₂, hr₁, hr₂, h⟩ := lgh_ch2 P h
  have h' := lgh_append h (xs := [(true, KN a)])
    (ys := syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁ ++ [assertTBI]) ++ []) (by simp)
  obtain ⟨hcov, hsnd⟩ := sound H n a s₀ _ shaped_s₀ h'
  have hp : ∀ q ∈ chain P.b P.cs as₂ ++ chain P.b P.cs as₁ ++ [assertTBI], q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | hq) | rfl
    · exact chain_mem P (run_ok (A := .bits) trivial hr₂) q hq
    · exact chain_mem P (run_ok (A := .cpy) trivial hr₁) q hq
    · exact insRaw_mem_of_mem P (by simp)
  have hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = true := fun a ha => Or.inl (run_cpy_mem hr₁ a ha)
  have hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₂ a ha with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- the committed cell
  let β : ℕ → Bool := fun d => match as₂.getD d .id with
    | .bit b => b
    | _ => false
  have hpost : ∀ s', Shaped s' → s'.cfg ∈ {c | LGH (gram P) n
      (syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁ ++ [assertTBI]) ++ []) c Set.univ} →
      s'.tb = true ∧ s'.ib = β (s'.chkV P.b) := by
    intro s' hs' h1
    have h2 := wpP_mono _ (fun c' hc' => lgh_nil_iff.1 hc') (lgh_prog (gram_good P).nodup hp h1)
    rw [inss_append, wpP_append, wp_chain2 H.cs hreg₁ hreg₂ hs'] at h2
    obtain ⟨hl₂, hl₁, v₂, v₁, e2, e1, h3⟩ := h2
    simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_assertTB] at h3
    have hk : s'.chkV P.b < as₂.length := hl₂ ▸ ofB_lt _ _
    have hk1 : s'.chkV P.b < as₁.length := hl₁ ▸ ofB_lt _ _
    rw [run_cpy_mem hr₁ _ (List.getD_mem' hk1), rho_id] at e1
    obtain ⟨β', hβ'⟩ := run_bits_mem hr₂ _ (List.getD_mem' hk)
    rw [hβ', rho_bit] at e2
    refine ⟨?_, ?_⟩
    · rw [← e1]; exact h3.1
    · simp only [β, hβ']; exact e2.1
  have hpin : Pin P {c | LGH (gram P) n
      (syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁ ++ [assertTBI]) ++ []) c Set.univ}
      (fun _ => true) β := fun s' hs' h1 => hpost s' hs' h1
  have hx := hsnd _ _ hpin
  have hall := ofB_all_true (g := fun _ => true) (n := 2 ^ P.b) (fun _ _ => rfl)
  refine ⟨ofB β (2 ^ P.b), by rw [H.hB]; exact ofB_lt _ _, ?_⟩
  rw [H.hB, show 2 ^ 2 ^ P.b - 1 = ofB (fun _ => true) (2 ^ P.b) by omega, hx, ← H.acc]
  exact ha

end Sound2

end TOHard2

end FOND
