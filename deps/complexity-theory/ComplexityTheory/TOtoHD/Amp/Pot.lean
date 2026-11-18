import ComplexityTheory.TOtoHD.Amp.InvStep
/-!
# The amplifier: the potentials

`psi_step`: under the invariant `Inv K` and honesty below `K`, a step never decreases the
potential `Psi K`, and a step keeping it constant is honest at level `K`.
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

@[simp] theorem cnt_cons_c (k : ℕ) (q : Pl) (l : List Pl) :
    List.count (Pl.c k) (q :: l) = List.count (Pl.c k) l + if q = Pl.c k then 1 else 0 := by
  simp [List.count_cons]

@[simp] theorem cnt_cons_d (k : ℕ) (q : Pl) (l : List Pl) :
    List.count (Pl.d k) (q :: l) = List.count (Pl.d k) l + if q = Pl.d k then 1 else 0 := by
  simp [List.count_cons]

section hon

variable {L K : ℕ} {x y : ACfg Q Φ}

theorem hon_nz (hx : ∀ z ph, x.1 ≠ .zt z ph) (hy : ∀ z ph, y.1 ≠ .zt z ph) : Hon L K x y :=
  fun z _ => ⟨fun h => absurd h.1 (hy z _), fun h => absurd h.1 (hx z _),
    fun h => absurd h.1 (hx z _)⟩

theorem hon_enter_of (z0 : ZI) (hx : ∀ z ph, x.1 ≠ .zt z ph) (hy : y.1 = .zt z0 .A)
    (h : z0.lvl L = K → x.2.2 (.side K z0.pr z0.sd) = 0) : Hon L K x y := by
  intro z hz
  refine ⟨fun h' => ?_, fun h' => absurd h'.1 (hx z _), fun h' => absurd h'.1 (hx z _)⟩
  rw [hy] at h'
  obtain ⟨h1, -⟩ := h'
  cases h1
  exact h hz

theorem hon_exit_of (z0 : ZI) (hx : x.1 = .zt z0 .B) (hy : ∀ z ph, y.1 ≠ .zt z ph)
    (h : z0.lvl L = K → x.2.2 (.side K z0.pr z0.sd) = 0) : Hon L K x y := by
  intro z hz
  refine ⟨fun h' => absurd h'.1 (hy z _), fun h' => absurd h'.2 (hy z _), fun h' => ?_⟩
  rw [hx] at h'
  obtain ⟨h1, -⟩ := h'
  cases h1
  exact h hz

theorem hon_in (z0 : ZI) (ph ph' : ZPh) (hx : x.1 = .zt z0 ph) (hy : y.1 = .zt z0 ph')
    (hn : ¬ (ph = .A ∧ ph' = .B)) : Hon L K x y := by
  intro z hz
  rw [hx, hy]
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · obtain ⟨h1, h2⟩ := h'
    cases h1
    exact absurd rfl (h2 ph)
  · obtain ⟨h1, h2⟩ := h'
    cases h1; cases h2
    exact absurd ⟨rfl, rfl⟩ hn
  · obtain ⟨h1, h2⟩ := h'
    cases h1
    exact absurd rfl (h2 ph')

theorem hon_mid_of (z0 : ZI) (hx : x.1 = .zt z0 .A) (hy : y.1 = .zt z0 .B)
    (h : z0.lvl L = K → x.2.2 (.side K z0.pr (!z0.sd)) = 0) : Hon L K x y := by
  intro z hz
  rw [hx, hy]
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · obtain ⟨h1, h2⟩ := h'
    cases h1
  · obtain ⟨h1, h2⟩ := h'
    cases h1
    exact h hz
  · obtain ⟨h1, h2⟩ := h'
    cases h1

end hon

/-- The tested sides are bounded by the level's pair sum. -/
theorem side_le_B {P : CM Q Φ} {L K : ℕ} {s0 : Finset Φ} {l : Loc Q} {S : Finset Φ} {m : Mk}
    (hI : Inv P L K s0 (l, S, m)) {k : ℕ} (hk : k ≤ K) (r : Bool) (hd : NotDr l)
    (hE : E l m k r = B k) :
    m (.side k r false) + m (.side k r true) = B k := by
  rw [← hE]; exact hI.sum k hk r hd

set_option maxHeartbeats 4000000 in
/-- **A step never decreases the potential of level `K`, and keeps it only if it is honest at
level `K`** (given the invariant and honesty below `K`). -/
theorem psi_step {P : CM Q Φ} {L K : ℕ} {s0 : Finset Φ} (hKL : K ≤ L) {x y : ACfg Q Φ}
    (hI : Inv P L K s0 x) (hH : ∀ k < K, Hon L k x y) (hs : AStep P L x y) :
    Psi L K x ≤ Psi L K y ∧ (Psi L K x = Psi L K y → Hon L K x y) := by
  obtain ⟨ρ, hρ, hsrc, -, hdl, rfl⟩ := hs
  obtain ⟨l, S, m⟩ := x
  dsimp only at hsrc hdl hH hI ⊢
  have hJ0 : ∀ k < K, ¬ InJ k l → m (.side k true true) = 0 := hI.restJ
  have hI0 : ∀ k < K, ¬ InI k l → m (.side k false true) = 0 := hI.restI
  cases hρ with
  | start =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    simp [Psi, owed, Rz, spawnOf]
  | bl0 =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    simp only [Psi, owed, Rz, spawnOf]
    by_cases hK : K = 0
    · subst hK; simp [B_zero]; ring
    · simp [Ne.symm hK]
  | blNext k hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    simp [Psi, owed, Rz, spawnOf]
  | blMain =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    simp [Psi, owed, Rz, spawnOf]
  | blBud k hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    by_cases hK : k + 1 = K
    · subst hK
      have hi := hI0 k (by omega) (by simp [InI])
      have hj := hJ0 k (by omega) (by simp [InJ])
      simp [Psi, owed, Rz, spawnOf, prg, hi, hj]; ring
    · simp [Psi, owed, Rz, spawnOf, hK]
  | inner k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side k true false)
    simp at hc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    cases s with
    | comp r0 => simp [Psi, owed, Rz, spawnOf, tgt]
    | bud b0 =>
      by_cases hK : k + 1 = K
      · subst hK; cases b0 <;> simp [Psi, owed, Rz, spawnOf, prg, tgt] <;> push_cast <;> ring
      · cases b0 <;> simp [Psi, owed, Rz, spawnOf, tgt, hK]
  | innerZ k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hd := hdl (.d k)
    simp at hd
    by_cases hK : K = k
    · subst hK
      have h1 := side_le_B hI le_rfl true trivial (by simp [E, Esp])
      have h1z : (m (.side K true false) : ℤ) + m (.side K true true) = B K := by exact_mod_cast h1
      have hs' : Psi (Q := Q) (Φ := Φ) L K (Loc.zt (ZI.sj K s false) ZPh.A, S, mv m [Pl.d K] []) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.sp K s SPos.inner, S, m) + (m (.side K true false) : ℤ) := by
        cases s with
        | comp r0 => simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd] <;> (simp only [Nat.cast_sub hd, Nat.cast_one]; linarith)
        | bud b0 => cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd] <;> (simp only [Nat.cast_sub hd, Nat.cast_one]; linarith)
      rw [upd_nil, hs']
      refine ⟨by omega, fun h => hon_enter_of (.sj K s false) (by simp) rfl (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_enter_of (.sj k s false) (by simp) rfl
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      by_cases hK' : k + 1 = K
      · subst hK'
        have h0 : m (.side k true false) = 0 :=
          hon_enter (hH k (Nat.lt_succ_self k)) (.sj k s false) rfl rfl (fun _ h => by cases h)
        have h1 := side_le_B (k := k) hI (by omega) true trivial (by simp [E, Esp])
        have h2 : m (.side k true true) = B k := by omega
        cases s with
        | comp r0 => simp [Psi, owed, Rz, spawnOf, ZI.lvl]
        | bud b0 => cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, prg, h2]
      · cases s with
        | comp r0 => simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
        | bud b0 => cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK, hK']
  | sjF k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    by_cases hK : K = k
    · subst hK
      have hs' : Psi (Q := Q) (Φ := Φ) L K (Loc.sp K s SPos.restj, S, mv m [] []) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.zt (ZI.sj K s false) ZPh.B, S, m) + (m (.side K true false) : ℤ) := by
        rcases s with r0 | b0
        · simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
        · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
      rw [upd_nil, hs']
      refine ⟨by omega, fun h => hon_exit_of (.sj K s false) rfl (by simp) (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_exit_of (.sj k s false) rfl (by simp)
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      rcases s with r0 | b0
      · simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
      · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, prg, Ne.symm hK]
  | restj k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    rcases s with r0 | b0
    · simp [Psi, owed, Rz, spawnOf]
    · cases b0 <;> simp [Psi, owed, Rz, spawnOf, prg]
  | restjZ k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hd := hdl (.d k)
    simp at hd
    by_cases hK : K = k
    · subst hK
      have h1 := side_le_B hI le_rfl true trivial (by simp [E, Esp])
      have h1z : (m (.side K true false) : ℤ) + m (.side K true true) = B K := by exact_mod_cast h1
      have hs' : Psi (Q := Q) (Φ := Φ) L K (Loc.zt (ZI.sj K s true) ZPh.A, S, mv m [Pl.d K] []) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.sp K s SPos.restj, S, m) + (m (.side K true true) : ℤ) := by
        rcases s with r0 | b0
        · simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd] <;> (simp only [Nat.cast_sub hd, Nat.cast_one]; linarith)
        · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd] <;> (simp only [Nat.cast_sub hd, Nat.cast_one]; linarith)
      rw [upd_nil, hs']
      refine ⟨by omega, fun h => hon_enter_of (.sj K s true) (by simp) rfl (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_enter_of (.sj k s true) (by simp) rfl
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      rcases s with r0 | b0
      · simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
      · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, prg, Ne.symm hK]
  | sjT k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side k false false)
    simp at hc
    by_cases hK : K = k
    · subst hK
      have hs' : Psi (Q := Q) (Φ := Φ) L K (Loc.sp K s SPos.outer, S,
            mv m [Pl.side K false false] [Pl.side K false true]) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.zt (ZI.sj K s true) ZPh.B, S, m) + (m (.side K true true) : ℤ) := by
        rcases s with r0 | b0
        · simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
        · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
      rw [upd_nil, hs']
      refine ⟨by omega, fun h => hon_exit_of (.sj K s true) rfl (by simp) (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_exit_of (.sj k s true) rfl (by simp)
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      rcases s with r0 | b0
      · simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
      · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, prg, Ne.symm hK] <;>
          split_ifs <;> push_cast <;> ring
  | outerIn k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    rcases s with r0 | b0
    · simp [Psi, owed, Rz, spawnOf]
    · by_cases hK : k + 1 = K
      · have hj := hJ0 k (by omega) (by simp [InJ])
        cases b0 <;> simp [Psi, owed, Rz, spawnOf, prg, hj]
      · cases b0 <;> simp [Psi, owed, Rz, spawnOf, hK]
  | outerZ k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hd := hdl (.d k)
    simp at hd
    by_cases hK : K = k
    · subst hK
      have h1 := side_le_B hI le_rfl false trivial (by simp [E, Esp])
      have h1z : (m (.side K false false) : ℤ) + m (.side K false true) = B K := by
        exact_mod_cast h1
      have hs' : Psi (Q := Q) (Φ := Φ) L K (Loc.zt (ZI.si K s false) ZPh.A, S, mv m [Pl.d K] []) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.sp K s SPos.outer, S, m) + (m (.side K false false) : ℤ) := by
        rcases s with r0 | b0
        · simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd] <;> (simp only [Nat.cast_sub hd, Nat.cast_one]; linarith)
        · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd] <;> (simp only [Nat.cast_sub hd, Nat.cast_one]; linarith)
      rw [upd_nil, hs']
      refine ⟨by omega, fun h => hon_enter_of (.si K s false) (by simp) rfl (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_enter_of (.si k s false) (by simp) rfl
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      by_cases hK' : k + 1 = K
      · subst hK'
        have h0 : m (.side k false false) = 0 :=
          hon_enter (hH k (Nat.lt_succ_self k)) (.si k s false) rfl rfl (fun _ h => by cases h)
        have h1 := side_le_B (k := k) hI (by omega) false trivial (by simp [E, Esp])
        have h2 : m (.side k false true) = B k := by omega
        rcases s with r0 | b0
        · simp [Psi, owed, Rz, spawnOf, ZI.lvl]
        · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, prg, h2, B_succ]
      · rcases s with r0 | b0
        · simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
        · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK, hK']
  | siF k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    by_cases hK : K = k
    · subst hK
      have hs' : Psi (Q := Q) (Φ := Φ) L K (Loc.sp K s SPos.resti, S, mv m [] []) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.zt (ZI.si K s false) ZPh.B, S, m) + (m (.side K false false) : ℤ) := by
        rcases s with r0 | b0
        · simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
        · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
      rw [upd_nil, hs']
      refine ⟨by omega, fun h => hon_exit_of (.si K s false) rfl (by simp) (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_exit_of (.si k s false) rfl (by simp)
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      rcases s with r0 | b0
      · simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
      · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, prg, Ne.symm hK]
  | resti k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine ⟨le_of_eq ?_, fun _ => hon_nz (by simp) (by simp)⟩
    rcases s with r0 | b0
    · simp [Psi, owed, Rz, spawnOf]
    · cases b0 <;> simp [Psi, owed, Rz, spawnOf, prg]
  | restiZ k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hd := hdl (.d k)
    simp at hd
    by_cases hK : K = k
    · subst hK
      have h1 := side_le_B hI le_rfl false trivial (by simp [E, Esp])
      have h1z : (m (.side K false false) : ℤ) + m (.side K false true) = B K := by
        exact_mod_cast h1
      have hs' : Psi (Q := Q) (Φ := Φ) L K (Loc.zt (ZI.si K s true) ZPh.A, S, mv m [Pl.d K] []) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.sp K s SPos.resti, S, m) + (m (.side K false true) : ℤ) := by
        rcases s with r0 | b0
        · simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd] <;> (simp only [Nat.cast_sub hd, Nat.cast_one]; linarith)
        · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd] <;> (simp only [Nat.cast_sub hd, Nat.cast_one]; linarith)
      rw [upd_nil, hs']
      refine ⟨by omega, fun h => hon_enter_of (.si K s true) (by simp) rfl (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_enter_of (.si k s true) (by simp) rfl
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      rcases s with r0 | b0
      · simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
      · cases b0 <;> simp [Psi, owed, Rz, spawnOf, ZI.lvl, prg, Ne.symm hK]
  | siT k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hy : ∀ z ph, after (Q := Q) k s ≠ Loc.zt z ph := by
      intro z ph h
      rcases s with r0 | b0
      · cases r0 <;> simp [after] at h
      · cases b0 <;> simp [after] at h
    by_cases hK : K = k
    · subst hK
      have hs' : Psi (Q := Q) (Φ := Φ) L K (after K s, S, mv m [] []) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.zt (ZI.si K s true) ZPh.B, S, m) + (m (.side K false true) : ℤ) := by
        rcases s with r0 | b0
        · cases r0 <;> simp [after, Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
        · cases b0 <;> simp [after, Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
      rw [upd_nil, hs']
      refine ⟨by omega, fun h => hon_exit_of (.si K s true) rfl hy (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_exit_of (.si k s true) rfl hy
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      by_cases hK' : k + 1 = K
      · subst hK'
        have hi : m (.side k false true) = 0 :=
          hon_exit (hH k (Nat.lt_succ_self k)) (.si k s true) rfl rfl (hy _)
        have hj := hJ0 k (Nat.lt_succ_self k) (by simp [InJ])
        rcases s with r0 | b0
        · cases r0 <;> simp [after, Psi, owed, Rz, spawnOf, ZI.lvl]
        · cases b0 <;> simp [after, Psi, owed, Rz, spawnOf, ZI.lvl, prg, hi, hj, B_succ] <;> ring
      · rcases s with r0 | b0
        · cases r0 <;> simp [after, Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
        · cases b0 <;> simp [after, Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK, hK']
  | zAA z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.c (z.lvl L))
    simp at hc
    refine ⟨le_of_eq ?_, fun _ => hon_in z .A .A' rfl rfl (by simp)⟩
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩ <;> (try rcases s with r0 | b0) <;>
      (try cases b0) <;> simp [Psi, owed, Rz, spawnOf, prg, ZI.lvl, ZI.pr, ZI.sd] at hc ⊢ <;>
      split_ifs <;> subst_vars <;> omega
  | zA'A z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side (z.lvl L) z.pr (!z.sd))
    simp at hc
    refine ⟨le_of_eq ?_, fun _ => hon_in z .A' .A rfl rfl (by simp)⟩
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩ <;> (try rcases s with r0 | b0) <;>
      (try cases b0) <;> (try cases b) <;>
      simp [Psi, owed, Rz, spawnOf, prg, ZI.lvl, ZI.pr, ZI.sd] at hc ⊢ <;>
      split_ifs <;> subst_vars <;> omega
  | zAB z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    by_cases hK : z.lvl L = K
    · have h1 : m (.side K z.pr false) + m (.side K z.pr true) = B K := by
        refine side_le_B hI le_rfl _ (by cases z <;> trivial) ?_
        rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩ <;> simp [ZI.lvl] at hK <;> subst hK <;>
          simp [E, Esp]
      have hs' : Psi (Q := Q) (Φ := Φ) L K (Loc.zt z ZPh.B, upd S [] [], mv m [] []) =
          Psi (Q := Q) (Φ := Φ) L K (Loc.zt z ZPh.A, S, m) +
            2 * (m (.side K z.pr (!z.sd)) : ℤ) := by
        rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩ <;> simp [ZI.lvl] at hK <;> subst hK <;>
          (try rcases s with r0 | b0) <;> (try cases b0) <;> (try cases b) <;>
          simp [Psi, owed, Rz, spawnOf, prg, ZI.lvl, ZI.pr, ZI.sd] at h1 ⊢ <;> omega
      rw [hs']
      exact ⟨by omega, fun h => hon_mid_of z rfl rfl (fun _ => by
        show m (.side K z.pr (!z.sd)) = 0
        omega)⟩
    · refine ⟨le_of_eq ?_, fun _ => hon_mid_of z rfl rfl (fun h => absurd h hK)⟩
      rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩ <;> simp only [ZI.lvl] at hK <;>
        (try rcases s with r0 | b0) <;> (try cases b0) <;>
        simp [Psi, owed, Rz, spawnOf, prg, ZI.lvl, hK]
  | zBB z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.c (z.lvl L))
    simp at hc
    refine ⟨le_of_eq ?_, fun _ => hon_in z .B .B' rfl rfl (by simp)⟩
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩ <;> (try rcases s with r0 | b0) <;>
      (try cases b0) <;> simp [Psi, owed, Rz, spawnOf, prg, ZI.lvl, ZI.pr, ZI.sd] at hc ⊢ <;>
      split_ifs <;> subst_vars <;> omega
  | zB'B z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side (z.lvl L) z.pr z.sd)
    simp at hc
    refine ⟨le_of_eq ?_, fun _ => hon_in z .B' .B rfl rfl (by simp)⟩
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩ <;> (try rcases s with r0 | b0) <;>
      (try cases b0) <;> (try cases b) <;>
      simp [Psi, owed, Rz, spawnOf, prg, ZI.lvl, ZI.pr, ZI.sd] at hc ⊢ <;>
      split_ifs <;> subst_vars <;> omega
  | mNop t ht hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact ⟨le_of_eq (by simp [Psi, owed, Rz, spawnOf]), fun _ => hon_nz (by simp) (by simp)⟩
  | mInc t ht r hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact ⟨le_of_eq (by simp [Psi, owed, Rz, spawnOf]), fun _ => hon_nz (by simp) (by simp)⟩
  | mDec t ht r hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact ⟨le_of_eq (by simp [Psi, owed, Rz, spawnOf]), fun _ => hon_nz (by simp) (by simp)⟩
  | mZ i t ht r hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hd := hdl (.d L)
    simp at hd
    by_cases hK : K = L
    · subst hK
      have h1 := side_le_B hI le_rfl r trivial (by simp [E])
      have h1z : (m (.side K r false) : ℤ) + m (.side K r true) = B K := by exact_mod_cast h1
      have hs' : Psi (Q := Q) (Φ := Φ) K K (Loc.zt (ZI.m i r) ZPh.A, upd S [] [], mv m [Pl.d K] []) =
          Psi (Q := Q) (Φ := Φ) K K (Loc.main t.src, S, m) + (m (.side K r true) : ℤ) := by
        simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
        simp only [Nat.cast_sub hd, Nat.cast_one]; linarith
      rw [hs']
      refine ⟨by omega, fun h => hon_enter_of (.m i r) (by simp) rfl (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_enter_of (.m i r) (by simp) rfl
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
  | mExit i t ht r hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    by_cases hK : K = L
    · subst hK
      have hs' : Psi (Q := Q) (Φ := Φ) K K (Loc.main t.dst, upd S t.add t.del, mv m [] []) =
          Psi (Q := Q) (Φ := Φ) K K (Loc.zt (ZI.m i r) ZPh.B, S, m) + (m (.side K r true) : ℤ) := by
        simp [Psi, owed, Rz, spawnOf, ZI.lvl, ZI.pr, ZI.sd]
      rw [hs']
      refine ⟨by omega, fun h => hon_exit_of (.m i r) rfl (by simp) (fun _ => ?_)⟩
      simp [ZI.pr, ZI.sd]; omega
    · refine ⟨le_of_eq ?_, fun _ => hon_exit_of (.m i r) rfl (by simp)
        (fun h => absurd h.symm (by simpa [ZI.lvl] using hK))⟩
      simp [Psi, owed, Rz, spawnOf, ZI.lvl, Ne.symm hK]
  | toDrain =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact ⟨le_of_eq (by simp [Psi, owed, Rz, spawnOf]), fun _ => hon_nz (by simp) (by simp)⟩
  | drain k r hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact ⟨le_of_eq (by simp [Psi, owed, Rz, spawnOf]), fun _ => hon_nz (by simp) (by simp)⟩
  | toDone =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact ⟨le_of_eq (by simp [Psi, owed, Rz, spawnOf]), fun _ => hon_nz (by simp) (by simp)⟩

end Amp

end HTN
