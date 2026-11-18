import ComplexityTheory.TOtoHD.Amp.Inv
/-!
# The amplifier: the invariant is preserved by honest steps

`inv_step`: if every zero test of a level below `K` is honest in a step, the step preserves
`Inv K`.
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

@[simp] theorem mv_apply (m : Mk) (dl il : List Pl) (p : Pl) :
    mv m dl il p = m p - dl.count p + il.count p := rfl

@[simp] theorem cnt_cons_side (k r b : _) (q : Pl) (l : List Pl) :
    List.count (Pl.side k r b) (q :: l) =
      List.count (Pl.side k r b) l + if q = Pl.side k r b then 1 else 0 := by
  simp [List.count_cons]

omit [DecidableEq Φ] in
@[simp] theorem upd_nil (S : Finset Φ) [DecidableEq Φ] : upd S [] [] = S := by
  ext f; simp [upd]

theorem lvl4 (a k : ℕ) : a < k ∨ a = k ∨ a = k + 1 ∨ k + 1 < a := by omega

omit [DecidableEq Φ] in
theorem valid_zt {P : CM Q Φ} {L : ℕ} {z : ZI} {ph ph' : ZPh} (h : Valid P L (.zt z ph)) :
    Valid P L (.zt z ph') := by
  cases z <;> exact h

omit [DecidableEq Φ] in
/-- The invariant is preserved by a step that does not change the sides and keeps the expected
sums. -/
theorem inv_of_same {P : CM Q Φ} {L K : ℕ} {s0 : Finset Φ} {l l' : Loc Q} {S S' : Finset Φ}
    {m m' : Mk} (hI : Inv P L K s0 (l, S, m)) (hv : Valid P L l')
    (hf : Pre l' → Pre l ∧ S' = S) (hside : ∀ k r b, m' (.side k r b) = m (.side k r b))
    (hE : NotDr l' → NotDr l ∧ ∀ k ≤ K, ∀ r, E l' m' k r = E l m k r)
    (hJ : ∀ k < K, ¬ InJ k l' → ¬ InJ k l ∨ m (.side k true true) = 0)
    (hI' : ∀ k < K, ¬ InI k l' → ¬ InI k l ∨ m (.side k false true) = 0) :
    Inv P L K s0 (l', S', m') := by
  obtain ⟨-, hf0, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨hv, fun h => ?_, fun k hk r hd => ?_, fun r h => ?_, fun k hk h => ?_,
    fun k hk h => ?_⟩
  · obtain ⟨h1, h2⟩ := hf h; rw [h2]; exact hf0 h1
  · obtain ⟨h1, h2⟩ := hE hd
    dsimp only
    rw [hside, hside, h2 k hk r]; exact hsum k hk r h1
  · dsimp only; rw [hside]; exact hzero r (hf h).1
  · dsimp only; rw [hside]
    rcases hJ k hk h with h' | h'
    · exact hrj k hk h'
    · exact h'
  · dsimp only; rw [hside]
    rcases hI' k hk h with h' | h'
    · exact hri k hk h'
    · exact h'

section rules

variable {P : CM Q Φ} {L K : ℕ} {s0 : Finset Φ} {S : Finset Φ} {m : Mk}

theorem inv_start (hI : Inv P L K s0 (.start, S, m)) :
    Inv P L K s0 (.bl 0, S, mv m []
      [.side 0 false false, .side 0 false false, .side 0 true false, .side 0 true false]) := by
  obtain ⟨hv, hf, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨Nat.zero_le _, fun _ => hf trivial, ?_, ?_, ?_, ?_⟩
  · intro k hk r _
    have h0 := hsum k hk r trivial
    simp only [E] at h0
    rcases Nat.eq_zero_or_pos k with rfl | h
    · cases r <;> simp [E, B_zero] <;> omega
    · have : k ≠ 0 := by omega
      simp [E, this]; omega
  · intro r _
    have hr := hzero r trivial
    dsimp only at hr ⊢
    simp; omega
  · intro k hk _
    have hr := hrj k hk (by simp [InJ])
    dsimp only at hr ⊢
    simp; omega
  · intro k hk _
    have hr := hri k hk (by simp [InI])
    dsimp only at hr ⊢
    simp; omega

theorem inv_inner {k : ℕ} {s : Site} (hI : Inv P L K s0 (.sp k s .inner, S, m))
    (hc : 1 ≤ m (.side k true false)) :
    Inv P L K s0 (.sp k s .inner, S, mv m [Pl.side k true false]
        [Pl.side k true true, tgt k s]) := by
  obtain ⟨hv, hf, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨hv, hf, ?_, ?_, ?_, ?_⟩
  · intro k' hk' r _
    have h0 := hsum k' hk' r trivial
    rcases lvl4 k' k with h | rfl | rfl | h
    · have e1 : k ≠ k' := by omega
      have e2 : k + 1 ≠ k' := by omega
      cases s <;> simp [E, Esp, tgt, prg, e1, e2, h.le] at h0 ⊢ <;> omega
    · cases s <;> cases r <;> simp [E, Esp, tgt, prg] at h0 ⊢ <;> omega
    · cases s with
      | comp r0 => cases r0 <;> cases r <;> simp [E, Esp, tgt, prg] at h0 ⊢ <;> omega
      | bud b => cases r <;> simp [E, Esp, tgt, prg] at h0 ⊢ <;> omega
    · have e1 : k ≠ k' := by omega
      have e2 : k + 1 ≠ k' := by omega
      have e3 : ¬ k' ≤ k := by omega
      cases s <;> simp [E, Esp, tgt, prg, e1, e2, e3, h] at h0 ⊢ <;> omega
  · intro r hp
    have hz := hzero r hp
    dsimp only at hz ⊢
    have hv' : k < L := hv
    have : k ≠ L := by omega
    cases s <;> simp [tgt, *]
  · intro k' hk' hJ
    simp [InJ] at hJ
    have hr := hrj k' hk' (by simp [InJ]; omega)
    dsimp only at hr ⊢
    cases s <;> simp [tgt] <;> omega
  · intro k' hk' hJ
    simp [InI] at hJ
    have hr := hri k' hk' (by simp [InI]; omega)
    dsimp only at hr ⊢
    cases s <;> simp [tgt] <;> omega

theorem inv_restj {k : ℕ} {s : Site} (hI : Inv P L K s0 (.sp k s .restj, S, m))
    (hc : 1 ≤ m (.side k true true)) :
    Inv P L K s0 (.sp k s .restj, S, mv m [Pl.side k true true] [Pl.side k true false]) := by
  obtain ⟨hv, hf, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨hv, hf, ?_, ?_, ?_, ?_⟩
  · intro k' hk' r _
    have h0 := hsum k' hk' r trivial
    by_cases e : k = k'
    · subst e; cases r <;> simp [E, Esp, prg] at h0 ⊢ <;> omega
    · simp [E, Esp, prg, e] at h0 ⊢; omega
  · intro r hp
    have hz := hzero r hp
    dsimp only at hz ⊢
    have hv' : k < L := hv
    have : k ≠ L := by omega
    simp [*]
  · intro k' hk' hJ
    simp [InJ] at hJ
    have hr := hrj k' hk' (by simp [InJ]; omega)
    dsimp only at hr ⊢
    simp; omega
  · intro k' hk' hJ
    have hr := hri k' hk' hJ
    dsimp only at hr ⊢
    simp; omega

theorem inv_resti {k : ℕ} {s : Site} (hI : Inv P L K s0 (.sp k s .resti, S, m))
    (hc : 1 ≤ m (.side k false true)) :
    Inv P L K s0 (.sp k s .resti, S, mv m [Pl.side k false true] [Pl.side k false false]) := by
  obtain ⟨hv, hf, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨hv, hf, ?_, ?_, ?_, ?_⟩
  · intro k' hk' r _
    have h0 := hsum k' hk' r trivial
    by_cases e : k = k'
    · subst e; cases r <;> simp [E, Esp, prg] at h0 ⊢ <;> omega
    · simp [E, Esp, prg, e] at h0 ⊢; omega
  · intro r hp
    have hz := hzero r hp
    dsimp only at hz ⊢
    have hv' : k < L := hv
    have : k ≠ L := by omega
    simp [*]
  · intro k' hk' hJ
    have hr := hrj k' hk' hJ
    dsimp only at hr ⊢
    simp; omega
  · intro k' hk' hJ
    simp [InI] at hJ
    have hr := hri k' hk' (by simp [InI]; omega)
    dsimp only at hr ⊢
    simp; omega

theorem inv_sjT {k : ℕ} {s : Site} (hI : Inv P L K s0 (.zt (.sj k s true) .B, S, m))
    (hc : 1 ≤ m (.side k false false)) (hj : k < K → m (.side k true true) = 0) :
    Inv P L K s0 (.sp k s .outer, S, mv m [Pl.side k false false] [Pl.side k false true]) := by
  obtain ⟨hv, hf, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨hv, hf, ?_, ?_, ?_, ?_⟩
  · intro k' hk' r _
    have h0 := hsum k' hk' r trivial
    rcases lvl4 k' k with h | rfl | rfl | h
    · have e1 : k ≠ k' := by omega
      have e2 : k + 1 ≠ k' := by omega
      simp [E, Esp, prg, e1, h.le] at h0 ⊢; omega
    · cases r <;> simp [E, Esp] at h0 ⊢ <;> omega
    · cases s with
      | comp r0 => cases r0 <;> cases r <;> simp [E, Esp, prg] at h0 ⊢ <;> first | omega | (rw [h0]; ring)
      | bud b => simp [E, Esp] at h0 ⊢; omega
    · have e1 : k ≠ k' := by omega
      have e3 : ¬ k' ≤ k := by omega
      simp [E, Esp, e1, e3, h] at h0 ⊢; omega
  · intro r hp
    have hz := hzero r hp
    dsimp only at hz ⊢
    have hv' : k < L := hv
    have : k ≠ L := by omega
    simp [*]
  · intro k' hk' hJ
    by_cases e : k' = k
    · subst e; dsimp only; simp; exact hj hk'
    · have hr := hrj k' hk' (by simp [InJ]; omega)
      dsimp only at hr ⊢
      simp; omega
  · intro k' hk' hJ
    simp [InI] at hJ
    have hr := hri k' hk' (by simp [InI]; omega)
    dsimp only at hr ⊢
    simp; omega

theorem inv_zmove (hKL : K ≤ L) {z : ZI} {ph ph' : ZPh} {b : Bool}
    (hI : Inv P L K s0 (.zt z ph, S, m)) (hc : 1 ≤ m (.side (z.lvl L) z.pr b)) :
    Inv P L K s0 (.zt z ph', S, mv m [Pl.side (z.lvl L) z.pr b] [Pl.side (z.lvl L) z.pr (!b)]) := by
  obtain ⟨hv, hf, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨valid_zt hv, ?_, ?_, ?_, ?_, ?_⟩
  · cases z <;> exact hf
  · intro k' hk' r hd
    have h0 := hsum k' hk' r (by cases z <;> trivial)
    cases z with
    | sj k s b0 =>
      by_cases e : k = k'
      · subst e; cases r <;> cases b <;> simp [ZI.lvl, ZI.pr, E, Esp, prg] at h0 hc ⊢ <;> omega
      · simp [ZI.lvl, ZI.pr, E, Esp, prg, e] at h0 ⊢; omega
    | si k s b0 =>
      by_cases e : k = k'
      · subst e; cases r <;> cases b <;> simp [ZI.lvl, ZI.pr, E, Esp, prg] at h0 hc ⊢ <;> omega
      · simp [ZI.lvl, ZI.pr, E, Esp, prg, e] at h0 ⊢; omega
    | m i r0 =>
      by_cases e : L = k'
      · subst e
        by_cases e' : r0 = r
        · subst e'; cases b <;> simp [ZI.lvl, ZI.pr, E] at h0 hc ⊢ <;> omega
        · simp [ZI.lvl, ZI.pr, E, e'] at h0 ⊢; omega
      · simp [ZI.lvl, ZI.pr, E, e] at h0 ⊢; omega
  · intro r hp
    cases z with
    | m i r0 => exact absurd hp id
    | sj k s b0 =>
      have hz := hzero r hp
      have hv' : k < L := hv
      have : k ≠ L := by omega
      dsimp only at hz ⊢; simp [ZI.lvl, *]
    | si k s b0 =>
      have hz := hzero r hp
      have hv' : k < L := hv
      have : k ≠ L := by omega
      dsimp only at hz ⊢; simp [ZI.lvl, *]
  · intro k' hk' hJ
    cases z with
    | sj k s b0 =>
      simp [InJ] at hJ
      have hr := hrj k' hk' (by simp [InJ]; omega)
      dsimp only at hr ⊢; simp [ZI.lvl]; omega
    | si k s b0 =>
      have hr := hrj k' hk' (by simp [InJ])
      dsimp only at hr ⊢; simp [ZI.lvl, ZI.pr]; omega
    | m i r0 =>
      have hr := hrj k' hk' (by simp [InJ])
      have : k' ≠ L := by omega
      dsimp only at hr ⊢; simp [ZI.lvl, *]; omega
  · intro k' hk' hJ
    cases z with
    | sj k s b0 =>
      have hr := hri k' hk' (by simpa [InI] using hJ)
      simp [InI] at hJ
      dsimp only at hr ⊢; simp [ZI.lvl, ZI.pr]; omega
    | si k s b0 =>
      simp [InI] at hJ
      have hr := hri k' hk' (by simp [InI]; omega)
      dsimp only at hr ⊢; simp [ZI.lvl]; omega
    | m i r0 =>
      have hr := hri k' hk' (by simp [InI])
      have : k' ≠ L := by omega
      dsimp only at hr ⊢; simp [ZI.lvl, *]; omega

theorem inv_mmove (hKL : K ≤ L) {q q' : Q} {S' : Finset Φ} {r : Bool} {b : Bool}
    (hI : Inv P L K s0 (.main q, S, m)) (hc : 1 ≤ m (.side L r b)) :
    Inv P L K s0 (.main q', S', mv m [Pl.side L r b] [Pl.side L r (!b)]) := by
  obtain ⟨hv, hf, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨trivial, fun h => absurd h id, ?_, fun _ h => absurd h id, ?_, ?_⟩
  · intro k' hk' r' _
    have h0 := hsum k' hk' r' trivial
    by_cases e : L = k'
    · subst e
      by_cases e' : r = r'
      · subst e'; cases b <;> simp [E] at h0 hc ⊢ <;> omega
      · simp [E, e'] at h0 ⊢; omega
    · simp [E, e] at h0 ⊢; omega
  · intro k' hk' _
    have hr := hrj k' hk' (by simp [InJ])
    have : L ≠ k' := by omega
    dsimp only at hr ⊢; simp [*]
  · intro k' hk' _
    have hr := hri k' hk' (by simp [InI])
    have : L ≠ k' := by omega
    dsimp only at hr ⊢; simp [*]

theorem inv_drain {k : ℕ} {r : Bool} (hI : Inv P L K s0 (.drain, S, m)) :
    Inv P L K s0 (.drain, S, mv m [Pl.side k r false] []) := by
  obtain ⟨hv, hf, hsum, hzero, hrj, hri⟩ := hI
  refine ⟨trivial, fun h => absurd h id, fun _ _ _ h => absurd h id, fun _ h => absurd h id,
    ?_, ?_⟩
  · intro k' hk' _
    have hr := hrj k' hk' (by simp [InJ])
    dsimp only at hr ⊢; simp [*]
  · intro k' hk' _
    have hr := hri k' hk' (by simp [InI])
    dsimp only at hr ⊢; simp [*]

end rules

end Amp

end HTN

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

theorem Esp_congr {k0 : ℕ} {s : Site} {π π' k : ℕ} {r : Bool} (h : k = k0 + 1 → π' = π) :
    Esp k0 s π' k r = Esp k0 s π k r := by
  unfold Esp
  split_ifs with h1 h2
  · rfl
  · rfl
  · rw [h (by omega)]

theorem hon_enter {L k : ℕ} {x y : ACfg Q Φ} (h : Hon L k x y) (z : ZI) (hz : z.lvl L = k)
    (hy : y.1 = .zt z .A) (hx : ∀ ph, x.1 ≠ .zt z ph) : x.2.2 (.side k z.pr z.sd) = 0 :=
  (h z hz).1 ⟨hy, hx⟩

theorem hon_exit {L k : ℕ} {x y : ACfg Q Φ} (h : Hon L k x y) (z : ZI) (hz : z.lvl L = k)
    (hx : x.1 = .zt z .B) (hy : ∀ ph, y.1 ≠ .zt z ph) : x.2.2 (.side k z.pr z.sd) = 0 :=
  (h z hz).2.2 ⟨hx, hy⟩

theorem hon_mid {L k : ℕ} {x y : ACfg Q Φ} (h : Hon L k x y) (z : ZI) (hz : z.lvl L = k)
    (hx : x.1 = .zt z .A) (hy : y.1 = .zt z .B) : x.2.2 (.side k z.pr (!z.sd)) = 0 :=
  (h z hz).2.1 ⟨hx, hy⟩

/-- **The invariant is preserved by every step that is honest at the levels below `K`.** -/
theorem inv_step {P : CM Q Φ} {L K : ℕ} {s0 : Finset Φ} (hKL : K ≤ L) {x y : ACfg Q Φ}
    (hI : Inv P L K s0 x) (hH : ∀ k < K, Hon L k x y) (hs : AStep P L x y) :
    Inv P L K s0 y := by
  obtain ⟨ρ, hρ, hsrc, -, hdl, rfl⟩ := hs
  obtain ⟨l, S, m⟩ := x
  dsimp only at hsrc hdl hH hI ⊢
  have hJ0 : ∀ k < K, ¬ InJ k l → m (.side k true true) = 0 := hI.restJ
  have hI0 : ∀ k < K, ¬ InI k l → m (.side k false true) = 0 := hI.restI
  have hS0 : ∀ k ≤ K, ∀ r, NotDr l →
      m (.side k r false) + m (.side k r true) = E l m k r := hI.sum
  cases hρ with
  | start =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc; rw [upd_nil]; exact inv_start hI
  | bl0 =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI (Nat.zero_le _) (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun _ _ _ => rfl⟩) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
      (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | blNext k hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => ?_⟩) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
      (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
    rcases lvl4 k' k with h | rfl | rfl | h
    · simp [E, Esp, h.le]
    · simp [E, Esp]
    · have hi := hI0 k (by omega) (by simp [InI])
      have hj := hJ0 k (by omega) (by simp [InJ])
      cases r <;> simp [E, Esp, prg, hi, hj]
    · have e3 : ¬ k' ≤ k := by omega
      simp [E, Esp, e3, h]
  | blMain =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI trivial (fun h => h.elim) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => by simp [E, show k' ≤ L by omega]⟩)
      (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | blBud k hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => ?_⟩) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
      (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
    simp only [E, Esp]
    split_ifs <;> first | rfl | omega
  | inner k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side k true false)
    simp at hc
    simpa using inv_inner hI hc
  | innerZ k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => ?_⟩) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
      (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
    simp only [E]
    refine Esp_congr fun hk1 => ?_
    have hkK : k < K := by omega
    have h0 : m (.side k true false) = 0 :=
      hon_enter (hH k hkK) (.sj k s false) rfl rfl (fun _ h => by cases h)
    have h1 := hS0 k (by omega) true trivial
    simp [E, Esp] at h1
    simp [prg]; omega
  | sjF k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => by simp [E, prg]⟩)
      (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | restj k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side k true true)
    simp at hc
    simpa using inv_restj hI hc
  | restjZ k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => by simp [E, prg]⟩)
      (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | sjT k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side k false false)
    simp at hc
    have hj : k < K → m (.side k true true) = 0 := fun hkK =>
      hon_exit (hH k hkK) (.sj k s true) rfl rfl (fun _ h => by cases h)
    simpa using inv_sjT hI hc hj
  | outerIn k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => ?_⟩) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
      (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
    · simp only [E]
      refine Esp_congr fun hk1 => ?_
      have hj := hJ0 k (by omega) (by simp [InJ])
      simp [prg, hj]
  | outerZ k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    refine inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => ?_⟩) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
      (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
    simp only [E]
    refine Esp_congr fun hk1 => ?_
    have hkK : k < K := by omega
    have h0 : m (.side k false false) = 0 :=
      hon_enter (hH k hkK) (.si k s false) rfl rfl (fun _ h => by cases h)
    have h1 := hS0 k (by omega) false trivial
    simp [E, Esp] at h1
    have h2 : m (.side k false true) = B k := by omega
    simp [prg, h2]
  | siF k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => by simp [E, prg]⟩)
      (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | resti k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side k false true)
    simp at hc
    simpa using inv_resti hI hc
  | restiZ k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun k' hk' r => by simp [E, prg]⟩)
      (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | siT k s hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hi : k < K → m (.side k false true) = 0 := fun hkK =>
      hon_exit (hH k hkK) (.si k s true) rfl rfl (by
        intro ph h
        cases s with
        | comp r0 => cases r0 <;> simp [after] at h
        | bud b0 => cases b0 <;> simp [after] at h)
    have hj : k < K → m (.side k true true) = 0 := fun hkK => hJ0 k hkK (by simp [InJ])
    cases s with
    | comp r0 =>
      cases r0 <;> simp only [after]
      · refine inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
          (fun _ => ⟨trivial, fun k' hk' r => ?_⟩) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
          (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
        rcases lvl4 k' k with h | rfl | rfl | h
        · simp [E, Esp, h.le]
        · simp [E, Esp]
        · have h1 := hi (by omega)
          have h2 := hj (by omega)
          cases r <;> simp [E, Esp, prg, h1, h2, B_succ]
        · have e3 : ¬ k' ≤ k := by omega
          simp [E, Esp, e3, h]
      · refine inv_of_same hI (show k + 1 ≤ L by omega) (fun _ => ⟨trivial, upd_nil S⟩)
          (fun _ _ _ => by simp) (fun _ => ⟨trivial, fun k' hk' r => ?_⟩)
          (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
          (fun k' hk' h => by
            by_cases e : k' = k
            · subst e; exact Or.inr (hi hk')
            · exact Or.inl (by simp [InI]; omega))
        rcases lvl4 k' k with h | rfl | rfl | h
        · simp [E, Esp, h.le, show k' ≤ k + 1 by omega]
        · simp [E, Esp]
        · cases r <;> simp [E, Esp, prg, B_succ]
        · have e3 : ¬ k' ≤ k := by omega
          simp [E, Esp, e3, h, show ¬ k' ≤ k + 1 by omega]
    | bud b0 =>
      cases b0 <;> simp only [after]
      · refine inv_of_same hI hk (fun _ => ⟨trivial, upd_nil S⟩) (fun _ _ _ => by simp)
          (fun _ => ⟨trivial, fun k' hk' r => by simp [E, Esp]⟩)
          (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
          (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
      · refine inv_of_same hI (show k + 1 ≤ L by omega) (fun _ => ⟨trivial, upd_nil S⟩)
          (fun _ _ _ => by simp) (fun _ => ⟨trivial, fun k' hk' r => ?_⟩)
          (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega))
          (fun k' hk' h => by
            by_cases e : k' = k
            · subst e; exact Or.inr (hi hk')
            · exact Or.inl (by simp [InI]; omega))
        simp only [E, Esp]
        split_ifs <;> first | rfl | omega
  | zAA z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI (valid_zt hI.valid) (fun h => ⟨by cases z <;> exact h, upd_nil S⟩)
      (fun _ _ _ => by simp)
      (fun _ => ⟨by cases z <;> trivial, fun k' hk' r => by cases z <;> simp [E, prg]⟩)
      (fun _ _ h => Or.inl (by cases z <;> exact h))
      (fun _ _ h => Or.inl (by cases z <;> exact h))
  | zA'A z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side (z.lvl L) z.pr (!z.sd))
    simp at hc
    simpa only [Bool.not_not, upd_nil] using inv_zmove (ph' := .A) hKL hI hc
  | zAB z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI (valid_zt hI.valid) (fun h => ⟨by cases z <;> exact h, upd_nil S⟩)
      (fun _ _ _ => by simp)
      (fun _ => ⟨by cases z <;> trivial, fun k' hk' r => by cases z <;> simp [E, prg]⟩)
      (fun _ _ h => Or.inl (by cases z <;> exact h))
      (fun _ _ h => Or.inl (by cases z <;> exact h))
  | zBB z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI (valid_zt hI.valid) (fun h => ⟨by cases z <;> exact h, upd_nil S⟩)
      (fun _ _ _ => by simp)
      (fun _ => ⟨by cases z <;> trivial, fun k' hk' r => by cases z <;> simp [E, prg]⟩)
      (fun _ _ h => Or.inl (by cases z <;> exact h))
      (fun _ _ h => Or.inl (by cases z <;> exact h))
  | zB'B z =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side (z.lvl L) z.pr z.sd)
    simp at hc
    simpa only [upd_nil] using inv_zmove (ph' := .B) hKL hI hc
  | mNop t ht hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI trivial (fun h => h.elim) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun _ _ _ => by simp [E]⟩)
      (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | mInc t ht r hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side L r false)
    simp at hc
    exact inv_mmove (b := false) hKL hI hc
  | mDec t ht r hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    have hc := hdl (.side L r true)
    simp at hc
    exact inv_mmove (b := true) hKL hI hc
  | mZ i t ht r hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI ⟨t, ht, hop⟩ (fun h => h.elim) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun _ _ _ => by simp [E]⟩)
      (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | mExit i t ht r hop =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI trivial (fun h => h.elim) (fun _ _ _ => by simp)
      (fun _ => ⟨trivial, fun _ _ _ => by simp [E]⟩)
      (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | toDrain =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI trivial (fun h => h.elim) (fun _ _ _ => by simp)
      (fun h => h.elim) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))
  | drain k r hk =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    simpa only [upd_nil] using inv_drain (k := k) (r := r) hI
  | toDone =>
    dsimp only at hsrc hdl hH ⊢; subst hsrc
    exact inv_of_same hI trivial (fun h => h.elim) (fun _ _ _ => by simp)
      (fun h => h.elim) (fun _ _ h => Or.inl (by revert h; simp [InJ]; try omega)) (fun _ _ h => Or.inl (by revert h; simp [InI]; try omega))

end Amp

end HTN
