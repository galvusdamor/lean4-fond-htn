import ComplexityTheory.TOtoHD.Amp.Honest
/-!
# The amplifier: soundness

An accepting run of the vector addition system is honest (`honest_run`); reading the counters
off the `true` sides of the two pairs of level `L` turns it into an accepting run of the counter
machine whose counters stay below `B L` (`sound`).
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

/-- The counter values encoded by a marking. -/
def cv (L : ℕ) (m : Mk) : Bool → ℕ := fun r => m (.side L r true)

/-- Reset counter `r`. -/
def zv (r : Bool) (v : Bool → ℕ) : Bool → ℕ := Function.update v r 0

/-- What a configuration of an honest run tells about the counter machine. -/
def Claim (P : CM Q Φ) (L : ℕ) (s0 : Finset Φ) (y : ACfg Q Φ) : Prop :=
  (∀ q, y.1 = .main q →
    Relation.ReflTransGen (CStepB P (B L)) (P.q0, s0, fun _ => 0) (q, y.2.1, cv L y.2.2)) ∧
  (∀ i r ph, y.1 = .zt (.m i r) ph → ∃ t, P.trs[i]? = some t ∧ t.op = .zero r ∧
    (∀ f ∈ t.pre, f ∈ y.2.1) ∧
    Relation.ReflTransGen (CStepB P (B L)) (P.q0, s0, fun _ => 0)
      (t.src, y.2.1, zv r (cv L y.2.2))) ∧
  (y.1 = .drain ∨ y.1 = .done →
    Relation.ReflTransGen (CStepB P (B L)) (P.q0, s0, fun _ => 0) (P.qf, y.2.1, cv L y.2.2))

theorem claim_vac {P : CM Q Φ} {L : ℕ} {s0 : Finset Φ} {y : ACfg Q Φ} (hp : Pre y.1) :
    Claim P L s0 y := by
  obtain ⟨l, S, m⟩ := y
  refine ⟨fun q h => ?_, fun i r ph h => ?_, fun h => ?_⟩
  · dsimp only at h hp; subst h; exact hp.elim
  · dsimp only at h hp; subst h; exact hp.elim
  · dsimp only at h hp; rcases h with rfl | rfl <;> exact hp.elim

theorem cv_le {P : CM Q Φ} {L : ℕ} {s0 : Finset Φ} {q : Q} {S : Finset Φ} {m : Mk}
    (hI : Inv P L L s0 (.main q, S, m)) (r : Bool) : cv L m r ≤ B L := by
  have := hI.sum L le_rfl r trivial
  simp only [E] at this
  simp only [cv]; omega

theorem zv_cv_mv {L : ℕ} {m : Mk} {dl il : List Pl} {r : Bool}
    (h : ∀ r', r' ≠ r → dl.count (.side L r' true) = 0 ∧ il.count (.side L r' true) = 0) :
    zv r (cv L (mv m dl il)) = zv r (cv L m) := by
  funext r'
  by_cases e : r' = r
  · subst e; simp [zv]
  · simp [zv, cv, mv, Function.update, e, (h r' e).1, (h r' e).2]

theorem cv_mv_of {L : ℕ} {m : Mk} {dl il : List Pl}
    (h : ∀ r, dl.count (.side L r true) = 0 ∧ il.count (.side L r true) = 0) :
    cv L (mv m dl il) = cv L m := by
  funext r; simp [cv, mv, (h r).1, (h r).2]

/-- **A step of an honest run preserves the claim.** -/
theorem claim_step {P : CM Q Φ} {L : ℕ} {s0 : Finset Φ} {x y : ACfg Q Φ}
    (hx : Claim P L s0 x) (hs : AStep P L x y) (hH : ∀ k ≤ L, Hon L k x y)
    (hIx : Inv P L L s0 x) (hIy : Inv P L L s0 y) : Claim P L s0 y := by
  unfold Claim at hx
  obtain ⟨ρ, hρ, hsrc, hpre, hdl, rfl⟩ := hs
  obtain ⟨l, S, m⟩ := x
  obtain ⟨hx1, hx2, hx3⟩ := hx
  dsimp only at hsrc hpre hdl hH hIx hIy hx1 hx2 hx3 ⊢
  cases hρ with
  | start => exact claim_vac (y := (_, _, _)) trivial
  | bl0 => exact claim_vac trivial
  | blNext k hk => exact claim_vac trivial
  | blBud k hk => exact claim_vac trivial
  | inner k s hk => exact claim_vac trivial
  | innerZ k s hk => exact claim_vac trivial
  | sjF k s hk => exact claim_vac trivial
  | restj k s hk => exact claim_vac trivial
  | restjZ k s hk => exact claim_vac trivial
  | sjT k s hk => exact claim_vac trivial
  | outerIn k s hk => exact claim_vac trivial
  | outerZ k s hk => exact claim_vac trivial
  | siF k s hk => exact claim_vac trivial
  | resti k s hk => exact claim_vac trivial
  | restiZ k s hk => exact claim_vac trivial
  | siT k s hk =>
    rcases s with r0 | b0
    · cases r0 <;> exact claim_vac trivial
    · cases b0 <;> exact claim_vac trivial
  | blMain =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    have hS := hIx.facts trivial
    have hz : ∀ r, m (.side L r true) = 0 := fun r => hIx.zero r trivial
    dsimp only at hS
    subst hS
    refine ⟨fun q h => ?_, fun i r ph h => (by cases h), fun h => by rcases h with h | h <;> cases h⟩
    cases h
    have : cv L (mv m [] []) = fun _ => 0 := by funext r; simp [cv, hz]
    rw [this, upd_nil]
  | mNop t ht hop =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    refine ⟨fun q h => ?_, fun i r ph h => (by cases h), fun h => by rcases h with h | h <;> cases h⟩
    cases h
    refine .tail (hx1 t.src rfl) ⟨?_, cv_le hIy⟩
    have hv : cv L (mv m [] []) = cv L m := cv_mv_of (fun _ => by simp)
    exact CStep.mk t ht S _ _ hpre (by rw [hop]; exact hv)
  | mInc t ht r hop =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    refine ⟨fun q h => ?_, fun i r ph h => (by cases h), fun h => by rcases h with h | h <;> cases h⟩
    cases h
    refine .tail (hx1 t.src rfl) ⟨?_, cv_le hIy⟩
    refine CStep.mk t ht S _ _ hpre ?_
    rw [hop]
    funext r'
    by_cases e : r' = r
    · subst e; simp [cv]
    · simp [cv, Function.update, e, Ne.symm e]
  | mDec t ht r hop =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    have hc := hdl (.side L r true)
    simp at hc
    refine ⟨fun q h => ?_, fun i r ph h => (by cases h), fun h => by rcases h with h | h <;> cases h⟩
    cases h
    refine .tail (hx1 t.src rfl) ⟨?_, cv_le hIy⟩
    refine CStep.mk t ht S _ _ hpre ?_
    rw [hop]
    refine ⟨hc, ?_⟩
    funext r'
    by_cases e : r' = r
    · subst e; simp [cv]
    · simp [cv, Function.update, e, Ne.symm e]
  | mZ i t ht r hop =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    have h0 : m (.side L r true) = 0 :=
      hon_enter (hH L le_rfl) (.m i r) rfl rfl (fun _ h => by cases h)
    refine ⟨fun q h => (by cases h), fun i' r' ph h => ?_, fun h => by rcases h with h | h <;> cases h⟩
    cases h
    rw [upd_nil]
    refine ⟨t, ht, hop, hpre, ?_⟩
    have : zv r (cv L (mv m [Pl.d L] [])) = cv L m := by
      funext r'
      by_cases e : r' = r
      · subst e; simp [zv, cv, h0]
      · simp [zv, cv, Function.update, e]
    rw [this]
    exact hx1 t.src rfl
  | mExit i t ht r hop =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    obtain ⟨t', ht', -, hpre', hrun⟩ := hx2 i r .B rfl
    rw [ht] at ht'
    cases ht'
    have h0 : m (.side L r true) = 0 :=
      hon_exit (hH L le_rfl) (.m i r) rfl rfl (fun _ h => by cases h)
    have hz : zv r (cv L m) = cv L m := by
      funext r'
      by_cases e : r' = r
      · subst e; simp [zv, cv, h0]
      · simp [zv, Function.update, e]
    rw [hz] at hrun
    refine ⟨fun q h => ?_, fun i r ph h => (by cases h), fun h => by rcases h with h | h <;> cases h⟩
    cases h
    refine .tail hrun ⟨?_, cv_le hIy⟩
    have hv : cv L (mv m [] []) = cv L m := cv_mv_of (fun _ => by simp)
    refine CStep.mk t (List.mem_of_getElem? ht) S _ _ hpre' ?_
    rw [hop]
    exact ⟨h0, hv⟩
  | toDrain =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    refine ⟨fun q h => (by cases h), fun i r ph h => (by cases h), fun _ => ?_⟩
    have hv : cv L (mv m [] []) = cv L m := cv_mv_of (fun _ => by simp)
    rw [hv, upd_nil]
    exact hx1 P.qf rfl
  | drain k r hk =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    refine ⟨fun q h => (by cases h), fun i r ph h => (by cases h), fun _ => ?_⟩
    have hv : cv L (mv m [Pl.side k r false] []) = cv L m := cv_mv_of (fun _ => by simp)
    rw [hv, upd_nil]
    exact hx3 (Or.inl rfl)
  | toDone =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc; unfold Claim; dsimp only
    refine ⟨fun q h => (by cases h), fun i r ph h => (by cases h), fun _ => ?_⟩
    have hv : cv L (mv m [] []) = cv L m := cv_mv_of (fun _ => by simp)
    rw [hv, upd_nil]
    exact hx3 (Or.inl rfl)
  | zAA z =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩
    · exact claim_vac (y := (_, _, _)) trivial
    · exact claim_vac (y := (_, _, _)) trivial
    · unfold Claim; dsimp only
      refine ⟨fun q h => (by cases h), fun i' r' ph h => ?_,
        fun h => (by rcases h with h | h <;> cases h)⟩
      cases h
      obtain ⟨t, ht, hop, hpre', hrun⟩ := hx2 i r _ rfl
      rw [upd_nil]
      refine ⟨t, ht, hop, hpre', ?_⟩
      rw [zv_cv_mv (fun r' e => by simp [ZI.lvl, ZI.pr, ZI.sd, e, Ne.symm e])]
      exact hrun
  | zA'A z =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩
    · exact claim_vac (y := (_, _, _)) trivial
    · exact claim_vac (y := (_, _, _)) trivial
    · unfold Claim; dsimp only
      refine ⟨fun q h => (by cases h), fun i' r' ph h => ?_,
        fun h => (by rcases h with h | h <;> cases h)⟩
      cases h
      obtain ⟨t, ht, hop, hpre', hrun⟩ := hx2 i r _ rfl
      rw [upd_nil]
      refine ⟨t, ht, hop, hpre', ?_⟩
      rw [zv_cv_mv (fun r' e => by simp [ZI.lvl, ZI.pr, ZI.sd, e, Ne.symm e])]
      exact hrun
  | zAB z =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩
    · exact claim_vac (y := (_, _, _)) trivial
    · exact claim_vac (y := (_, _, _)) trivial
    · unfold Claim; dsimp only
      refine ⟨fun q h => (by cases h), fun i' r' ph h => ?_,
        fun h => (by rcases h with h | h <;> cases h)⟩
      cases h
      obtain ⟨t, ht, hop, hpre', hrun⟩ := hx2 i r _ rfl
      rw [upd_nil]
      refine ⟨t, ht, hop, hpre', ?_⟩
      rw [zv_cv_mv (fun r' e => by simp [ZI.lvl, ZI.pr, ZI.sd, e, Ne.symm e])]
      exact hrun
  | zBB z =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩
    · exact claim_vac (y := (_, _, _)) trivial
    · exact claim_vac (y := (_, _, _)) trivial
    · unfold Claim; dsimp only
      refine ⟨fun q h => (by cases h), fun i' r' ph h => ?_,
        fun h => (by rcases h with h | h <;> cases h)⟩
      cases h
      obtain ⟨t, ht, hop, hpre', hrun⟩ := hx2 i r _ rfl
      rw [upd_nil]
      refine ⟨t, ht, hop, hpre', ?_⟩
      rw [zv_cv_mv (fun r' e => by simp [ZI.lvl, ZI.pr, ZI.sd, e, Ne.symm e])]
      exact hrun
  | zB'B z =>
    dsimp only at hsrc hpre hdl hH hIy ⊢; subst hsrc
    rcases z with ⟨k, s, b⟩ | ⟨k, s, b⟩ | ⟨i, r⟩
    · exact claim_vac (y := (_, _, _)) trivial
    · exact claim_vac (y := (_, _, _)) trivial
    · unfold Claim; dsimp only
      refine ⟨fun q h => (by cases h), fun i' r' ph h => ?_,
        fun h => (by rcases h with h | h <;> cases h)⟩
      cases h
      obtain ⟨t, ht, hop, hpre', hrun⟩ := hx2 i r _ rfl
      rw [upd_nil]
      refine ⟨t, ht, hop, hpre', ?_⟩
      rw [zv_cv_mv (fun r' e => by simp [ZI.lvl, ZI.pr, ZI.sd, e, Ne.symm e])]
      exact hrun

/-- **Soundness of the amplifier**: an accepting run of the vector addition system yields an
accepting run of the counter machine with counters at most `B L`. -/
theorem sound {P : CM Q Φ} {L : ℕ} {s0 : Finset Φ} {g : List Φ} (h : AAcc P L s0 g) :
    CAcc P (B L) s0 g := by
  obtain ⟨S, hrun, hg⟩ := h
  have hr := honest_run hrun
  have key : ∀ y, Relation.ReflTransGen (fun x y => AStep P L x y ∧ (∀ k ≤ L, Hon L k x y) ∧
      Inv P L L s0 x ∧ Inv P L L s0 y) (ainit s0) y → Claim P L s0 y := by
    intro y hy
    induction hy with
    | refl => exact claim_vac trivial
    | tail _ hbc ih => exact claim_step ih hbc.1 hbc.2.1 hbc.2.2.1 hbc.2.2.2
  have := (key _ hr).2.2 (Or.inr rfl)
  refine ⟨S, ?_, hg⟩
  have hv : cv L (fun _ => 0) = fun _ => 0 := rfl
  rw [hv] at this
  exact this

end Amp

end HTN
