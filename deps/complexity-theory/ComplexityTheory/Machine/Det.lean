import ComplexityTheory.Machine.SimMain
/-!
# Deterministic programs are simulated by deterministic Turing machines

The transitions of the simulating machine `HTN.Mach.simM` branch only at `guess` and `choose`
instructions.  For a program without them (`HTN.Mach.NoChoice`), the states that never perform a
`guess` (`HTN.Mach.QS.NG`) are closed under the transitions and have at most one transition each
(`HTN.Mach.ng_closed`, `HTN.Mach.length_δ_le`).

**Main theorem** (`HTN.Mach.exists_tm_det`): `HTN.Mach.exists_tm`, with a machine that is in
addition deterministic (at most one transition per state and symbol).
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM

/-- An action other than guessing. -/
def Act.NG : Act → Prop
  | .guess => False
  | _ => True

/-- A phase that does not guess. -/
def Phase.NG : Phase → Prop
  | .scan act _ _ _ => act.NG
  | .top act _ _ => act.NG
  | _ => True

/-- A state that does not guess. -/
def QS.NG : QS → Prop
  | .base ph => ph.NG
  | .mv _ _ tgt => tgt.NG

/-- A program without the nondeterministic instructions `guess` and `choose`. -/
def NoChoice (C : List Ins) : Prop := ∀ ins ∈ C, (∀ k, ins ≠ .guess k) ∧ ∀ a b, ins ≠ .choose a b

theorem mvTo_ng {right : Bool} {r : ℕ} {tgt : Phase} (h : tgt.NG) : (mvTo right r tgt).NG := by
  cases r <;> exact h

theorem contPh_ng (cont : Option ℕ) : (contPh cont).NG := by
  cases cont <;> trivial

variable {C : List Ins} {K kin : ℕ}

/-- **The non-guessing states are closed under the transitions** of a program without choice. -/
theorem ng_closed (hC : NoChoice C) {q : QS} (hq : q.NG) {γ : Sym} {t : Tr}
    (ht : t ∈ δ C K kin q γ) : t.1.NG := by
  cases q with
  | mv right r tgt =>
    simp only [δ, List.mem_singleton] at ht
    subst ht
    exact mvTo_ng hq
  | base ph =>
    simp only [δ] at ht
    cases ph with
    | exec pc =>
      simp only [phaseTr, execTr] at ht
      rcases hc : C[pc]? with _ | ins
      · rw [hc] at ht; simp at ht
      have hmem := (hC ins (List.mem_of_getElem? hc))
      rw [hc] at ht
      cases ins with
      | push k b =>
        simp only [startTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      | pop k =>
        simp only [startTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      | br k a₀ aF aT =>
        simp only [startTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      | jmp a => simp only [List.mem_singleton] at ht; subst ht; trivial
      | guess k => exact absurd rfl (hmem.1 k)
      | choose a₁ a₂ => exact absurd rfl (hmem.2 a₁ a₂)
      | accept => simp at ht
    | p0 =>
      rcases γ with _ | b
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; trivial
    | pEnd b =>
      rcases γ with _ | c
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; trivial
    | pMark ob =>
      rcases ob with _ | b
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; trivial
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
    | pre => simp only [phaseTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
    | pChk =>
      rcases γ with _ | c
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; trivial
    | pSeek =>
      rcases γ with _ | c
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; trivial
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; trivial
    | pTake =>
      rcases γ with _ | b
      · simp [phaseTr] at ht
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; trivial
    | pRet b =>
      rcases γ with _ | c
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; trivial
    | scan act k cont first =>
      rcases γ with _ | c
      · simp only [phaseTr] at ht
        cases act with
        | push b =>
          simp only [scanBlankTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
        | guess => exact absurd hq id
        | pop =>
          simp only [scanBlankTr] at ht
          split_ifs at ht <;>
            (simp only [List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG]))
        | br a₀ aF aT =>
          simp only [scanBlankTr] at ht
          split_ifs at ht <;>
            (simp only [List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG]))
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; exact mvTo_ng hq
    | top act k cont =>
      simp only [phaseTr] at ht
      cases act with
      | pop => simp only [topTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      | br a₀ aF aT =>
        rcases γ with _ | b
        · simp [topTr] at ht
        · simp only [topTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      | push b => simp [topTr] at ht
      | guess => simp [topTr] at ht
    | rScan cont =>
      rcases γ with _ | _ | _
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; (dsimp only; refine mvTo_ng ?_; simp [Phase.NG, Act.NG])
      · simp only [phaseTr, List.mem_singleton] at ht; subst ht; exact contPh_ng cont

/-- **A non-guessing state has at most one transition** in a program without choice. -/
theorem length_δ_le (hC : NoChoice C) {q : QS} (hq : q.NG) (γ : Sym) :
    (δ C K kin q γ).length ≤ 1 := by
  cases q with
  | mv right r tgt => simp [δ]
  | base ph =>
    simp only [δ]
    cases ph with
    | exec pc =>
      simp only [phaseTr, execTr]
      rcases hc : C[pc]? with _ | ins
      · simp
      have hmem := (hC ins (List.mem_of_getElem? hc))
      cases ins with
      | guess k => exact absurd rfl (hmem.1 k)
      | choose a₁ a₂ => exact absurd rfl (hmem.2 a₁ a₂)
      | _ => simp [startTr]
    | scan act k cont first =>
      rcases γ with _ | c
      · simp only [phaseTr]
        cases act with
        | guess => exact absurd hq id
        | _ => (simp only [scanBlankTr]; try split_ifs) <;> simp
      · simp [phaseTr]
    | top act k cont =>
      simp only [phaseTr]
      cases act <;> rcases γ with _ | b <;> simp [topTr]
    | rScan cont => rcases γ with _ | _ | _ <;> simp [phaseTr]
    | pMark ob => rcases ob with _ | b <;> simp [phaseTr]
    | _ => rcases γ with _ | _ <;> simp [phaseTr]

theorem subsingleton_of_length_le {α : Type*} {l : List α} (h : l.length ≤ 1) :
    {t | t ∈ l}.Subsingleton := by
  match l, h with
  | [], _ => intro a ha; simp at ha
  | [x], _ => intro a ha b hb; simp only [Set.mem_setOf_eq, List.mem_singleton] at ha hb; rw [ha, hb]

/-- **Deterministic programs are simulated by deterministic single-tape Turing machines** with
finitely many states. -/
theorem exists_tm_det (C : List Ins) (K kin : ℕ) (hwf : ProgWF C K) (hk : kin < K)
    (hC : NoChoice C) :
    ∃ (k : ℕ) (M : NTM (Fin k) (Option Bool)), M.blank = none ∧
      (∀ q γ, (M.step q γ).Subsingleton) ∧ ∀ x : List Bool,
      ((∃ N c, M.Reaches N (M.initConfig (x.map some)) c ∧ c.state ∈ M.accept) →
        ∃ T σ', SReach C T ⟨0, inStore kin x⟩ σ' ∧ Accepting C σ') ∧
      (∀ T H σ', x.length ≤ H → SReachP C (fun τ => Hgt K H τ.S) T ⟨0, inStore kin x⟩ σ' →
        Accepting C σ' →
        M.AcceptsWithin (x.map some)
            ((x.length + 1) * (6 * (x.length + 2) * (K + 1)) + T * (3 * (H + 2) * (K + 1))) ∧
          M.AcceptsInSpace (x.map some) (x.length + 2 + (H + 1) * (K + 1))) := by
  set N := simM C K kin
  set R : Set QS := {q | q.Bnd (bigB C K kin) ∧ q.NG}
  have h₀ : N.init ∈ R := ⟨trivial, trivial⟩
  have hcl : ∀ q ∈ R, ∀ γ t, t ∈ N.step q γ → t.1 ∈ R := fun q hq γ t ht =>
    ⟨bnd_closed hk hq.1 ht, ng_closed hC hq.2 ht⟩
  letI : Fintype R := ((finite_qsBnd (bigB C K kin)).subset fun _ h => h.1).fintype
  set N' := N.restrict R h₀
  set e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  refine ⟨Fintype.card R, NTM.relabel e N', rfl, fun q γ => ?_, fun x => ⟨?_, ?_⟩⟩
  · rintro _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩
    have hs := subsingleton_of_length_le (length_δ_le (K := K) (kin := kin) hC
      (e.symm q).2.2 γ) ht₁.2 ht₂.2
    have h1 : t₁.1 = t₂.1 := Subtype.ext (congrArg Prod.fst hs)
    have h2 : t₁.2 = t₂.2 := Prod.ext (congrArg (·.2.1) hs) (congrArg (·.2.2) hs)
    simp only [h1, h2]
  · rintro ⟨n, c, hr, hc⟩
    have h1 := NTM.reaches_of_relabel e N' hr
    have h2 := NTM.reaches_of_restrict (N := N) h1
    refine (simM_spec hwf hk x).1 ⟨n, (NTM.Config.relabel e.symm c).unrestrict, ?_, hc⟩
    simpa [NTM.Config.relabel, NTM.relabel, NTM.initConfig, Config.unrestrict, N', NTM.restrict]
      using h2
  · intro T H σ' hH hr hacc
    obtain ⟨m, hm, c, hrc, hc⟩ := (simM_spec hwf hk x).2 T H σ' hH hr hacc
    have hinit : (N'.initConfig (x.map some)).unrestrict = N.initConfig (x.map some) := rfl
    rw [← hinit] at hrc
    obtain ⟨hcR, hr'⟩ := NTM.restrict_reachesSpace (N := N) h₀ hcl hrc
    have hr'' := NTM.relabel_reachesSpace e N' hr'
    have hacc' : (NTM.Config.relabel e (⟨⟨c.state, hcR⟩, c.head, c.tape⟩ : Config R (Option Bool))).state
        ∈ (NTM.relabel e N').accept := by
      simpa [NTM.Config.relabel, NTM.relabel, N', NTM.restrict] using hc
    have hinit' : NTM.Config.relabel e (N'.initConfig (x.map some)) =
        (NTM.relabel e N').initConfig (x.map some) := rfl
    rw [hinit'] at hr''
    exact ⟨⟨m, hm, _, NTM.ReachesSpace.reaches _ hr'', hacc'⟩, ⟨m, _, hr'', hacc'⟩⟩

end Mach

end HTN
