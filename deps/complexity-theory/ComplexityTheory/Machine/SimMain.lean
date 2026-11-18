import ComplexityTheory.Machine.SimPre
import ComplexityTheory.TM.Theory.SepGuess
/-!
# Stack machines are simulated by single-tape Turing machines

**Main theorem** (`HTN.Mach.exists_tm`). For every stack machine `C` using the stacks
`0, …, K - 1` and every input stack `kin < K` there is a nondeterministic single-tape Turing
machine `M` with finitely many states (`Fin k`) over the alphabet `Option Bool` such that, on
every input `x`,

* if `M` accepts `x` at all, then `C` accepts from address `0` with `x` (reversed) on stack
  `kin` and all other stacks empty (`HTN.Mach.inStore`);
* if `C` accepts from there by a run of `T` steps along which all stacks have height at most
  `H ≥ |x|`, then `M` accepts `x` within `(|x| + 1) * (6 * (|x| + 2) * (K + 1)) +
  T * (3 * (H + 2) * (K + 1))` steps, and within the space `|x| + 2 + (H + 1) * (K + 1)`.

`M` is `HTN.Mach.simM` restricted to the finitely many states whose numbers are bounded
(`HTN.Mach.QS.Bnd`), which are closed under its transitions, relabelled by `Fin k`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM

/-! ### Bounded states -/

/-- The largest number occurring in an instruction. -/
def Ins.maxN : Ins → ℕ
  | .push k _ => k
  | .pop k => k
  | .br k a₀ aF aT => max k (max a₀ (max aF aT))
  | .jmp a => a
  | .guess k => k
  | .choose a₁ a₂ => max a₁ a₂
  | .accept => 0

/-- The largest number occurring in a program. -/
def maxNum (C : List Ins) : ℕ := C.foldr (fun ins m => max ins.maxN m) 0

theorem maxN_le {C : List Ins} {pc : ℕ} {ins : Ins} (h : C[pc]? = some ins) :
    ins.maxN ≤ maxNum C := by
  have hm : ins ∈ C := List.mem_of_getElem? h
  clear h
  induction C with
  | nil => simp at hm
  | cons a C ih =>
    simp only [maxNum, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hm with rfl | hm
    · exact le_max_left _ _
    · exact le_trans (ih hm) (le_max_right _ _)

/-- An action with bounded numbers. -/
def Act.Bnd (B : ℕ) : Act → Prop
  | .br a₀ aF aT => a₀ ≤ B ∧ aF ≤ B ∧ aT ≤ B
  | _ => True

/-- A continuation with a bounded number. -/
def optBnd (B : ℕ) : Option ℕ → Prop
  | some a => a ≤ B
  | none => True

/-- A phase with bounded numbers. -/
def Phase.Bnd (B : ℕ) : Phase → Prop
  | .exec pc => pc ≤ B
  | .scan act k cont _ => act.Bnd B ∧ k ≤ B ∧ optBnd B cont
  | .top act k cont => act.Bnd B ∧ k ≤ B ∧ optBnd B cont
  | .rScan cont => optBnd B cont
  | _ => True

/-- A state with bounded numbers. -/
def QS.Bnd (B : ℕ) : QS → Prop
  | .base ph => ph.Bnd B
  | .mv _ r tgt => r ≤ B ∧ tgt.Bnd B

theorem mvTo_bnd {B : ℕ} {right : Bool} {r : ℕ} {tgt : Phase} (hr : r ≤ B + 1) (ht : tgt.Bnd B) :
    (mvTo right r tgt).Bnd B := by
  cases r with
  | zero => exact ht
  | succ r => exact ⟨by omega, ht⟩

/-- The bound for the states of the simulation of `C`. -/
def bigB (C : List Ins) (K kin : ℕ) : ℕ := C.length + K + kin + maxNum C + 2

variable {C : List Ins} {K kin : ℕ}

theorem contPh_bnd {B : ℕ} {cont : Option ℕ} (h : optBnd B cont) : (contPh cont).Bnd B := by
  cases cont with
  | none => trivial
  | some pc => exact h

/-- **The bounded states are closed under the transitions.** -/
theorem bnd_closed (hk : kin < K) {q : QS} (hq : q.Bnd (bigB C K kin)) {γ : Sym} {t : Tr}
    (ht : t ∈ δ C K kin q γ) : t.1.Bnd (bigB C K kin) := by
  set B := bigB C K kin with hB
  have hK : K + 1 ≤ B + 1 := by rw [hB]; unfold bigB; omega
  have hkin : kin ≤ B := by rw [hB]; unfold bigB; omega
  cases q with
  | mv right r tgt =>
    simp only [δ, List.mem_singleton] at ht
    (subst ht; dsimp only)
    exact mvTo_bnd (by have := hq.1; omega) hq.2
  | base ph =>
    simp only [δ] at ht
    cases ph with
    | exec pc =>
      simp only [phaseTr, execTr] at ht
      rcases hc : C[pc]? with _ | ins
      · rw [hc] at ht; simp at ht
      have hpc : pc < C.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hc; cases hc
      have hmax := maxN_le hc
      have hL : pc + 1 ≤ B := by rw [hB]; unfold bigB; omega
      have hM : maxNum C ≤ B := by rw [hB]; unfold bigB; omega
      rw [hc] at ht
      cases ins with
      | push k b =>
        simp only [startTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        exact mvTo_bnd (by omega) ⟨trivial, by simp [Ins.maxN] at hmax; omega, hL⟩
      | pop k =>
        simp only [startTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        exact mvTo_bnd (by omega) ⟨trivial, by simp [Ins.maxN] at hmax; omega, hL⟩
      | br k a₀ aF aT =>
        simp only [startTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        simp only [Ins.maxN, max_le_iff] at hmax
        exact mvTo_bnd (by omega) ⟨⟨by omega, by omega, by omega⟩, by omega, trivial⟩
      | jmp a =>
        simp only [List.mem_singleton] at ht; (subst ht; dsimp only)
        simp only [Ins.maxN] at hmax
        show a ≤ B; omega
      | guess k =>
        simp only [startTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        exact mvTo_bnd (by omega) ⟨trivial, by simp [Ins.maxN] at hmax; omega, hL⟩
      | choose a₁ a₂ =>
        simp only [Ins.maxN, max_le_iff] at hmax
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · show a₁ ≤ B; omega
        · show a₂ ≤ B; omega
      | accept => simp at ht
    | p0 =>
      cases γ <;> simp only [phaseTr, List.mem_singleton] at ht <;> (subst ht; dsimp only)
      · exact mvTo_bnd (by omega) trivial
      · trivial
    | pEnd b =>
      cases γ <;> simp only [phaseTr, List.mem_singleton] at ht <;> (subst ht; dsimp only)
      · exact mvTo_bnd (by omega) trivial
      · trivial
    | pMark ob =>
      cases ob <;> simp only [phaseTr, List.mem_singleton] at ht <;> (subst ht; dsimp only)
      · show 0 ≤ B; omega
      · exact mvTo_bnd (by omega) ⟨trivial, hkin, trivial⟩
    | pre =>
      simp only [phaseTr, List.mem_singleton] at ht; (subst ht; dsimp only)
      exact mvTo_bnd (by omega) trivial
    | pChk =>
      cases γ <;> simp only [phaseTr, List.mem_singleton] at ht <;> (subst ht; dsimp only)
      · exact mvTo_bnd (by omega) (show 0 ≤ B by omega)
      · trivial
    | pSeek =>
      cases γ <;> simp only [phaseTr, List.mem_singleton] at ht <;> (subst ht; dsimp only) <;> trivial
    | pTake =>
      cases γ <;> simp only [phaseTr, List.mem_singleton, List.not_mem_nil] at ht
      (subst ht; dsimp only); trivial
    | pRet b =>
      cases γ <;> simp only [phaseTr, List.mem_singleton] at ht <;> (subst ht; dsimp only)
      · exact mvTo_bnd (by omega) ⟨trivial, hkin, trivial⟩
      · trivial
    | scan act k cont first =>
      obtain ⟨ha, hk', hc⟩ := hq
      cases γ with
      | some c =>
        simp only [phaseTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        exact mvTo_bnd (by omega) ⟨ha, hk', hc⟩
      | none =>
        simp only [phaseTr, scanBlankTr] at ht
        cases act with
        | push b =>
          simp only [List.mem_singleton] at ht; (subst ht; dsimp only)
          exact mvTo_bnd (by omega) hc
        | guess =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl <;> exact mvTo_bnd (by omega) hc
        | pop =>
          cases first <;> simp only [List.mem_singleton, if_true, if_false,
            Bool.false_eq_true] at ht <;> (subst ht; dsimp only)
          · exact mvTo_bnd (by omega) ⟨trivial, hk', hc⟩
          · exact mvTo_bnd (by omega) hc
        | br a₀ aF aT =>
          cases first <;> simp only [List.mem_singleton, if_true, if_false,
            Bool.false_eq_true] at ht <;> (subst ht; dsimp only)
          · exact mvTo_bnd (by omega) ⟨ha, hk', hc⟩
          · exact mvTo_bnd (by omega) (show a₀ ≤ B from ha.1)
    | top act k cont =>
      obtain ⟨ha, hk', hc⟩ := hq
      simp only [phaseTr] at ht
      cases act with
      | pop =>
        simp only [topTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        exact mvTo_bnd (by omega) hc
      | br a₀ aF aT =>
        cases γ with
        | none => simp [topTr] at ht
        | some b =>
          simp only [topTr, List.mem_singleton] at ht; (subst ht; dsimp only)
          refine mvTo_bnd (by omega) ?_
          show (if b = true then aT else aF) ≤ B
          split_ifs
          · exact ha.2.2
          · exact ha.2.1
      | push b => simp [topTr] at ht
      | guess => simp [topTr] at ht
    | rScan cont =>
      rcases γ with _ | _ | _
      · simp only [phaseTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        exact mvTo_bnd (by omega) hq
      · simp only [phaseTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        exact mvTo_bnd (by omega) hq
      · simp only [phaseTr, List.mem_singleton] at ht; (subst ht; dsimp only)
        exact contPh_bnd hq

/-! ### Finitely many bounded states -/

theorem finite_optBnd (B : ℕ) : {o : Option ℕ | optBnd B o}.Finite := by
  refine ((Set.finite_Iic B).image some |>.insert none).subset ?_
  rintro (_ | a) h
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨a, h, rfl⟩

theorem finite_actBnd (B : ℕ) : {a : Act | a.Bnd B}.Finite := by
  refine (((Set.finite_range Act.push).union (Set.finite_singleton Act.guess)).union
    ((Set.finite_singleton Act.pop).union
      (((Set.finite_Iic B).prod ((Set.finite_Iic B).prod (Set.finite_Iic B))).image
        fun t => Act.br t.1 t.2.1 t.2.2))).subset ?_
  rintro (b | _ | _ | ⟨a₀, aF, aT⟩) h
  · exact Or.inl (Or.inl ⟨b, rfl⟩)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨(a₀, aF, aT), ⟨h.1, h.2.1, h.2.2⟩, rfl⟩)

theorem finite_phaseBnd (B : ℕ) : {p : Phase | p.Bnd B}.Finite := by
  have hscan : ((fun t : Act × ℕ × Option ℕ × Bool => Phase.scan t.1 t.2.1 t.2.2.1 t.2.2.2) ''
      ({a | a.Bnd B} ×ˢ Set.Iic B ×ˢ {o | optBnd B o} ×ˢ Set.univ)).Finite :=
    ((finite_actBnd B).prod ((Set.finite_Iic B).prod ((finite_optBnd B).prod
      Set.finite_univ))).image _
  have htop : ((fun t : Act × ℕ × Option ℕ => Phase.top t.1 t.2.1 t.2.2) ''
      ({a | a.Bnd B} ×ˢ Set.Iic B ×ˢ {o | optBnd B o})).Finite :=
    ((finite_actBnd B).prod ((Set.finite_Iic B).prod (finite_optBnd B))).image _
  refine (((((Set.finite_Iic B).image Phase.exec).union
    ((Set.finite_range Phase.pEnd).union ((Set.finite_range Phase.pMark).union
      (Set.finite_range Phase.pRet)))).union
    ((({Phase.p0, Phase.pre, Phase.pChk, Phase.pSeek, Phase.pTake} : Set Phase).toFinite).union
      ((finite_optBnd B).image Phase.rScan))).union (hscan.union htop)).subset ?_
  intro p hp
  cases p with
  | exec pc => exact Or.inl (Or.inl (Or.inl ⟨pc, hp, rfl⟩))
  | p0 => exact Or.inl (Or.inr (Or.inl (by simp)))
  | pEnd b => exact Or.inl (Or.inl (Or.inr (Or.inl ⟨b, rfl⟩)))
  | pMark ob => exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨ob, rfl⟩))))
  | pre => exact Or.inl (Or.inr (Or.inl (by simp)))
  | pChk => exact Or.inl (Or.inr (Or.inl (by simp)))
  | pSeek => exact Or.inl (Or.inr (Or.inl (by simp)))
  | pTake => exact Or.inl (Or.inr (Or.inl (by simp)))
  | pRet b => exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨b, rfl⟩))))
  | scan act k cont first =>
    exact Or.inr (Or.inl ⟨(act, k, cont, first), ⟨hp.1, hp.2.1, hp.2.2, trivial⟩, rfl⟩)
  | top act k cont => exact Or.inr (Or.inr ⟨(act, k, cont), ⟨hp.1, hp.2.1, hp.2.2⟩, rfl⟩)
  | rScan cont => exact Or.inl (Or.inr (Or.inr ⟨cont, hp, rfl⟩))

theorem finite_qsBnd (B : ℕ) : {q : QS | q.Bnd B}.Finite := by
  refine (((finite_phaseBnd B).image QS.base).union
    (((Set.finite_univ (α := Bool)).prod ((Set.finite_Iic B).prod (finite_phaseBnd B))).image
      fun t => QS.mv t.1 t.2.1 t.2.2)).subset ?_
  intro q hq
  cases q with
  | base ph => exact Or.inl ⟨ph, hq, rfl⟩
  | mv right r tgt => exact Or.inr ⟨(right, r, tgt), ⟨trivial, hq.1, hq.2⟩, rfl⟩

/-! ### Relabelling and space -/

theorem _root_.TM.NTM.relabel_reachesSpace {Q Q' Γ : Type*} (e : Q ≃ Q') (N : NTM Q Γ) {S : ℕ} :
    ∀ {n : ℕ} {c c' : Config Q Γ}, N.ReachesSpace S n c c' →
      (NTM.relabel e N).ReachesSpace S n (NTM.Config.relabel e c) (NTM.Config.relabel e c') := by
  intro n
  induction n with
  | zero => intro c c' h; obtain ⟨rfl, hh⟩ := h; exact ⟨rfl, hh⟩
  | succ n ih =>
      intro c c' h
      obtain ⟨hh, d, ⟨q', γ', m, hmem, rfl⟩, hd⟩ := h
      refine ⟨hh, _, ⟨e q', γ', m, ?_, rfl⟩, ih hd⟩
      exact ⟨(q', γ', m), by simpa [NTM.Config.relabel] using hmem, rfl⟩

/-! ### The main theorem -/

theorem hgt_inStore {H : ℕ} (x : List Bool) (hx : x.length ≤ H) : Hgt K H (inStore kin x) := by
  intro r _
  unfold inStore
  by_cases h : r = kin
  · subst h; simp; omega
  · rw [Function.update_of_ne h]; simp

theorem good_accept {n : ℕ} {σ : SCfg} (h : Accepting C σ) :
    (good K n σ).state ∈ (simM C K kin).accept := ⟨σ.pc, rfl, h⟩

/-- **Soundness and completeness of `simM`.** -/
theorem simM_spec (hwf : ProgWF C K) (hk : kin < K) (x : List Bool) :
    ((∃ N c, (simM C K kin).Reaches N ((simM C K kin).initConfig (x.map some)) c ∧
        c.state ∈ (simM C K kin).accept) →
      ∃ T σ', SReach C T ⟨0, inStore kin x⟩ σ' ∧ Accepting C σ') ∧
    (∀ T H σ', x.length ≤ H → SReachP C (fun τ => Hgt K H τ.S) T ⟨0, inStore kin x⟩ σ' →
      Accepting C σ' →
      ∃ m ≤ (x.length + 1) * (6 * (x.length + 2) * (K + 1)) + T * (3 * (H + 2) * (K + 1)),
        ∃ c, (simM C K kin).ReachesSpace (x.length + 2 + (H + 1) * (K + 1)) m
          ((simM C K kin).initConfig (x.map some)) c ∧ c.state ∈ (simM C K kin).accept) := by
  obtain ⟨m₀, hm₀, hpre⟩ := sim_pre (C := C) hk x
  refine ⟨fun ⟨N, c, hr, hc⟩ => ?_, fun T H σ' hH hr hacc => ?_⟩
  · obtain ⟨-, hr'⟩ := hpre.passes N c hr hc
    exact sim_sound hwf _ hr' hc
  · obtain ⟨m₁, hm₁, hr'⟩ := sim_reach (kin := kin) (n := x.length) hwf T hr
    refine ⟨m₀ + m₁, by omega, good K x.length σ', ?_, good_accept hacc⟩
    exact (hpre.reach.mono _ (by nlinarith)).trans _ hr'

/-- **Stack machines are simulated by single-tape Turing machines with finitely many states.** -/
theorem exists_tm (C : List Ins) (K kin : ℕ) (hwf : ProgWF C K) (hk : kin < K) :
    ∃ (k : ℕ) (M : NTM (Fin k) (Option Bool)), M.blank = none ∧ ∀ x : List Bool,
      ((∃ N c, M.Reaches N (M.initConfig (x.map some)) c ∧ c.state ∈ M.accept) →
        ∃ T σ', SReach C T ⟨0, inStore kin x⟩ σ' ∧ Accepting C σ') ∧
      (∀ T H σ', x.length ≤ H → SReachP C (fun τ => Hgt K H τ.S) T ⟨0, inStore kin x⟩ σ' →
        Accepting C σ' →
        M.AcceptsWithin (x.map some)
            ((x.length + 1) * (6 * (x.length + 2) * (K + 1)) + T * (3 * (H + 2) * (K + 1))) ∧
          M.AcceptsInSpace (x.map some) (x.length + 2 + (H + 1) * (K + 1))) := by
  set N := simM C K kin
  set R : Set QS := {q | q.Bnd (bigB C K kin)}
  have h₀ : N.init ∈ R := trivial
  have hcl : ∀ q ∈ R, ∀ γ t, t ∈ N.step q γ → t.1 ∈ R := fun q hq γ t ht => bnd_closed hk hq ht
  letI : Fintype R := (finite_qsBnd (bigB C K kin)).fintype
  set N' := N.restrict R h₀
  set e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  refine ⟨Fintype.card R, NTM.relabel e N', rfl, fun x => ⟨?_, ?_⟩⟩
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
