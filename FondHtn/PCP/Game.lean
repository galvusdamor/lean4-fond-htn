import FondHtn.PCP.GameBase
/-!
# The game of the construction

`FOND.PCP.game_sound`, `FOND.PCP.game_complete`: the chain game with control chain
`init · A · fin` and pool `{B · endB, cheat₁ⁿ¹, cheat₂ⁿ²}` from the empty state is won iff the
projections of `A` and `B` to both modes agree (for completeness, given enough cheats).

Soundness, for a mode `m` (an outcome of `init`): the cheats of mode `m` are disabled until
`fin`, so the mode-`m` facts follow the letters of `A` and `B` (`FOND.PCP.View`), and `fin`
(after `endB`) needs `fr m`. Completeness: in mode `m` interleave the two chains, each mode-`m`
character of `A` immediately consumed by `B`, with a cheat of the other mode before each letter.
-/

namespace FOND

namespace PCP

open HTN HTN.Undec AcycHard

variable {M : TSM} {X s₁ s₂ : List ℕ}


/-! ## Effects on the views -/

/-- The pending character after a letter of `A`. -/
def nxtA (o p : Option Ch) : Option Ch := o.or p
/-- The pending character after a letter of `B`. -/
def nxtB : Option Ch → Option Ch → Option Ch
  | none, p => p
  | some _, _ => none

theorem viewA {m : ℕ} (hm : m = 1 ∨ m = 2) {s : Set ℕ} {p : Option Ch} {ℓ : Letter}
    (hv : View m s p) (hpre : ∀ f ∈ preA 1 ℓ.1 ++ preA 2 ℓ.2, f ∈ s) :
    (∀ c, proj m ℓ = some c → p = none) ∧
    View m (Action.applyEff ({f | f ∈ addA 1 ℓ.1 ++ addA 2 ℓ.2},
      {f | f ∈ preA 1 ℓ.1 ++ preA 2 ℓ.2}) s) (nxtA (proj m ℓ) p) := by
  have hp : ∀ c, proj m ℓ = some c → p = none := by
    intro c hc
    apply hv.fr_mem.1
    apply hpre
    rw [mem_sel modeParts_preA hm (mf_fr m), hc]
    simp [preA]
  refine ⟨hp, fun f hf => ?_⟩
  rw [mem_applyEff, mem_sel modeParts_preA hm hf, mem_sel modeParts_addA hm hf, hv f hf]
  cases hc : proj m ℓ with
  | none => simp [preA, addA, nxtA]
  | some c =>
    rw [hp c hc]
    simp only [pv, preA, addA, nxtA, Option.some_or, List.mem_singleton]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact absurd h1 h2
      · exact h
    · exact Or.inr

theorem viewB {m : ℕ} (hm : m = 1 ∨ m = 2) {s : Set ℕ} {p : Option Ch} {ℓ : Letter}
    (hv : View m s p) (hpre : ∀ f ∈ preB 1 ℓ.1 ++ preB 2 ℓ.2, f ∈ s) :
    (∀ c, proj m ℓ = some c → p = some c) ∧
    View m (Action.applyEff ({f | f ∈ addB 1 ℓ.1 ++ addB 2 ℓ.2},
      {f | f ∈ preB 1 ℓ.1 ++ preB 2 ℓ.2}) s) (nxtB (proj m ℓ) p) := by
  have hp : ∀ c, proj m ℓ = some c → p = some c := by
    intro c hc
    apply hv.pd_mem.1
    apply hpre
    rw [mem_sel modeParts_preB hm (mf_pd m c), hc]
    simp [preB]
  refine ⟨hp, fun f hf => ?_⟩
  rw [mem_applyEff, mem_sel modeParts_preB hm hf, mem_sel modeParts_addB hm hf, hv f hf]
  cases hc : proj m ℓ with
  | none => simp [preB, addB, nxtB]
  | some c =>
    rw [hp c hc]
    simp only [pv, preB, addB, nxtB, List.mem_singleton]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact absurd h1 h2
      · exact h
    · exact Or.inr

/-- Facts of neither mode are not touched by the letters. -/
theorem keep_sel {g g' : ℕ → Option Ch → List ℕ} (hg : ModeParts g) (hg' : ModeParts g')
    {ℓ : Letter} {s : Set ℕ} {f : ℕ} (h1 : ¬ MF 1 f) (h2 : ¬ MF 2 f) :
    f ∈ Action.applyEff ({f | f ∈ g 1 ℓ.1 ++ g 2 ℓ.2}, {f | f ∈ g' 1 ℓ.1 ++ g' 2 ℓ.2}) s ↔
      f ∈ s := by
  rw [mem_applyEff]
  have ha : f ∉ g 1 ℓ.1 ++ g 2 ℓ.2 := fun h => (mf_of_sel hg h).elim h1 h2
  have hd : f ∉ g' 1 ℓ.1 ++ g' 2 ℓ.2 := fun h => (mf_of_sel hg' h).elim h1 h2
  simp [ha, hd]

theorem mem_addOnly {A : List ℕ} {s : Set ℕ} {f : ℕ} :
    f ∈ Action.applyEff ({f | f ∈ A}, {f | f ∈ ([] : List ℕ)}) s ↔ f ∈ s ∨ f ∈ A := by
  rw [mem_applyEff]; simp

theorem view_addOnly {m : ℕ} {A : List ℕ} (hA : ∀ x ∈ A, ¬ MF m x) {s : Set ℕ} {p : Option Ch}
    (hv : View m s p) : View m (Action.applyEff ({f | f ∈ A}, {f | f ∈ ([] : List ℕ)}) s) p := by
  intro f hf
  rw [mem_addOnly, ← hv f hf]
  exact ⟨fun h => h.elim id fun h => absurd hf (hA f h), Or.inl⟩

theorem not_mf_cheat {m k : ℕ} (hk : k ≠ m) :
    ∀ x ∈ fr k :: (chars M X s₁ s₂).map (pd k), ¬ MF m x := by
  intro x hx hx'
  simp only [List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨c, -, rfl⟩
  · exact hk (mf_unique (mf_fr k) hx')
  · exact hk (mf_unique (mf_pd k c) hx')

theorem not_mem_cheat_ok {k k' : ℕ} : ok k' ∉ fr k :: (chars M X s₁ s₂).map (pd k) := by
  intro h
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with h | ⟨c, -, h⟩
  · exact not_mf_ok (h ▸ mf_fr k)
  · exact not_mf_ok (h ▸ mf_pd k c)

theorem not_mem_cheat_dB {k : ℕ} : dB ∉ fr k :: (chars M X s₁ s₂).map (pd k) := by
  intro h
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with h | ⟨c, -, h⟩
  · exact not_mf_dB (h ▸ mf_fr k)
  · exact not_mf_dB (h ▸ mf_pd k c)

theorem other_mode {m : ℕ} (hm : m = 1 ∨ m = 2) :
    (3 - m = 1 ∨ 3 - m = 2) ∧ 3 - m ≠ m ∧ ∀ f, MF 1 f ∨ MF 2 f → MF m f ∨ MF (3 - m) f := by
  rcases hm with rfl | rfl
  · exact ⟨Or.inr rfl, by omega, fun f h => h⟩
  · exact ⟨Or.inl rfl, by omega, fun f h => h.symm⟩

/-! ## Soundness -/

theorem sound_aux {m : ℕ} (hm : m = 1 ∨ m = 2) {ctl : List ℕ} {P : Multiset (List ℕ)}
    {s : Set ℕ} (h : CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl P s) :
    ∀ (aR bR : List Letter) (bc : List ℕ) (K : ℕ → ℕ) (p : Option Ch),
      ctl = aR.map nA ++ [nFin] → P = Pl bc K →
      (∀ ℓ ∈ aR, ℓ ∈ letters M X s₁ s₂) → (∀ ℓ ∈ bR, ℓ ∈ letters M X s₁ s₂) →
      ((bc = bR.map nB ++ [nEnd] ∧ dB ∉ s) ∨ (bc = [] ∧ bR = [])) → ok m ∉ s → View m s p →
      p.toList ++ pm m aR = pm m bR := by
  induction h with
  | done _ =>
    intro aR bR bc K p hctl
    simp at hctl
  | @ctl a ctl' P s happ _ ih =>
    intro aR bR bc K p hctl hP hA hB hbc hok hv
    cases aR with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hctl
      obtain ⟨rfl, rfl⟩ := hctl
      rw [δ_fin, app_fin] at happ
      obtain ⟨h1, h2, h3⟩ := happ
      rcases hbc with ⟨-, h⟩ | ⟨-, rfl⟩
      · exact absurd h3 h
      · have : p = none := hv.fr_mem.1 (by rcases hm with rfl | rfl <;> assumption)
        subst this; rfl
    | cons ℓ aR' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hctl
      obtain ⟨rfl, rfl⟩ := hctl
      have hℓ := hA ℓ (List.mem_cons_self ..)
      rw [δ_nA hℓ, app_A] at happ
      obtain ⟨hp, hv'⟩ := viewA hm hv happ
      have ho := (out_A (ℓ := ℓ) (s := s)).2 rfl
      rw [← δ_nA hℓ] at ho
      have key := ih _ ho aR' bR bc K _ rfl hP (fun x hx => hA x (List.mem_cons_of_mem _ hx)) hB
        (by
          rcases hbc with ⟨h1, h2⟩ | h
          · exact Or.inl ⟨h1, by rwa [keep_sel modeParts_addA modeParts_preA not_mf_dB not_mf_dB]⟩
          · exact Or.inr h)
        (by rwa [keep_sel modeParts_addA modeParts_preA not_mf_ok not_mf_ok]) hv'
      rw [pm_cons, ← key]
      cases hc : proj m ℓ with
      | none => simp [nxtA]
      | some c => rw [hp c hc]; simp [nxtA]
  | @pool ctl P s a c hc happ _ ih =>
    intro aR bR bc K p hctl hP hA hB hbc hok hv
    subst hP
    rcases pool_cases hc with ⟨hbc', hnew⟩ | ⟨k, j, hk, hK, rfl, rfl, hnew⟩
    · rcases hbc with ⟨rfl, hdB⟩ | ⟨rfl, -⟩
      · cases bR with
        | nil =>
          simp only [List.map_nil, List.nil_append, List.cons.injEq] at hbc'
          obtain ⟨rfl, rfl⟩ := hbc'
          have ho : Action.applyEff ({f | f ∈ [dB]}, {f | f ∈ ([] : List ℕ)}) s ∈
              ((Pb M X s₁ s₂).δ nEnd).outcomes s := by rw [δ_end]; exact out_end.2 rfl
          refine ih _ ho aR [] [] K p hctl hnew hA (fun _ h => absurd h List.not_mem_nil)
            (Or.inr ⟨rfl, rfl⟩) ?_ (view_addOnly (fun x hx => ?_) hv)
          · rw [mem_addOnly]; simp only [List.mem_singleton]
            exact fun h => h.elim hok ok_ne_dB
          · rw [List.mem_singleton.1 hx]; exact not_mf_dB
        | cons ℓ bR' =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at hbc'
          obtain ⟨rfl, rfl⟩ := hbc'
          have hℓ := hB ℓ (List.mem_cons_self ..)
          rw [δ_nB hℓ, app_B] at happ
          obtain ⟨hp, hv'⟩ := viewB hm hv happ
          have ho := (out_B (ℓ := ℓ) (s := s)).2 rfl
          rw [← δ_nB hℓ] at ho
          have key := ih _ ho aR bR' _ K _ hctl hnew hA
            (fun x hx => hB x (List.mem_cons_of_mem _ hx))
            (Or.inl ⟨rfl, by rwa [keep_sel modeParts_addB modeParts_preB not_mf_dB not_mf_dB]⟩)
            (by rwa [keep_sel modeParts_addB modeParts_preB not_mf_ok not_mf_ok]) hv'
          rw [pm_cons, ← key]
          cases hc : proj m ℓ with
          | none => simp [nxtB]
          | some c => rw [hp c hc]; simp [nxtB]
      · exact absurd hbc' (List.cons_ne_nil _ _)
    · rw [δ_cheat hk, app_cheat] at happ
      have hkm : k ≠ m := by rintro rfl; exact hok happ
      have ho : Action.applyEff ({f | f ∈ fr k :: (chars M X s₁ s₂).map (pd k)},
          {f | f ∈ ([] : List ℕ)}) s ∈ ((Pb M X s₁ s₂).δ (nCheat k)).outcomes s := by
        rw [δ_cheat hk]; exact out_cheat.2 rfl
      refine ih _ ho aR bR bc _ p hctl hnew hA hB ?_ ?_ (view_addOnly (not_mf_cheat hkm) hv)
      · rcases hbc with ⟨h1, h2⟩ | h
        · refine Or.inl ⟨h1, ?_⟩
          rw [mem_addOnly]
          exact fun h => h.elim h2 not_mem_cheat_dB
        · exact Or.inr h
      · rw [mem_addOnly]
        exact fun h => h.elim hok not_mem_cheat_ok

/-! ## Letters -/

theorem proj_eq (k : ℕ) (ℓ : Letter) : proj k ℓ = ℓ.1 ∨ proj k ℓ = ℓ.2 := by
  unfold proj; split <;> simp

theorem letter_chars {ℓ : Letter} (h : ℓ ∈ letters M X s₁ s₂) {k : ℕ} {c : Ch}
    (hc : proj k ℓ = some c) : c ∈ chars M X s₁ s₂ := by
  obtain ⟨c', hc', hℓ⟩ := mem_letters.1 h
  rcases proj_eq k ℓ with h' | h' <;> rw [h'] at hc <;>
    rcases hℓ with rfl | rfl | rfl <;> simp at hc <;> subst hc <;> exact hc'

theorem letter_ne {ℓ : Letter} (h : ℓ ∈ letters M X s₁ s₂) : ∃ f, f ∈ preB 1 ℓ.1 ++ preB 2 ℓ.2 := by
  obtain ⟨c, -, rfl | rfl | rfl⟩ := mem_letters.1 h
  · exact ⟨pd 2 c, by simp [preB]⟩
  · exact ⟨pd 1 c, by simp [preB]⟩
  · exact ⟨pd 1 c, by simp [preB]⟩

/-! ## Moves -/

theorem mv_cheat {ctl : List ℕ} {bc : List ℕ} {K : ℕ → ℕ} {k j : ℕ} {s : Set ℕ}
    (hk : k = 1 ∨ k = 2) (hK : K k = j + 1) (hok : ok k ∈ s)
    (h : CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl (Pl bc (Function.update K k j))
      (Action.applyEff ({f | f ∈ fr k :: (chars M X s₁ s₂).map (pd k)}, {f | f ∈ ([] : List ℕ)}) s)) :
    CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl (Pl bc K) s := by
  refine CWin.pool (pool_cheat hk hK).1 (by rw [δ_cheat hk, app_cheat]; exact hok) ?_
  intro s' hs'
  rw [δ_cheat hk, out_cheat] at hs'
  subst hs'
  rw [(pool_cheat hk hK).2]; exact h

theorem mv_B {ℓ : Letter} (hℓ : ℓ ∈ letters M X s₁ s₂) {ctl bc : List ℕ} {K : ℕ → ℕ} {s : Set ℕ}
    (happ : ∀ f ∈ preB 1 ℓ.1 ++ preB 2 ℓ.2, f ∈ s)
    (h : CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl (Pl bc K) (Action.applyEff
      ({f | f ∈ addB 1 ℓ.1 ++ addB 2 ℓ.2}, {f | f ∈ preB 1 ℓ.1 ++ preB 2 ℓ.2}) s)) :
    CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl (Pl (nB ℓ :: bc) K) s := by
  refine CWin.pool pool_B.1 (by rw [δ_nB hℓ, app_B]; exact happ) ?_
  intro s' hs'
  rw [δ_nB hℓ, out_B] at hs'
  subst hs'
  rw [pool_B.2]; exact h

theorem mv_end {ctl : List ℕ} {K : ℕ → ℕ} {s : Set ℕ}
    (h : CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl (Pl [] K)
      (Action.applyEff ({f | f ∈ [dB]}, {f | f ∈ ([] : List ℕ)}) s)) :
    CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl (Pl [nEnd] K) s := by
  refine CWin.pool pool_B.1 (by rw [δ_end]; exact app_end) ?_
  intro s' hs'
  rw [δ_end, out_end] at hs'
  subst hs'
  rw [pool_B.2]; exact h

theorem mv_A {ℓ : Letter} (hℓ : ℓ ∈ letters M X s₁ s₂) {ctl : List ℕ} {P : Multiset (List ℕ)}
    {s : Set ℕ} (happ : ∀ f ∈ preA 1 ℓ.1 ++ preA 2 ℓ.2, f ∈ s)
    (h : CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl P (Action.applyEff
      ({f | f ∈ addA 1 ℓ.1 ++ addA 2 ℓ.2}, {f | f ∈ preA 1 ℓ.1 ++ preA 2 ℓ.2}) s)) :
    CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ (nA ℓ :: ctl) P s := by
  refine CWin.ctl (by rw [δ_nA hℓ, app_A]; exact happ) ?_
  intro s' hs'
  rw [δ_nA hℓ, out_A] at hs'
  subst hs'; exact h

theorem mv_fin {ctl : List ℕ} {P : Multiset (List ℕ)} {s : Set ℕ}
    (happ : fr 1 ∈ s ∧ fr 2 ∈ s ∧ dB ∈ s)
    (h : CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ ctl P
      (Action.applyEff ({f | f ∈ [ok 1, ok 2]}, {f | f ∈ ([] : List ℕ)}) s)) :
    CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ (nFin :: ctl) P s := by
  refine CWin.ctl (by rw [δ_fin, app_fin]; exact happ) ?_
  intro s' hs'
  rw [δ_fin, out_fin] at hs'
  subst hs'; exact h

/-! ## Completeness -/

/-- After `fin`, the remaining cheats are executable. -/
theorem finish : ∀ (n : ℕ) (K : ℕ → ℕ) (s : Set ℕ), K 1 + K 2 = n → ok 1 ∈ s → ok 2 ∈ s →
    CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ [] (Pl [] K) s := by
  intro n
  induction n with
  | zero =>
    intro K s hn _ _
    refine CWin.done fun c hc => ?_
    have h1 : K 1 = 0 := by omega
    have h2 : K 2 = 0 := by omega
    simp only [Pl, h1, h2, List.replicate_zero, Multiset.mem_cons, Multiset.notMem_zero,
      or_false] at hc
    rcases hc with rfl | rfl | rfl <;> rfl
  | succ n ih =>
    intro K s hn h1 h2
    have hkeep : ∀ k, ok k ∈ s → ∀ k', ok k ∈ Action.applyEff
        ({f | f ∈ fr k' :: (chars M X s₁ s₂).map (pd k')}, {f | f ∈ ([] : List ℕ)}) s :=
      fun k hk k' => mem_addOnly.2 (Or.inl hk)
    by_cases hK1 : K 1 = 0
    · obtain ⟨j, hj⟩ : ∃ j, K 2 = j + 1 := ⟨K 2 - 1, by omega⟩
      refine mv_cheat (Or.inr rfl) hj h2 (ih _ _ ?_ (hkeep _ h1 _) (hkeep _ h2 _))
      simp [Function.update_apply]; omega
    · obtain ⟨j, hj⟩ : ∃ j, K 1 = j + 1 := ⟨K 1 - 1, by omega⟩
      refine mv_cheat (Or.inl rfl) hj h1 (ih _ _ ?_ (hkeep _ h1 _) (hkeep _ h2 _))
      simp [Function.update_apply]; omega

theorem complete_aux {m : ℕ} (hm : m = 1 ∨ m = 2) : ∀ (n : ℕ) (aR bR : List Letter)
    (p : Option Ch) (s : Set ℕ) (K : ℕ → ℕ), aR.length + bR.length = n → n < K (3 - m) →
    (∀ ℓ ∈ aR, ℓ ∈ letters M X s₁ s₂) → (∀ ℓ ∈ bR, ℓ ∈ letters M X s₁ s₂) →
    p.toList ++ pm m aR = pm m bR → View m s p → ok (3 - m) ∈ s →
    CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ (aR.map nA ++ [nFin]) (Pl (bR.map nB ++ [nEnd]) K) s := by
  obtain ⟨hm', hmm', hcov⟩ := other_mode hm
  -- the state after a cheat of the other mode
  have hcheat : ∀ (s : Set ℕ) (p : Option Ch), View m s p → ok (3 - m) ∈ s →
      let t := Action.applyEff ({f | f ∈ fr (3 - m) :: (chars M X s₁ s₂).map (pd (3 - m))},
        {f | f ∈ ([] : List ℕ)}) s
      View m t p ∧ ok (3 - m) ∈ t ∧ fr (3 - m) ∈ t ∧ ∀ c ∈ chars M X s₁ s₂, pd (3 - m) c ∈ t := by
    intro s p hv hok
    refine ⟨view_addOnly (not_mf_cheat hmm') hv, mem_addOnly.2 (Or.inl hok),
      mem_addOnly.2 (Or.inr (List.mem_cons_self ..)), fun c hc => mem_addOnly.2 (Or.inr ?_)⟩
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem hc)
  have appA : ∀ {s : Set ℕ} {p : Option Ch} {ℓ : Letter}, View m s p →
      (∀ c, proj m ℓ = some c → p = none) → fr (3 - m) ∈ s →
      ∀ f ∈ preA 1 ℓ.1 ++ preA 2 ℓ.2, f ∈ s := by
    intro s p ℓ hv hp hfr f hf
    rcases hcov f (mf_of_sel modeParts_preA hf) with hf' | hf'
    · rw [mem_sel modeParts_preA hm hf'] at hf
      cases hc : proj m ℓ with
      | none => rw [hc] at hf; simp [preA] at hf
      | some c =>
        rw [hc] at hf; simp only [preA, List.mem_singleton] at hf; subst hf
        exact hv.fr_mem.2 (hp c hc)
    · rw [mem_sel modeParts_preA hm' hf'] at hf
      cases hc : proj (3 - m) ℓ with
      | none => rw [hc] at hf; simp [preA] at hf
      | some c => rw [hc] at hf; simp only [preA, List.mem_singleton] at hf; subst hf; exact hfr
  have appB : ∀ {s : Set ℕ} {p : Option Ch} {ℓ : Letter}, ℓ ∈ letters M X s₁ s₂ → View m s p →
      (∀ c, proj m ℓ = some c → p = some c) → (∀ c ∈ chars M X s₁ s₂, pd (3 - m) c ∈ s) →
      ∀ f ∈ preB 1 ℓ.1 ++ preB 2 ℓ.2, f ∈ s := by
    intro s p ℓ hℓ hv hp hpd f hf
    rcases hcov f (mf_of_sel modeParts_preB hf) with hf' | hf'
    · rw [mem_sel modeParts_preB hm hf'] at hf
      cases hc : proj m ℓ with
      | none => rw [hc] at hf; simp [preB] at hf
      | some c =>
        rw [hc] at hf; simp only [preB, List.mem_singleton] at hf; subst hf
        exact hv.pd_mem.2 (hp c hc)
    · rw [mem_sel modeParts_preB hm' hf'] at hf
      cases hc : proj (3 - m) ℓ with
      | none => rw [hc] at hf; simp [preB] at hf
      | some c =>
        rw [hc] at hf; simp only [preB, List.mem_singleton] at hf; subst hf
        exact hpd c (letter_chars hℓ hc)
  intro n
  induction n with
  | zero =>
    intro aR bR p s K hn hK hA hB heq hv hok
    have haR : aR = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hbR : bR = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst haR hbR
    have hp : p = none := by cases p <;> simp_all
    subst hp
    obtain ⟨j, hj⟩ : ∃ j, K (3 - m) = j + 1 := ⟨K (3 - m) - 1, by omega⟩
    obtain ⟨hv₁, hok₁, hfr₁, -⟩ := hcheat s none hv hok
    refine mv_cheat hm' hj hok (mv_end (mv_fin ?_ (finish _ _ _ rfl ?_ ?_)))
    · have hfrm := hv₁.fr_mem.2 rfl
      refine ⟨?_, ?_, mem_addOnly.2 (Or.inr (List.mem_singleton_self _))⟩ <;>
        refine mem_addOnly.2 (Or.inl ?_) <;> rcases hm with rfl | rfl <;> assumption
    · exact mem_addOnly.2 (Or.inr (by simp))
    · exact mem_addOnly.2 (Or.inr (by simp))
  | succ n ih =>
    intro aR bR p s K hn hK hA hB heq hv hok
    obtain ⟨j, hj⟩ : ∃ j, K (3 - m) = j + 1 := ⟨K (3 - m) - 1, by omega⟩
    obtain ⟨hv₁, hok₁, hfr₁, hpd₁⟩ := hcheat s p hv hok
    have hK' : n < Function.update K (3 - m) j (3 - m) := by simp; omega
    refine mv_cheat hm' hj hok ?_
    by_cases c1 : ∃ ℓ aR', aR = ℓ :: aR' ∧ proj m ℓ = none
    · obtain ⟨ℓ, aR', rfl, hc⟩ := c1
      have hℓ := hA ℓ (List.mem_cons_self ..)
      have hpre := appA hv₁ (fun c h => by rw [hc] at h; cases h) hfr₁
      obtain ⟨-, hv₂⟩ := viewA hm hv₁ hpre
      refine mv_A hℓ hpre (ih aR' bR _ _ _ (by simp at hn; omega) hK'
        (fun x hx => hA x (List.mem_cons_of_mem _ hx)) hB ?_ hv₂ ?_)
      · rw [hc]; simpa [nxtA, pm_cons, hc] using heq
      · rwa [keep_sel modeParts_addA modeParts_preA not_mf_ok not_mf_ok]
    by_cases c2 : ∃ ℓ bR', bR = ℓ :: bR' ∧ proj m ℓ = none
    · obtain ⟨ℓ, bR', rfl, hc⟩ := c2
      have hℓ := hB ℓ (List.mem_cons_self ..)
      have hpre := appB hℓ hv₁ (fun c h => by rw [hc] at h; cases h) hpd₁
      obtain ⟨-, hv₂⟩ := viewB hm hv₁ hpre
      refine mv_B hℓ hpre (ih aR bR' _ _ _ (by simp at hn; omega) hK' hA
        (fun x hx => hB x (List.mem_cons_of_mem _ hx)) ?_ hv₂ ?_)
      · rw [hc]; simpa [nxtB, pm_cons, hc] using heq
      · rwa [keep_sel modeParts_addB modeParts_preB not_mf_ok not_mf_ok]
    by_cases c3 : ∃ ℓ bR' c, bR = ℓ :: bR' ∧ proj m ℓ = some c ∧ p = some c
    · obtain ⟨ℓ, bR', c, rfl, hc, rfl⟩ := c3
      have hℓ := hB ℓ (List.mem_cons_self ..)
      have hpre := appB hℓ hv₁ (fun c' h => by rw [hc] at h; exact h) hpd₁
      obtain ⟨-, hv₂⟩ := viewB hm hv₁ hpre
      refine mv_B hℓ hpre (ih aR bR' _ _ _ (by simp at hn; omega) hK' hA
        (fun x hx => hB x (List.mem_cons_of_mem _ hx)) ?_ hv₂ ?_)
      · rw [hc]; simpa [nxtB, pm_cons, hc] using heq
      · rwa [keep_sel modeParts_addB modeParts_preB not_mf_ok not_mf_ok]
    by_cases c4 : ∃ ℓ aR' c, aR = ℓ :: aR' ∧ proj m ℓ = some c ∧ p = none
    · obtain ⟨ℓ, aR', c, rfl, hc, rfl⟩ := c4
      have hℓ := hA ℓ (List.mem_cons_self ..)
      have hpre := appA (ℓ := ℓ) hv₁ (fun _ _ => rfl) hfr₁
      obtain ⟨-, hv₂⟩ := viewA hm hv₁ hpre
      refine mv_A hℓ hpre (ih aR' bR _ _ _ (by simp at hn; omega) hK'
        (fun x hx => hA x (List.mem_cons_of_mem _ hx)) hB ?_ hv₂ ?_)
      · rw [hc]; simpa [nxtA, pm_cons, hc] using heq
      · rwa [keep_sel modeParts_addA modeParts_preA not_mf_ok not_mf_ok]
    -- no other case is possible
    exfalso
    push_neg at c1 c2 c3 c4
    have hB' : ∀ ℓ bR', bR = ℓ :: bR' → ∃ c, proj m ℓ = some c := by
      intro ℓ bR' h
      cases hc : proj m ℓ with
      | none => exact absurd hc (c2 ℓ bR' h)
      | some c => exact ⟨c, rfl⟩
    cases aR with
    | cons ℓ aR' =>
      obtain ⟨c, hc⟩ : ∃ c, proj m ℓ = some c := by
        cases hc : proj m ℓ with
        | none => exact absurd hc (c1 ℓ aR' rfl)
        | some c => exact ⟨c, rfl⟩
      obtain ⟨c', rfl⟩ : ∃ c', p = some c' := by
        cases p with
        | none => exact absurd rfl (c4 ℓ aR' c rfl hc)
        | some c' => exact ⟨c', rfl⟩
      cases bR with
      | nil => simp [pm_cons] at heq
      | cons ℓ' bR' =>
        obtain ⟨c'', hc''⟩ := hB' ℓ' bR' rfl
        rw [pm_cons, pm_cons, hc, hc''] at heq
        simp only [Option.toList_some, List.cons_append, List.cons.injEq] at heq
        exact c3 ℓ' bR' c'' rfl hc'' (heq.1 ▸ rfl)
    | nil =>
      cases bR with
      | nil => simp at hn
      | cons ℓ' bR' =>
        obtain ⟨c'', hc''⟩ := hB' ℓ' bR' rfl
        rw [pm_cons, hc''] at heq
        cases p with
        | none => simp at heq
        | some c' =>
          simp only [Option.toList_some, pm_nil, List.append_nil, List.singleton_append,
            List.cons.injEq] at heq
          exact c3 ℓ' bR' c'' rfl hc'' (heq.1 ▸ rfl)

/-! ## The game -/

theorem view_init {m : ℕ} (hm : m = 1 ∨ m = 2) :
    View m (Action.applyEff ({f | f ∈ [fr m, ok (3 - m)]}, {f | f ∈ ([] : List ℕ)}) ∅) none := by
  intro f hf
  rw [mem_addOnly]
  simp only [Set.mem_empty_iff_false, false_or, List.mem_cons, List.not_mem_nil, or_false, pv]
  constructor
  · rintro (h | rfl)
    · exact h
    · exact absurd hf not_mf_ok
  · exact Or.inl

/-- **Soundness of the game.** -/
theorem game_sound {aR bR : List Letter} {K : ℕ → ℕ} (hA : ∀ ℓ ∈ aR, ℓ ∈ letters M X s₁ s₂)
    (hB : ∀ ℓ ∈ bR, ℓ ∈ letters M X s₁ s₂) (hne : bR ≠ [])
    (h : CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ (nInit :: (aR.map nA ++ [nFin]))
      (Pl (bR.map nB ++ [nEnd]) K) ∅) :
    pm 1 aR = pm 1 bR ∧ pm 2 aR = pm 2 bR := by
  cases h with
  | ctl happ hall =>
    have hm : ∀ m, (m = 1 ∨ m = 2) →
        Action.applyEff ({f | f ∈ [fr m, ok (3 - m)]}, {f | f ∈ ([] : List ℕ)}) ∅ ∈
          ((Pb M X s₁ s₂).δ nInit).outcomes ∅ → pm m aR = pm m bR := by
      intro m hm ho
      have := sound_aux hm (hall _ ho) aR bR _ K none rfl rfl hA hB
        (Or.inl ⟨rfl, by
          rw [mem_addOnly]
          simp only [Set.mem_empty_iff_false, false_or, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | h)
          · exact not_mf_dB (h ▸ mf_fr m)
          · exact ok_ne_dB h.symm⟩)
        (by
          rw [mem_addOnly]
          simp only [Set.mem_empty_iff_false, false_or, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | h)
          · exact not_mf_ok (h ▸ mf_fr m)
          · have := ok_inj h; rcases hm with rfl | rfl <;> omega)
        (view_init hm)
      simpa using this
    refine ⟨hm 1 (Or.inl rfl) ?_, hm 2 (Or.inr rfl) ?_⟩
    · rw [δ_init, out_init]; exact Or.inl rfl
    · rw [δ_init, out_init]; exact Or.inr rfl
  | pool hc happ hall =>
    rcases pool_cases hc with ⟨hbc, -⟩ | ⟨k, j, hk, -, rfl, -, -⟩
    · obtain ⟨ℓ, bR', rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hbc
      obtain ⟨rfl, -⟩ := hbc
      have hℓ := hB ℓ (List.mem_cons_self ..)
      rw [δ_nB hℓ, app_B] at happ
      obtain ⟨f, hf⟩ := letter_ne hℓ
      exact absurd (happ f hf) (Set.notMem_empty f)
    · rw [δ_cheat hk, app_cheat] at happ
      exact absurd happ (Set.notMem_empty _)

/-- **Completeness of the game.** -/
theorem game_complete {aR bR : List Letter} {K : ℕ → ℕ} (hA : ∀ ℓ ∈ aR, ℓ ∈ letters M X s₁ s₂)
    (hB : ∀ ℓ ∈ bR, ℓ ∈ letters M X s₁ s₂) (h1 : pm 1 aR = pm 1 bR) (h2 : pm 2 aR = pm 2 bR)
    (hK1 : aR.length + bR.length < K 1) (hK2 : aR.length + bR.length < K 2) :
    CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ (nInit :: (aR.map nA ++ [nFin]))
      (Pl (bR.map nB ++ [nEnd]) K) ∅ := by
  refine CWin.ctl (by rw [δ_init]; exact app_init) ?_
  intro s' hs'
  rw [δ_init, out_init] at hs'
  have hok : ∀ m, ok (3 - m) ∈ Action.applyEff ({f | f ∈ [fr m, ok (3 - m)]},
      {f | f ∈ ([] : List ℕ)}) (∅ : Set ℕ) := fun m => mem_addOnly.2 (Or.inr (by simp))
  rcases hs' with rfl | rfl
  · exact complete_aux (Or.inl rfl) _ aR bR none _ K rfl hK2 hA hB (by simpa using h1)
      (view_init (Or.inl rfl)) (hok 1)
  · exact complete_aux (Or.inr rfl) _ aR bR none _ K rfl hK1 hA hB (by simpa using h2)
      (view_init (Or.inr rfl)) (hok 2)

end PCP

end FOND
