import FondHtn.PCP.LangB
/-!
# The game of the construction: actions, facts and pools

Basic facts for the analysis of the chain game of `FOND.PCP.desc` (`FondHtn/PCP/Game.lean`):
the actions of the names, distinctness of the facts, the mode-`m` view of a state and the moves
on the pool `{B, S₁, S₂}`.
-/

namespace FOND

namespace PCP

open HTN HTN.Undec

variable {M : TSM} {X s₁ s₂ : List ℕ}

/-! ## Facts -/

/-- The facts of mode `m`. -/
def MF (m f : ℕ) : Prop := f = fr m ∨ ∃ c, f = pd m c

theorem fr_inj {m m' : ℕ} (h : fr m = fr m') : m = m' := (Nat.pair_eq_pair.1 h).2
theorem pd_inj {m m' : ℕ} {c c' : Ch} (h : pd m c = pd m' c') : m = m' ∧ c = c' := by
  have h1 := Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 h).2
  exact ⟨h1.1, codeC_inj h1.2⟩
theorem fr_ne_pd {m m' : ℕ} {c : Ch} : fr m ≠ pd m' c := fun h => by
  have := (Nat.pair_eq_pair.1 h).1; omega
theorem ok_inj {m m' : ℕ} (h : ok m = ok m') : m = m' := (Nat.pair_eq_pair.1 h).2

theorem mf_unique {m m' f : ℕ} (h : MF m f) (h' : MF m' f) : m = m' := by
  rcases h with rfl | ⟨c, rfl⟩ <;> rcases h' with h' | ⟨c', h'⟩
  · exact fr_inj h'
  · exact absurd h' fr_ne_pd
  · exact absurd h'.symm fr_ne_pd
  · exact (pd_inj h').1

theorem not_mf_ok {m k : ℕ} : ¬ MF m (ok k) := by
  rintro (h | ⟨c, h⟩) <;> have := (Nat.pair_eq_pair.1 h).1 <;> omega

theorem not_mf_dB {m : ℕ} : ¬ MF m dB := by
  rintro (h | ⟨c, h⟩) <;> have := (Nat.pair_eq_pair.1 h).1 <;> omega

theorem ok_ne_dB {k : ℕ} : ok k ≠ dB := fun h => by have := (Nat.pair_eq_pair.1 h).1; omega

theorem mf_fr (m : ℕ) : MF m (fr m) := Or.inl rfl
theorem mf_pd (m : ℕ) (c : Ch) : MF m (pd m c) := Or.inr ⟨c, rfl⟩

/-! ## Modes -/

/-- The character of a letter seen by mode `m`. -/
def proj : ℕ → Letter → Option Ch
  | 1, ℓ => ℓ.1
  | _, ℓ => ℓ.2

/-- The projection of a word to mode `m`. -/
def pm (m : ℕ) (w : List Letter) : List Ch := w.filterMap (proj m)

@[simp] theorem pm_nil (m : ℕ) : pm m [] = [] := rfl
theorem pm_cons (m : ℕ) (ℓ : Letter) (w : List Letter) :
    pm m (ℓ :: w) = (proj m ℓ).toList ++ pm m w := by
  unfold pm; cases h : proj m ℓ <;> simp [List.filterMap_cons, h]

theorem pm_one (w : List Letter) : pm 1 w = p1 w := rfl
theorem pm_two (w : List Letter) : pm 2 w = p2 w := rfl

/-- The parts of the letter actions (`preA`, `addA`, `preB`, `addB`) are facts of their mode. -/
def ModeParts (g : ℕ → Option Ch → List ℕ) : Prop := ∀ k o x, x ∈ g k o → MF k x

theorem modeParts_preA : ModeParts preA := by
  intro k o x hx; cases o <;> simp [preA] at hx; subst hx; exact mf_fr k
theorem modeParts_addA : ModeParts addA := by
  intro k o x hx; cases o <;> simp [addA] at hx; subst hx; exact mf_pd k _
theorem modeParts_preB : ModeParts preB := by
  intro k o x hx; cases o <;> simp [preB] at hx; subst hx; exact mf_pd k _
theorem modeParts_addB : ModeParts addB := by
  intro k o x hx; cases o <;> simp [addB] at hx; subst hx; exact mf_fr k

theorem mem_sel {g : ℕ → Option Ch → List ℕ} (hg : ModeParts g) {m : ℕ} (hm : m = 1 ∨ m = 2)
    {f : ℕ} (hf : MF m f) (ℓ : Letter) : f ∈ g 1 ℓ.1 ++ g 2 ℓ.2 ↔ f ∈ g m (proj m ℓ) := by
  rw [List.mem_append]
  rcases hm with rfl | rfl
  · refine ⟨fun h => h.elim id fun h => ?_, Or.inl⟩
    exact absurd (mf_unique hf (hg _ _ _ h)) (by omega)
  · refine ⟨fun h => h.elim (fun h => ?_) id, Or.inr⟩
    exact absurd (mf_unique hf (hg _ _ _ h)) (by omega)

theorem mf_of_sel {g : ℕ → Option Ch → List ℕ} (hg : ModeParts g) {f : ℕ} {ℓ : Letter}
    (h : f ∈ g 1 ℓ.1 ++ g 2 ℓ.2) : MF 1 f ∨ MF 2 f := by
  rcases List.mem_append.1 h with h | h
  · exact Or.inl (hg _ _ _ h)
  · exact Or.inr (hg _ _ _ h)

/-- The mode-`m` part of a state: `fr m` if nothing is pending, `pd m c` if `c` is pending. -/
def pv (m : ℕ) : Option Ch → List ℕ
  | none => [fr m]
  | some c => [pd m c]

/-- The mode-`m` facts of `s` are exactly `pv m p`. -/
def View (m : ℕ) (s : Set ℕ) (p : Option Ch) : Prop := ∀ f, MF m f → (f ∈ s ↔ f ∈ pv m p)

theorem View.fr_mem {m : ℕ} {s : Set ℕ} {p : Option Ch} (h : View m s p) :
    fr m ∈ s ↔ p = none := by
  rw [h _ (mf_fr m)]
  cases p <;> simp [pv]
  exact fun h' => fr_ne_pd h'

theorem View.pd_mem {m : ℕ} {s : Set ℕ} {p : Option Ch} (h : View m s p) {c : Ch} :
    pd m c ∈ s ↔ p = some c := by
  rw [h _ (mf_pd m c)]
  cases p with
  | none => simp [pv]; exact fun h' => fr_ne_pd h'.symm
  | some c' =>
    simp only [pv, List.mem_singleton, Option.some.injEq]
    exact ⟨fun h' => ((pd_inj h').2).symm ▸ rfl, fun h' => h' ▸ rfl⟩

/-! ## Actions -/

theorem toAction_applicable {a : FActDesc} (h : a.2.2.1 = []) {s : Set ℕ} :
    a.toAction.Applicable s ↔ ∀ f ∈ a.2.1, f ∈ s := by
  simp only [Action.Applicable, FActDesc.toAction, h, List.not_mem_nil, Set.setOf_false,
    Set.empty_disjoint, and_true]
  exact ⟨fun h f hf => h hf, fun h f hf => h f hf⟩

theorem toAction_outcomes {a : FActDesc} {x : List ℕ × List ℕ} (h : a.effs = [x])
    {s s' : Set ℕ} :
    s' ∈ a.toAction.outcomes s ↔ s' = Action.applyEff ({f | f ∈ x.1}, {f | f ∈ x.2}) s := by
  simp only [Action.mem_outcomes, FActDesc.toAction, h, List.mem_singleton, Set.mem_setOf_eq]
  constructor
  · rintro ⟨e, ⟨y, rfl, rfl⟩, rfl⟩; rfl
  · rintro rfl; exact ⟨_, ⟨x, rfl, rfl⟩, rfl⟩

theorem mem_applyEff {A D : List ℕ} {s : Set ℕ} {f : ℕ} :
    f ∈ Action.applyEff ({f | f ∈ A}, {f | f ∈ D}) s ↔ (f ∈ s ∧ f ∉ D) ∨ f ∈ A := by
  simp [Action.applyEff]

theorem actA_mem {ℓ : Letter} (h : ℓ ∈ letters M X s₁ s₂) : actA ℓ ∈ actions M X s₁ s₂ := by
  simp only [actions, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨ℓ, h, rfl⟩)
theorem actB_mem {ℓ : Letter} (h : ℓ ∈ letters M X s₁ s₂) : actB ℓ ∈ actions M X s₁ s₂ := by
  simp only [actions, List.mem_append, List.mem_map]
  exact Or.inr ⟨ℓ, h, rfl⟩

theorem δ_nA {ℓ : Letter} (h : ℓ ∈ letters M X s₁ s₂) : (Pb M X s₁ s₂).δ (nA ℓ) = (actA ℓ).toAction :=
  δ_eq (actA_mem h)
theorem δ_nB {ℓ : Letter} (h : ℓ ∈ letters M X s₁ s₂) : (Pb M X s₁ s₂).δ (nB ℓ) = (actB ℓ).toAction :=
  δ_eq (actB_mem h)
theorem δ_init : (Pb M X s₁ s₂).δ nInit = actInit.toAction := δ_eq (a := actInit) (by simp [actions])
theorem δ_fin : (Pb M X s₁ s₂).δ nFin = actFin.toAction := δ_eq (a := actFin) (by simp [actions])
theorem δ_end : (Pb M X s₁ s₂).δ nEnd = actEnd.toAction := δ_eq (a := actEnd) (by simp [actions])
theorem δ_cheat {k : ℕ} (hk : k = 1 ∨ k = 2) :
    (Pb M X s₁ s₂).δ (nCheat k) = (actCheat M X s₁ s₂ k).toAction :=
  δ_eq (a := actCheat M X s₁ s₂ k) (by rcases hk with rfl | rfl <;> simp [actions])

/-! ### Applicability and outcomes of each action -/

theorem app_A {ℓ : Letter} {s : Set ℕ} : (actA ℓ).toAction.Applicable s ↔
    ∀ f ∈ preA 1 ℓ.1 ++ preA 2 ℓ.2, f ∈ s := toAction_applicable rfl
theorem app_B {ℓ : Letter} {s : Set ℕ} : (actB ℓ).toAction.Applicable s ↔
    ∀ f ∈ preB 1 ℓ.1 ++ preB 2 ℓ.2, f ∈ s := toAction_applicable rfl
theorem app_fin {s : Set ℕ} : actFin.toAction.Applicable s ↔ fr 1 ∈ s ∧ fr 2 ∈ s ∧ dB ∈ s := by
  rw [toAction_applicable rfl]; simp [actFin]
theorem app_end {s : Set ℕ} : actEnd.toAction.Applicable s := by
  rw [toAction_applicable rfl]; simp [actEnd]
theorem app_init {s : Set ℕ} : actInit.toAction.Applicable s := by
  rw [toAction_applicable rfl]; simp [actInit]
theorem app_cheat {k : ℕ} {s : Set ℕ} : (actCheat M X s₁ s₂ k).toAction.Applicable s ↔ ok k ∈ s := by
  rw [toAction_applicable rfl]; simp [actCheat]

theorem out_A {ℓ : Letter} {s s' : Set ℕ} : s' ∈ (actA ℓ).toAction.outcomes s ↔
    s' = Action.applyEff ({f | f ∈ addA 1 ℓ.1 ++ addA 2 ℓ.2}, {f | f ∈ preA 1 ℓ.1 ++ preA 2 ℓ.2}) s :=
  toAction_outcomes (x := (addA 1 ℓ.1 ++ addA 2 ℓ.2, preA 1 ℓ.1 ++ preA 2 ℓ.2)) rfl
theorem out_B {ℓ : Letter} {s s' : Set ℕ} : s' ∈ (actB ℓ).toAction.outcomes s ↔
    s' = Action.applyEff ({f | f ∈ addB 1 ℓ.1 ++ addB 2 ℓ.2}, {f | f ∈ preB 1 ℓ.1 ++ preB 2 ℓ.2}) s :=
  toAction_outcomes (x := (addB 1 ℓ.1 ++ addB 2 ℓ.2, preB 1 ℓ.1 ++ preB 2 ℓ.2)) rfl
theorem out_fin {s s' : Set ℕ} : s' ∈ actFin.toAction.outcomes s ↔
    s' = Action.applyEff ({f | f ∈ [ok 1, ok 2]}, {f | f ∈ ([] : List ℕ)}) s :=
  toAction_outcomes (x := ([ok 1, ok 2], [])) rfl
theorem out_end {s s' : Set ℕ} : s' ∈ actEnd.toAction.outcomes s ↔
    s' = Action.applyEff ({f | f ∈ [dB]}, {f | f ∈ ([] : List ℕ)}) s :=
  toAction_outcomes (x := ([dB], [])) rfl
theorem out_cheat {k : ℕ} {s s' : Set ℕ} : s' ∈ (actCheat M X s₁ s₂ k).toAction.outcomes s ↔
    s' = Action.applyEff ({f | f ∈ fr k :: (chars M X s₁ s₂).map (pd k)}, {f | f ∈ ([] : List ℕ)}) s :=
  toAction_outcomes (x := (fr k :: (chars M X s₁ s₂).map (pd k), [])) rfl
theorem out_init {s s' : Set ℕ} : s' ∈ actInit.toAction.outcomes s ↔
    s' = Action.applyEff ({f | f ∈ [fr 1, ok 2]}, {f | f ∈ ([] : List ℕ)}) s ∨
    s' = Action.applyEff ({f | f ∈ [fr 2, ok 1]}, {f | f ∈ ([] : List ℕ)}) s := by
  rw [Action.mem_outcomes]
  constructor
  · rintro ⟨e, ⟨y, hy, rfl⟩, rfl⟩
    simp only [actInit, FActDesc.effs, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨([fr 1, ok 2], []), by simp [actInit, FActDesc.effs], rfl⟩, rfl⟩
    · exact ⟨_, ⟨([fr 2, ok 1], []), by simp [actInit, FActDesc.effs], rfl⟩, rfl⟩

/-! ## The pool -/

/-- The pool: chain `B` (rest `bc`) and the supply chains with `K 1`, `K 2` cheats left. -/
def Pl (bc : List ℕ) (K : ℕ → ℕ) : Multiset (List ℕ) :=
  bc ::ₘ List.replicate (K 1) (nCheat 1) ::ₘ List.replicate (K 2) (nCheat 2) ::ₘ 0

theorem Pl_eq1 (bc : List ℕ) (K : ℕ → ℕ) : Pl bc K =
    List.replicate (K 1) (nCheat 1) ::ₘ bc ::ₘ List.replicate (K 2) (nCheat 2) ::ₘ 0 := by
  rw [Pl, Multiset.cons_swap]

theorem Pl_eq2 (bc : List ℕ) (K : ℕ → ℕ) : Pl bc K =
    List.replicate (K 2) (nCheat 2) ::ₘ bc ::ₘ List.replicate (K 1) (nCheat 1) ::ₘ 0 := by
  rw [Pl, Multiset.cons_swap (List.replicate (K 1) _), Multiset.cons_swap bc]

theorem pool_cheat {bc : List ℕ} {K : ℕ → ℕ} {k j : ℕ} (hk : k = 1 ∨ k = 2) (hK : K k = j + 1) :
    nCheat k :: List.replicate j (nCheat k) ∈ Pl bc K ∧
    List.replicate j (nCheat k) ::ₘ (Pl bc K).erase (nCheat k :: List.replicate j (nCheat k)) =
      Pl bc (Function.update K k j) := by
  rcases hk with rfl | rfl
  · rw [Pl_eq1, hK, List.replicate_succ, Multiset.erase_cons_head, Pl_eq1]
    refine ⟨by simp, ?_⟩
    simp [Function.update_apply]
  · rw [Pl_eq2, hK, List.replicate_succ, Multiset.erase_cons_head, Pl_eq2]
    refine ⟨by simp, ?_⟩
    simp [Function.update_apply]

/-- The moves on the pool. -/
theorem pool_cases {bc : List ℕ} {K : ℕ → ℕ} {a : ℕ} {c : List ℕ} (h : a :: c ∈ Pl bc K) :
    (a :: c = bc ∧ c ::ₘ (Pl bc K).erase (a :: c) = Pl c K) ∨
    (∃ k j, (k = 1 ∨ k = 2) ∧ K k = j + 1 ∧ a = nCheat k ∧ c = List.replicate j (nCheat k) ∧
      c ::ₘ (Pl bc K).erase (a :: c) = Pl bc (Function.update K k j)) := by
  simp only [Pl, Multiset.mem_cons, Multiset.notMem_zero, or_false] at h
  rcases h with h | h | h
  · left; refine ⟨h, ?_⟩
    rw [h, Pl, Multiset.erase_cons_head, Pl]
  · right
    cases hK : K 1 with
    | zero => rw [hK] at h; simp at h
    | succ j =>
      rw [hK, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨1, j, Or.inl rfl, hK, rfl, rfl, (pool_cheat (Or.inl rfl) hK).2⟩
  · right
    cases hK : K 2 with
    | zero => rw [hK] at h; simp at h
    | succ j =>
      rw [hK, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨2, j, Or.inr rfl, hK, rfl, rfl, (pool_cheat (Or.inr rfl) hK).2⟩

theorem pool_B {x : ℕ} {bc : List ℕ} {K : ℕ → ℕ} :
    x :: bc ∈ Pl (x :: bc) K ∧ bc ::ₘ (Pl (x :: bc) K).erase (x :: bc) = Pl bc K := by
  refine ⟨by simp [Pl], ?_⟩
  rw [Pl, Multiset.erase_cons_head, Pl]

end PCP

end FOND
