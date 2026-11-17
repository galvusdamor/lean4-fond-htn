import FondHtn.DB25.Machine
/-!
# The meaning of the machine blocks

* `FOND.DB.loop_sem` — a loop block requires the transition's state and head literals and, if the
  checked cell is under the head, that it holds the read symbol; it writes the next content and
  updates head and state (`FOND.DB.stepRho`);
* `FOND.DB.pre_sem` — the initial block: for every cell chosen by nature, the content is the input
  symbol;
* `FOND.DB.final_sem` — the final block requires an accepting state.

Terminal conditions are assumed to depend only on the cell, head and content registers
(`FOND.DB.Good`).
-/

namespace FOND

namespace DB

/-! ## Registers are distinct -/

@[simp] theorem cB_inj {a b : ℕ} : cB a = cB b ↔ a = b := by simp [cB, Nat.pair_eq_pair]
@[simp] theorem hB_inj {a b : ℕ} : hB a = hB b ↔ a = b := by simp [hB, Nat.pair_eq_pair]
@[simp] theorem sB_inj {a b : ℕ} : sB a = sB b ↔ a = b := by simp [sB, Nat.pair_eq_pair]
@[simp] theorem tB_inj {a b : ℕ} : tB a = tB b ↔ a = b := by simp [tB, Nat.pair_eq_pair]
@[simp] theorem dB_inj {a b : ℕ} : dB a = dB b ↔ a = b := by simp [dB, Nat.pair_eq_pair]
@[simp] theorem gB_inj {a b : ℕ} : gB a = gB b ↔ a = b := by simp [gB, Nat.pair_eq_pair]

section Distinct
variable (a b : ℕ)
@[simp] theorem cB_ne_hB : cB a ≠ hB b := by simp [cB, hB, Nat.pair_eq_pair]
@[simp] theorem cB_ne_sB : cB a ≠ sB b := by simp [cB, sB, Nat.pair_eq_pair]
@[simp] theorem cB_ne_tB : cB a ≠ tB b := by simp [cB, tB, Nat.pair_eq_pair]
@[simp] theorem cB_ne_dB : cB a ≠ dB b := by simp [cB, dB, Nat.pair_eq_pair]
@[simp] theorem cB_ne_gB : cB a ≠ gB b := by simp [cB, gB, Nat.pair_eq_pair]
@[simp] theorem hB_ne_cB : hB a ≠ cB b := by simp [cB, hB, Nat.pair_eq_pair]
@[simp] theorem hB_ne_sB : hB a ≠ sB b := by simp [hB, sB, Nat.pair_eq_pair]
@[simp] theorem hB_ne_tB : hB a ≠ tB b := by simp [hB, tB, Nat.pair_eq_pair]
@[simp] theorem hB_ne_dB : hB a ≠ dB b := by simp [hB, dB, Nat.pair_eq_pair]
@[simp] theorem hB_ne_gB : hB a ≠ gB b := by simp [hB, gB, Nat.pair_eq_pair]
@[simp] theorem sB_ne_cB : sB a ≠ cB b := by simp [cB, sB, Nat.pair_eq_pair]
@[simp] theorem sB_ne_hB : sB a ≠ hB b := by simp [hB, sB, Nat.pair_eq_pair]
@[simp] theorem sB_ne_tB : sB a ≠ tB b := by simp [sB, tB, Nat.pair_eq_pair]
@[simp] theorem sB_ne_dB : sB a ≠ dB b := by simp [sB, dB, Nat.pair_eq_pair]
@[simp] theorem sB_ne_gB : sB a ≠ gB b := by simp [sB, gB, Nat.pair_eq_pair]
@[simp] theorem tB_ne_cB : tB a ≠ cB b := by simp [cB, tB, Nat.pair_eq_pair]
@[simp] theorem tB_ne_hB : tB a ≠ hB b := by simp [hB, tB, Nat.pair_eq_pair]
@[simp] theorem tB_ne_sB : tB a ≠ sB b := by simp [sB, tB, Nat.pair_eq_pair]
@[simp] theorem tB_ne_dB : tB a ≠ dB b := by simp [tB, dB, Nat.pair_eq_pair]
@[simp] theorem dB_ne_cB : dB a ≠ cB b := by simp [cB, dB, Nat.pair_eq_pair]
@[simp] theorem dB_ne_hB : dB a ≠ hB b := by simp [hB, dB, Nat.pair_eq_pair]
@[simp] theorem dB_ne_sB : dB a ≠ sB b := by simp [sB, dB, Nat.pair_eq_pair]
@[simp] theorem dB_ne_tB : dB a ≠ tB b := by simp [tB, dB, Nat.pair_eq_pair]
@[simp] theorem gB_ne_cB : gB a ≠ cB b := by simp [cB, gB, Nat.pair_eq_pair]
@[simp] theorem gB_ne_hB : gB a ≠ hB b := by simp [hB, gB, Nat.pair_eq_pair]
@[simp] theorem gB_ne_sB : gB a ≠ sB b := by simp [sB, gB, Nat.pair_eq_pair]
end Distinct

/-! ## Blocks of choices -/

/-- `ρ` with the registers `rs` overwritten by `τ`. -/
def updOn (rs : List ℕ) (τ ρ : ℕ → Bool) : ℕ → Bool := fun x => if x ∈ rs then τ x else ρ x

theorem blockSem_append (a b : List Op) (K : (ℕ → Bool) → ℕ → Prop) :
    blockSem (a ++ b) K = blockSem a (blockSem b K) := by
  simp [blockSem, List.foldr_append]

theorem blockSem_cons (op : Op) (ops : List Op) (K : (ℕ → Bool) → ℕ → Prop) :
    blockSem (op :: ops) K = opSem op (blockSem ops K) := rfl

theorem updOn_nil (τ ρ : ℕ → Bool) : updOn [] τ ρ = ρ := by funext x; simp [updOn]

theorem updOn_cons_eq (r : ℕ) (rs : List ℕ) (τ ρ : ℕ → Bool) :
    updOn (r :: rs) τ ρ = updOn rs τ (Function.update ρ r (τ r)) := by
  funext x
  by_cases hx : x ∈ rs
  · simp [updOn, hx]
  · by_cases hxr : x = r
    · subst hxr; simp [updOn, hx]
    · simp [updOn, hx, hxr]

theorem updOn_cons_eq' (r : ℕ) (rs : List ℕ) (τ ρ : ℕ → Bool) (b : Bool) :
    updOn rs τ (Function.update ρ r b) = updOn (r :: rs) (fun x => if x ∈ rs then τ x else b) ρ := by
  funext x
  by_cases hx : x ∈ rs
  · simp [updOn, hx]
  · by_cases hxr : x = r
    · subst hxr; simp [updOn, hx]
    · simp [updOn, hx, hxr]

theorem blockSem_choices (rest : List Op) (K : (ℕ → Bool) → ℕ → Prop) : ∀ (rs : List ℕ)
    (ρ : ℕ → Bool) (q : ℕ),
    blockSem (rs.map Op.choice ++ rest) K ρ q ↔ ∃ τ, blockSem rest K (updOn rs τ ρ) q
  | [], ρ, q => by simp [updOn_nil]
  | r :: rs, ρ, q => by
    rw [List.map_cons, List.cons_append, blockSem_cons, opSem]
    simp only [blockSem_choices rest K rs]
    constructor
    · rintro ⟨b, τ, h⟩
      exact ⟨_, by rw [← updOn_cons_eq' r rs τ ρ b]; exact h⟩
    · rintro ⟨τ, h⟩
      exact ⟨τ r, τ, by rw [← updOn_cons_eq]; exact h⟩

theorem blockSem_natures (rest : List Op) (K : (ℕ → Bool) → ℕ → Prop) : ∀ (rs : List ℕ)
    (ρ : ℕ → Bool) (q : ℕ),
    blockSem (rs.map Op.nature ++ rest) K ρ q ↔ ∀ τ, blockSem rest K (updOn rs τ ρ) q
  | [], ρ, q => by simp [updOn_nil]
  | r :: rs, ρ, q => by
    rw [List.map_cons, List.cons_append, blockSem_cons, opSem]
    simp only [blockSem_natures rest K rs]
    constructor
    · intro h τ
      rw [updOn_cons_eq]; exact h (τ r) τ
    · intro h b τ
      rw [updOn_cons_eq']; exact h _

/-! ## Terminal conditions reading only cell, head and content -/

/-- `ρ` and `ρ'` agree on the cell, head and content registers. -/
def Agree (n : ℕ) (ρ ρ' : ℕ → Bool) : Prop :=
  (∀ b < n, ρ (cB b) = ρ' (cB b)) ∧ (∀ b < n, ρ (hB b) = ρ' (hB b)) ∧
    ρ (sB 0) = ρ' (sB 0) ∧ ρ (sB 1) = ρ' (sB 1)

/-- The condition depends only on the cell, head and content registers. -/
def Good (n : ℕ) (K : (ℕ → Bool) → ℕ → Prop) : Prop :=
  ∀ ρ ρ' q, Agree n ρ ρ' → (K ρ q ↔ K ρ' q)

/-! ## CNFs -/

theorem satC_cons (ρ : ℕ → Bool) (l : ℕ × Bool) (C : Clause) :
    SatC ρ (l :: C) ↔ ρ l.1 = l.2 ∨ SatC ρ C := by
  simp [SatC]

theorem satC_nil (ρ : ℕ → Bool) : ¬ SatC ρ [] := by simp [SatC]

theorem satC_append (ρ : ℕ → Bool) (C D : Clause) : SatC ρ (C ++ D) ↔ SatC ρ C ∨ SatC ρ D := by
  simp only [SatC, List.mem_append]
  constructor
  · rintro ⟨l, hl | hl, h⟩
    · exact Or.inl ⟨l, hl, h⟩
    · exact Or.inr ⟨l, hl, h⟩
  · rintro (⟨l, hl, h⟩ | ⟨l, hl, h⟩)
    · exact ⟨l, Or.inl hl, h⟩
    · exact ⟨l, Or.inr hl, h⟩

theorem satC_map_range (ρ : ℕ → Bool) (n : ℕ) (f : ℕ → ℕ × Bool) :
    SatC ρ ((List.range n).map f) ↔ ∃ b < n, ρ (f b).1 = (f b).2 := by
  simp [SatC]

/-- **The CNF of a step.** -/
theorem sat_phiStep (n : ℕ) (τ : TrD) (ρ : ℕ → Bool) :
    (∀ C ∈ phiStep n τ, SatC ρ C) ↔
      (∀ b < n, ρ (dB b) = true → ρ (cB b) ≠ ρ (hB b)) ∧
      (∀ j < 2, (∃ b < n, ρ (dB b) = true) ∨ ρ (sB j) = ebit τ.2.1 j) ∧
      (∀ j < 2, (∃ b < n, ρ (dB b) = true) ∨ ρ (tB j) = ebit τ.2.2.2 j) ∧
      (∀ b < n, ∀ j < 2, ρ (cB b) ≠ ρ (hB b) → ρ (tB j) = ρ (sB j)) := by
  simp only [phiStep, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    refine ⟨fun b hb hd => ?_, fun j hj => ?_, fun j hj => ?_, fun b hb j hj hne => ?_⟩
    · have h1 := h _ (Or.inl (Or.inl (Or.inl ⟨b, hb, Or.inl rfl⟩)))
      have h2 := h _ (Or.inl (Or.inl (Or.inl ⟨b, hb, Or.inr rfl⟩)))
      simp only [satC_cons, satC_nil, or_false] at h1 h2
      intro heq
      rw [heq] at h1
      cases hh : ρ (hB b) <;> simp_all
    · have h1 := h _ (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩)))
      rw [satC_append, satC_map_range] at h1
      simpa [satC_cons, satC_nil] using h1
    · have h1 := h _ (Or.inl (Or.inr ⟨j, hj, rfl⟩))
      rw [satC_append, satC_map_range] at h1
      simpa [satC_cons, satC_nil] using h1
    · have h1 := h _ (Or.inr ⟨b, hb, j, hj, Or.inl rfl⟩)
      have h2 := h _ (Or.inr ⟨b, hb, j, hj, Or.inr (Or.inl rfl)⟩)
      have h3 := h _ (Or.inr ⟨b, hb, j, hj, Or.inr (Or.inr (Or.inl rfl))⟩)
      have h4 := h _ (Or.inr ⟨b, hb, j, hj, Or.inr (Or.inr (Or.inr rfl))⟩)
      simp only [satC_cons, satC_nil, or_false] at h1 h2 h3 h4
      cases hc : ρ (cB b) <;> cases hh : ρ (hB b) <;> cases ht : ρ (tB j) <;>
        cases hs : ρ (sB j) <;> simp_all
  · rintro ⟨hD, hR, hW, hK⟩ C hC
    rcases hC with ((⟨b, hb, rfl | rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨b, hb, j, hj, hC⟩
    · simp only [satC_cons, satC_nil, or_false]
      have := hD b hb
      cases hd : ρ (dB b) <;> cases hc : ρ (cB b) <;> cases hh : ρ (hB b) <;> simp_all
    · simp only [satC_cons, satC_nil, or_false]
      have := hD b hb
      cases hd : ρ (dB b) <;> cases hc : ρ (cB b) <;> cases hh : ρ (hB b) <;> simp_all
    · rw [satC_append, satC_map_range]
      rcases hR j hj with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [satC_cons, h])
    · rw [satC_append, satC_map_range]
      rcases hW j hj with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [satC_cons, h])
    · have := hK b hb j hj
      by_cases heq : ρ (cB b) = ρ (hB b)
      · rcases hC with rfl | rfl | rfl | rfl <;> simp only [satC_cons, satC_nil, or_false] <;>
          revert heq <;> cases ρ (cB b) <;> cases ρ (hB b) <;> simp
      · have hts := this heq
        rcases hC with rfl | rfl | rfl | rfl <;> simp only [satC_cons, satC_nil, or_false] <;>
          rw [hts] <;> cases ρ (sB j) <;> simp

/-! ## Loop blocks -/

/-- The checked cell is under the head. -/
def EqCH (n : ℕ) (ρ : ℕ → Bool) : Prop := ∀ b < n, ρ (cB b) = ρ (hB b)

instance (n : ℕ) (ρ : ℕ → Bool) : Decidable (EqCH n ρ) := by unfold EqCH; infer_instance

/-- The next content bit. -/
def nextSym (n : ℕ) (d : TrD × HU) (ρ : ℕ → Bool) (j : ℕ) : Bool :=
  if EqCH n ρ then ebit d.1.2.2.2 j else ρ (sB j)

/-- The registers after a loop block. -/
def stepRho (n : ℕ) (d : TrD × HU) (ρ : ℕ → Bool) : ℕ → Bool :=
  setAll (Function.update (Function.update ρ (sB 0) (nextSym n d ρ 0)) (sB 1) (nextSym n d ρ 1))
    (d.2.2.map hl)

theorem setAll_of_not_key {ρ : ℕ → Bool} {sets : List (ℕ × Bool)} {x : ℕ}
    (h : ∀ b, (x, b) ∉ sets) : setAll ρ sets x = ρ x := by
  simp [setAll, h true, h false]

theorem setAll_congr {ρ ρ' : ℕ → Bool} (sets : List (ℕ × Bool)) {x : ℕ} (h : ρ x = ρ' x) :
    setAll ρ sets x = setAll ρ' sets x := by
  simp only [setAll]; split_ifs <;> simp_all

theorem not_key_hl {x : ℕ} (hx : ∀ i, x ≠ hB i) (L : List (ℕ × Bool)) : ∀ b, (x, b) ∉ L.map hl := by
  intro b h
  obtain ⟨l, -, hl'⟩ := List.mem_map.1 h
  simp only [hl, Prod.mk.injEq] at hl'
  exact hx _ hl'.1.symm

theorem agree_setAll {n : ℕ} {ρ ρ' : ℕ → Bool} (L : List (ℕ × Bool)) (h : Agree n ρ ρ') :
    Agree n (setAll ρ (L.map hl)) (setAll ρ' (L.map hl)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun b hb => ?_, fun b hb => setAll_congr _ (h2 b hb), ?_, ?_⟩
  · rw [setAll_of_not_key (not_key_hl (fun i => cB_ne_hB _ _) L),
      setAll_of_not_key (not_key_hl (fun i => cB_ne_hB _ _) L)]; exact h1 b hb
  · rw [setAll_of_not_key (not_key_hl (fun i => sB_ne_hB _ _) L),
      setAll_of_not_key (not_key_hl (fun i => sB_ne_hB _ _) L)]; exact h3
  · rw [setAll_of_not_key (not_key_hl (fun i => sB_ne_hB _ _) L),
      setAll_of_not_key (not_key_hl (fun i => sB_ne_hB _ _) L)]; exact h4

theorem mem_stepChoices {n x : ℕ} : x ∈ stepChoices n ↔ x = tB 0 ∨ x = tB 1 ∨ ∃ b < n, x = dB b := by
  simp only [stepChoices, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range]
  constructor
  · rintro ((h | h) | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨b, hb, rfl⟩)
  · rintro (h | h | ⟨b, hb, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨b, hb, rfl⟩

/-- **A loop block.** -/
theorem loop_sem {n : ℕ} {K : (ℕ → Bool) → ℕ → Prop} (hK : Good n K) (d : TrD × HU)
    (ρ : ℕ → Bool) (q : ℕ) :
    blockSem (loopOps n d) K ρ q ↔ q = d.1.1 ∧ (∀ l ∈ d.2.1, ρ (hB l.1) = l.2) ∧
      (EqCH n ρ → ρ (sB 0) = ebit d.1.2.1 0 ∧ ρ (sB 1) = ebit d.1.2.1 1) ∧
      K (stepRho n d ρ) d.1.2.2.1 := by
  rw [loopOps, blockSem_choices]
  simp only [blockSem, List.foldr_cons, List.foldr_nil, opSem]
  -- values of the updated registers
  have hc : ∀ τ b, updOn (stepChoices n) τ ρ (cB b) = ρ (cB b) := fun τ b => by
    simp [updOn, mem_stepChoices]
  have hh : ∀ τ b, updOn (stepChoices n) τ ρ (hB b) = ρ (hB b) := fun τ b => by
    simp [updOn, mem_stepChoices]
  have hs : ∀ τ j, updOn (stepChoices n) τ ρ (sB j) = ρ (sB j) := fun τ j => by
    simp [updOn, mem_stepChoices]
  have ht : ∀ τ j, j < 2 → updOn (stepChoices n) τ ρ (tB j) = τ (tB j) := fun τ j hj => by
    have : tB j ∈ stepChoices n := by
      rw [mem_stepChoices]; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp
    simp [updOn, this]
  have hd : ∀ τ b, b < n → updOn (stepChoices n) τ ρ (dB b) = τ (dB b) := fun τ b hb => by
    have : dB b ∈ stepChoices n := mem_stepChoices.2 (Or.inr (Or.inr ⟨b, hb, rfl⟩))
    simp [updOn, this]
  -- the state after the copies
  set ρ3 : (ℕ → Bool) → ℕ → Bool := fun τ =>
    Function.update (Function.update (updOn (stepChoices n) τ ρ) (sB 0)
      (updOn (stepChoices n) τ ρ (tB 0))) (sB 1)
      (Function.update (updOn (stepChoices n) τ ρ) (sB 0) (updOn (stepChoices n) τ ρ (tB 0))
        (tB 1)) with hρ3
  have hagree : ∀ τ, (∀ j < 2, τ (tB j) = nextSym n d ρ j) →
      Agree n (setAll (ρ3 τ) (d.2.2.map hl)) (stepRho n d ρ) := by
    intro τ hτ
    refine agree_setAll _ ⟨fun b _ => ?_, fun b _ => ?_, ?_, ?_⟩
    · simp [ρ3, hc]
    · simp [ρ3, hh]
    · simp [ρ3, ht τ 0 (by omega), hτ 0 (by omega)]
    · simp [ρ3, ht τ 1 (by omega), hτ 1 (by omega)]
  have hpre : ∀ τ, (∀ l ∈ d.2.1.map hl, ρ3 τ l.1 = l.2) ↔ ∀ l ∈ d.2.1, ρ (hB l.1) = l.2 := by
    intro τ
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hl]
    exact forall₂_congr fun l _ => by simp [ρ3, hh]
  constructor
  · rintro ⟨τ, hΦ, hq, hp, hKK⟩
    have hp := (hpre τ).1 hp
    rw [sat_phiStep] at hΦ
    obtain ⟨hD, hR, hW, hKc⟩ := hΦ
    simp only [hc, hh, hs] at hD hR hW hKc
    have hτ : ∀ j < 2, τ (tB j) = nextSym n d ρ j := by
      intro j hj
      rw [← ht τ j hj]
      unfold nextSym
      split_ifs with heq
      · have hnd : ¬ ∃ b < n, updOn (stepChoices n) τ ρ (dB b) = true := by
          rintro ⟨b, hb, hdb⟩; exact hD b hb hdb (heq b hb)
        exact (hW j hj).resolve_left hnd
      · simp only [EqCH, not_forall] at heq
        obtain ⟨b, hb, hne⟩ := heq
        exact hKc b hb j hj hne
    refine ⟨hq, hp, fun heq => ?_, (hK _ _ _ (hagree τ hτ)).1 hKK⟩
    have hnd : ¬ ∃ b < n, updOn (stepChoices n) τ ρ (dB b) = true := by
      rintro ⟨b, hb, hdb⟩; exact hD b hb hdb (heq b hb)
    exact ⟨(hR 0 (by omega)).resolve_left hnd, (hR 1 (by omega)).resolve_left hnd⟩
  · rintro ⟨hq, hp, hread, hKs⟩
    let τ : ℕ → Bool := fun x => if x = tB 0 then nextSym n d ρ 0 else if x = tB 1 then
      nextSym n d ρ 1 else decide (∃ b < n, x = dB b ∧ ρ (cB b) ≠ ρ (hB b))
    have hτ : ∀ j < 2, τ (tB j) = nextSym n d ρ j := by
      intro j hj; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [τ]
    have hτd : ∀ b < n, τ (dB b) = decide (ρ (cB b) ≠ ρ (hB b)) := by
      intro b hb
      simp only [τ, dB_ne_tB, if_false]
      congr 1
      exact propext ⟨fun ⟨b', hb', he, h⟩ => by rw [dB_inj] at he; subst he; exact h,
        fun h => ⟨b, hb, rfl, h⟩⟩
    refine ⟨τ, ?_, hq, (hpre τ).2 hp, (hK _ _ _ (hagree τ hτ)).2 hKs⟩
    rw [sat_phiStep]
    simp only [hc, hh, hs]
    refine ⟨fun b hb hdb => ?_, fun j hj => ?_, fun j hj => ?_, fun b hb j hj hne => ?_⟩
    · rw [hd τ b hb, hτd b hb] at hdb; simpa using hdb
    · by_cases heq : EqCH n ρ
      · right
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · exact (hread heq).1
        · exact (hread heq).2
      · left
        simp only [EqCH, not_forall] at heq
        obtain ⟨b, hb, hne⟩ := heq
        exact ⟨b, hb, by rw [hd τ b hb, hτd b hb]; simpa using hne⟩
    · by_cases heq : EqCH n ρ
      · right; rw [ht τ j hj, hτ j hj]; simp [nextSym, heq]
      · left
        simp only [EqCH, not_forall] at heq
        obtain ⟨b, hb, hne⟩ := heq
        exact ⟨b, hb, by rw [hd τ b hb, hτd b hb]; simpa using hne⟩
    · rw [ht τ j hj, hτ j hj]
      have : ¬ EqCH n ρ := fun h => hne (h b hb)
      simp [nextSym, this]

/-! ## Final blocks -/

theorem setAll_nil (ρ : ℕ → Bool) : setAll ρ [] = ρ := by funext x; simp [setAll]

theorem final_sem (acc : ℕ) (K : (ℕ → Bool) → ℕ → Prop) (ρ : ℕ → Bool) (q : ℕ) :
    blockSem (finalOps acc) K ρ q ↔ q = acc ∧ K ρ acc := by
  simp [finalOps, blockSem, opSem, setAll_nil]

end DB


end FOND
