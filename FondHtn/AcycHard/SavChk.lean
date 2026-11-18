import FondHtn.ATM.Savitch
/-!
# The check automaton of the Savitch game

A configuration `c` with the head on the cells `0 … S - 1` is written as the list of its first
`S` cells, each cell carrying the tape symbol and the state if the head is there
(`FOND.AcycHard.Sav.enc`).  The nondeterministic automaton `FOND.AcycHard.Sav.chk` reads the
pairs of cells of two such lists from left to right and accepts iff the configurations are equal
or the second follows from the first by one step of the machine
(`FOND.AcycHard.Sav.acc_iff`).

States: `start` (cell `0`), `eqp`/`eqd` (equality, before/after the head), `pre` (before the
head), `pl q'` (the new head is one cell left: the old head comes next), `pr q'` (the new head
comes next), `dn` (after the step).
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

namespace Sav

open HTN TM

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] (N : NTM Q Γ)

/-- The contents of a cell: tape symbol and the state if the head is there. -/
abbrev X (Q Γ : Type) := Γ × Option Q

/-- The states of the check automaton. -/
inductive CS (Q : Type)
  | start
  | eqp
  | eqd
  | pre
  | pl (q : Q)
  | pr (q : Q)
  | dn
  deriving DecidableEq

/-- Equal cells without the head. -/
def NoM (p : X Q Γ × X Q Γ) : Prop := p.1 = p.2 ∧ p.1.2 = none

/-- The transitions before the head (`pre`). -/
def preT (p : X Q Γ × X Q Γ) (c' : CS Q) : Prop :=
  (NoM p ∧ c' = .pre) ∨ (p.1.2 = none ∧ ∃ q', p.2 = (p.1.1, some q') ∧ c' = .pl q') ∨
  (∃ q, p.1.2 = some q ∧ ∃ q' γ',
    ((q', γ', Move.stay) ∈ N.step q p.1.1 ∧ p.2 = (γ', some q') ∧ c' = .dn) ∨
    ((q', γ', Move.right) ∈ N.step q p.1.1 ∧ p.2 = (γ', none) ∧ c' = .pr q'))

/-- The transitions of the equality branch before the head. -/
def eqT (p : X Q Γ × X Q Γ) (c' : CS Q) : Prop :=
  p.1 = p.2 ∧ ((p.1.2 = none ∧ c' = .eqp) ∨ (p.1.2 ≠ none ∧ c' = .eqd))

/-- A left move at cell `0` (the head stays). -/
def left0 (p : X Q Γ × X Q Γ) (c' : CS Q) : Prop :=
  ∃ q, p.1.2 = some q ∧ ∃ q' γ', (q', γ', Move.left) ∈ N.step q p.1.1 ∧ p.2 = (γ', some q') ∧
    c' = .dn

/-- **The transitions of the check automaton.** -/
def chk : CS Q → X Q Γ × X Q Γ → CS Q → Prop
  | .start, p, c' => eqT p c' ∨ preT N p c' ∨ left0 N p c'
  | .eqp, p, c' => eqT p c'
  | .eqd, p, c' => NoM p ∧ c' = .eqd
  | .pre, p, c' => preT N p c'
  | .pl q', p, c' => (∃ q, p.1.2 = some q ∧ ∃ γ', (q', γ', Move.left) ∈ N.step q p.1.1 ∧
      p.2 = (γ', none)) ∧ c' = .dn
  | .pr q', p, c' => p.1.2 = none ∧ p.2 = (p.1.1, some q') ∧ c' = .dn
  | .dn, p, c' => NoM p ∧ c' = .dn

/-- Accepting states. -/
def final : CS Q → Prop
  | .eqd => True
  | .dn => True
  | _ => False

/-- **Acceptance** of a list of pairs from a state. -/
def Acc : CS Q → List (X Q Γ × X Q Γ) → Prop
  | c, [] => final c
  | c, p :: ps => ∃ c', chk N c p c' ∧ Acc c' ps

/-! ## Encodings of configurations -/

/-- Cell `i` of a configuration. -/
def mk (c : Config Q Γ) (i : ℕ) : X Q Γ := (c.tape i, if i = c.head then some c.state else none)

/-- **The first `S` cells of a configuration.** -/
def enc (S : ℕ) (c : Config Q Γ) : List (X Q Γ) := (List.range S).map (mk c)

@[simp] theorem mk_fst (c : Config Q Γ) (i : ℕ) : (mk c i).1 = c.tape i := rfl

theorem mk_snd_none {c : Config Q Γ} {i : ℕ} : (mk c i).2 = none ↔ i ≠ c.head := by
  simp [mk]

theorem mk_snd_some {c : Config Q Γ} {i : ℕ} {q : Q} : (mk c i).2 = some q ↔ i = c.head ∧ c.state = q := by
  simp [mk]

variable (S : ℕ) (c c' : Config Q Γ)

/-- The pairs of cells from position `i` on. -/
def sfx (i : ℕ) : List (X Q Γ × X Q Γ) := (List.range' i (S - i)).map fun l => (mk c l, mk c' l)

theorem sfx_lt {i : ℕ} (h : i < S) : sfx S c c' i = (mk c i, mk c' i) :: sfx S c c' (i + 1) := by
  unfold sfx
  rw [show S - i = (S - (i + 1)) + 1 by omega, List.range'_succ]; rfl

theorem sfx_ge {i : ℕ} (h : S ≤ i) : sfx S c c' i = [] := by simp [sfx, Nat.sub_eq_zero_of_le h]

theorem zip_enc : (enc S c).zip (enc S c') = sfx S c c' 0 := by
  simp [enc, sfx, List.range_eq_range', List.zip_map']

/-- Equal cells without the head, from position `i` on. -/
def Dn (i : ℕ) : Prop := ∀ l, i ≤ l → l < S → NoM (mk c l, mk c' l)

theorem dn_ge {i : ℕ} (h : S ≤ i) : Dn S c c' i := fun l hl hl' => absurd hl' (by omega)

theorem dn_lt {i : ℕ} (h : i < S) : Dn S c c' i ↔ NoM (mk c i, mk c' i) ∧ Dn S c c' (i + 1) := by
  constructor
  · intro hd; exact ⟨hd i le_rfl h, fun l hl hl' => hd l (by omega) hl'⟩
  · rintro ⟨h1, h2⟩ l hl hl'
    rcases Nat.eq_or_lt_of_le hl with rfl | hl
    · exact h1
    · exact h2 l hl hl'

/-! ## Acceptance from each state -/

theorem acc_dn_eqd : ∀ (n i : ℕ), S - i = n →
    (Acc N .dn (sfx S c c' i) ↔ Dn S c c' i) ∧ (Acc N .eqd (sfx S c c' i) ↔ Dn S c c' i) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    rw [sfx_ge S c c' (by omega)]
    exact ⟨iff_of_true trivial (dn_ge S c c' (by omega)), iff_of_true trivial (dn_ge S c c' (by omega))⟩
  | succ n ih =>
    intro i hi
    rw [sfx_lt S c c' (by omega), dn_lt S c c' (by omega)]
    obtain ⟨ih1, ih2⟩ := ih (i + 1) (by omega)
    simp only [Acc, chk]
    constructor
    · constructor
      · rintro ⟨c'', ⟨h1, rfl⟩, h2⟩; exact ⟨h1, ih1.1 h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨_, ⟨h1, rfl⟩, ih1.2 h2⟩
    · constructor
      · rintro ⟨c'', ⟨h1, rfl⟩, h2⟩; exact ⟨h1, ih2.1 h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨_, ⟨h1, rfl⟩, ih2.2 h2⟩

theorem acc_dn (i : ℕ) : Acc N .dn (sfx S c c' i) ↔ Dn S c c' i := (acc_dn_eqd N S c c' _ i rfl).1
theorem acc_eqd (i : ℕ) : Acc N .eqd (sfx S c c' i) ↔ Dn S c c' i := (acc_dn_eqd N S c c' _ i rfl).2

theorem acc_pr (q' : Q) (i : ℕ) : Acc N (.pr q') (sfx S c c' i) ↔
    i < S ∧ (mk c i).2 = none ∧ mk c' i = (c.tape i, some q') ∧ Dn S c c' (i + 1) := by
  rcases Nat.lt_or_ge i S with h | h
  · rw [sfx_lt S c c' h]
    simp only [Acc, chk, mk_fst]
    constructor
    · rintro ⟨c'', ⟨h1, h2, rfl⟩, h3⟩; exact ⟨h, h1, h2, (acc_dn N S c c' _).1 h3⟩
    · rintro ⟨-, h1, h2, h3⟩; exact ⟨_, ⟨h1, h2, rfl⟩, (acc_dn N S c c' _).2 h3⟩
  · rw [sfx_ge S c c' h]; simp [Acc, final]; omega

theorem acc_pl (q' : Q) (i : ℕ) : Acc N (.pl q') (sfx S c c' i) ↔
    i < S ∧ (∃ q, (mk c i).2 = some q ∧ ∃ γ', (q', γ', Move.left) ∈ N.step q (c.tape i) ∧
      mk c' i = (γ', none)) ∧ Dn S c c' (i + 1) := by
  rcases Nat.lt_or_ge i S with h | h
  · rw [sfx_lt S c c' h]
    simp only [Acc, chk, mk_fst]
    constructor
    · rintro ⟨c'', ⟨h1, rfl⟩, h3⟩; exact ⟨h, h1, (acc_dn N S c c' _).1 h3⟩
    · rintro ⟨-, h1, h3⟩; exact ⟨_, ⟨h1, rfl⟩, (acc_dn N S c c' _).2 h3⟩
  · rw [sfx_ge S c c' h]; simp [Acc, final]; omega

/-- Cells without the head below `l`. -/
def NoMBelow (i l : ℕ) : Prop := ∀ m, i ≤ m → m < l → NoM (mk c m, mk c' m)

theorem acc_eqp : ∀ (n i : ℕ), S - i = n → (Acc N .eqp (sfx S c c' i) ↔
    ∃ l, i ≤ l ∧ l < S ∧ NoMBelow c c' i l ∧ mk c l = mk c' l ∧ (mk c l).2 ≠ none ∧
      Dn S c c' (l + 1)) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    rw [sfx_ge S c c' (by omega)]
    simp only [Acc, final, false_iff, not_exists, not_and]
    intro l h1 h2; omega
  | succ n ih =>
    intro i hi
    rw [sfx_lt S c c' (by omega)]
    simp only [Acc, chk, eqT]
    constructor
    · rintro ⟨c'', ⟨he, (⟨hn, rfl⟩ | ⟨hn, rfl⟩)⟩, h⟩
      · obtain ⟨l, h1, h2, h3, h4, h5, h6⟩ := (ih (i + 1) (by omega)).1 h
        refine ⟨l, by omega, h2, fun m hm hm' => ?_, h4, h5, h6⟩
        rcases Nat.eq_or_lt_of_le hm with rfl | hm
        · exact ⟨he, hn⟩
        · exact h3 m hm hm'
      · exact ⟨i, le_rfl, by omega, fun m hm hm' => absurd hm' (by omega), he, hn,
          (acc_eqd N S c c' _).1 h⟩
    · rintro ⟨l, h1, h2, h3, h4, h5, h6⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | hl
      · exact ⟨_, ⟨h4, Or.inr ⟨h5, rfl⟩⟩, (acc_eqd N S c c' _).2 h6⟩
      · obtain ⟨he, hn⟩ := h3 i le_rfl hl
        exact ⟨_, ⟨he, Or.inl ⟨hn, rfl⟩⟩, (ih (i + 1) (by omega)).2
          ⟨l, hl, h2, fun m hm hm' => h3 m (by omega) hm', h4, h5, h6⟩⟩

/-- The events of a step at position `l`. -/
def EvP (l : ℕ) : Prop :=
  ((mk c l).2 = none ∧ ∃ q', mk c' l = (c.tape l, some q') ∧ Acc N (.pl q') (sfx S c c' (l + 1))) ∨
  (∃ q, (mk c l).2 = some q ∧ ∃ q' γ',
    ((q', γ', Move.stay) ∈ N.step q (c.tape l) ∧ mk c' l = (γ', some q') ∧ Dn S c c' (l + 1)) ∨
    ((q', γ', Move.right) ∈ N.step q (c.tape l) ∧ mk c' l = (γ', none) ∧
      Acc N (.pr q') (sfx S c c' (l + 1))))

theorem acc_pre : ∀ (n i : ℕ), S - i = n → (Acc N .pre (sfx S c c' i) ↔
    ∃ l, i ≤ l ∧ l < S ∧ NoMBelow c c' i l ∧ EvP N S c c' l) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    rw [sfx_ge S c c' (by omega)]
    simp only [Acc, final, false_iff, not_exists, not_and]
    intro l h1 h2; omega
  | succ n ih =>
    intro i hi
    rw [sfx_lt S c c' (by omega)]
    simp only [Acc, chk, preT, mk_fst]
    constructor
    · rintro ⟨c'', hT, h⟩
      rcases hT with ⟨hn, rfl⟩ | ⟨hn, q', he, rfl⟩ | ⟨q, hq, q', γ', ⟨hs, he, rfl⟩ | ⟨hr, he, rfl⟩⟩
      · obtain ⟨l, h1, h2, h3, h4⟩ := (ih (i + 1) (by omega)).1 h
        refine ⟨l, by omega, h2, fun m hm hm' => ?_, h4⟩
        rcases Nat.eq_or_lt_of_le hm with rfl | hm
        · exact hn
        · exact h3 m hm hm'
      · exact ⟨i, le_rfl, by omega, fun m hm hm' => absurd hm' (by omega), Or.inl ⟨hn, q', he, h⟩⟩
      · exact ⟨i, le_rfl, by omega, fun m hm hm' => absurd hm' (by omega),
          Or.inr ⟨q, hq, q', γ', Or.inl ⟨hs, he, (acc_dn N S c c' _).1 h⟩⟩⟩
      · exact ⟨i, le_rfl, by omega, fun m hm hm' => absurd hm' (by omega),
          Or.inr ⟨q, hq, q', γ', Or.inr ⟨hr, he, h⟩⟩⟩
    · rintro ⟨l, h1, h2, h3, h4⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | hl
      · rcases h4 with ⟨hn, q', he, h⟩ | ⟨q, hq, q', γ', ⟨hs, he, h⟩ | ⟨hr, he, h⟩⟩
        · exact ⟨_, Or.inr (Or.inl ⟨hn, q', he, rfl⟩), h⟩
        · exact ⟨_, Or.inr (Or.inr ⟨q, hq, q', γ', Or.inl ⟨hs, he, rfl⟩⟩), (acc_dn N S c c' _).2 h⟩
        · exact ⟨_, Or.inr (Or.inr ⟨q, hq, q', γ', Or.inr ⟨hr, he, rfl⟩⟩), h⟩
      · exact ⟨_, Or.inl ⟨h3 i le_rfl hl, rfl⟩, (ih (i + 1) (by omega)).2
          ⟨l, hl, h2, fun m hm hm' => h3 m (by omega) hm', h4⟩⟩

theorem acc_start (hS : 0 < S) : Acc N .start (sfx S c c' 0) ↔
    Acc N .eqp (sfx S c c' 0) ∨ Acc N .pre (sfx S c c' 0) ∨
      ((∃ q, (mk c 0).2 = some q ∧ ∃ q' γ', (q', γ', Move.left) ∈ N.step q (c.tape 0) ∧
        mk c' 0 = (γ', some q')) ∧ Dn S c c' 1) := by
  rw [sfx_lt S c c' hS]
  simp only [Acc, chk, left0, mk_fst]
  constructor
  · rintro ⟨c'', (h | h | ⟨q, hq, q', γ', hl, he, rfl⟩), h'⟩
    · exact Or.inl ⟨c'', h, h'⟩
    · exact Or.inr (Or.inl ⟨c'', h, h'⟩)
    · exact Or.inr (Or.inr ⟨⟨q, hq, q', γ', hl, he⟩, (acc_dn N S c c' _).1 h'⟩)
  · rintro (⟨c'', h, h'⟩ | ⟨c'', h, h'⟩ | ⟨⟨q, hq, q', γ', hl, he⟩, h'⟩)
    · exact ⟨c'', Or.inl h, h'⟩
    · exact ⟨c'', Or.inr (Or.inl h), h'⟩
    · exact ⟨_, Or.inr (Or.inr ⟨q, hq, q', γ', hl, he, rfl⟩), (acc_dn N S c c' _).2 h'⟩

/-! ## Correctness -/

theorem noM_iff {m : ℕ} : NoM (mk c m, mk c' m) ↔ c.tape m = c'.tape m ∧ m ≠ c.head ∧ m ≠ c'.head := by
  simp only [NoM, mk, Prod.mk.injEq]
  by_cases h1 : m = c.head <;> by_cases h2 : m = c'.head <;> simp [h1, h2] <;> intros <;> simp_all

theorem config_eq {c c' : Config Q Γ} (h1 : c.state = c'.state) (h2 : c.head = c'.head)
    (h3 : ∀ i, c.tape i = c'.tape i) : c = c' := by
  cases c; cases c'; simp_all; funext i; exact h3 i

/-- **The check automaton accepts exactly equality and one step.** -/
theorem acc_iff (hS : 0 < S) (hc : c.head < S) (hc' : c'.head < S)
    (hout : ∀ i, S ≤ i → c.tape i = c'.tape i) :
    Acc N .start (sfx S c c' 0) ↔ c = c' ∨ N.Step c c' := by
  have hD : ∀ i, Dn S c c' i ↔ ∀ l, i ≤ l → l < S → c.tape l = c'.tape l ∧ l ≠ c.head ∧ l ≠ c'.head :=
    fun i => forall_congr' fun l => forall_congr' fun _ => forall_congr' fun _ => noM_iff c c'
  have hB : ∀ i l, NoMBelow c c' i l ↔ ∀ m, i ≤ m → m < l → c.tape m = c'.tape m ∧ m ≠ c.head ∧
      m ≠ c'.head := fun i l => forall_congr' fun m => forall_congr' fun _ => forall_congr' fun _ =>
    noM_iff c c'
  constructor
  · intro h
    rcases (acc_start N S c c' hS).1 h with h | h | ⟨⟨q, hq, q', γ', hl, he⟩, hd⟩
    · -- equality
      obtain ⟨l, -, hlS, hb, he, hm, hd⟩ := (acc_eqp N S c c' _ 0 rfl).1 h
      rw [hB] at hb; rw [hD] at hd
      have hl1 : l = c.head := by by_contra hne; exact hm (mk_snd_none.2 hne)
      have h2 := congrArg Prod.snd he
      have hl2 : l = c'.head := by
        by_contra hne; rw [mk_snd_none.2 hne] at h2; exact hm h2
      simp only [mk, if_pos hl1, if_pos hl2, Option.some.injEq] at h2
      left
      refine config_eq h2 (hl1 ▸ hl2) fun i => ?_
      rcases lt_trichotomy i l with hi | rfl | hi
      · exact (hb i (Nat.zero_le _) hi).1
      · exact congrArg Prod.fst he
      · rcases Nat.lt_or_ge i S with hiS | hiS
        · exact (hd i hi hiS).1
        · exact hout i hiS
    · obtain ⟨l, -, hlS, hb, hev⟩ := (acc_pre N S c c' _ 0 rfl).1 h
      rw [hB] at hb
      right
      rcases hev with ⟨hn, q', he, hpl⟩ | ⟨q, hq, q', γ', ⟨hs, he, hd⟩ | ⟨hr, he, hpr⟩⟩
      · -- left move
        obtain ⟨hlS', ⟨q₀, hq₀, γ', hmv, he'⟩, hd⟩ := (acc_pl N S c c' q' (l + 1)).1 hpl
        rw [hD] at hd
        obtain ⟨hh, rfl⟩ := mk_snd_some.1 hq₀
        simp only [mk, Prod.mk.injEq] at he he'
        have hl' : l = c'.head := by by_contra hne; simp [hne] at he
        rw [if_pos hl', Option.some.injEq] at he
        have hl'' : l + 1 ≠ c'.head := by omega
        rw [if_neg hl''] at he'
        refine ⟨q', γ', .left, hh ▸ hmv, config_eq he.2 (by simp [Move.apply]; omega) fun i => ?_⟩
        simp only [Function.update_apply]
        split_ifs with hi
        · subst hi; rw [← hh]; exact he'.1
        · rcases lt_trichotomy i l with hi' | rfl | hi'
          · exact (hb i (Nat.zero_le _) hi').1.symm
          · exact he.1
          · rcases Nat.lt_or_ge i S with hiS | hiS
            · exact (hd i (by omega) hiS).1.symm
            · exact (hout i hiS).symm
      · -- stay
        rw [hD] at hd
        obtain ⟨hh, rfl⟩ := mk_snd_some.1 hq
        simp only [mk, Prod.mk.injEq] at he
        have hl' : l = c'.head := by by_contra hne; simp [hne] at he
        rw [if_pos hl', Option.some.injEq] at he
        refine ⟨q', γ', .stay, hh ▸ hs, config_eq he.2 (by simp [Move.apply]; omega) fun i => ?_⟩
        simp only [Function.update_apply]
        split_ifs with hi
        · subst hi; rw [← hh]; exact he.1
        · rcases lt_trichotomy i l with hi' | rfl | hi'
          · exact (hb i (Nat.zero_le _) hi').1.symm
          · exact absurd hh hi
          · rcases Nat.lt_or_ge i S with hiS | hiS
            · exact (hd i (by omega) hiS).1.symm
            · exact (hout i hiS).symm
      · -- right
        obtain ⟨hlS', hn, he', hd⟩ := (acc_pr N S c c' q' (l + 1)).1 hpr
        rw [hD] at hd
        obtain ⟨hh, rfl⟩ := mk_snd_some.1 hq
        simp only [mk, Prod.mk.injEq] at he he'
        have hl' : l + 1 = c'.head := by by_contra hne; simp [hne] at he'
        rw [if_pos hl', Option.some.injEq] at he'
        have hl'' : l ≠ c'.head := by omega
        rw [if_neg hl''] at he
        refine ⟨q', γ', .right, hh ▸ hr, config_eq he'.2 (by simp [Move.apply]; omega) fun i => ?_⟩
        simp only [Function.update_apply]
        split_ifs with hi
        · subst hi; rw [← hh]; exact he.1
        · rcases lt_trichotomy i l with hi' | rfl | hi'
          · exact (hb i (Nat.zero_le _) hi').1.symm
          · exact absurd hh hi
          · rcases Nat.eq_or_lt_of_le (show l + 1 ≤ i by omega) with rfl | hi''
            · exact he'.1
            · rcases Nat.lt_or_ge i S with hiS | hiS
              · exact (hd i (by omega) hiS).1.symm
              · exact (hout i hiS).symm
    · -- left move at cell `0`
      rw [hD] at hd
      right
      obtain ⟨hh, rfl⟩ := mk_snd_some.1 hq
      simp only [mk, Prod.mk.injEq] at he
      have hl' : 0 = c'.head := by by_contra hne; simp [hne] at he
      rw [if_pos hl', Option.some.injEq] at he
      refine ⟨q', γ', .left, hh ▸ hl, config_eq he.2 (by simp [Move.apply]; omega) fun i => ?_⟩
      simp only [Function.update_apply]
      split_ifs with hi
      · subst hi; rw [← hh]; exact he.1
      · rcases Nat.lt_or_ge i S with hiS | hiS
        · exact (hd i (by omega) hiS).1.symm
        · exact (hout i hiS).symm
  · rintro (rfl | ⟨q', γ', m, hmem, rfl⟩)
    · refine (acc_start N S c c hS).2 (Or.inl ((acc_eqp N S c c _ 0 rfl).2
        ⟨c.head, Nat.zero_le _, hc, (hB 0 c.head).2 fun m _ hm => ⟨rfl, by omega, by omega⟩, rfl,
          by simp [mk], (hD _).2 fun l hl _ => ⟨rfl, by omega, by omega⟩⟩))
    · have hm0 : (mk c c.head).2 = some c.state := by simp [mk]
      cases m with
      | stay =>
        refine (acc_start N S c _ hS).2 (Or.inr (Or.inl ((acc_pre N S c _ _ 0 rfl).2
          ⟨c.head, Nat.zero_le _, hc, (hB _ _).2 fun m _ hm => ⟨by simp [Function.update_apply]; omega,
            by omega, by simp [Move.apply]; omega⟩, Or.inr ⟨c.state, hm0, q', γ', Or.inl ⟨hmem,
              by simp [mk, Move.apply], (hD _).2 fun l hl _ => ⟨by simp [Function.update_apply]; omega,
                by omega, by simp [Move.apply]; omega⟩⟩⟩⟩)))
      | right =>
        simp only [Move.apply] at hc'
        refine (acc_start N S c _ hS).2 (Or.inr (Or.inl ((acc_pre N S c _ _ 0 rfl).2
          ⟨c.head, Nat.zero_le _, hc, (hB _ _).2 fun m _ hm => ⟨by simp [Function.update_apply]; omega,
            by omega, by simp [Move.apply]; omega⟩, Or.inr ⟨c.state, hm0, q', γ', Or.inr ⟨hmem,
              by simp [mk, Move.apply], (acc_pr N S c _ q' _).2 ⟨hc', by simp [mk], by
                simp [mk, Move.apply, Function.update_apply], (hD _).2 fun l hl _ =>
                  ⟨by simp [Function.update_apply]; omega, by omega, by simp [Move.apply]; omega⟩⟩⟩⟩⟩)))
      | left =>
        rcases Nat.eq_zero_or_pos c.head with h0 | h0
        · refine (acc_start N S c _ hS).2 (Or.inr (Or.inr ⟨⟨c.state, by simp [mk, h0], q', γ',
            by rw [← h0]; exact hmem, by simp [mk, Move.apply, h0, Function.update_apply]⟩, (hD _).2 fun l hl _ =>
              ⟨by simp [Function.update_apply]; omega, by omega, by simp [Move.apply]; omega⟩⟩))
        · obtain ⟨l, hl⟩ : ∃ l, c.head = l + 1 := ⟨c.head - 1, by omega⟩
          refine (acc_start N S c _ hS).2 (Or.inr (Or.inl ((acc_pre N S c _ _ 0 rfl).2
            ⟨l, Nat.zero_le _, by omega, (hB _ _).2 fun m _ hm => ⟨by simp [Function.update_apply]; omega,
              by omega, by simp [Move.apply]; omega⟩, Or.inl ⟨by simp [mk]; omega, q', by
                simp [mk, Move.apply, Function.update_apply, hl], (acc_pl N S c _ q' _).2 ⟨by omega,
                  ⟨c.state, by simp [mk, hl], γ', by rw [← hl]; exact hmem, by
                    simp [mk, Move.apply, Function.update_apply, hl]⟩, (hD _).2 fun l' hl' _ =>
                      ⟨by simp [Function.update_apply]; omega, by omega, by simp [Move.apply]; omega⟩⟩⟩⟩)))

/-! ## Validity: accepted lists are encodings -/

/-- The numbers of head markers still to be read in the two components. -/
def need : CS Q → ℕ × ℕ
  | .start => (1, 1)
  | .eqp => (1, 1)
  | .pre => (1, 1)
  | .pl _ => (1, 0)
  | .pr _ => (0, 1)
  | .eqd => (0, 0)
  | .dn => (0, 0)

/-- The numbers of markers of a list of pairs. -/
def cnt (ps : List (X Q Γ × X Q Γ)) : ℕ × ℕ :=
  (ps.countP fun p => p.1.2.isSome, ps.countP fun p => p.2.2.isSome)

theorem cnt_cons (p : X Q Γ × X Q Γ) (ps : List (X Q Γ × X Q Γ)) :
    cnt (p :: ps) = ((cnt ps).1 + (if p.1.2.isSome then 1 else 0),
      (cnt ps).2 + (if p.2.2.isSome then 1 else 0)) := by
  simp [cnt, List.countP_cons]

theorem acc_cnt : ∀ (ps : List (X Q Γ × X Q Γ)) (c : CS Q), Acc N c ps → cnt ps = need c := by
  intro ps
  induction ps with
  | nil => intro c h; cases c <;> simp_all [Acc, final, cnt, need]
  | cons p ps ih =>
    intro c ⟨c', hT, h⟩
    have e := ih c' h
    rw [cnt_cons, e]
    obtain ⟨⟨a, mu⟩, ⟨b, mv⟩⟩ := p
    cases c <;> simp only [chk, eqT, preT, left0, NoM] at hT <;> aesop (add norm simp [need])

/-- Configurations with the head on the first `S` cells that agree with `t₀` outside them. -/
def Fits (S : ℕ) (t₀ : ℕ → Γ) (c : Config Q Γ) : Prop := c.head < S ∧ ∀ i, S ≤ i → c.tape i = t₀ i

theorem exists_one {α : Type} {p : α → Bool} : ∀ {l : List α}, l.countP p = 1 →
    ∃ j, ∃ hj : j < l.length, p l[j] = true ∧ ∀ i (hi : i < l.length), i ≠ j → p l[i] = false := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro h
    rw [List.countP_cons] at h
    by_cases ha : p a = true
    · rw [if_pos ha] at h
      have h0 : l.countP p = 0 := by omega
      refine ⟨0, by simp, by simpa using ha, fun i hi hne => ?_⟩
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [List.getElem_cons_succ]
      rw [List.countP_eq_zero] at h0
      simpa using h0 _ (List.getElem_mem _)
    · rw [if_neg ha] at h
      obtain ⟨j, hj, h1, h2⟩ := ih (by omega)
      refine ⟨j + 1, by simp; omega, by simpa using h1, fun i hi hne => ?_⟩
      rcases i with _ | i
      · simpa using ha
      · exact h2 i (by simp at hi; omega) (by omega)

theorem decode {t₀ : ℕ → Γ} {x : List (X Q Γ)} (hx : x.length = S)
    (h1 : x.countP (fun u => u.2.isSome) = 1) : ∃ c, Fits S t₀ c ∧ x = enc S c := by
  obtain ⟨j, hj, hs, hr⟩ := exists_one h1
  refine ⟨⟨x[j].2.get hs, j, fun i => if h : i < x.length then x[i].1 else t₀ i⟩,
    ⟨by simp; omega, fun i hi => by simp; intro h; omega⟩, ?_⟩
  refine List.ext_getElem (by simp [enc, hx]) fun i h1 h2 => ?_
  simp only [enc, List.getElem_map, List.getElem_range, mk, dif_pos h1]
  refine Prod.ext rfl ?_
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij]; simpa using hr i h1 hij

theorem enc_inj {t₀ : ℕ → Γ} (hc : Fits S t₀ c) (hc' : Fits S t₀ c') (h : enc S c = enc S c') :
    c = c' := by
  have hm : ∀ i, i < S → mk c i = mk c' i := fun i hi => by
    have := congrArg (fun l => l[i]?) h
    simpa [enc, hi] using this
  have h1 := hm c.head hc.1
  have hs : (mk c' c.head).2 = some c.state := by rw [← h1]; simp [mk]
  obtain ⟨hh, hst⟩ := mk_snd_some.1 hs
  refine config_eq hst.symm hh fun i => ?_
  rcases Nat.lt_or_ge i S with hi | hi
  · exact congrArg Prod.fst (hm i hi)
  · rw [hc.2 i hi, hc'.2 i hi]

/-- **The check automaton on arbitrary lists**: accepted lists encode equal or successive
configurations. -/
theorem acc_zip_iff (hS : 0 < S) (t₀ : ℕ → Γ) {x y : List (X Q Γ)} (hx : x.length = S)
    (hy : y.length = S) : Acc N .start (x.zip y) ↔ ∃ c c', Fits S t₀ c ∧ Fits S t₀ c' ∧
      x = enc S c ∧ y = enc S c' ∧ (c = c' ∨ N.Step c c') := by
  constructor
  · intro h
    have hc := acc_cnt N _ _ h
    simp only [cnt, need, Prod.mk.injEq] at hc
    have e1 : x.countP (fun u => u.2.isSome) = 1 := by
      rw [← hc.1]
      have := List.countP_map (p := fun u : X Q Γ => u.2.isSome) (f := Prod.fst) (l := x.zip y)
      rw [List.map_fst_zip (by omega)] at this
      exact this
    have e2 : y.countP (fun u => u.2.isSome) = 1 := by
      rw [← hc.2]
      have := List.countP_map (p := fun u : X Q Γ => u.2.isSome) (f := Prod.snd) (l := x.zip y)
      rw [List.map_snd_zip (by omega)] at this
      exact this
    obtain ⟨c, hc, rfl⟩ := decode S hx e1
    obtain ⟨c', hc', rfl⟩ := decode S hy e2
    rw [zip_enc] at h
    exact ⟨c, c', hc, hc', rfl, rfl, (acc_iff N S c c' hS hc.1 hc'.1 fun i hi => by
      rw [hc.2 i hi, hc'.2 i hi]).1 h⟩
  · rintro ⟨c, c', hc, hc', rfl, rfl, h⟩
    rw [zip_enc]
    exact (acc_iff N S c c' hS hc.1 hc'.1 fun i hi => by rw [hc.2 i hi, hc'.2 i hi]).2 h

/-! ## The Savitch game on lists -/

/-- **The Savitch game on lists of cells**: the existential player writes a midpoint list. -/
def LW : ℕ → List (X Q Γ) → List (X Q Γ) → Prop
  | 0, x, y => Acc N .start (x.zip y)
  | k + 1, x, y => ∃ m : List (X Q Γ), m.length = S ∧ LW k x m ∧ LW k m y

theorem savWin_fits {t₀ : ℕ → Γ} {k : ℕ} {c d : Config Q Γ} (hc : Fits S t₀ c)
    (h : ATM.SavWin N S k c d) : Fits S t₀ d := by
  obtain ⟨n, -, hr⟩ := (ATM.savWin_iff N S k c d).1 h
  obtain ⟨h1, h2⟩ := ATM.tape_of_reachesSpace N S hr
  exact ⟨h2, fun i hi => by rw [h1 i hi, hc.2 i hi]⟩

theorem enc_length (c : Config Q Γ) : (enc S c).length = S := by simp [enc]

/-- **The list game is the Savitch game.** -/
theorem lw_iff (hS : 0 < S) (t₀ : ℕ → Γ) : ∀ (k : ℕ) (x y : List (X Q Γ)), x.length = S →
    y.length = S → (LW N S k x y ↔ ∃ c c', Fits S t₀ c ∧ Fits S t₀ c' ∧ x = enc S c ∧
      y = enc S c' ∧ ATM.SavWin N S k c c') := by
  intro k
  induction k with
  | zero =>
    intro x y hx hy
    rw [LW, acc_zip_iff N S hS t₀ hx hy]
    refine exists_congr fun c => exists_congr fun c' => ?_
    constructor
    · rintro ⟨h1, h2, h3, h4, h5 | h5⟩
      · exact ⟨h1, h2, h3, h4, Or.inl ⟨h5, h1.1⟩⟩
      · exact ⟨h1, h2, h3, h4, Or.inr ⟨h1.1, h5, h2.1⟩⟩
    · rintro ⟨h1, h2, h3, h4, ⟨h5, -⟩ | ⟨-, h5, -⟩⟩
      · exact ⟨h1, h2, h3, h4, Or.inl h5⟩
      · exact ⟨h1, h2, h3, h4, Or.inr h5⟩
  | succ k ih =>
    intro x y hx hy
    simp only [LW]
    constructor
    · rintro ⟨m, hm, h1, h2⟩
      obtain ⟨c, d, hc, hd, rfl, rfl, w1⟩ := (ih _ _ hx hm).1 h1
      obtain ⟨d', c', hd', hc', e, rfl, w2⟩ := (ih _ _ hm hy).1 h2
      obtain rfl := enc_inj S d d' hd hd' e
      exact ⟨c, c', hc, hc', rfl, rfl, d, w1, w2⟩
    · rintro ⟨c, c', hc, hc', rfl, rfl, d, w1, w2⟩
      have hd := savWin_fits N S hc w1
      exact ⟨enc S d, enc_length S d, (ih _ _ hx (enc_length S d)).2 ⟨c, d, hc, hd, rfl, rfl, w1⟩,
        (ih _ _ (enc_length S d) hy).2 ⟨d, c', hd, hc', rfl, rfl, w2⟩⟩

end Sav

end AcycHard

end FOND
