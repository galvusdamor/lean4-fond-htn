import FondHtn.DB25Games.Build
/-!
# The hardness game, turn by turn

Legal states `FOND.DBG.st p i X P G`: phase `p`, cell `i`, claim `X`, proposal `P`, assertion
`G`.  The lemmas `win_ph0` … `win_ph3` describe one turn each.
-/

set_option linter.unnecessarySeqFocus false

namespace FOND

namespace DBG

open TM TM.NTM

/-- Proposals. -/
inductive Prp (k : ℕ) where
  | none
  | tri (l c r : CS k)
  | shift

/-- Assertions. -/
inductive GS where
  | none
  | j (j : ℕ)
  | b

variable {k : ℕ}

/-- **The legal states.** -/
def st (p i : ℕ) (X : V k) (P : Prp k) (G : GS) : Fct k → Bool
  | .ph j => decide (j = p)
  | .ib b => i.testBit b
  | .x v => decide (v = X)
  | .pl v => match P with | .tri l _ _ => decide (v = l) | _ => false
  | .pc v => match P with | .tri _ c _ => decide (v = c) | _ => false
  | .pr v => match P with | .tri _ _ r => decide (v = r) | _ => false
  | .sh => match P with | .shift => true | _ => false
  | .g => match G with | .none => false | _ => true
  | .gj j => match G with | .j j' => decide (j = j') | _ => false
  | .gb => match G with | .b => true | _ => false

/-- Admissible assertions. -/
def GOk (n : ℕ) : GS → Prop
  | .j j => j ≤ n
  | _ => True

theorem eff_apply {α : Type} [DecidableEq α] (a : Act α) (s : α → Bool) (f : α) :
    eff a s f = if f ∈ a.2.2.1 then true else if f ∈ a.2.2.2 then false else s f := rfl

/-! ## Effects -/

section Eff

variable (n : ℕ)

theorem eff_prop (pre npre : List (Fct k)) (i : ℕ) (X : V k) (G : GS) (hG : GOk n G) (l c r : CS k) :
    eff (pre, npre, [.ph 1, .pl l, .pc c, .pr r], .ph 0 :: gAll n) (st 0 i X .none G) =
      st 1 i X (.tri l c r) .none := by
  funext f
  rw [eff_apply]
  cases f <;> simp [st] <;> cases G <;> simp_all [GOk] <;> omega

theorem eff_shift (pre npre : List (Fct k)) (i : ℕ) (X : V k) (G : GS) (hG : GOk n G) :
    eff (pre, npre, [.ph 1, .sh], .ph 0 :: gAll n) (st 0 i X .none G) = st 1 i X .shift .none := by
  funext f
  rw [eff_apply]
  cases f <;> simp [st] <;> cases G <;> simp_all [GOk] <;> omega

theorem eff_L {m i j : ℕ} (hi : i < 2 ^ m) (hj : j < m) (h0 : ∀ b < j, i.testBit b = false)
    (h1 : i.testBit j = true) (pre npre : List (Fct k)) (X : V k) (P : Prp k) (v : CS k) :
    eff (pre, npre, .ph 2 :: .x (some v) :: ibs j, .ph 1 :: .ib j :: (allX ++ allP)) (st 1 i X P .none) =
      st 2 (i - 1) (some v) .none .none := by
  funext f
  rw [eff_apply]
  have hp := testBit_pred hi hj h0 h1
  cases f <;> simp [st, hp, DB.decSet]

theorem eff_C (pre npre : List (Fct k)) (i : ℕ) (X : V k) (P : Prp k) (v : CS k) :
    eff (pre, npre, [.ph 2, .x (some v)], .ph 1 :: (allX ++ allP)) (st 1 i X P .none) =
      st 2 i (some v) .none .none := by
  funext f
  rw [eff_apply]
  cases f <;> simp [st]

theorem eff_R {m i j : ℕ} (hi : i + 1 < 2 ^ m) (hj : j < m) (h0 : ∀ b < j, i.testBit b = true)
    (h1 : i.testBit j = false) (pre npre : List (Fct k)) (X : V k) (P : Prp k) (v : CS k) :
    eff (pre, npre, [.ph 2, .x (some v), .ib j], .ph 1 :: (ibs j ++ allX ++ allP)) (st 1 i X P .none) =
      st 2 (i + 1) (some v) .none .none := by
  funext f
  rw [eff_apply]
  have hp := testBit_succ hi hj h0 h1
  cases f <;> simp [st, hp, DB.incSet] <;> try omega
  rename_i b
  by_cases hbj : b = j
  · subst hbj; simp
  · by_cases hb : b < j
    · simp [hb, hbj]
    · simp [hb, hbj]

theorem eff_Sh {m i j : ℕ} (hi : i + 1 < 2 ^ m) (hj : j < m) (h0 : ∀ b < j, i.testBit b = true)
    (h1 : i.testBit j = false) (pre npre : List (Fct k)) (P : Prp k) :
    eff (pre, npre, [.ph 2, .ib j], .ph 1 :: (ibs j ++ allP)) (st 1 i (none : V k) P .none) =
      st 2 (i + 1) none .none .none := by
  funext f
  rw [eff_apply]
  have hp := testBit_succ hi hj h0 h1
  cases f <;> simp [st, hp, DB.incSet] <;> try omega
  rename_i b
  by_cases hbj : b = j
  · subst hbj; simp
  · by_cases hb : b < j
    · simp [hb, hbj]
    · simp [hb, hbj]

theorem eff_noG (pre npre : List (Fct k)) (i : ℕ) (X : V k) :
    eff (pre, npre, [.ph 3], [.ph 2]) (st 2 i X .none .none) = st 3 i X .none .none := by
  funext f
  rw [eff_apply]
  cases f <;> simp [st]

theorem eff_gb (pre npre : List (Fct k)) (i : ℕ) (X : V k) :
    eff (pre, npre, [.ph 3, .g, .gb], [.ph 2]) (st 2 i X .none .none) = st 3 i X .none .b := by
  funext f
  rw [eff_apply]
  cases f <;> simp [st]

theorem eff_gj (pre npre : List (Fct k)) (i j : ℕ) (X : V k) :
    eff (pre, npre, [.ph 3, .g, .gj j], [.ph 2]) (st 2 i X .none .none) = st 3 i X .none (.j j) := by
  funext f
  rw [eff_apply]
  cases f <;> simp [st]

theorem eff_pass (pre npre : List (Fct k)) (i : ℕ) (X : V k) (G : GS) :
    eff (pre, npre, [.ph 0], [.ph 3]) (st 3 i X .none G) = st 0 i X .none G := by
  funext f
  rw [eff_apply]
  cases f <;> simp [st]

/-- A refutation kills: no phase is left. -/
theorem eff_kill_ph {p : ℕ} (pre npre : List (Fct k)) (s : Fct k → Bool)
    (hs : ∀ j, s (.ph j) = decide (j = p)) : ∀ j < 4, eff (pre, npre, [], [.ph p]) s (.ph j) = false := by
  intro j _
  rw [eff_apply]
  by_cases h : j = p
  · subst h; simp
  · simp [h, hs]

end Eff

/-! ## The turns -/

variable (M : NTM (Fin k) Sym) (m : ℕ) (u : List Sym)

theorem st_ph (p i : ℕ) (X : V k) (P : Prp k) (G : GS) : ∀ j, st p i X P G (.ph j) = decide (j = p) :=
  fun _ => rfl

theorem mem_acts_0 {a : Act (Fct k)} (h : a ∈ blk0 M m u) : a ∈ acts M m u := by
  simp [acts, h]
theorem mem_acts_1 {a : Act (Fct k)} (h : a ∈ blk1 m) : a ∈ acts M m u := by
  simp [acts, h]
theorem mem_acts_2 {a : Act (Fct k)} (h : a ∈ blk2 u) : a ∈ acts M m u := by
  simp [acts, h]
theorem mem_acts_3 {a : Act (Fct k)} (h : a ∈ blk3 M m u) : a ∈ acts M m u := by
  simp [acts, h]

theorem not_win_zero {p i : ℕ} (hp : p ≠ 0) (X : V k) (P : Prp k) (G : GS) (e : Bool) :
    ¬ Win (acts M m u) goal 0 e (st p i X P G) := by
  intro h
  have := h (.ph 0) (by simp [goal])
  simp [st] at this; omega

theorem win_zero_ph0 (i : ℕ) (X : V k) (G : GS) (e : Bool) :
    Win (acts M m u) goal 0 e (st 0 i X .none G) ↔ G ≠ .none := by
  simp only [win_zero, Sat, goal, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  cases G <;> simp [st]

/-- Valid proposals. -/
def Valid0 (i : ℕ) (X : V k) : Prp k → Prop
  | .none => False
  | .tri l c r => (i ≠ 0 ∧ Matches M X (M.F (some l) c r)) ∨ (i = 0 ∧ Matches M X (M.F none c r))
  | .shift => X = none ∧ i + 1 < 2 ^ m

theorem exists_bit_of_ne_zero {i : ℕ} (hi : i < 2 ^ m) (h : i ≠ 0) : ∃ b < m, i.testBit b = true := by
  by_contra hc
  push_neg at hc
  exact h (eq_zero_of_testBit hi fun b hb => by simpa using hc b hb)

/-- **Turn 0.** -/
theorem win_ph0 {i : ℕ} (hi : i < 2 ^ m) (X : V k) (G : GS) (hG : GOk u.length G) (T : ℕ) :
    Win (acts M m u) goal (T + 1) true (st 0 i X .none G) ↔
      ∃ P, Valid0 M m i X P ∧ Win (acts M m u) goal T false (st 1 i X P .none) := by
  constructor
  · rintro ⟨a, ha, happ, hw⟩
    rcases blk_of_app M m u (st_ph 0 i X .none G) ha happ with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · simp only [blk0, List.mem_append, List.mem_flatMap, List.mem_map] at h
      rcases h with (⟨t, ht, b, hb, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨b, hb, rfl⟩
      · have hx : t.1 = X := by simpa [st] using happ.1 (.x t.1) (by simp)
        have hb' : i.testBit b = true := happ.1 (.ib b) (by simp)
        refine ⟨.tri t.2.1 t.2.2.1 t.2.2.2, Or.inl ⟨ne_zero_of_testBit hb', hx ▸ (mem_trip1 M).1 ht⟩, ?_⟩
        rwa [eff_prop u.length _ _ i X G hG] at hw
      · have hx : t.1 = X := by simpa [st] using happ.1 (.x t.1) (by simp)
        have h0 : i = 0 := eq_zero_of_testBit hi fun b hb => happ.2 (.ib b) (by simp [hb])
        refine ⟨.tri t.2.1 t.2.2.1 t.2.2.2, Or.inr ⟨h0, hx ▸ (mem_trip0 M).1 ht⟩, ?_⟩
        rwa [eff_prop u.length _ _ i X G hG] at hw
      · have hx : (none : V k) = X := by simpa [st] using happ.1 (.x none) (by simp)
        have hb' : i.testBit b = false := happ.2 (.ib b) (by simp)
        refine ⟨.shift, ⟨hx.symm, succ_lt_of_testBit hi (List.mem_range.1 hb) hb'⟩, ?_⟩
        rwa [eff_shift u.length _ _ i X G hG] at hw
    all_goals omega
  · rintro ⟨P, hP, hw⟩
    cases P with
    | none => exact hP.elim
    | tri l c r =>
      rcases hP with ⟨hi0, hm⟩ | ⟨hi0, hm⟩
      · obtain ⟨b, hb, hbit⟩ := exists_bit_of_ne_zero m hi hi0
        refine ⟨_, mem_acts_0 M m u (a := ([.ph 0, .x X, .ib b], [], [.ph 1, .pl l, .pc c, .pr r],
          .ph 0 :: gAll u.length)) ?_, ⟨by simp [st, hbit], by simp⟩, by
            rwa [eff_prop u.length _ _ i X G hG]⟩
        simp only [blk0, List.mem_append, List.mem_flatMap, List.mem_map]
        exact Or.inl (Or.inl ⟨(X, l, c, r), (mem_trip1 M).2 hm, b, List.mem_range.2 hb, rfl⟩)
      · subst hi0
        refine ⟨_, mem_acts_0 M m u (a := ([.ph 0, .x X], ibs m, [.ph 1, .pl l, .pc c, .pr r],
          .ph 0 :: gAll u.length)) ?_, ⟨by simp [st], by
            simp only [mem_ibs]; rintro _ ⟨b, -, rfl⟩; simp [st]⟩, by
            rwa [eff_prop u.length _ _ 0 X G hG]⟩
        simp only [blk0, List.mem_append, List.mem_flatMap, List.mem_map]
        exact Or.inl (Or.inr ⟨(X, l, c, r), (mem_trip0 M).2 hm, rfl⟩)
    | shift =>
      obtain ⟨rfl, hlt⟩ := hP
      obtain ⟨j, hj, -, h1⟩ := DB.exists_inc m i.testBit (by rw [DB.bval_testBit hi]; exact hlt)
      refine ⟨_, mem_acts_0 M m u (a := ([.ph 0, .x none], [.ib j], [.ph 1, .sh],
        .ph 0 :: gAll u.length)) ?_, ⟨by simp [st], by simp [st, h1]⟩, by
          rwa [eff_shift u.length _ _ i none G hG]⟩
      simp only [blk0, List.mem_append, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨j, List.mem_range.2 hj, rfl⟩

theorem testBit_all_of_succ_eq {i : ℕ} (h : i + 1 = 2 ^ m) : ∀ b < m, i.testBit b = true := by
  intro b hb
  rw [show i = 2 ^ m - 1 by omega, Nat.testBit_two_pow_sub_one]; simpa using hb

/-- **Turn 1, after a proposal.** -/
theorem win_ph1_tri {i : ℕ} (hi : i < 2 ^ m) (X : V k) (l c r : CS k) (T : ℕ) :
    Win (acts M m u) goal (T + 1) false (st 1 i X (.tri l c r) .none) ↔
      (i ≠ 0 → Win (acts M m u) goal T true (st 2 (i - 1) (some l) .none .none)) ∧
      Win (acts M m u) goal T true (st 2 i (some c) .none .none) ∧
      (i + 1 < 2 ^ m → Win (acts M m u) goal T true (st 2 (i + 1) (some r) .none .none)) ∧
      (i + 1 = 2 ^ m → r.1 = none) := by
  constructor
  · intro h
    refine ⟨fun hi0 => ?_, ?_, fun hlt => ?_, fun heq => ?_⟩
    · obtain ⟨j, hj, h0, h1⟩ := DB.exists_dec m i.testBit (by rw [DB.bval_testBit hi]; omega)
      have := h _ (mem_acts_1 M m u (a := ([.ph 1, .pl l, .ib j], ibs j, .ph 2 :: .x (some l) :: ibs j,
        .ph 1 :: .ib j :: (allX ++ allP))) (by
          simp only [blk1, List.mem_append, List.mem_flatMap, List.mem_map]
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨l, mem_allC l, j, List.mem_range.2 hj, rfl⟩)))))
        ⟨by simp [st, h1], by simp only [mem_ibs]; rintro _ ⟨b, hb, rfl⟩; exact h0 b hb⟩
      rwa [eff_L hi hj h0 h1] at this
    · have := h _ (mem_acts_1 M m u (a := ([.ph 1, .pc c], [], [.ph 2, .x (some c)],
        .ph 1 :: (allX ++ allP))) (by
          simp only [blk1, List.mem_append, List.mem_flatMap, List.mem_map]
          exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c, mem_allC c, rfl⟩)))))
        ⟨by simp [st], by simp⟩
      rwa [eff_C] at this
    · obtain ⟨j, hj, h0, h1⟩ := DB.exists_inc m i.testBit (by rw [DB.bval_testBit hi]; exact hlt)
      have := h _ (mem_acts_1 M m u (a := (.ph 1 :: .pr r :: ibs j, [.ib j],
        [.ph 2, .x (some r), .ib j], .ph 1 :: (ibs j ++ allX ++ allP))) (by
          simp only [blk1, List.mem_append, List.mem_flatMap, List.mem_map]
          exact Or.inl (Or.inl (Or.inr ⟨r, mem_allC r, j, List.mem_range.2 hj, rfl⟩))))
        ⟨by simp only [List.mem_cons, mem_ibs]; rintro _ (rfl | rfl | ⟨b, hb, rfl⟩) <;> [simp [st]; simp [st]; exact h0 b hb],
          by simp [st, h1]⟩
      rwa [eff_R hlt hj h0 h1] at this
    · by_contra hr
      have hall := testBit_all_of_succ_eq m heq
      have := h _ (mem_acts_1 M m u (a := (.ph 1 :: .pr r :: ibs m, [], [], [.ph 1])) (by
          simp only [blk1, List.mem_append, List.mem_flatMap, List.mem_map]
          exact Or.inr ⟨r, (mem_headC r).2 hr, rfl⟩))
        ⟨by simp only [List.mem_cons, mem_ibs]; rintro _ (rfl | rfl | ⟨b, hb, rfl⟩) <;> [simp [st]; simp [st]; exact hall b hb],
          by simp⟩
      exact not_win_dead M m u (eff_kill_ph _ _ _ (st_ph 1 i X _ .none)) T this
  · rintro ⟨hL, hC, hR, hK⟩ a ha happ
    rcases blk_of_app M m u (st_ph 1 i X (.tri l c r) .none) ha happ with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · simp only [blk1, List.mem_append, List.mem_flatMap, List.mem_map] at h
      rcases h with (((⟨v, -, j, hj, rfl⟩ | ⟨v, -, rfl⟩) | ⟨v, -, j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨v, hv, rfl⟩
      · have hv : v = l := by simpa [st] using happ.1 (.pl v) (by simp)
        have h1 : i.testBit j = true := happ.1 (.ib j) (by simp)
        have h0 : ∀ b < j, i.testBit b = false := fun b hb => happ.2 (.ib b) (by simp [hb])
        subst hv
        rw [eff_L hi (List.mem_range.1 hj) h0 h1]
        exact hL (ne_zero_of_testBit h1)
      · have hv : v = c := by simpa [st] using happ.1 (.pc v) (by simp)
        subst hv; rw [eff_C]; exact hC
      · have hv : v = r := by simpa [st] using happ.1 (.pr v) (by simp)
        have h0 : ∀ b < j, i.testBit b = true := fun b hb => happ.1 (.ib b) (by simp [hb])
        have h1 : i.testBit j = false := happ.2 (.ib j) (by simp)
        have hlt := succ_lt_of_testBit hi (List.mem_range.1 hj) h1
        subst hv
        rw [eff_R hlt (List.mem_range.1 hj) h0 h1]
        exact hR hlt
      · have := happ.1 .sh (by simp)
        simp [st] at this
      · have hv' : v = r := by simpa [st] using happ.1 (.pr v) (by simp)
        have hall : ∀ b < m, i.testBit b = true := fun b hb => happ.1 (.ib b) (by simp [hb])
        subst hv'
        exact absurd (hK (succ_eq_of_testBit hi hall)) ((mem_headC v).1 hv)
    · omega
    · omega

/-- **Turn 1, after a shift.** -/
theorem win_ph1_shift {i : ℕ} (hlt : i + 1 < 2 ^ m) (T : ℕ) :
    Win (acts M m u) goal (T + 1) false (st 1 i (none : V k) .shift .none) ↔
      Win (acts M m u) goal T true (st 2 (i + 1) none .none .none) := by
  have hi : i < 2 ^ m := by omega
  constructor
  · intro h
    obtain ⟨j, hj, h0, h1⟩ := DB.exists_inc m i.testBit (by rw [DB.bval_testBit hi]; exact hlt)
    have := h _ (mem_acts_1 M m u (a := (.ph 1 :: .sh :: ibs j, [.ib j], [.ph 2, .ib j],
      .ph 1 :: (ibs j ++ allP))) (by
        simp only [blk1, List.mem_append, List.mem_flatMap, List.mem_map]
        exact Or.inl (Or.inr ⟨j, List.mem_range.2 hj, rfl⟩)))
      ⟨by simp only [List.mem_cons, mem_ibs]; rintro _ (rfl | rfl | ⟨b, hb, rfl⟩) <;> [simp [st]; simp [st]; exact h0 b hb],
        by simp [st, h1]⟩
    rwa [eff_Sh hlt hj h0 h1] at this
  · intro hw a ha happ
    rcases blk_of_app M m u (st_ph 1 i none .shift .none) ha happ with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · simp only [blk1, List.mem_append, List.mem_flatMap, List.mem_map] at h
      rcases h with (((⟨v, -, j, hj, rfl⟩ | ⟨v, -, rfl⟩) | ⟨v, -, j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨v, hv, rfl⟩
      · have := happ.1 (.pl v) (by simp); simp [st] at this
      · have := happ.1 (.pc v) (by simp); simp [st] at this
      · have := happ.1 (.pr v) (by simp); simp [st] at this
      · have h0 : ∀ b < j, i.testBit b = true := fun b hb => happ.1 (.ib b) (by simp [hb])
        have h1 : i.testBit j = false := happ.2 (.ib j) (by simp)
        rw [eff_Sh hlt (List.mem_range.1 hj) h0 h1]
        exact hw
      · have := happ.1 (.pr v) (by simp); simp [st] at this
    · omega
    · omega


/-- **Turn 2.** -/
theorem win_ph2 (i : ℕ) (X : V k) (T : ℕ) :
    Win (acts M m u) goal (T + 1) true (st 2 i X .none .none) ↔
      ∃ G, GOk u.length G ∧ Win (acts M m u) goal T false (st 3 i X .none G) := by
  constructor
  · rintro ⟨a, ha, happ, hw⟩
    rcases blk_of_app M m u (st_ph 2 i X .none .none) ha happ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · omega
    · simp only [blk2, List.mem_cons, List.mem_map] at h
      rcases h with rfl | rfl | ⟨j, hj, rfl⟩
      · exact ⟨.none, trivial, by rwa [eff_noG] at hw⟩
      · exact ⟨.b, trivial, by rwa [eff_gb] at hw⟩
      · exact ⟨.j j, by simpa [GOk, Nat.lt_succ_iff] using hj, by rwa [eff_gj] at hw⟩
    · omega
  · rintro ⟨G, hG, hw⟩
    cases G with
    | none =>
      exact ⟨([.ph 2], [], [.ph 3], [.ph 2]), mem_acts_2 M m u (by simp [blk2]), ⟨by simp [st], by simp⟩,
        by rwa [eff_noG]⟩
    | b =>
      exact ⟨([.ph 2], [], [.ph 3, .g, .gb], [.ph 2]), mem_acts_2 M m u (by simp [blk2]),
        ⟨by simp [st], by simp⟩, by rwa [eff_gb]⟩
    | j j =>
      refine ⟨([.ph 2], [], [.ph 3, .g, .gj j], [.ph 2]), mem_acts_2 M m u ?_, ⟨by simp [st], by simp⟩,
        by rwa [eff_gj]⟩
      simp only [blk2, List.mem_cons, List.mem_map, List.mem_range]
      exact Or.inr (Or.inr ⟨j, by simp only [GOk] at hG; omega, rfl⟩)

/-- Refutable assertions. -/
def Refut (i : ℕ) (X : V k) : GS → Prop
  | .none => False
  | .j j => i ≠ j ∨ X ≠ some (row0 M u j)
  | .b => i ≤ u.length ∨ X ≠ some (none, M.blank)

theorem lt_bw_left {i : ℕ} (hi : i < 2 ^ m) : i < 2 ^ bw m u :=
  lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by unfold bw; omega))

theorem lt_bw_right {j : ℕ} (hj : j ≤ u.length) : j < 2 ^ bw m u :=
  lt_of_le_of_lt hj (lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by omega)
    (by unfold bw; omega)))

theorem kill3 {i : ℕ} {X : V k} {G : GS} {T : ℕ}
    (h : Win (acts M m u) goal (T + 1) false (st 3 i X .none G)) (pre npre : List (Fct k))
    (ha : (pre, npre, [], [.ph 3]) ∈ acts M m u) (happ : App (pre, npre, [], [.ph 3]) (st 3 i X .none G)) :
    False :=
  not_win_dead M m u (eff_kill_ph _ _ _ (st_ph 3 i X .none G)) T (h _ ha happ)

/-- **Turn 3.** -/
theorem win_ph3 {i : ℕ} (hi : i < 2 ^ m) (X : V k) (G : GS) (hG : GOk u.length G) (T : ℕ) :
    Win (acts M m u) goal (T + 1) false (st 3 i X .none G) ↔
      ¬ Refut M u i X G ∧ Win (acts M m u) goal T true (st 0 i X .none G) := by
  have mem3 : ∀ a ∈ blk3 M m u, a ∈ acts M m u := fun a h => mem_acts_3 M m u h
  constructor
  · intro h
    refine ⟨fun hr => ?_, ?_⟩
    · cases G with
      | none => exact hr
      | j j =>
        simp only [GOk] at hG
        rcases hr with hne | hX
        · obtain ⟨b, hb, hdiff⟩ : ∃ b < bw m u, i.testBit b ≠ j.testBit b := by
            by_contra hc; push_neg at hc
            exact hne (eq_of_testBit_lt (lt_bw_left m u hi) (lt_bw_right m u hG) hc)
          have hmem : mis j b ∈ blk3 M m u := by
            simp only [blk3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
            exact Or.inr (Or.inl (Or.inl (Or.inl ⟨j, by omega, b, hb, rfl⟩)))
          unfold mis at hmem
          by_cases hjb : j.testBit b = true
          · rw [if_pos hjb] at hmem
            exact kill3 M m u h _ _ (mem3 _ hmem) ⟨by simp [st], by simp [st]; simpa [hjb] using hdiff⟩
          · rw [if_neg hjb] at hmem
            exact kill3 M m u h _ _ (mem3 _ hmem) ⟨by simp [st]; simpa [hjb] using hdiff, by simp⟩
        · have hmem : ([.ph 3, .gj j, .x X], [], [], [.ph 3]) ∈ blk3 M m u := by
            simp only [blk3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
              List.mem_range, List.mem_filter]
            exact Or.inr (Or.inl (Or.inl (Or.inr ⟨j, by omega, X, ⟨mem_allV X, by simpa using hX⟩, rfl⟩)))
          exact kill3 M m u h _ _ (mem3 _ hmem) ⟨by simp [st], by simp⟩
      | b =>
        rcases hr with hle | hX
        · have hmem : (.ph 3 :: .gb :: ((List.range (bw m u)).filter (fun b => i.testBit b)).map .ib,
              ((List.range (bw m u)).filter (fun b => !i.testBit b)).map .ib, [], [.ph 3]) ∈
                blk3 M m u := by
            simp only [blk3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
              List.mem_range]
            exact Or.inr (Or.inr ⟨i, by omega, rfl⟩)
          refine kill3 M m u h _ _ (mem3 _ hmem) ⟨?_, ?_⟩
          · simp only [List.mem_cons, List.mem_map, List.mem_filter]
            rintro _ (rfl | rfl | ⟨b, ⟨-, hb⟩, rfl⟩)
            · simp [st]
            · simp [st]
            · exact hb
          · simp only [List.mem_map, List.mem_filter]
            rintro _ ⟨b, ⟨-, hb⟩, rfl⟩
            simpa [st] using hb
        · have hmem : ([.ph 3, .gb, .x X], [], [], [.ph 3]) ∈ blk3 M m u := by
            simp only [blk3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
              List.mem_range, List.mem_filter]
            exact Or.inr (Or.inl (Or.inr ⟨X, ⟨mem_allV X, by simpa using hX⟩, rfl⟩))
          exact kill3 M m u h _ _ (mem3 _ hmem) ⟨by simp [st], by simp⟩
    · have := h ([.ph 3], [], [.ph 0], [.ph 3]) (mem3 _ (by simp [blk3])) ⟨by simp [st], by simp⟩
      rwa [eff_pass] at this
  · rintro ⟨hnr, hw⟩ a ha happ
    rcases blk_of_app M m u (st_ph 3 i X .none G) ha happ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · omega
    · omega
    have gj_of : ∀ j, st 3 i X .none G (.gj j) = true → G = .j j := by
      intro j hj; cases G <;> simp [st] at hj; subst hj; rfl
    have gb_of : st 3 i X .none G .gb = true → G = .b := by
      intro hj; cases G <;> simp [st] at hj; rfl
    simp only [blk3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map] at h
    rcases h with rfl | (((⟨j, hj, b, hb, rfl⟩ | ⟨j, hj, v, hv, rfl⟩) | ⟨v, hv, rfl⟩) | ⟨j, hj, rfl⟩)
    · rw [eff_pass]; exact hw
    · exfalso
      have hG' := gj_of j (happ.1 (.gj j) (by unfold mis; split_ifs <;> simp))
      subst hG'
      apply hnr
      refine Or.inl fun hij => ?_
      subst hij
      unfold mis at happ
      split_ifs at happ with hjb
      · have := happ.2 (.ib b) (by simp); simp [st] at this; rw [this] at hjb; simp at hjb
      · have := happ.1 (.ib b) (by simp); simp [st] at this; exact hjb this
    · exfalso
      have hG' := gj_of j (happ.1 (.gj j) (by simp))
      subst hG'
      have hx : v = X := by simpa [st] using happ.1 (.x v) (by simp)
      subst hx
      exact hnr (Or.inr (by simpa using (List.mem_filter.1 hv).2))
    · exfalso
      have hG' := gb_of (happ.1 .gb (by simp))
      subst hG'
      have hx : v = X := by simpa [st] using happ.1 (.x v) (by simp)
      subst hx
      exact hnr (Or.inr (by simpa using (List.mem_filter.1 hv).2))
    · exfalso
      have hG' := gb_of (happ.1 .gb (by simp))
      subst hG'
      have heq : i = j := by
        refine eq_of_testBit_lt (lt_bw_left m u hi) (lt_bw_right m u (by simp at hj; omega)) fun b hb => ?_
        by_cases hjb : j.testBit b = true
        · rw [hjb]; exact happ.1 (.ib b) (by simp [hb, hjb])
        · have := happ.2 (.ib b) (by simp [hb, hjb])
          simp [st] at this; simpa [hjb] using this
      exact hnr (Or.inl (by simp at hj; omega))

end DBG

end FOND
