import FondHtn.DB25Games.Game
import FondHtn.DB25Games.Tab
import FondHtn.DB25.Bits
/-!
# [DB25, Thm. 1] hardness: the game of a space-bounded deterministic machine

For a deterministic machine `M` (states `Fin k`, symbols `Option Bool`), `m` address bits and an
input `u`, `FOND.DBG.acts M m u` is a STRIPS action set over the structured facts
`FOND.DBG.Fct k`.  A **cycle** of the game has four turns and checks one step of the truncated
tableau (`FOND.DBG.tabT`) *backwards in time*, as in [DB25]:

* the state holds a **claim** `(i, X)`: a cell `i < 2 ^ m` (bits `ib b`) and an entry `X`
  (`x X`; `X = none` is the claim "an accepting state is shown at some cell `j ≥ i`");
* turn 0 (Éloise) proposes the three entries `l, c, r` at the previous time whose local rule gives
  `X` (or, for `X = none`, gives an accepting state), or shifts the claim to the right;
* turn 1 (Abélard) picks one of the three entries; the claim moves to `i - 1`, `i` or `i + 1`
  (binary decrement / increment of the cell bits); a head next to the right border refutes;
* turn 2 (Éloise) may assert that the claim is the first row (`g`, with a case `gj j`: `i = j ≤
  |u|`, or `gb`: `i > |u|`), turn 3 (Abélard) may refute this assertion.

The goal is `{ph 0, g}`: after the last cycle the claim must be a true entry of the first row.
Positions only change the claim, so time is the number of remaining cycles.  This is the
[DB25] construction with explicit gadgets (deviations: no turn-counter lemma — the phases are
built in —, an accepting claim instead of a halting state, and the goal assertion `g` checked
by refutation actions instead of a compiled disjunctive goal).
-/

namespace FOND

namespace DBG

open TM TM.NTM

/-! ## Bits -/

section Bits

theorem testBit_ge {i m b : ℕ} (hi : i < 2 ^ m) (hb : m ≤ b) : i.testBit b = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hb))

theorem ne_zero_of_testBit {i b : ℕ} (h : i.testBit b = true) : i ≠ 0 := by
  rintro rfl; simp at h

theorem eq_of_testBit_lt {i j B : ℕ} (hi : i < 2 ^ B) (hj : j < 2 ^ B)
    (h : ∀ b < B, i.testBit b = j.testBit b) : i = j := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < B
  · exact h b hb
  · rw [testBit_ge hi (by omega), testBit_ge hj (by omega)]

theorem eq_zero_of_testBit {i m : ℕ} (hi : i < 2 ^ m) (h : ∀ b < m, i.testBit b = false) : i = 0 :=
  eq_of_testBit_lt hi (Nat.two_pow_pos m) fun b hb => by rw [h b hb]; simp

theorem succ_lt_of_testBit {i m b : ℕ} (hi : i < 2 ^ m) (hb : b < m) (h : i.testBit b = false) :
    i + 1 < 2 ^ m := by
  by_contra hc
  have : i = 2 ^ m - 1 := by omega
  rw [this, Nat.testBit_two_pow_sub_one] at h
  simp at h; omega

theorem succ_eq_of_testBit {i m : ℕ} (hi : i < 2 ^ m) (h : ∀ b < m, i.testBit b = true) :
    i + 1 = 2 ^ m := by
  have := DB.bval_allTrue m i.testBit h
  rwa [DB.bval_testBit hi] at this

theorem testBit_pred {i m j : ℕ} (hi : i < 2 ^ m) (hj : j < m) (h0 : ∀ b < j, i.testBit b = false)
    (h1 : i.testBit j = true) : ∀ b, (i - 1).testBit b = DB.decSet i.testBit j b := by
  have hd := DB.bval_decSet m i.testBit j hj h0 h1
  rw [DB.bval_testBit hi] at hd
  have he : DB.bval m (i - 1).testBit = DB.bval m (DB.decSet i.testBit j) := by
    rw [DB.bval_testBit (by omega)]; omega
  intro b
  by_cases hb : b < m
  · exact DB.bval_inj m he b hb
  · rw [testBit_ge (by omega : i - 1 < 2 ^ m) (by omega)]
    simp only [DB.decSet]
    rw [if_neg (by omega), if_neg (by omega), testBit_ge hi (by omega)]

theorem testBit_succ {i m j : ℕ} (hi : i + 1 < 2 ^ m) (hj : j < m) (h0 : ∀ b < j, i.testBit b = true)
    (h1 : i.testBit j = false) : ∀ b, (i + 1).testBit b = DB.incSet i.testBit j b := by
  have hd := DB.bval_incSet m i.testBit j hj h0 h1
  rw [DB.bval_testBit (by omega)] at hd
  have he : DB.bval m (i + 1).testBit = DB.bval m (DB.incSet i.testBit j) := by
    rw [DB.bval_testBit hi]; omega
  intro b
  by_cases hb : b < m
  · exact DB.bval_inj m he b hb
  · rw [testBit_ge hi (by omega)]
    simp only [DB.incSet]
    rw [if_neg (by omega), if_neg (by omega), testBit_ge (by omega : i < 2 ^ m) (by omega)]

end Bits

/-! ## Facts and actions -/

/-- Tape symbols. -/
abbrev Sym : Type := Option Bool

/-- Tableau entries. -/
abbrev CS (k : ℕ) : Type := CSym (Fin k) Sym

/-- Claims: an entry, or `none` ("accepting somewhere to the right"). -/
abbrev V (k : ℕ) : Type := Option (CS k)

/-- **The facts.** -/
inductive Fct (k : ℕ) where
  | ph (j : ℕ)
  | ib (b : ℕ)
  | x (v : V k)
  | pl (v : CS k)
  | pc (v : CS k)
  | pr (v : CS k)
  | sh
  | g
  | gj (j : ℕ)
  | gb
  deriving DecidableEq

variable {k : ℕ} (M : NTM (Fin k) Sym)

/-- `X` is matched by the entry `y`. -/
def Matches (X : V k) (y : CS k) : Prop := X = some y ∨ (X = none ∧ ∃ q ∈ M.accept, y.1 = some q)

/-- Proposals away from the left border. -/
noncomputable def trip1 : List (V k × CS k × CS k × CS k) := by
  classical
  exact (Finset.univ.filter fun t : V k × CS k × CS k × CS k =>
    Matches M t.1 (M.F (some t.2.1) t.2.2.1 t.2.2.2)).toList

/-- Proposals at the left border. -/
noncomputable def trip0 : List (V k × CS k × CS k × CS k) := by
  classical
  exact (Finset.univ.filter fun t : V k × CS k × CS k × CS k =>
    Matches M t.1 (M.F none t.2.2.1 t.2.2.2)).toList

theorem mem_trip1 {t : V k × CS k × CS k × CS k} :
    t ∈ trip1 M ↔ Matches M t.1 (M.F (some t.2.1) t.2.2.1 t.2.2.2) := by
  classical
  simp [trip1]

theorem mem_trip0 {t : V k × CS k × CS k × CS k} :
    t ∈ trip0 M ↔ Matches M t.1 (M.F none t.2.2.1 t.2.2.2) := by
  classical
  simp [trip0]

/-- All claims. -/
noncomputable def allV : List (V k) := Finset.univ.toList
/-- All entries. -/
noncomputable def allC : List (CS k) := Finset.univ.toList
/-- The entries with a head. -/
noncomputable def headC : List (CS k) := by
  classical
  exact (Finset.univ.filter fun v : CS k => v.1 ≠ none).toList

@[simp] theorem mem_allV (v : V k) : v ∈ allV := by simp [allV]
@[simp] theorem mem_allC (v : CS k) : v ∈ allC := by simp [allC]
@[simp] theorem mem_headC (v : CS k) : v ∈ headC ↔ v.1 ≠ none := by
  classical
  simp [headC]

/-- All claim facts. -/
noncomputable def allX : List (Fct k) := allV.map .x
/-- All proposal facts. -/
noncomputable def allP : List (Fct k) := allC.flatMap (fun v => [.pl v, .pc v, .pr v]) ++ [.sh]
/-- All assertion facts (`n = |u|`). -/
def gAll (n : ℕ) : List (Fct k) := [.g, .gb] ++ (List.range (n + 1)).map .gj
/-- The cell bits below `j`. -/
def ibs (j : ℕ) : List (Fct k) := (List.range j).map .ib

@[simp] theorem mem_allX (f : Fct k) : f ∈ allX ↔ ∃ v, f = .x v := by
  simp [allX, eq_comm]
@[simp] theorem mem_allP (f : Fct k) : f ∈ allP ↔ (∃ v, f = .pl v ∨ f = .pc v ∨ f = .pr v) ∨ f = .sh := by
  simp [allP]
@[simp] theorem mem_gAll (n : ℕ) (f : Fct k) : f ∈ gAll n ↔ f = .g ∨ f = .gb ∨ ∃ j ≤ n, f = .gj j := by
  simp [gAll, eq_comm]
@[simp] theorem mem_ibs (j : ℕ) (f : Fct k) : f ∈ ibs j ↔ ∃ b < j, f = .ib b := by
  simp [ibs, eq_comm]

variable (m : ℕ) (u : List Sym)

/-- The first row of the tableau. -/
def row0 (j : ℕ) : CS k := (if j = 0 then some M.init else none, u.getD j M.blank)

/-- Turn 0 (Éloise): proposals and shifts. -/
noncomputable def blk0 : List (Act (Fct k)) :=
  (trip1 M).flatMap (fun t => (List.range m).map fun b =>
    ([.ph 0, .x t.1, .ib b], [], [.ph 1, .pl t.2.1, .pc t.2.2.1, .pr t.2.2.2], .ph 0 :: gAll u.length)) ++
  (trip0 M).map (fun t =>
    ([.ph 0, .x t.1], ibs m, [.ph 1, .pl t.2.1, .pc t.2.2.1, .pr t.2.2.2], .ph 0 :: gAll u.length)) ++
  (List.range m).map (fun b => ([.ph 0, .x none], [.ib b], [.ph 1, .sh], .ph 0 :: gAll u.length))

/-- Turn 1 (Abélard): the choice of an entry, with the cell update; border refutations. -/
noncomputable def blk1 : List (Act (Fct k)) :=
  allC.flatMap (fun v => (List.range m).map fun j =>
    ([.ph 1, .pl v, .ib j], ibs j, .ph 2 :: .x (some v) :: ibs j, .ph 1 :: .ib j :: (allX ++ allP))) ++
  allC.map (fun v => ([.ph 1, .pc v], [], [.ph 2, .x (some v)], .ph 1 :: (allX ++ allP))) ++
  allC.flatMap (fun v => (List.range m).map fun j =>
    (.ph 1 :: .pr v :: ibs j, [.ib j], [.ph 2, .x (some v), .ib j], .ph 1 :: (ibs j ++ allX ++ allP))) ++
  (List.range m).map (fun j => (.ph 1 :: .sh :: ibs j, [.ib j], [.ph 2, .ib j], .ph 1 :: (ibs j ++ allP))) ++
  headC.map (fun v => (.ph 1 :: .pr v :: ibs m, [], [], [.ph 1]))

/-- Turn 2 (Éloise): the first-row assertion. -/
def blk2 : List (Act (Fct k)) :=
  ([.ph 2], [], [.ph 3], [.ph 2]) :: ([.ph 2], [], [.ph 3, .g, .gb], [.ph 2]) ::
    (List.range (u.length + 1)).map (fun j => ([.ph 2], [], [.ph 3, .g, .gj j], [.ph 2]))

/-- The bit width of the comparisons of turn 3. -/
def bw : ℕ := m + u.length + 1

/-- A bit mismatch between the cell and `j`. -/
def mis (j b : ℕ) : Act (Fct k) :=
  if j.testBit b then ([.ph 3, .gj j], [.ib b], [], [.ph 3]) else ([.ph 3, .gj j, .ib b], [], [], [.ph 3])

/-- Turn 3 (Abélard): pass, or refute the assertion. -/
noncomputable def blk3 : List (Act (Fct k)) :=
  ([.ph 3], [], [.ph 0], [.ph 3]) ::
  ((List.range (u.length + 1)).flatMap (fun j => (List.range (bw m u)).map (mis j)) ++
  (List.range (u.length + 1)).flatMap (fun j => (allV.filter (· ≠ some (row0 M u j))).map fun v =>
    ([.ph 3, .gj j, .x v], [], [], [.ph 3])) ++
  (allV.filter (· ≠ some (none, M.blank))).map (fun v => ([.ph 3, .gb, .x v], [], [], [.ph 3])) ++
  (List.range (u.length + 1)).map (fun j =>
    (.ph 3 :: .gb :: ((List.range (bw m u)).filter (fun b => j.testBit b)).map .ib,
      ((List.range (bw m u)).filter (fun b => !j.testBit b)).map .ib, [], [.ph 3])))

/-- **The actions.** -/
noncomputable def acts : List (Act (Fct k)) := blk0 M m u ++ blk1 m ++ blk2 u ++ blk3 M m u

/-- **The goal.** -/
def goal : List (Fct k) := [.ph 0, .g]

/-- **The initial state**: phase 0, cell 0, claim "accepting somewhere". -/
def init : List (Fct k) := [.ph 0, .x none]

/-! ## Phases -/

theorem ph_blk0 : ∀ a ∈ blk0 M m u, (.ph 0 : Fct k) ∈ a.1 := by
  intro a ha
  simp only [blk0, List.mem_append, List.mem_flatMap, List.mem_map] at ha
  rcases ha with (⟨t, -, b, -, rfl⟩ | ⟨t, -, rfl⟩) | ⟨b, -, rfl⟩ <;> simp

theorem ph_blk1 : ∀ a ∈ blk1 (k := k) m, (.ph 1 : Fct k) ∈ a.1 := by
  intro a ha
  simp only [blk1, List.mem_append, List.mem_flatMap, List.mem_map] at ha
  rcases ha with (((⟨v, -, j, -, rfl⟩ | ⟨v, -, rfl⟩) | ⟨v, -, j, -, rfl⟩) | ⟨j, -, rfl⟩) | ⟨v, -, rfl⟩ <;>
    simp

theorem ph_blk2 : ∀ a ∈ blk2 (k := k) u, (.ph 2 : Fct k) ∈ a.1 := by
  intro a ha
  simp only [blk2, List.mem_cons, List.mem_map] at ha
  rcases ha with rfl | rfl | ⟨j, -, rfl⟩ <;> simp

theorem ph_mis (j b : ℕ) : (.ph 3 : Fct k) ∈ (mis j b).1 := by
  unfold mis; split_ifs <;> simp

theorem ph_blk3 : ∀ a ∈ blk3 M m u, (.ph 3 : Fct k) ∈ a.1 := by
  intro a ha
  simp only [blk3, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map] at ha
  rcases ha with rfl | (((⟨j, -, b, -, rfl⟩ | ⟨j, -, v, -, rfl⟩) | ⟨v, -, rfl⟩) | ⟨j, -, rfl⟩)
  all_goals first | exact ph_mis j b | simp

/-- In a state with phase `p` only, an applicable action is in block `p`. -/
theorem blk_of_app {s : Fct k → Bool} {p : ℕ} (hs : ∀ j, s (.ph j) = decide (j = p)) {a : Act (Fct k)}
    (ha : a ∈ acts M m u) (happ : App a s) :
    (p = 0 ∧ a ∈ blk0 M m u) ∨ (p = 1 ∧ a ∈ blk1 m) ∨ (p = 2 ∧ a ∈ blk2 u) ∨ (p = 3 ∧ a ∈ blk3 M m u) := by
  have key : ∀ j, (.ph j : Fct k) ∈ a.1 → j = p := fun j hj => by
    have := happ.1 _ hj; rw [hs] at this; simpa using this
  simp only [acts, List.mem_append] at ha
  rcases ha with ((h | h) | h) | h
  · exact Or.inl ⟨(key 0 (ph_blk0 M m u a h)).symm, h⟩
  · exact Or.inr (Or.inl ⟨(key 1 (ph_blk1 m a h)).symm, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(key 2 (ph_blk2 u a h)).symm, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(key 3 (ph_blk3 M m u a h)).symm, h⟩))

/-- **A state without phase is lost by Éloise** (once Abélard has refuted). -/
theorem not_win_dead {s : Fct k → Bool} (hs : ∀ j < 4, s (.ph j) = false) :
    ∀ T, ¬ Win (acts M m u) goal T true s := by
  intro T hw
  cases T with
  | zero => have := hw (.ph 0) (by simp [goal]); rw [hs 0 (by omega)] at this; simp at this
  | succ T =>
    obtain ⟨a, ha, happ, -⟩ := hw
    simp only [acts, List.mem_append] at ha
    rcases ha with ((h | h) | h) | h
    · have := happ.1 _ (ph_blk0 M m u a h); rw [hs 0 (by omega)] at this; simp at this
    · have := happ.1 _ (ph_blk1 m a h); rw [hs 1 (by omega)] at this; simp at this
    · have := happ.1 _ (ph_blk2 u a h); rw [hs 2 (by omega)] at this; simp at this
    · have := happ.1 _ (ph_blk3 M m u a h); rw [hs 3 (by omega)] at this; simp at this

end DBG

end FOND
