import Mathlib

/-!
# Reachability by a fixed-point table over a finite box

A generic, executable reachability check: for a successor function `succ : σ → List σ` and a
finite list `box` of states, the table `tblStep^[n] (tblInit x₀)` assigns to every state of the
box the truth value of "reachable from `x₀` in at most `n` steps through states of the box".
The table never changes its shape, which is what makes the iteration polynomial time (its size
is that of the initial table).
-/

namespace HTN

namespace FixTbl

set_option linter.unusedSectionVars false

variable {σ : Type} [DecidableEq σ] (succ : σ → List σ) (box : List σ)

/-- Reachable in at most `n` steps, through states of the box. -/
def ReachB : ℕ → σ → σ → Prop
  | 0, x, y => x = y ∧ x ∈ box
  | n + 1, x, y => ReachB n x y ∨ ∃ z, ReachB n x z ∧ y ∈ succ z ∧ y ∈ box

/-- The initial table. -/
def tblInit (x₀ : σ) : List (σ × Bool) := box.map fun x => (x, decide (x = x₀))

/-- One round of the table. -/
def tblStep (t : List (σ × Bool)) : List (σ × Bool) :=
  t.map fun p => (p.1, p.2 || t.any fun p' => p'.2 && decide (p.1 ∈ succ p'.1))

/-- The answer: some state of the table is marked and satisfies `goal`. -/
def tblAny (goal : σ → Bool) (t : List (σ × Bool)) : Bool := t.any fun p => p.2 && goal p.1

variable {succ box}

theorem mem_box_of_reachB : ∀ {n : ℕ} {x y : σ}, ReachB succ box n x y → y ∈ box
  | 0, _, _, h => h.1 ▸ h.2
  | _ + 1, _, _, Or.inl h => mem_box_of_reachB h
  | _ + 1, _, _, Or.inr ⟨_, _, _, hy⟩ => hy

theorem mem_box_left : ∀ {n : ℕ} {x y : σ}, ReachB succ box n x y → x ∈ box
  | 0, _, _, h => h.2
  | _ + 1, _, _, Or.inl h => mem_box_left h
  | _ + 1, _, _, Or.inr ⟨_, h, _, _⟩ => mem_box_left h

theorem reachB_mono : ∀ {n m : ℕ} {x y : σ}, n ≤ m → ReachB succ box n x y → ReachB succ box m x y
  | n, 0, x, y, hnm, h => by
    rw [Nat.le_zero.1 hnm] at h
    exact h
  | n, m + 1, x, y, hnm, h => by
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact Or.inl (reachB_mono (Nat.le_of_lt_succ hlt) h)
    · rw [show n = m + 1 by omega] at h
      exact h

theorem reachB_refl {x : σ} (hx : x ∈ box) (n : ℕ) : ReachB succ box n x x :=
  reachB_mono (Nat.zero_le n) ⟨rfl, hx⟩

/-- Prepending a step. -/
theorem reachB_cons : ∀ {n : ℕ} {x y z : σ}, x ∈ box → y ∈ succ x → ReachB succ box n y z →
    ReachB succ box (n + 1) x z
  | 0, x, y, z, hx, hy, h => by
    obtain ⟨rfl, hyb⟩ := h
    exact Or.inr ⟨x, ⟨rfl, hx⟩, hy, hyb⟩
  | n + 1, x, y, z, hx, hy, h => by
    rcases h with h | ⟨w, hw, hzw, hzb⟩
    · exact Or.inl (reachB_cons hx hy h)
    · exact Or.inr ⟨w, reachB_cons hx hy hw, hzw, hzb⟩

/-- **The table after `n` rounds**: its first components are the box, and a state is marked iff
it is reachable from `x₀` in at most `n` steps through the box. -/
theorem tbl_spec (x₀ : σ) (n : ℕ) :
    ((tblStep succ)^[n] (tblInit box x₀)).map Prod.fst = box ∧
      ∀ p ∈ (tblStep succ)^[n] (tblInit box x₀), (p.2 = true ↔ ReachB succ box n x₀ p.1) := by
  induction n with
  | zero =>
    refine ⟨by simp [tblInit, List.map_map, Function.comp_def], fun p hp => ?_⟩
    simp only [Function.iterate_zero, id, tblInit, List.mem_map] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    simp only [decide_eq_true_eq, ReachB]
    exact ⟨fun h => ⟨h.symm, h ▸ hx⟩, fun h => h.1.symm⟩
  | succ n ih =>
    obtain ⟨hfst, hspec⟩ := ih
    rw [Function.iterate_succ_apply']
    set t := (tblStep succ)^[n] (tblInit box x₀) with ht
    refine ⟨by simp [tblStep, List.map_map, Function.comp_def, hfst], fun p hp => ?_⟩
    simp only [tblStep, List.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    have hrbox : r.1 ∈ box := hfst ▸ List.mem_map_of_mem hr
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [hspec r hr]
    show _ ↔ ReachB succ box n x₀ r.1 ∨ ∃ z, ReachB succ box n x₀ z ∧ r.1 ∈ succ z ∧ r.1 ∈ box
    constructor
    · rintro (h | ⟨p', hp', hm, hs⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p'.1, (hspec p' hp').1 hm, hs, hrbox⟩
    · rintro (h | ⟨z, hz, hs, -⟩)
      · exact Or.inl h
      · have hzb : z ∈ t.map Prod.fst := hfst ▸ mem_box_of_reachB hz
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hzb
        exact Or.inr ⟨p', hp', (hspec p' hp').2 hz, hs⟩

/-- **The answer of the table.** -/
theorem tblAny_iterate (x₀ : σ) (n : ℕ) (goal : σ → Bool) :
    tblAny goal ((tblStep succ)^[n] (tblInit box x₀)) = true ↔
      ∃ y, ReachB succ box n x₀ y ∧ goal y = true := by
  obtain ⟨hfst, hspec⟩ := tbl_spec (succ := succ) (box := box) x₀ n
  unfold tblAny
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [Bool.and_eq_true] at h
    exact ⟨p.1, (hspec p hp).1 h.1, h.2⟩
  · rintro ⟨y, hy, hg⟩
    have hyb : y ∈ ((tblStep succ)^[n] (tblInit box x₀)).map Prod.fst := by
      rw [hfst]; exact mem_box_of_reachB hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hyb
    exact ⟨p, hp, by rw [Bool.and_eq_true]; exact ⟨(hspec p hp).2 hy, hg⟩⟩

end FixTbl

end HTN
