import Mathlib
import ComplexityTheory.TM.Basic
/-!
# Nondeterministic Turing machines with an exponential time bound

This file provides the machine model used for the hardness side of the compilability results:
nondeterministic Turing machines (NTMs) working on a one-way infinite tape, together with the
notion of *acceptance within `K` steps* and, in particular, of acceptance within an
exponential number of steps `K = 2^(p(|w|))`.

The model mirrors the one used in

  R. Alford, P. Bercher, D. Aha, *Tight Bounds for HTN Planning* (ICAPS 2015), Thm. 6.1

and in Theorem 4.3.7 of

  P. Bercher, G. Behnke, D. Höller, T. Geier, R. Alford,
  *Propositional Hierarchical Task Network Planning: Problem Classes and Complexity Results*,

namely `N = (S, Σ, Γ, δ, q₀, F)` with `δ : S × Γ → 2^(S × Γ × {-1,0,1})`, working on a tape
that is infinite to the right only and initially contains the input followed by blanks.

Mathlib's `Turing.TM0` uses a two-way infinite tape represented by a zipper (`Turing.Tape`).
For the HTN encoding we need an explicit *time bound*, an explicit *cell index* for every tape
cell (the encoding has one counter per cell index) and the guarantee that the head never moves
left of the input; a tape `ℕ → Γ` with a head position `head : ℕ` makes all of this directly
available, so we use that representation here.  The semantics is the usual one and agrees with
`Turing.TM0` on machines that never move left of their input.

## Main definitions

* `TM.NTM Q Γ` — a nondeterministic Turing machine,
* `TM.Config Q Γ` — a configuration (state, head position, tape),
* `TM.NTM.Step`, `TM.NTM.Reaches` — the (n-step) transition relation,
* `TM.NTM.AcceptsWithin N w K` — `N` accepts the input `w` within `K` steps,
* `TM.NTM.AcceptsExp N p w` — acceptance within `2 ^ p(|w|)` steps,
* `TM.IsHistory` — a *witness* for acceptance: the finite sequence of configurations of an
  accepting run.

## Main results

* `TM.NTM.acceptsWithin_iff_exists_history` — acceptance within `K` steps is equivalent to the
  existence of a checkable witness (a history of at most `K` steps whose consecutive
  configurations are related by the transition relation).  This is the statement that the
  HTN encoding of Theorem 4.3.7 checks.
* `TM.NTM.Reaches.head_le`, `TM.NTM.Reaches.tape_eq_of_lt` — after `n` steps the head has
  moved at most `n` cells and only the first `head + n` cells can have changed; hence a run of
  `K` steps only involves the tape cells `0, …, K`, which is why the encoding needs `K + 1`
  cell counters.
-/

namespace TM

@[simp] lemma Move.apply_left (n : ℕ) : Move.left.apply n = n - 1 := rfl
@[simp] lemma Move.apply_stay (n : ℕ) : Move.stay.apply n = n := rfl
@[simp] lemma Move.apply_right (n : ℕ) : Move.right.apply n = n + 1 := rfl

lemma Move.apply_le (m : Move) (n : ℕ) : m.apply n ≤ n + 1 := by
  cases m <;> simp only [Move.apply] <;> omega

namespace NTM

variable {Q Γ : Type*} (N : NTM Q Γ)

@[simp] lemma reaches_zero {c c' : Config Q Γ} : N.Reaches 0 c c' ↔ c = c' := Iff.rfl

@[simp] lemma reaches_succ {n : ℕ} {c c' : Config Q Γ} :
    N.Reaches (n + 1) c c' ↔ ∃ d, N.Step c d ∧ N.Reaches n d c' := Iff.rfl

lemma Reaches.trans {m n : ℕ} {c d e : Config Q Γ} (h₁ : N.Reaches m c d)
    (h₂ : N.Reaches n d e) : N.Reaches (m + n) c e := by
  induction m generalizing c with
  | zero => cases h₁; simpa using h₂
  | succ m ih =>
      obtain ⟨x, hx, hxd⟩ := h₁
      have hrec : N.Reaches (m + n) x e := ih hxd
      rw [show m + 1 + n = (m + n) + 1 by omega]
      exact ⟨x, hx, hrec⟩

lemma acceptsWithin_mono {w : List Γ} {K K' : ℕ} (h : K ≤ K') (hacc : N.AcceptsWithin w K) :
    N.AcceptsWithin w K' := by
  obtain ⟨n, hn, c, hc, hacc⟩ := hacc
  exact ⟨n, hn.trans h, c, hc, hacc⟩

/-! ### Locality of a run

A machine that runs for `n` steps only sees the first `head + n + 1` tape cells.  This is the
reason why a run of `K` steps can be described by `K + 1` tapes of `K + 1` cells each, which is
what the HTN encoding of Theorem 4.3.7 does. -/

lemma Step.head_le {c c' : Config Q Γ} (h : N.Step c c') : c'.head ≤ c.head + 1 := by
  obtain ⟨q', γ', m, -, rfl⟩ := h
  exact m.apply_le _

lemma Step.tape_eq_of_ne {c c' : Config Q Γ} (h : N.Step c c') {i : ℕ} (hi : i ≠ c.head) :
    c'.tape i = c.tape i := by
  obtain ⟨q', γ', m, -, rfl⟩ := h
  simp [Function.update_of_ne hi]

lemma Reaches.head_le {n : ℕ} {c c' : Config Q Γ} (h : N.Reaches n c c') :
    c'.head ≤ c.head + n := by
  induction n generalizing c with
  | zero => cases h; simp
  | succ n ih =>
      obtain ⟨d, hstep, hd⟩ := h
      have h₁ := ih hd
      have h₂ := hstep.head_le
      omega

/-- Only the cells that the head can reach are modified. -/
lemma Reaches.tape_eq_of_lt {n : ℕ} {c c' : Config Q Γ} (h : N.Reaches n c c') {i : ℕ}
    (hi : c.head + n < i) : c'.tape i = c.tape i := by
  induction n generalizing c with
  | zero => cases h; rfl
  | succ n ih =>
      obtain ⟨d, hstep, hd⟩ := h
      have hdhead : d.head ≤ c.head + 1 := hstep.head_le
      have h₁ : d.head + n < i := by omega
      have hne : i ≠ c.head := by omega
      have h₂ : d.tape i = c.tape i := Step.tape_eq_of_ne N hstep hne
      rw [ih hd h₁, h₂]

end NTM

/-! ### Histories: checkable witnesses of acceptance

The HTN encoding does not simulate the machine step by step; the *plan* of the constructed
planning problem is a witness `W = #w₀#w₁# … #w_K` of an accepting run, and the hierarchy
enforces that `W` is a valid witness.  The following definition is the formal counterpart of
such a witness. -/

/-- `IsHistory N w T hist` states that `hist 0, …, hist T` is an accepting run of `N` on the
input `w`: it starts in the initial configuration, every step is a transition of `N`, and the
last configuration is accepting. -/
structure IsHistory {Q Γ : Type*} (N : NTM Q Γ) (w : List Γ) (T : ℕ)
    (hist : ℕ → Config Q Γ) : Prop where
  /-- The run starts in the initial configuration. -/
  init : hist 0 = N.initConfig w
  /-- Consecutive configurations are related by the transition relation. -/
  step : ∀ i < T, N.Step (hist i) (hist (i + 1))
  /-- The run ends in an accepting state. -/
  accept : (hist T).state ∈ N.accept

namespace NTM

variable {Q Γ : Type*} (N : NTM Q Γ)

/-- A reachability proof can be turned into the explicit sequence of configurations it
traverses. -/
lemma exists_path_of_reaches {n : ℕ} {c c' : Config Q Γ} (h : N.Reaches n c c') :
    ∃ hist : ℕ → Config Q Γ, hist 0 = c ∧ (∀ i < n, N.Step (hist i) (hist (i + 1))) ∧
      hist n = c' := by
  induction n generalizing c with
  | zero =>
      have hcc : c = c' := h
      exact ⟨fun _ => c, rfl, by omega, hcc⟩
  | succ n ih =>
      obtain ⟨d, hstep, hd⟩ := h
      obtain ⟨hist, h0, hsteps, hlast⟩ := ih hd
      refine ⟨fun i => if i = 0 then c else hist (i - 1), by simp, ?_, ?_⟩
      · intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simpa [h0] using hstep
        · have h1 : ¬ i = 0 := by omega
          have h2 : ¬ i + 1 = 0 := by omega
          simp only [h1, h2, if_false]
          have hlt : i - 1 < n := by omega
          simpa [show i + 1 - 1 = (i - 1) + 1 by omega] using hsteps (i - 1) hlt
      · have h3 : ¬ n + 1 = 0 := by omega
        simpa [h3] using hlast

lemma reaches_of_isHistory {w : List Γ} {T : ℕ} {hist : ℕ → Config Q Γ}
    (h : IsHistory N w T hist) : ∀ n ≤ T, N.Reaches n (N.initConfig w) (hist n) := by
  intro n hn
  induction n with
  | zero => simpa using h.init.symm
  | succ n ih =>
      have hn' : n ≤ T := by omega
      have hrec := ih hn'
      have hstep : N.Step (hist n) (hist (n + 1)) := h.step n (by omega)
      have := Reaches.trans N hrec (show N.Reaches 1 (hist n) (hist (n + 1)) from
        ⟨hist (n + 1), hstep, rfl⟩)
      simpa using this

/-- **Acceptance is witnessed by a history.**  `N` accepts `w` within `K` steps iff there is a
sequence of at most `K + 1` configurations starting in the initial configuration, each obtained
from its predecessor by a transition, and ending in an accepting state. -/
theorem acceptsWithin_iff_exists_history (w : List Γ) (K : ℕ) :
    N.AcceptsWithin w K ↔ ∃ T ≤ K, ∃ hist : ℕ → Config Q Γ, IsHistory N w T hist := by
  constructor
  · rintro ⟨n, hn, c, hc, hacc⟩
    obtain ⟨hist, h0, hsteps, hlast⟩ := exists_path_of_reaches N hc
    exact ⟨n, hn, hist, ⟨h0, hsteps, by rw [hlast]; exact hacc⟩⟩
  · rintro ⟨T, hT, hist, hhist⟩
    exact ⟨T, hT, hist T, reaches_of_isHistory N hhist T le_rfl, hhist.accept⟩

/-- In a history of length `T`, the head is always in one of the first `T + 1` cells. -/
lemma isHistory_head_le {w : List Γ} {T : ℕ} {hist : ℕ → Config Q Γ}
    (h : IsHistory N w T hist) : ∀ i ≤ T, (hist i).head ≤ i := by
  intro i hi
  have := (reaches_of_isHistory N h i hi).head_le
  simpa [initConfig] using this

end NTM

end TM
