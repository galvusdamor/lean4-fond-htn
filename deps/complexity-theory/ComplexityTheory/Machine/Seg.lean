import ComplexityTheory.TM.Theory.Machine
import ComplexityTheory.Complexity.Hypotheses
/-!
# Segments of runs of a nondeterministic Turing machine

Simulating one machine by another is proved in two directions: every run of the simulated
machine gives a run of the simulating one (*completeness*), and every accepting run of the
simulating machine comes from a run of the simulated one (*soundness*).  For a simulating machine
that is deterministic except at a few explicit choice points, soundness follows from the
following bookkeeping device.

* `TM.NTM.Passes N c c' m` — every accepting run from `c` passes through `c'` after exactly `m`
  steps;
* `TM.NTM.Seg N S c c' m` — `c` reaches `c'` in `m` steps within the space `S` (the head stays on
  the cells `0, …, S - 1`), and every accepting run from `c` passes through `c'` after `m` steps.

Segments compose (`Seg.trans`), and a single deterministic, non-accepting step is a segment
(`Seg.single`).  So a deterministic routine is a segment as soon as each of its steps is, and a
run of the simulating machine can be cut into the segments that simulate single steps.

The file also provides the basic algebra of `TM.NTM.ReachesSpace` (`ReachesSpace.trans`,
`ReachesSpace.mono`, `ReachesSpace.reaches`) and the restriction of a machine to a finite set of
states closed under its transitions (`TM.NTM.restrict`), which turns a machine with an infinite
state type into one with finitely many states.
-/

namespace TM

namespace NTM

variable {Q Γ : Type*} (N : NTM Q Γ)

/-! ### Space-bounded reachability -/

theorem ReachesSpace.reaches {S n : ℕ} {c c' : Config Q Γ} (h : N.ReachesSpace S n c c') :
    N.Reaches n c c' := by
  induction n generalizing c with
  | zero => exact h.1
  | succ n ih => obtain ⟨-, d, hd, h'⟩ := h; exact ⟨d, hd, ih h'⟩

theorem ReachesSpace.head_lt {S n : ℕ} {c c' : Config Q Γ} (h : N.ReachesSpace S n c c') :
    c.head < S := by
  cases n with
  | zero => exact h.2
  | succ n => exact h.1

theorem ReachesSpace.head_lt' {S n : ℕ} {c c' : Config Q Γ} (h : N.ReachesSpace S n c c') :
    c'.head < S := by
  induction n generalizing c with
  | zero => obtain ⟨rfl, h⟩ := h; exact h
  | succ n ih => obtain ⟨-, d, -, h'⟩ := h; exact ih h'

theorem ReachesSpace.trans {S m n : ℕ} {c d e : Config Q Γ} (h₁ : N.ReachesSpace S m c d)
    (h₂ : N.ReachesSpace S n d e) : N.ReachesSpace S (m + n) c e := by
  induction m generalizing c with
  | zero => obtain ⟨rfl, -⟩ := h₁; simpa using h₂
  | succ m ih =>
    obtain ⟨hc, x, hx, hxd⟩ := h₁
    rw [show m + 1 + n = (m + n) + 1 by omega]
    exact ⟨hc, x, hx, ih hxd⟩

theorem ReachesSpace.mono {S S' n : ℕ} {c c' : Config Q Γ} (h : N.ReachesSpace S n c c')
    (hS : S ≤ S') : N.ReachesSpace S' n c c' := by
  induction n generalizing c with
  | zero => exact ⟨h.1, lt_of_lt_of_le h.2 hS⟩
  | succ n ih => obtain ⟨hc, d, hd, h'⟩ := h; exact ⟨lt_of_lt_of_le hc hS, d, hd, ih h'⟩

theorem ReachesSpace.refl {S : ℕ} {c : Config Q Γ} (h : c.head < S) : N.ReachesSpace S 0 c c :=
  ⟨rfl, h⟩

theorem ReachesSpace.single {S : ℕ} {c d : Config Q Γ} (hs : N.Step c d) (hc : c.head < S)
    (hd : d.head < S) : N.ReachesSpace S 1 c d := ⟨hc, d, hs, rfl, hd⟩

/-! ### Segments -/

/-- Every accepting run from `c` passes through `c'` after exactly `m` steps. -/
def Passes (c c' : Config Q Γ) (m : ℕ) : Prop :=
  ∀ n d, N.Reaches n c d → d.state ∈ N.accept → m ≤ n ∧ N.Reaches (n - m) c' d

/-- **A segment**: `c` reaches `c'` in `m` steps within the space `S`, and every accepting run
from `c` passes through `c'`. -/
structure Seg (S : ℕ) (c c' : Config Q Γ) (m : ℕ) : Prop where
  reach : N.ReachesSpace S m c c'
  passes : N.Passes c c' m

variable {N}

theorem Passes.refl (c : Config Q Γ) : N.Passes c c 0 := fun n _ h _ => ⟨Nat.zero_le _, by simpa using h⟩

theorem Passes.trans {c c' c'' : Config Q Γ} {m m' : ℕ} (h₁ : N.Passes c c' m)
    (h₂ : N.Passes c' c'' m') : N.Passes c c'' (m + m') := by
  intro n d hr hd
  obtain ⟨hm, hr'⟩ := h₁ n d hr hd
  obtain ⟨hm', hr''⟩ := h₂ _ d hr' hd
  exact ⟨by omega, by rw [show n - (m + m') = n - m - m' by omega]; exact hr''⟩

theorem Seg.refl {S : ℕ} {c : Config Q Γ} (h : c.head < S) : N.Seg S c c 0 :=
  ⟨ReachesSpace.refl N h, Passes.refl c⟩

theorem Seg.trans {S m m' : ℕ} {c c' c'' : Config Q Γ} (h₁ : N.Seg S c c' m)
    (h₂ : N.Seg S c' c'' m') : N.Seg S c c'' (m + m') :=
  ⟨h₁.reach.trans N h₂.reach, h₁.passes.trans h₂.passes⟩

theorem Seg.mono {S S' m : ℕ} {c c' : Config Q Γ} (h : N.Seg S c c' m) (hS : S ≤ S') :
    N.Seg S' c c' m := ⟨h.reach.mono N hS, h.passes⟩

theorem Seg.reaches {S m : ℕ} {c c' : Config Q Γ} (h : N.Seg S c c' m) : N.Reaches m c c' :=
  h.reach.reaches N

theorem Seg.of_eq {S m m' : ℕ} {c c' : Config Q Γ} (h : N.Seg S c c' m) (e : m = m') :
    N.Seg S c c' m' := e ▸ h

/-- **A single deterministic step** out of a non-accepting configuration is a segment. -/
theorem Seg.single {S : ℕ} {c c₁ : Config Q Γ} (hna : c.state ∉ N.accept)
    (hdet : ∀ d, N.Step c d ↔ d = c₁) (hc : c.head < S) (hc₁ : c₁.head < S) :
    N.Seg S c c₁ 1 := by
  refine ⟨ReachesSpace.single N ((hdet c₁).2 rfl) hc hc₁, fun n d hr hd => ?_⟩
  cases n with
  | zero => obtain rfl := hr; exact absurd hd hna
  | succ n =>
    obtain ⟨e, he, hr'⟩ := hr
    obtain rfl := (hdet e).1 he
    exact ⟨by omega, by simpa using hr'⟩

/-- An accepting run out of a non-accepting configuration starts with a step. -/
theorem exists_step_of_reaches {n : ℕ} {c d : Config Q Γ} (hr : N.Reaches n c d)
    (hd : d.state ∈ N.accept) (hna : c.state ∉ N.accept) :
    ∃ n' e, n = n' + 1 ∧ N.Step c e ∧ N.Reaches n' e d := by
  cases n with
  | zero => obtain rfl := hr; exact absurd hd hna
  | succ n => obtain ⟨e, he, hr'⟩ := hr; exact ⟨n, e, rfl, he, hr'⟩

/-! ### Restriction to a finite set of states -/

variable (N)

/-- The machine restricted to a set `R` of states that contains the initial state: its states
are the elements of `R`, and only transitions into `R` are kept. -/
def restrict (R : Set Q) (h₀ : N.init ∈ R) : NTM R Γ where
  step q γ := {t | t.1.val ∈ R ∧ (t.1.val, t.2.1, t.2.2) ∈ N.step q.val γ}
  init := ⟨N.init, h₀⟩
  accept := {q | q.val ∈ N.accept}
  blank := N.blank

/-- A configuration of the restricted machine, read in the original one. -/
def _root_.TM.Config.unrestrict {R : Set Q} (c : Config R Γ) : Config Q Γ := ⟨c.state.val, c.head, c.tape⟩

variable {N}

/-- If `R` is closed under the transitions, runs of the original machine from states of `R` are
runs of the restricted one. -/
theorem restrict_reaches {R : Set Q} (h₀ : N.init ∈ R)
    (hcl : ∀ q ∈ R, ∀ γ t, t ∈ N.step q γ → t.1 ∈ R) :
    ∀ {n : ℕ} {c : Config R Γ} {d : Config Q Γ}, N.Reaches n c.unrestrict d →
      ∃ hd : d.state ∈ R, (N.restrict R h₀).Reaches n c ⟨⟨d.state, hd⟩, d.head, d.tape⟩ := by
  intro n
  induction n with
  | zero =>
    intro c d h
    obtain rfl := h
    exact ⟨c.state.2, rfl⟩
  | succ n ih =>
    intro c d h
    obtain ⟨e, ⟨q', γ', m, ht, rfl⟩, hr⟩ := h
    have hq' : q' ∈ R := hcl _ c.state.2 _ (q', γ', m) ht
    obtain ⟨hd, hr'⟩ := ih (c := ⟨⟨q', hq'⟩, m.apply c.head,
      Function.update c.tape c.head γ'⟩) hr
    exact ⟨hd, _, ⟨⟨q', hq'⟩, γ', m, ⟨hq', ht⟩, rfl⟩, hr'⟩

/-- Runs of the restricted machine are runs of the original one. -/
theorem reaches_of_restrict {R : Set Q} {h₀ : N.init ∈ R} :
    ∀ {n : ℕ} {c d : Config R Γ}, (N.restrict R h₀).Reaches n c d →
      N.Reaches n c.unrestrict d.unrestrict := by
  intro n
  induction n with
  | zero => intro c d h; obtain rfl := h; rfl
  | succ n ih =>
    intro c d h
    obtain ⟨e, ⟨q', γ', m, ⟨-, ht⟩, rfl⟩, hr⟩ := h
    exact ⟨_, ⟨q'.val, γ', m, ht, rfl⟩, ih hr⟩

theorem restrict_reachesSpace {R : Set Q} (h₀ : N.init ∈ R)
    (hcl : ∀ q ∈ R, ∀ γ t, t ∈ N.step q γ → t.1 ∈ R) {S : ℕ} :
    ∀ {n : ℕ} {c : Config R Γ} {d : Config Q Γ}, N.ReachesSpace S n c.unrestrict d →
      ∃ hd : d.state ∈ R, (N.restrict R h₀).ReachesSpace S n c ⟨⟨d.state, hd⟩, d.head, d.tape⟩ := by
  intro n
  induction n with
  | zero =>
    intro c d h
    obtain ⟨rfl, hh⟩ := h
    exact ⟨c.state.2, rfl, hh⟩
  | succ n ih =>
    intro c d h
    obtain ⟨hh, e, ⟨q', γ', m, ht, rfl⟩, hr⟩ := h
    have hq' : q' ∈ R := hcl _ c.state.2 _ (q', γ', m) ht
    obtain ⟨hd, hr'⟩ := ih (c := ⟨⟨q', hq'⟩, m.apply c.head,
      Function.update c.tape c.head γ'⟩) hr
    exact ⟨hd, hh, _, ⟨⟨q', hq'⟩, γ', m, ⟨hq', ht⟩, rfl⟩, hr'⟩

theorem reachesSpace_of_restrict {R : Set Q} {h₀ : N.init ∈ R} {S : ℕ} :
    ∀ {n : ℕ} {c d : Config R Γ}, (N.restrict R h₀).ReachesSpace S n c d →
      N.ReachesSpace S n c.unrestrict d.unrestrict := by
  intro n
  induction n with
  | zero => intro c d h; obtain ⟨rfl, hh⟩ := h; exact ⟨rfl, hh⟩
  | succ n ih =>
    intro c d h
    obtain ⟨hh, e, ⟨q', γ', m, ⟨-, ht⟩, rfl⟩, hr⟩ := h
    exact ⟨hh, _, ⟨q'.val, γ', m, ht, rfl⟩, ih hr⟩

end NTM

end TM
