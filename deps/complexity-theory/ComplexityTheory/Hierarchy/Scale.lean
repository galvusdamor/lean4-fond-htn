import Mathlib.Tactic
import ComplexityTheory.Complexity.Basic
/-!
# Quantifier hierarchies over an abstract resource scale

This file is the first of three (`Scale.lean`, `Transfer.lean`, `KarpLipton.lean`) that answer a
structural question about the complexity hypotheses of Table 3 of the compilability development:

> `NEXPTIME ⊆ EXPTIME/poly` looks like the Karp–Lipton hypothesis `NP ⊆ P/poly` lifted one
> exponential.  Does the Karp–Lipton collapse lift with it, to the exponential hierarchy?

Answering that formally needs the *shape* of both hierarchies, not their content: both the
polynomial hierarchy and the exponential hierarchy are "a prefix of bounded quantifiers in front
of a predicate of a deterministic base class", and they differ only in

* which predicates are in the base class (`P` versus `EXPTIME`), and
* which strings may be quantified over (polynomially long versus exponentially long ones).

A `HTN.Hier.Scale` packages exactly those two parameters, plus the admissible *advice* strings,
and the hierarchy is defined once, over an arbitrary scale.  `Transfer.lean` then links two
scales by padding — which is what "one exponential up" means — and `KarpLipton.lean` isolates the
one ingredient of the Karp–Lipton argument that the padding does **not** carry upwards.

Nothing here is specific to `P`/`EXPTIME`: the scale is abstract, so the theorems are statements
about quantifier prefixes, and the complexity-theoretic content sits in the hypotheses.  See
`Example.lean` for a check that the structures are inhabited, so that the theorems are not
vacuous.

## Main definitions

* `HTN.Hier.Scale` — a base class of relations, the admissible quantified strings and the
  admissible advice strings, both as a function of the input length;
* `HTN.Hier.qpre` — the alternating bounded-quantifier prefix of a given length;
* `HTN.Hier.SigmaLevel s k`, `HTN.Hier.PiLevel s k` — the levels of the hierarchy of the scale;
* `HTN.Hier.InAdvice s` — the scale's advice class (`P/poly` at the polynomial scale);
* `HTN.Hier.CollapseStep`, `HTN.Hier.CollapseAt` — "the hierarchy collapses to level `k`".
-/

namespace HTN

namespace Hier

/-- A relation between an input word and a list of quantified strings.  The base class of a
scale consists of such relations, so that a quantifier prefix of any length can be put in front
of one member of the class. -/
abbrev Rel := Word → List Word → Prop

/-- **A resource scale.**

* `base` is the deterministic class the quantifier prefix sits in front of (`P` for the
  polynomial hierarchy, `EXPTIME` for the exponential one);
* `Q n y` says that the string `y` is short enough to be quantified over at input length `n`
  (polynomially long, resp. exponentially long);
* `A n c` says that `c` is admissible as an advice string at input length `n`.

Both `Q` and `A` are required to contain the empty string; no other closure property is assumed
here, the ones a particular theorem needs are hypotheses of that theorem. -/
structure Scale where
  /-- The deterministic base class of the scale. -/
  base : Rel → Prop
  /-- The strings that may be quantified over, as a function of the input length. -/
  Q : ℕ → Word → Prop
  /-- The strings admissible as advice, as a function of the input length. -/
  A : ℕ → Word → Prop
  /-- The empty string may always be quantified over. -/
  Q_nil : ∀ n, Q n []
  /-- The empty string is always admissible as advice. -/
  A_nil : ∀ n, A n []

/-- **The alternating bounded-quantifier prefix.**  `qpre s R k b x ys` puts `k` quantifiers,
alternating and starting with `∃` when `b = true`, in front of `R x`.  The strings already
quantified are accumulated in `ys`, most recent first, and handed to `R` in the order they were
introduced. -/
def qpre (s : Scale) (R : Rel) : ℕ → Bool → Word → List Word → Prop
  | 0, _, x, ys => R x ys.reverse
  | (k + 1), true, x, ys => ∃ y, s.Q x.length y ∧ qpre s R k false x (y :: ys)
  | (k + 1), false, x, ys => ∀ y, s.Q x.length y → qpre s R k true x (y :: ys)

@[simp] theorem qpre_zero (s : Scale) (R : Rel) (b : Bool) (x : Word) (ys : List Word) :
    qpre s R 0 b x ys = R x ys.reverse := rfl

@[simp] theorem qpre_succ_true (s : Scale) (R : Rel) (k : ℕ) (x : Word) (ys : List Word) :
    qpre s R (k + 1) true x ys = ∃ y, s.Q x.length y ∧ qpre s R k false x (y :: ys) := rfl

@[simp] theorem qpre_succ_false (s : Scale) (R : Rel) (k : ℕ) (x : Word) (ys : List Word) :
    qpre s R (k + 1) false x ys = ∀ y, s.Q x.length y → qpre s R k true x (y :: ys) := rfl

/-- The quantifier prefix depends on the scale only through its quantifier budget. -/
theorem qpre_congr_scale {s₁ s₂ : Scale} (hQ : ∀ n y, s₁.Q n y ↔ s₂.Q n y) (R : Rel) (x : Word) :
    ∀ (k : ℕ) (b : Bool) (ys : List Word), qpre s₁ R k b x ys ↔ qpre s₂ R k b x ys := by
  intro k
  induction k with
  | zero => intro b ys; exact Iff.rfl
  | succ k ih =>
      intro b ys
      cases b with
      | false =>
          simp only [qpre_succ_false]
          exact forall_congr' fun y =>
            imp_congr (hQ x.length y) (ih true (y :: ys))
      | true =>
          simp only [qpre_succ_true]
          exact exists_congr fun y => and_congr (hQ x.length y) (ih false (y :: ys))

/-- **Level `k` of the existential side of the hierarchy of the scale `s`**: `Σ_k^P` when the
scale is the polynomial one, `Σ_k^EXP` when it is the exponential one. -/
def SigmaLevel (s : Scale) (k : ℕ) (L : Lang) : Prop :=
  ∃ R, s.base R ∧ ∀ x, L x ↔ qpre s R k true x []

/-- **Level `k` of the universal side**: the complements of the languages of `SigmaLevel s k`. -/
def PiLevel (s : Scale) (k : ℕ) (L : Lang) : Prop :=
  SigmaLevel s k (fun x => ¬ L x)

/-- The levels of the hierarchy depend on the scale only through its base class and its
quantifier budget — not through its advice budget. -/
theorem sigmaLevel_congr_scale {s₁ s₂ : Scale} (hbase : ∀ R, s₁.base R ↔ s₂.base R)
    (hQ : ∀ n y, s₁.Q n y ↔ s₂.Q n y) (k : ℕ) (L : Lang) :
    SigmaLevel s₁ k L ↔ SigmaLevel s₂ k L := by
  constructor <;> rintro ⟨R, hR, hL⟩
  · exact ⟨R, (hbase R).1 hR, fun x => (hL x).trans (qpre_congr_scale hQ R x k true [])⟩
  · exact ⟨R, (hbase R).2 hR,
      fun x => (hL x).trans (qpre_congr_scale (fun n y => (hQ n y).symm) R x k true [])⟩

/-- Level `0` of either side is the base class of the scale. -/
theorem sigmaLevel_zero (s : Scale) (L : Lang) :
    SigmaLevel s 0 L ↔ ∃ R, s.base R ∧ ∀ x, L x ↔ R x [] := by
  simp [SigmaLevel]

/-- The membership condition of level `1`: one existential quantifier over an admissible
string. -/
theorem sigmaLevel_one (s : Scale) (L : Lang) :
    SigmaLevel s 1 L ↔ ∃ R, s.base R ∧ ∀ x, L x ↔ ∃ y, s.Q x.length y ∧ R x [y] := by
  simp [SigmaLevel]

/-- The membership condition of level `2`: `∃ ∀` over admissible strings. -/
theorem sigmaLevel_two (s : Scale) (L : Lang) :
    SigmaLevel s 2 L ↔ ∃ R, s.base R ∧
      ∀ x, L x ↔ ∃ y, s.Q x.length y ∧ ∀ z, s.Q x.length z → R x [y, z] := by
  simp [SigmaLevel]

/-- The membership condition of `Π₂`: `∀ ∃` over admissible strings. -/
theorem piLevel_two (s : Scale) (L : Lang) :
    PiLevel s 2 L ↔ ∃ R, s.base R ∧
      ∀ x, ¬ L x ↔ ∃ y, s.Q x.length y ∧ ∀ z, s.Q x.length z → R x [y, z] := by
  simp [PiLevel, SigmaLevel]

/-- **The advice class of the scale**: a language decided by a base-class relation from the input
together with one admissible advice string depending only on the input length.  At the polynomial
scale this is `P/poly`; at the exponential scale, with exponentially long advice admissible, it
is `EXPTIME/2^poly`. -/
def InAdvice (s : Scale) (L : Lang) : Prop :=
  ∃ a : ℕ → Word, (∀ n, s.A n (a n)) ∧ ∃ R, s.base R ∧ ∀ x, L x ↔ R x [a x.length]

/-- **The hierarchy of the scale collapses to level `k`, one step**: everything at level `k + 1`
is already at level `k`. -/
def CollapseStep (s : Scale) (k : ℕ) : Prop :=
  ∀ L, SigmaLevel s (k + 1) L → SigmaLevel s k L

/-- **The hierarchy of the scale collapses to level `k`**: every level is already at level `k`.
This is the conclusion of the Karp–Lipton theorem, for `k = 2`, at the polynomial scale. -/
def CollapseAt (s : Scale) (k : ℕ) : Prop :=
  ∀ j L, SigmaLevel s j L → SigmaLevel s k L

theorem CollapseAt.step {s : Scale} {k : ℕ} (h : CollapseAt s k) : CollapseStep s k :=
  fun L hL => h (k + 1) L hL

end Hier

end HTN
