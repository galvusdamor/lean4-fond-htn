import ComplexityTheory.Complexity.CobhamString
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Nondeterministic polynomial space, as a machine model of this development

The eight Karp–Lipton cells of Table 3 (see `TABLE3-PLAN.md`) need, besides a hardness family in
the source class and the generic bridge "compilation + hardness family ⟹ polynomial advice", an
**upper bound for the target class**: plan existence for the target is decidable in polynomial
space.  This development formalised polynomial *time* only (Cobham's class,
`ComplexityTheory/Complexity/Cobham.lean`); this file adds the space-bounded model the target
side needs.

## The model

A machine is a **transition system on bit strings**:

* configurations are bit strings, and the machine may only visit configurations whose length is
  bounded by a fixed polynomial in the length of its input and of its advice;
* the initial-configuration test, the transition relation and the acceptance test are
  **predicates of Cobham's class** (`HTN.PTime.CobhamB`), that is, they are decidable in
  polynomial time in the length of their arguments.

Both restrictions are essential.  Dropping the length bound gives unbounded computation;
dropping "polynomial time" on the three tests gives a degenerate class — a single step could
then decide anything computable about the input, since the input is one of the arguments of the
tests.  With both in place the model is the usual `NPSPACE`: a polynomial-time checkable
transition relation over configurations of polynomial size.

A machine reads two strings, its **input** and its **advice**.  Keeping them apart avoids having
to write a pairing function inside Cobham's class; `HTN.Space.InNSpace` uses the empty advice and
`HTN.Space.InNSpacePoly` — the class `NPSPACE/poly` — allows advice of polynomial length
depending on the length of the input only.

## What is proved here

* `HTN.Space.NSpace.pre` — the input of a machine may be pre-processed by any function of
  Cobham's class, and `HTN.Space.NSpace.accepts_pre` says the pre-processed machine accepts `x`
  exactly when the original one accepts the processed input.  This is the closure property the
  bridge of `HtnComplexity/Space/Bridge.lean` runs on;
* `HTN.Space.inNSpacePoly_of_precomp` — its packaged form: if a polynomial-time map `F` turns a
  word into the input of a fixed machine, with advice depending on the length of the word only,
  then the language is in `NPSPACE/poly`;
* `HTN.Space.InNSpace.inNSpacePoly` — no advice is advice.

Nondeterminism is built in (the transition is a relation), so the class is `NPSPACE`, not
`PSPACE`.  By Savitch's theorem the two coincide; Savitch is *not* formalised here, so a
hypothesis "`L ∉ PSPACE/poly`" of the literature corresponds to the hypothesis
`¬ InNSpacePoly L` used in this development only through that classical theorem.
-/

namespace HTN

namespace Space

open PTime

/-- **A nondeterministic polynomial-space machine.**  Configurations are bit strings; the three
tests read a configuration (or two), the input `x` and the advice `a`, are predicates of
Cobham's class, and every configuration the machine can be in is polynomially bounded in
`|x| + |a|`. -/
structure NSpace where
  /-- `initB [c, x, a]`: `c` is an initial configuration on input `x` with advice `a`. -/
  initB : Args → Bool
  /-- `stepB [c', c, x, a]`: the machine may pass from `c` to `c'`. -/
  stepB : Args → Bool
  /-- `accB [c, x, a]`: `c` is accepting. -/
  accB : Args → Bool
  /-- The initial test is polynomial time. -/
  cobham_initB : CobhamB initB
  /-- The transition relation is polynomial time. -/
  cobham_stepB : CobhamB stepB
  /-- The acceptance test is polynomial time. -/
  cobham_accB : CobhamB accB
  /-- The space bound. -/
  bound : Polynomial ℕ
  /-- An initial configuration is polynomially bounded. -/
  initB_length : ∀ c x a, initB [c, x, a] = true → c.length ≤ bound.eval (x.length + a.length)
  /-- A configuration the machine steps into is polynomially bounded. -/
  stepB_length : ∀ c' c x a,
    stepB [c', c, x, a] = true → c'.length ≤ bound.eval (x.length + a.length)

namespace NSpace

variable (M : NSpace)

/-- One transition of the machine. -/
def Step (x a c c' : List Bool) : Prop := M.stepB [c', c, x, a] = true

/-- Reachability: a run of the machine. -/
def Reach (x a : List Bool) : List Bool → List Bool → Prop :=
  Relation.ReflTransGen (M.Step x a)

/-- **The machine accepts**: some run from an initial configuration reaches an accepting one. -/
def Accepts (x a : List Bool) : Prop :=
  ∃ c₀ c, M.initB [c₀, x, a] = true ∧ M.Reach x a c₀ c ∧ M.accB [c, x, a] = true

/-- Every configuration a run visits is polynomially bounded. -/
theorem length_le_of_reach {x a c₀ c : List Bool} (h₀ : M.initB [c₀, x, a] = true)
    (h : M.Reach x a c₀ c) : c.length ≤ M.bound.eval (x.length + a.length) := by
  induction h with
  | refl => exact M.initB_length _ _ _ h₀
  | tail _ hstep _ => exact M.stepB_length _ _ _ _ hstep

end NSpace

/-- **`NPSPACE`**: the languages a machine of the model accepts, with no advice. -/
def InNSpace (L : List Bool → Prop) : Prop := ∃ M : NSpace, ∀ x, L x ↔ M.Accepts x []

/-- **`NPSPACE/poly`**: the languages a machine of the model accepts with an advice string of
polynomial length depending on the length of the input only. -/
def InNSpacePoly (L : List Bool → Prop) : Prop :=
  ∃ (M : NSpace) (adv : ℕ → List Bool) (r : Polynomial ℕ),
    (∀ n, (adv n).length ≤ r.eval n) ∧ ∀ x, L x ↔ M.Accepts x (adv x.length)

/-- No advice is advice. -/
theorem InNSpace.inNSpacePoly {L : List Bool → Prop} (h : InNSpace L) : InNSpacePoly L := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun _ => [], 0, fun _ => by simp, fun x => hM x⟩

/-! ### Pre-processing the input -/

namespace NSpace

/-- Substituting a computed string for the input argument of a ternary test. -/
def preTest3 (p : Args → Bool) (f : Fn) : Args → Bool :=
  fun args => p [args.getD 0 [], f [args.getD 1 []], args.getD 2 []]

/-- Substituting a computed string for the input argument of a quaternary test. -/
def preTest4 (p : Args → Bool) (f : Fn) : Args → Bool :=
  fun args => p [args.getD 0 [], args.getD 1 [], f [args.getD 2 []], args.getD 3 []]

theorem cobhamB_preTest3 {p : Args → Bool} (hp : CobhamB p) {f : Fn} (hf : Cobham f) :
    CobhamB (preTest3 p f) :=
  (hp.comp3 (Cobham.proj 0) (cobham_c1 hf (Cobham.proj 1)) (Cobham.proj 2)).of_eq fun args => by
    simp [preTest3, compFn, proj]

theorem cobhamB_preTest4 {p : Args → Bool} (hp : CobhamB p) {f : Fn} (hf : Cobham f) :
    CobhamB (preTest4 p f) :=
  (hp.comp4 (Cobham.proj 0) (Cobham.proj 1) (cobham_c1 hf (Cobham.proj 2))
    (Cobham.proj 3)).of_eq fun args => by
    simp [preTest4, compFn, proj]

variable (M : NSpace) (f : Fn) (p : Polynomial ℕ)

/-- **The input of a machine may be pre-processed by a function of Cobham's class**, provided a
polynomial bound on the length of its value is available (which every function of the class
has, `HTN.PTime.Cobham.poly_length`). -/
noncomputable def pre (hf : Cobham f)
    (hp : ∀ y : List Bool, (f [y]).length ≤ p.eval y.length) : NSpace where
  initB := preTest3 M.initB f
  stepB := preTest4 M.stepB f
  accB := preTest3 M.accB f
  cobham_initB := cobhamB_preTest3 M.cobham_initB hf
  cobham_stepB := cobhamB_preTest4 M.cobham_stepB hf
  cobham_accB := cobhamB_preTest3 M.cobham_accB hf
  bound := M.bound.comp (p + Polynomial.X)
  initB_length := by
    intro c x a h
    have h' := M.initB_length c (f [x]) a h
    refine h'.trans ?_
    have : (f [x]).length + a.length ≤ (p + Polynomial.X).eval (x.length + a.length) := by
      have h1 : (f [x]).length ≤ p.eval (x.length + a.length) :=
        (hp x).trans (Polynomial.eval_mono_nat p (Nat.le_add_right _ _))
      have h2 : a.length ≤ x.length + a.length := Nat.le_add_left _ _
      simpa using Nat.add_le_add h1 h2
    simpa using Polynomial.eval_mono_nat M.bound this
  stepB_length := by
    intro c' c x a h
    have h' := M.stepB_length c' c (f [x]) a h
    refine h'.trans ?_
    have : (f [x]).length + a.length ≤ (p + Polynomial.X).eval (x.length + a.length) := by
      have h1 : (f [x]).length ≤ p.eval (x.length + a.length) :=
        (hp x).trans (Polynomial.eval_mono_nat p (Nat.le_add_right _ _))
      have h2 : a.length ≤ x.length + a.length := Nat.le_add_left _ _
      simpa using Nat.add_le_add h1 h2
    simpa using Polynomial.eval_mono_nat M.bound this

variable {M f p}

@[simp] theorem pre_step (hf : Cobham f) (hp : ∀ y : List Bool, (f [y]).length ≤ p.eval y.length)
    (x a c c' : List Bool) : (M.pre f p hf hp).Step x a c c' ↔ M.Step (f [x]) a c c' := Iff.rfl

theorem pre_reach (hf : Cobham f) (hp : ∀ y : List Bool, (f [y]).length ≤ p.eval y.length)
    (x a c c' : List Bool) : (M.pre f p hf hp).Reach x a c c' ↔ M.Reach (f [x]) a c c' := Iff.rfl

/-- **The pre-processed machine accepts `x` exactly when the original one accepts `f [x]`.** -/
theorem accepts_pre (hf : Cobham f) (hp : ∀ y : List Bool, (f [y]).length ≤ p.eval y.length)
    (x a : List Bool) : (M.pre f p hf hp).Accepts x a ↔ M.Accepts (f [x]) a := Iff.rfl

end NSpace

/-- **A machine reached through a polynomial-time pre-processing of the word, with advice
depending on the length of the word only, puts the language into `NPSPACE/poly`.** -/
theorem inNSpacePoly_of_precomp {L : List Bool → Prop} (M : NSpace)
    {F : List Bool → List Bool} (hF : PolyTimeFun F) (adv : ℕ → List Bool) (r : Polynomial ℕ)
    (hadv : ∀ n, (adv n).length ≤ r.eval n)
    (h : ∀ w, L w ↔ M.Accepts (F w) (adv w.length)) : InNSpacePoly L := by
  obtain ⟨f, hf, hFf⟩ := hF.cobham
  obtain ⟨p, hp⟩ := hf.poly_length
  have hp' : ∀ y : List Bool, (f [y]).length ≤ p.eval y.length := by
    intro y
    simpa [argSize_cons] using hp [y]
  refine ⟨M.pre f p hf hp', adv, r, hadv, fun w => ?_⟩
  rw [NSpace.accepts_pre, ← hFf w]
  exact h w

end Space

end HTN
