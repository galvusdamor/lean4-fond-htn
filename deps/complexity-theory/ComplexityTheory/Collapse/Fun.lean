import ComplexityTheory.Complexity.CobhamString
import ComplexityTheory.Complexity.Basic
/-!
# Polynomial *space* as a concrete class of bit-string functions

The development formalises polynomial time as Cobham's class
(`ComplexityTheory/Complexity/Cobham.lean`) and nondeterministic polynomial space as a machine
model (`ComplexityTheory/Space/Model.lean`).  The complexity-theoretic arguments behind the
Karp–Lipton cells of Table 3 — "an inclusion with polynomial advice collapses two classes" —
need a *deterministic* polynomial-space class in which one can **program**: brute-force a
polynomially long advice string, loop over exponentially many objects, and negate a computed
answer.  A nondeterministic machine cannot do the last of these, which is why
`HTN.Space.InNSpace` is not the right home for the argument.

This file adds that class, in the same machine-independent style as Cobham's:

> **`HTN.PSpace.PSpaceF`** is the smallest class of functions on bit strings which contains
> Cobham's class and is closed under composition and under **bounded exponential iteration**:
> from a function `F` of the class one may form
>
>     (s, st, rest…)  ↦  F^{val s} (st, rest…)
>
> — the state `st` updated `val s` times, `val s` being the binary value of `s`, hence
> exponentially many times in `|s|` — provided the result is, at every argument, no longer than
> a function of the class already available.

The reading is the usual one: a polynomial-space computation is an update of a state of
polynomial size, iterated for exponentially many steps; the side condition is exactly "the state
stays polynomially bounded".  As with Cobham's class, the identification of the class with
`FPSPACE` is a classical theorem which is *not* formalised here.  What is proved here is the
sanity check that the class deserves the name:

* `HTN.PSpace.PSpaceF.poly_length` — every function of the class has output length bounded by a
  fixed polynomial in the length of its longest argument;
* `HTN.PSpace.PSpaceF.cobham` — polynomial time is polynomial space.

The predicate form is `HTN.PSpace.PSpaceB`, and `HTN.PSpace.InPSpace` /
`HTN.PSpace.InPSpacePoly` are the language classes `PSPACE` and `PSPACE/poly`.
-/

namespace HTN

namespace PSpace

open PTime

/-! ### Reading a bit string as a binary numeral -/

@[simp] theorem val_nil : val [] = 0 := rfl

@[simp] theorem val_cons (b : Bool) (x : List Bool) :
    val (b :: x) = (if b then 1 else 0) + 2 * val x := rfl

@[simp] theorem val_cons_false (x : List Bool) : val (false :: x) = 2 * val x := by
  simp [val]

@[simp] theorem val_cons_true (x : List Bool) : val (true :: x) = 1 + 2 * val x := by
  simp [val]

theorem val_lt_two_pow : ∀ x : List Bool, val x < 2 ^ x.length
  | [] => by simp
  | b :: x => by
    have h := val_lt_two_pow x
    have hp : (2:ℕ) ^ (x.length + 1) = 2 ^ x.length + 2 ^ x.length := by ring
    rcases b with _ | _
    · rw [List.length_cons, val_cons_false]; omega
    · rw [List.length_cons, val_cons_true]; omega

/-- Every number below `2 ^ k` is the value of a bit string of length `k`. -/
theorem exists_val_eq : ∀ (k n : ℕ), n < 2 ^ k → ∃ s : List Bool, s.length = k ∧ val s = n
  | 0, n, h => ⟨[], rfl, by simpa using (Nat.lt_one_iff.1 (by simpa using h)).symm⟩
  | k + 1, n, h => by
    have h2 : n / 2 < 2 ^ k := by
      have : n < 2 ^ k * 2 := by simpa [pow_succ] using h
      omega
    obtain ⟨s, hs, hv⟩ := exists_val_eq k (n / 2) h2
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · exact ⟨false :: s, by simp [hs], by rw [val_cons_false, hv]; omega⟩
    · exact ⟨true :: s, by simp [hs], by rw [val_cons_true, hv]; omega⟩

/-! ### The iteration scheme -/

@[simp] theorem loopAux_zero (F : Fn) (rest : Args) (st : List Bool) :
    loopAux F rest 0 st = st := rfl

@[simp] theorem loopAux_succ (F : Fn) (rest : Args) (n : ℕ) (st : List Bool) :
    loopAux F rest (n + 1) st = F (loopAux F rest n st :: rest) := rfl

@[simp] theorem loopFn_apply (F : Fn) (s st : List Bool) (rest : Args) :
    loopFn F (s :: st :: rest) = loopAux F rest (val s) st := rfl

/-! ### The class -/

theorem PSpaceF.of_eq {f g : Fn} (hf : PSpaceF f) (h : ∀ args, f args = g args) : PSpaceF g := by
  have : f = g := funext h
  exact this ▸ hf

/-! ### Composition helpers -/

theorem psC1 {g f : Fn} (hg : PSpaceF g) (hf : PSpaceF f) : PSpaceF (compFn g [f]) :=
  PSpaceF.comp hg (by intro h hh; rw [List.mem_singleton.1 hh]; exact hf)

theorem psC2 {g f₁ f₂ : Fn} (hg : PSpaceF g) (h₁ : PSpaceF f₁) (h₂ : PSpaceF f₂) :
    PSpaceF (compFn g [f₁, f₂]) := by
  refine PSpaceF.comp hg ?_
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact h₁
  · exact h₂

theorem psC3 {g f₁ f₂ f₃ : Fn} (hg : PSpaceF g) (h₁ : PSpaceF f₁) (h₂ : PSpaceF f₂)
    (h₃ : PSpaceF f₃) : PSpaceF (compFn g [f₁, f₂, f₃]) := by
  refine PSpaceF.comp hg ?_
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃

theorem psC4 {g f₁ f₂ f₃ f₄ : Fn} (hg : PSpaceF g) (h₁ : PSpaceF f₁) (h₂ : PSpaceF f₂)
    (h₃ : PSpaceF f₃) (h₄ : PSpaceF f₄) : PSpaceF (compFn g [f₁, f₂, f₃, f₄]) := by
  refine PSpaceF.comp hg ?_
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

theorem psProj (n : ℕ) : PSpaceF (proj n) := PSpaceF.cobham (Cobham.proj n)

/-! ### Every function of the class is polynomially bounded -/

/-- **Every function of the class has a polynomial length bound.** -/
theorem PSpaceF.poly_length {f : Fn} (hf : PSpaceF f) :
    ∃ p : Polynomial ℕ, ∀ args, (f args).length ≤ p.eval (argSize args) := by
  induction hf with
  | cobham h => exact h.poly_length
  | @comp g hs _ _ ihg ihhs =>
    obtain ⟨pg, hpg⟩ := ihg
    obtain ⟨q, hq⟩ := exists_common_bound ihhs
    refine ⟨pg.comp q, fun args => ?_⟩
    have hsize : argSize (hs.map fun h => h args) ≤ q.eval (argSize args) :=
      argSize_map_le hq args
    calc (compFn g hs args).length ≤ pg.eval (argSize (hs.map fun h => h args)) := hpg _
      _ ≤ pg.eval (q.eval (argSize args)) := Polynomial.eval_mono_nat pg hsize
      _ = (pg.comp q).eval (argSize args) := by simp
  | @loop F bd _ _ hbound _ ihbd =>
    obtain ⟨p, hp⟩ := ihbd
    exact ⟨p, fun args => (hbound args).trans (hp args)⟩

/-! ### Predicates -/

theorem PSpaceB.of_cobhamB {p : Args → Bool} (h : CobhamB p) : PSpaceB p := PSpaceF.cobham h

theorem PSpaceB.of_eq {p q : Args → Bool} (hp : PSpaceB p) (h : ∀ args, q args = p args) :
    PSpaceB q := PSpaceF.of_eq hp fun args => by rw [h]

/-! ### The language classes -/

/-- **`PSPACE/poly`**: the same, with an advice string of polynomial length depending on the
length of the input only. -/
def InPSpacePoly (L : List Bool → Prop) : Prop :=
  ∃ (p : Args → Bool) (adv : ℕ → List Bool) (r : Polynomial ℕ),
    PSpaceB p ∧ (∀ n, (adv n).length ≤ r.eval n) ∧ ∀ x, L x ↔ p [x, adv x.length] = true

/-- No advice is advice. -/
theorem InPSpace.inPSpacePoly {L : List Bool → Prop} (h : InPSpace L) : InPSpacePoly L := by
  obtain ⟨p, hp, hL⟩ := h
  refine ⟨fun args => p [args.getD 0 []], fun _ => [], 0, ?_, fun _ => by simp, fun x => hL x⟩
  exact PSpaceF.of_eq (psC1 hp (psProj 0)) fun args => by simp [compFn, proj]

end PSpace

end HTN
