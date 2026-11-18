import ComplexityTheory.Hierarchy.Collapse
/-!
# The hypotheses of the collapse theorem are satisfiable

`Collapse.lean` proves the Karp–Lipton collapse of the hierarchy of a scale from three bundles:
`HTN.Hier.SearchClosure` (the base class can run the self-reduction), `HTN.Hier.Closure` (the base
class is closed under complement, padding and unpairing, and the quantifier budget has a pairing)
and the advice hypothesis `HTN.Hier.DecisionAdviceP`.  A theorem with unsatisfiable hypotheses
proves nothing, and two of the fields pull in opposite directions — the budget must be closed
under pairing, which no *fixed* length bound is, while the self-reduction must terminate, which
needs a bound.  This file checks that they can be met together.

The scale `HTN.Hier.exampleScale` has the exponentially shaped quantifier budget of the weak
exponential hierarchy — the union `⋃_k {w : |w| ≤ 2 ^ (n + k)}` of all exponential bounds, which
is what makes it closed under pairing — and a degenerate base class (every relation), so that the
closure fields and the advice hypothesis hold.  The witness bound of a relation is a bound for
*that* relation, obtained per input and per parameter list, which is exactly the shape
`HTN.Hier.SearchClosure.bnd` allows.

`HTN.Hier.exampleCollapseAt` is then the conclusion of the main theorem at that scale.  Its
content is not complexity-theoretic — the example's base class decides everything — it is the
guarantee that `HTN.Hier.collapseAt_two_of_decisionAdvice` is not vacuous.

The pairing is the usual one: the first component with its bits doubled, a separator `10`, then
the second component.
-/

namespace HTN

namespace Hier

/-! ### A pairing of words -/

/-- Each bit of the word, doubled. -/
def dbl : Word → Word
  | [] => []
  | b :: t => b :: b :: dbl t

/-- The pairing: the doubled first component, the separator `10`, the second component. -/
def pairW (u v : Word) : Word := dbl u ++ true :: false :: v

/-- The decoding of a pairing. -/
def unpairW : Word → Word × Word
  | true :: false :: rest => ([], rest)
  | a :: _ :: rest => (a :: (unpairW rest).1, (unpairW rest).2)
  | _ => ([], [])

theorem dbl_length (u : Word) : (dbl u).length = 2 * u.length := by
  induction u with
  | nil => simp [dbl]
  | cons b t ih =>
      simp only [dbl, List.length_cons, ih]
      omega

theorem pairW_cons (b : Bool) (t v : Word) : pairW (b :: t) v = b :: b :: pairW t v := by
  simp [pairW, dbl]

theorem unpairW_pairW (u v : Word) : unpairW (pairW u v) = (u, v) := by
  induction u with
  | nil => rfl
  | cons b t ih =>
      rw [pairW_cons]
      cases b <;> simp [unpairW, ih]

theorem unpairW_length (t : Word) :
    (unpairW t).1.length ≤ t.length ∧ (unpairW t).2.length ≤ t.length := by
  induction t using unpairW.induct with
  | case1 rest =>
      refine ⟨by simp [unpairW], ?_⟩
      simp only [unpairW, List.length_cons]
      omega
  | case2 a b rest _ ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · simp only [unpairW, List.length_cons]
        omega
      · simp only [unpairW, List.length_cons]
        omega
  | case3 t _ _ => simp [unpairW]

/-! ### The example scale -/

/-- The quantifier budget of the weak exponential hierarchy: every word of length at most
`2 ^ (n + k)` for some `k`, that is, the union of all exponential bounds.  Unlike a single
exponential bound it is closed under pairing. -/
def expBudget (n : ℕ) (w : Word) : Prop := ∃ k, w.length ≤ 2 ^ (n + k)

theorem expBudget_nil (n : ℕ) : expBudget n [] := ⟨0, by simp⟩

theorem expBudget_of_le {n m : ℕ} {w : Word} (h : w.length ≤ m) : expBudget n w :=
  ⟨m, le_trans h (le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (Nat.pow_le_pow_right (by norm_num)
    (Nat.le_add_left m n)))⟩

theorem expBudget_mono {n : ℕ} {w w' : Word} (h : w'.length ≤ w.length) (hw : expBudget n w) :
    expBudget n w' := by
  obtain ⟨k, hk⟩ := hw
  exact ⟨k, le_trans h hk⟩

theorem expBudget_pairW {n : ℕ} {u v : Word} (hu : expBudget n u) (hv : expBudget n v) :
    expBudget n (pairW u v) := by
  obtain ⟨k₁, h₁⟩ := hu
  obtain ⟨k₂, h₂⟩ := hv
  have hdbl : (dbl u).length = 2 * u.length := dbl_length u
  refine ⟨max k₁ k₂ + 3, ?_⟩
  have h₁' : u.length ≤ 2 ^ (n + max k₁ k₂) :=
    le_trans h₁ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h₂' : v.length ≤ 2 ^ (n + max k₁ k₂) :=
    le_trans h₂ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hpos : 1 ≤ 2 ^ (n + max k₁ k₂) := Nat.one_le_two_pow
  have hsplit : (2 : ℕ) ^ (n + (max k₁ k₂ + 3)) = 8 * 2 ^ (n + max k₁ k₂) := by
    rw [show n + (max k₁ k₂ + 3) = (n + max k₁ k₂) + 3 by omega, pow_add]
    norm_num [mul_comm]
  simp only [pairW, List.length_append, List.length_cons, hdbl, hsplit]
  omega

/-- **The example scale**: the exponentially shaped quantifier budget, the empty advice budget,
and every relation in the base class. -/
def exampleScale : Scale where
  base := fun _ => True
  Q := expBudget
  A := fun _ c => c = []
  Q_nil := expBudget_nil
  A_nil := fun _ => rfl

open Classical in
/-- The witness bound of a relation at an input and a parameter list: the length of some witness,
when there is one. -/
noncomputable def exampleBnd (R : Rel) (x : Word) (ws : List Word) : ℕ :=
  if h : ∃ z, R x (ws ++ [z]) then h.choose.length else 0

/-- The structural hypotheses of the self-reduction hold at the example scale. -/
noncomputable def exampleSearchClosure : SearchClosure exampleScale where
  bnd := exampleBnd
  Q_of_le := fun _ _ _ _ h => expBudget_of_le h
  witness_short := by
    rintro R - x ws ⟨z, -, hz⟩
    have h : ∃ z, R x (ws ++ [z]) := ⟨z, hz⟩
    refine ⟨h.choose, ?_, h.choose_spec⟩
    simp [exampleBnd, dif_pos h]
  A_Q := by
    rintro n c rfl
    exact expBudget_nil n
  base_prefRel := fun _ _ => trivial
  base_greedy := fun _ _ _ _ => trivial

/-- The closure hypotheses of the collapse induction hold at the example scale. -/
def exampleClosure : Closure exampleScale where
  compl := fun _ _ => trivial
  dropLast := fun _ _ => trivial
  pair := pairW
  fst := fun t => (unpairW t).1
  snd := fun t => (unpairW t).2
  fst_pair := fun u v => by rw [unpairW_pairW]
  snd_pair := fun u v => by rw [unpairW_pairW]
  Q_pair := fun _ _ _ hu hv => expBudget_pairW hu hv
  Q_fst := fun _ t ht => expBudget_mono (unpairW_length t).1 ht
  Q_snd := fun _ t ht => expBudget_mono (unpairW_length t).2 ht
  base_unpair := fun _ _ => trivial

/-- The advice hypothesis holds at the example scale, the decision relation being the question
itself. -/
theorem exampleDecisionAdvice (R : Rel) (_ : exampleScale.base R) :
    DecisionAdviceP exampleScale R := by
  refine ⟨fun _ => [], fun _ => rfl,
    fun x ys => match ys with
      | _ :: ws => ExQ exampleScale R x ws
      | [] => False, trivial, fun x ws _ => Iff.rfl⟩

/-- **The hypotheses of the collapse theorem are satisfiable**: at the example scale they all
hold, and the theorem applies. -/
theorem exampleCollapseAt : CollapseAt exampleScale 2 :=
  collapseAt_two_of_decisionAdvice exampleClosure exampleSearchClosure exampleDecisionAdvice

end Hier

end HTN
