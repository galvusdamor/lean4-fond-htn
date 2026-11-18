import ComplexityTheory.Hierarchy.Absorb
/-!
# Advice inside a level of the hierarchy

`HTN.Hier.InAdvice` is advice inside the *base* class of a scale: at the exponential scale,
`EXPTIME/poly`.  One of the three open cells of Table 3 has a target class whose plan-existence
problem is not deterministic — `HTN-AC-1` is the `NEXPTIME` class of the table — so the advice a
compilation into it produces is advice inside `Σ₁`, not inside the base class.  This file adds the
corresponding notion, one level of the hierarchy at a time:

> `HTN.Hier.InAdviceAt s k L` — the language `L` is decided by a level-`k` question about the
> input, with one admissible advice string per input length as an extra parameter.

At `k = 0` this is `HTN.Hier.InAdvice` (`HTN.Hier.inAdviceAt_zero_iff`); at the exponential scale
`k = 1` is `NEXPTIME/poly`.

## Main definitions and results

* `HTN.Hier.InAdviceAt` — advice inside level `k`;
* `HTN.Hier.qpreP_dropLast` — a trailing dummy quantifier changes nothing;
* `HTN.Hier.QLenFree`, `HTN.Hier.qpreP_subst` — a quantifier budget independent of the input
  length, and the substitution of a computed string into the input of a block;
* `HTN.Hier.inAdviceAt_zero_iff` — level `0` is the base class, so the notion extends `InAdvice`;
* `HTN.Hier.InAdvice.inAdviceAt` — advice inside the base class is advice inside every level.
-/

namespace HTN

namespace Hier

variable {s : Scale}

/-- **A trailing dummy quantifier changes nothing**: a block of `k + 1` quantifiers over a
relation that ignores the last string it is given is a block of `k` quantifiers over the
relation itself. -/
theorem qpreP_dropLast (R : Rel) (x : Word) :
    ∀ (k : ℕ) (b : Bool) (ws : List Word),
      qpreP s (fun x ys => R x ys.dropLast) (k + 1) b x ws ↔ qpreP s R k b x ws := by
  intro k
  induction k with
  | zero =>
      intro b ws
      cases b with
      | true =>
          simp only [qpreP_succ_true, qpreP_zero]
          constructor
          · rintro ⟨y, -, h⟩; simpa using h
          · intro h; exact ⟨[], s.Q_nil _, by simpa using h⟩
      | false =>
          simp only [qpreP_succ_false, qpreP_zero]
          constructor
          · intro h; simpa using h [] (s.Q_nil _)
          · intro h y _; simpa using h
  | succ k ih =>
      intro b ws
      cases b with
      | true =>
          simp only [qpreP_succ_true]
          exact exists_congr fun y => and_congr_right fun _ => ih false (ws ++ [y])
      | false =>
          simp only [qpreP_succ_false]
          exact forall_congr' fun y => imp_congr Iff.rfl (ih true (ws ++ [y]))

/-- **A quantifier budget that does not depend on the input length.**  The budget of the weak
exponential hierarchy — every word of length at most `2 ^ (n + k)` for *some* `k`, the union of
all exponential bounds — has this shape, and it is what lets a level-`k` question about a
computed string be read as a level-`k` question about the string it was computed from. -/
def QLenFree (s : Scale) : Prop := ∀ n m y, s.Q n y ↔ s.Q m y

/-- **Substituting into the input of a quantifier block.**  With a length-free budget, a block
over the relation `fun x ys => R (F x) ys` at the input `x` is the block over `R` at the computed
input `F x`. -/
theorem qpreP_subst (hQ : QLenFree s) (R : Rel) (F : Word → Word) :
    ∀ (k : ℕ) (b : Bool) (x : Word) (ws : List Word),
      qpreP s (fun x ys => R (F x) ys) k b x ws ↔ qpreP s R k b (F x) ws := by
  intro k
  induction k with
  | zero => intro b x ws; simp
  | succ k ih =>
      intro b x ws
      cases b with
      | true =>
          simp only [qpreP_succ_true]
          exact exists_congr fun y =>
            and_congr (hQ _ _ y) (ih false x (ws ++ [y]))
      | false =>
          simp only [qpreP_succ_false]
          exact forall_congr' fun y => imp_congr (hQ _ _ y) (ih true x (ws ++ [y]))

/-- **Advice inside level `k` of the hierarchy of the scale.**  One admissible advice string per
input length is handed, as a parameter, to a level-`k` quantifier block over a base relation.

At the exponential scale: `k = 0` is `EXPTIME/poly`, `k = 1` is `NEXPTIME/poly`. -/
def InAdviceAt (s : Scale) (k : ℕ) (L : Lang) : Prop :=
  ∃ a : ℕ → Word, (∀ n, s.A n (a n)) ∧ ∃ R, s.base R ∧
    ∀ x, L x ↔ qpreP s R k true x [a x.length]

/-- Advice inside level `0` is advice inside the base class. -/
theorem inAdviceAt_zero_iff (L : Lang) : InAdviceAt s 0 L ↔ InAdvice s L := by
  constructor <;> rintro ⟨a, ha, R, hR, hL⟩ <;>
    exact ⟨a, ha, R, hR, fun x => by simpa using hL x⟩

/-- Advice inside the base class is advice inside every level, provided the base class is closed
under ignoring the last quantified string. -/
theorem InAdvice.inAdviceAt (hdrop : ∀ R, s.base R → s.base fun x ys => R x ys.dropLast)
    {L : Lang} (h : InAdvice s L) : ∀ k, InAdviceAt s k L := by
  intro k
  induction k with
  | zero => exact (inAdviceAt_zero_iff L).2 h
  | succ k ih =>
      obtain ⟨a, ha, R, hR, hL⟩ := ih
      exact ⟨a, ha, fun x ys => R x ys.dropLast, hdrop R hR,
        fun x => (hL x).trans (qpreP_dropLast R x k true [a x.length]).symm⟩

end Hier

end HTN
