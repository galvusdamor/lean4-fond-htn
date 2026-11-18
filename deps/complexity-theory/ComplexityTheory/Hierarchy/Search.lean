import ComplexityTheory.Hierarchy.KarpLipton
/-!
# Search reduces to decision, by the bit-by-bit self-reduction

`KarpLipton.lean` isolates the one ingredient the Karp–Lipton quantifier swap needs beyond the
shape of the hierarchy: from advice that *decides* the existential question one must *produce a
witness*.  This file supplies that ingredient — the bit-by-bit self-reduction — and it is the
point at which the **weak** exponential hierarchy behaves like the polynomial one.

## Why this works at the weak exponential scale

The reading that makes the self-reduction fail one exponential up is the one in which a query
asked during the reduction is a *fresh input* of the advised machine: the query mentions an
exponentially long string, so its advice would be the advice for exponential length, which is no
longer guessable, and the machine's own time bound would be measured against the long query.

That is not the reading of the weak hierarchy, and it is not the reading of `Scale`.  In a level
`Σ_k` of the weak exponential hierarchy the quantified strings are arguments of *one* base-class
predicate whose resources are measured against the original input `x`: the base relation is
`R : Word → List Word → Prop`, and the advice string of `DecisionAdviceP` is indexed by
`x.length` only.  The self-reduction therefore

* never changes the input `x`, hence never needs advice for a new length — the single guessed
  advice string serves every query; and
* makes as many queries as the witness has bits, each one evaluation of the advised base relation
  at `x`.  At the exponential scale that is `2 ^ poly` evaluations of a `2 ^ poly`-time predicate,
  which is again `2 ^ poly`: exactly the closure the base class has.

So the classical proof does lift to the weak hierarchy, and the residue is one honest closure
hypothesis about the base class — that it can run the loop
(`HTN.Hier.SearchClosure.base_greedy`, `Swap.lean`) — instead of a complexity-theoretic
assumption.  The *strong* hierarchy is the one where this fails, because there the outer machine
is polynomially bounded while the strings are exponentially long, so it cannot even read them;
see `Strong.lean`.

## Main definitions and results

* `HTN.Hier.ExQ`, `HTN.Hier.DecisionAdviceP` — the existential question attached to a base
  relation with the strings quantified so far as parameters, and the advice hypothesis for it;
* `HTN.Hier.prefRel` — the prefix-extension relation: *is there a witness of the admissible
  length extending `p`?*;
* `HTN.Hier.greedy` — the bit-by-bit search, driven by a decision relation;
* `HTN.Hier.greedy_sound` — **the self-reduction is correct**: if the decision relation answers
  the prefix-extension questions and some witness exists, the search returns one.

The length bound of the witnesses is carried per relation and per parameter list
(`HTN.Hier.greedy_sound` takes it as `bnd`), not as a global budget of the scale: the quantifier
budget of a level of the hierarchy is a union over all bounds — which is what makes it closed
under pairing, as `Collapse.lean` needs — while each individual base relation reads only a
bounded part of its arguments.
-/

namespace HTN

namespace Hier

/-! ### The existential question, with parameters -/

/-- **The existential question attached to `R`, with the parameters `ws` already fixed**: is there
an admissible `z` with `R x (ws ++ [z])`?  At the exponential scale, and with `ws` the strings
quantified so far, this is the `NEXPTIME` question the advice is assumed to answer. -/
def ExQ (s : Scale) (R : Rel) (x : Word) (ws : List Word) : Prop :=
  ∃ z, s.Q x.length z ∧ R x (ws ++ [z])

/-- **Decision advice for the existential question, with parameters.**  One advice string per
input length answers the question for every admissible list of parameters.  Read at the
exponential scale, with `base = EXPTIME` and polynomial advice, this is `NEXPTIME ⊆ EXPTIME/poly`
in the relational form the weak hierarchy uses: the advice depends on `x.length` alone, not on
the length of the exponentially long parameters. -/
def DecisionAdviceP (s : Scale) (R : Rel) : Prop :=
  ∃ a : ℕ → Word, (∀ n, s.A n (a n)) ∧ ∃ D : Rel, s.base D ∧
    ∀ x ws, (∀ w ∈ ws, s.Q x.length w) → (ExQ s R x ws ↔ D x (a x.length :: ws))

/-- **The prefix-extension relation of `R`, for the witness bound `bnd`**: on a parameter list
ending in `p` and a candidate `z`, it says that `z` is of the admissible length, extends `p`, and
is a witness for `R`.  Its existential question is *is there a witness extending `p`?*, which is
what the self-reduction asks. -/
def prefRel (bnd : Word → List Word → ℕ) (R : Rel) : Rel := fun x ys =>
  match ys.reverse with
  | z :: p :: rest => z.length ≤ bnd x rest.reverse ∧ p <+: z ∧ R x (rest.reverse ++ [z])
  | _ => False

@[simp] theorem prefRel_apply (bnd : Word → List Word → ℕ) (R : Rel) (x : Word)
    (ws : List Word) (p z : Word) :
    prefRel bnd R x (ws ++ [p, z]) ↔ z.length ≤ bnd x ws ∧ p <+: z ∧ R x (ws ++ [z]) := by
  have hrev : (ws ++ [p, z]).reverse = z :: p :: ws.reverse := by simp
  simp [prefRel, hrev]

/-- The invariant of the search: the current prefix is a prefix of a witness of the admissible
length. -/
def GoodPrefix (R : Rel) (bnd : Word → List Word → ℕ) (x : Word) (ws : List Word) (p : Word) :
    Prop :=
  ∃ z, z.length ≤ bnd x ws ∧ p <+: z ∧ R x (ws ++ [z])

/-- The existential question of the prefix-extension relation is exactly the invariant of the
search, provided every word of the admissible length may be quantified over. -/
theorem exQ_prefRel {s : Scale} {bnd : Word → List Word → ℕ} (R : Rel) (x : Word)
    (ws : List Word) (p : Word)
    (hQ : ∀ w : Word, w.length ≤ bnd x ws → s.Q x.length w) :
    ExQ s (prefRel bnd R) x (ws ++ [p]) ↔ GoodPrefix R bnd x ws p := by
  constructor
  · rintro ⟨z, -, hz⟩
    have : prefRel bnd R x (ws ++ [p, z]) := by
      simpa [List.append_assoc] using hz
    rw [prefRel_apply] at this
    exact ⟨z, this.1, this.2.1, this.2.2⟩
  · rintro ⟨z, hlen, hp, hR⟩
    refine ⟨z, hQ z hlen, ?_⟩
    have : prefRel bnd R x (ws ++ [p, z]) := by
      rw [prefRel_apply]; exact ⟨hlen, hp, hR⟩
    simpa [List.append_assoc] using this

/-! ### The bit-by-bit search -/

open Classical in
/-- **The self-reduction.**  `greedy D c x ws k p` extends the prefix `p` by up to `k` bits,
asking the decision relation `D` — with the guessed advice `c` and the parameters `ws` — whether
a witness extending the candidate prefix exists.  When neither extension is possible the prefix
itself is returned. -/
noncomputable def greedy (D : Rel) (c : Word) (x : Word) (ws : List Word) :
    ℕ → Word → Word
  | 0, p => p
  | (k + 1), p =>
      if D x (c :: (ws ++ [p ++ [true]])) then greedy D c x ws k (p ++ [true])
      else if D x (c :: (ws ++ [p ++ [false]])) then greedy D c x ws k (p ++ [false])
      else p

@[simp] theorem greedy_zero (D : Rel) (c x : Word) (ws : List Word) (p : Word) :
    greedy D c x ws 0 p = p := rfl

open Classical in
theorem greedy_succ (D : Rel) (c x : Word) (ws : List Word) (k : ℕ) (p : Word) :
    greedy D c x ws (k + 1) p =
      if D x (c :: (ws ++ [p ++ [true]])) then greedy D c x ws k (p ++ [true])
      else if D x (c :: (ws ++ [p ++ [false]])) then greedy D c x ws k (p ++ [false])
      else p := rfl

theorem goodPrefix_nil {R : Rel} {bnd : Word → List Word → ℕ} {x : Word} {ws : List Word}
    {z : Word} (hlen : z.length ≤ bnd x ws) (hR : R x (ws ++ [z])) :
    GoodPrefix R bnd x ws [] :=
  ⟨z, hlen, List.nil_prefix, hR⟩

/-- A prefix that cannot be extended is itself a witness: if `p` is a prefix of a witness and
neither `p ++ [true]` nor `p ++ [false]` is, then `p` is the witness. -/
theorem of_goodPrefix_of_not_extend {R : Rel} {bnd : Word → List Word → ℕ} {x : Word}
    {ws : List Word} {p : Word} (h : GoodPrefix R bnd x ws p)
    (ht : ¬ GoodPrefix R bnd x ws (p ++ [true])) (hf : ¬ GoodPrefix R bnd x ws (p ++ [false])) :
    R x (ws ++ [p]) := by
  obtain ⟨z, hz, hp, hR⟩ := h
  obtain ⟨t, rfl⟩ := hp
  cases t with
  | nil => simpa using hR
  | cons b t =>
      cases b with
      | true => exact absurd ⟨p ++ true :: t, hz, by simp, hR⟩ ht
      | false => exact absurd ⟨p ++ false :: t, hz, by simp, hR⟩ hf

/-- **The self-reduction is correct.**  If the decision relation `D` — with the advice `c` —
answers the prefix-extension questions for the parameters `ws`, and the current prefix is a
prefix of a witness of the admissible length, and exactly as many bits remain as the bound
allows, then the search returns an admissible witness. -/
theorem greedy_sound {s : Scale} {R D : Rel} {bnd : Word → List Word → ℕ} {c x : Word}
    {ws : List Word}
    (hQ : ∀ w : Word, w.length ≤ bnd x ws → s.Q x.length w)
    (hD : ∀ q : Word, q.length ≤ bnd x ws →
      (GoodPrefix R bnd x ws q ↔ D x (c :: (ws ++ [q])))) :
    ∀ (k : ℕ) (p : Word), p.length + k = bnd x ws → GoodPrefix R bnd x ws p →
      s.Q x.length (greedy D c x ws k p) ∧ R x (ws ++ [greedy D c x ws k p]) := by
  intro k
  induction k with
  | zero =>
      intro p hlen hp
      obtain ⟨z, hz, hpz, hR⟩ := hp
      have hpz' : p = z := hpz.eq_of_length (by have := hpz.length_le; omega)
      subst hpz'
      exact ⟨hQ p (by omega), by simpa using hR⟩
  | succ k ih =>
      intro p hlen hp
      rw [greedy_succ]
      have hlen1 : (p ++ [true]).length ≤ bnd x ws := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hlen0 : (p ++ [false]).length ≤ bnd x ws := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      by_cases htrue : D x (c :: (ws ++ [p ++ [true]]))
      · rw [if_pos htrue]
        refine ih (p ++ [true]) ?_ ((hD _ hlen1).2 htrue)
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · rw [if_neg htrue]
        by_cases hfalse : D x (c :: (ws ++ [p ++ [false]]))
        · rw [if_pos hfalse]
          refine ih (p ++ [false]) ?_ ((hD _ hlen0).2 hfalse)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · rw [if_neg hfalse]
          have hQp : s.Q x.length p := by
            obtain ⟨z, hz, hpz, -⟩ := hp
            exact hQ p (le_trans hpz.length_le hz)
          refine ⟨hQp, of_goodPrefix_of_not_extend hp ?_ ?_⟩
          · exact fun hg => htrue ((hD _ hlen1).1 hg)
          · exact fun hg => hfalse ((hD _ hlen0).1 hg)

end Hier

end HTN
