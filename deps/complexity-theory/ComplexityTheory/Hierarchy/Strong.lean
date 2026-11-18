import ComplexityTheory.Hierarchy.Cells
/-!
# Weak versus strong: two different exponential hierarchies

There are two hierarchies above `EXPTIME` in the literature, and they behave very differently.

* The **weak** (or just "the") exponential hierarchy `EXPH = ⋃_k Σ_k^EXP`.  Its levels are given
  by a prefix of alternating quantifiers over *exponentially long* strings in front of a
  deterministic exponential-time predicate — equivalently, by alternating exponential time with a
  bounded number of alternations.  No collapse of `EXPH` is known.
* The **strong** exponential hierarchy `SEH`, whose levels are built by *oracle access* with a
  polynomial-time outer machine: `P^NE ⊆ NP^NE ⊆ NP^{NP^NE} ⊆ …`.  Here the outer machine runs in
  polynomial time, so the strings it hands to the next level (its oracle queries) are only
  *polynomially long*, while the base class is exponential.  This hierarchy is known to collapse,
  to `P^NE` (Hemachandra, *The strong exponential hierarchy collapses*, 1987).

Both are "alternating bounded quantifiers in front of a predicate of a deterministic base class",
so both are hierarchies of a `HTN.Hier.Scale` (`Scale.lean`) — but of *different* scales, with the
same base class and different quantifier budgets: exponentially long strings for `EXPH`,
polynomially long ones for `SEH`.  `HTN.Hier.Scale.withQuant` is that change of budget.

This file records two things.

* Which hierarchy the rest of this development talks about: the hypothesis `¬ CollapseAt s 2` of
  `HTN.Hier.not_adviceHyp_of_not_collapseAt` (and hence the reading of the Table 3 discussion in
  §44 of `NOTES.md`) is about the levels `SigmaLevel s k`, whose quantifiers range over the *full*
  budget `s.Q` of the scale — the exponentially long strings, at the exponential scale.  That is
  the **weak** hierarchy `EXPH`, not `SEH`.
* That the distinction is not cosmetic, and that a collapse of the short-budget hierarchy carries
  no information about the long-budget one.  Since the framework is abstract, this can be proved
  rather than asserted: `HTN.Hier.exists_collapse_short_not_long` exhibits a base class and two
  quantifier budgets, one contained in the other, for which the short-budget hierarchy collapses
  to its level `0` while the long-budget hierarchy does not even collapse to level `2`.  So
  "`CollapseAt (short budget) k`" does not imply "`CollapseAt (long budget) 2`" as a theorem of the
  framework: the two collapse statements are about different objects, and a proof of one is not a
  proof of the other.

The model used for that separation is deliberately a toy one (its base class is a small family of
relations, not a complexity class); it is a *consistency* statement about the framework, showing
that no general argument can transport the collapse, and it is of course not a claim about the
real `SEH` and `EXPH`.  What is true of the real classes is the same, for a better reason: the
collapse of `SEH` is proved by a census argument that exploits the polynomial length of the outer
machine's queries, and it says nothing about alternating exponential time.

## Main definitions and results

* `HTN.Hier.Scale.withQuant` — the same base class and advice budget with a different quantifier
  budget: `EXPH` and the shape of `SEH` differ exactly by this;
* `HTN.Hier.tagBase`, `HTN.Hier.shortScale`, `HTN.Hier.longScale` — the toy model;
* `HTN.Hier.collapseAt_shortScale`, `HTN.Hier.not_collapseAt_longScale`,
  `HTN.Hier.exists_collapse_short_not_long` — the separation of the two collapse statements;
* `HTN.Hier.sigmaLevel_two_shortScale_ne_longScale` — in the model the two second levels are not
  even the same collection of languages.
-/

namespace HTN

namespace Hier

/-- The same scale with a different quantifier budget: same base class, same advice budget.  The
weak exponential hierarchy and the shape of the strong one differ exactly by this — the strong
hierarchy's outer machine is polynomial time, so the strings passed to the next level are
polynomially long, whereas the levels of `EXPH` quantify over exponentially long strings. -/
def Scale.withQuant (s : Scale) (Q' : ℕ → Word → Prop) (h : ∀ n, Q' n []) : Scale :=
  { s with Q := Q', Q_nil := h }

@[simp] theorem withQuant_base (s : Scale) (Q' : ℕ → Word → Prop) (h : ∀ n, Q' n []) :
    (s.withQuant Q' h).base = s.base := rfl

@[simp] theorem withQuant_Q (s : Scale) (Q' : ℕ → Word → Prop) (h : ∀ n, Q' n []) :
    (s.withQuant Q' h).Q = Q' := rfl

/-! ### A model separating the two collapse statements -/

/-- The relations of the toy base class: a language of the input, conjoined with the requirement
that every quantified string be empty.  A relation of this shape cannot distinguish quantified
strings beyond "empty or not", which is precisely the feature the two budgets differ on. -/
def tagRel (f : Word → Prop) : Rel := fun x ys => f x ∧ ∀ y ∈ ys, y = []

/-- The base class of the toy model. -/
def tagBase : Rel → Prop := fun R => ∃ f, ∀ x ys, R x ys ↔ tagRel f x ys

/-- The toy scale with the **short** quantifier budget: only the empty string may be quantified
over.  This plays the role of the polynomially long queries of the strong hierarchy's outer
machine. -/
def shortScale : Scale where
  base := tagBase
  Q := fun _ y => y = []
  A := fun _ _ => True
  Q_nil := fun _ => rfl
  A_nil := fun _ => trivial

/-- The toy scale with the **long** quantifier budget: every string may be quantified over.  This
plays the role of the exponentially long strings quantified over by the levels of `EXPH`. -/
def longScale : Scale where
  base := tagBase
  Q := fun _ _ => True
  A := fun _ _ => True
  Q_nil := fun _ => trivial
  A_nil := fun _ => trivial

theorem shortScale_base_eq_longScale_base : shortScale.base = longScale.base := rfl

theorem shortScale_Q_le_longScale_Q (n : ℕ) (y : Word) : shortScale.Q n y → longScale.Q n y :=
  fun _ => trivial

/-- Under the short budget every quantifier is forced onto the empty string, so a prefix of any
length in front of a relation of the toy base class says nothing beyond `f x`. -/
theorem qpre_shortScale (f : Word → Prop) (x : Word) :
    ∀ (k : ℕ) (b : Bool) (ys : List Word), (∀ y ∈ ys, y = []) →
      (qpre shortScale (tagRel f) k b x ys ↔ f x) := by
  intro k
  induction k with
  | zero =>
      intro b ys hys
      simp only [qpre_zero, tagRel]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, fun y hy => hys y (List.mem_reverse.mp hy)⟩
  | succ k ih =>
      intro b ys hys
      cases b with
      | true =>
          simp only [qpre_succ_true]
          constructor
          · rintro ⟨y, hy, h⟩
            exact (ih false (y :: ys) (by
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hy
              · exact hys z hz)).1 h
          · intro h
            refine ⟨[], rfl, ?_⟩
            refine (ih false ([] :: ys) ?_).2 h
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · rfl
            · exact hys z hz
      | false =>
          simp only [qpre_succ_false]
          constructor
          · intro h
            refine (ih true ([] :: ys) ?_).1 (h [] rfl)
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · rfl
            · exact hys z hz
          · intro h y hy
            refine (ih true (y :: ys) ?_).2 h
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hy
            · exact hys z hz

/-- In the short-budget model every language sits at every level. -/
theorem sigmaLevel_shortScale (k : ℕ) (L : Lang) : SigmaLevel shortScale k L := by
  refine ⟨tagRel L, ⟨L, fun _ _ => Iff.rfl⟩, fun x => ?_⟩
  exact (qpre_shortScale L x k true [] (by simp)).symm

/-- **The short-budget hierarchy of the model collapses**, to its level `0`. -/
theorem collapseAt_shortScale : CollapseAt shortScale 0 :=
  fun _ L _ => sigmaLevel_shortScale 0 L

/-- Level `0` of the long-budget model is still everything: no quantifier is in the way. -/
theorem sigmaLevel_zero_longScale (L : Lang) : SigmaLevel longScale 0 L := by
  refine ⟨tagRel L, ⟨L, fun _ _ => Iff.rfl⟩, fun x => ?_⟩
  simp [tagRel]

/-- Level `2` of the long-budget model contains only the empty language: the universal quantifier
ranges over *all* strings, and a relation of the toy base class rejects every nonempty one. -/
theorem sigmaLevel_two_longScale (L : Lang) : SigmaLevel longScale 2 L ↔ ∀ x, ¬ L x := by
  constructor
  · rintro ⟨R, ⟨f, hf⟩, hL⟩ x hx
    have h := (hL x).1 hx
    simp only [qpre_succ_true, qpre_succ_false, qpre_zero] at h
    obtain ⟨y, -, h⟩ := h
    have h' := h [true] trivial
    rw [hf] at h'
    have : ([true] : Word) = [] := h'.2 [true] (by simp)
    exact absurd this (by simp)
  · intro hL
    refine ⟨tagRel (fun _ => False), ⟨fun _ => False, fun _ _ => Iff.rfl⟩, fun x => ?_⟩
    simp only [qpre_succ_true, qpre_succ_false, qpre_zero, tagRel]
    constructor
    · intro hx; exact absurd hx (hL x)
    · rintro ⟨y, -, h⟩
      exact absurd (h [] trivial).1 not_false

/-- **The long-budget hierarchy of the model does not collapse** to level `2`: the universal
language is at level `0` and not at level `2`. -/
theorem not_collapseAt_longScale : ¬ CollapseAt longScale 2 := by
  intro h
  have h2 : SigmaLevel longScale 2 (fun _ => True) := h 0 _ (sigmaLevel_zero_longScale _)
  exact ((sigmaLevel_two_longScale _).1 h2 []) trivial

/-- **The two collapse statements are different statements.**  There is a base class and two
quantifier budgets, the first contained in the second, such that the hierarchy of the short budget
collapses to its bottom level while the hierarchy of the long budget does not collapse even to
level `2`.

Read at the exponential scale: the fact that the *strong* exponential hierarchy collapses — its
levels being reached by an outer machine whose queries are polynomially long — is no evidence for
a collapse of the exponential hierarchy `EXPH`, whose levels quantify over exponentially long
strings.  Nothing in the shape of the two hierarchies connects the two collapses, which is what
this theorem says formally. -/
theorem exists_collapse_short_not_long :
    ∃ s l : Scale, (∀ R, s.base R ↔ l.base R) ∧ (∀ n y, s.Q n y → l.Q n y) ∧
      CollapseAt s 0 ∧ ¬ CollapseAt l 2 :=
  ⟨shortScale, longScale, fun _ => Iff.rfl, shortScale_Q_le_longScale_Q,
    collapseAt_shortScale, not_collapseAt_longScale⟩

/-- In the model the second levels of the two budgets are not the same collection of languages —
so even the individual levels, not only the collapse statements, have to be kept apart. -/
theorem sigmaLevel_two_shortScale_ne_longScale :
    SigmaLevel shortScale 2 ≠ SigmaLevel longScale 2 := by
  intro h
  have h2 : SigmaLevel longScale 2 (fun _ => True) := by
    rw [← h]; exact sigmaLevel_shortScale 2 _
  exact ((sigmaLevel_two_longScale _).1 h2 []) trivial

/-- The hypothesis carried by `HTN.Hier.not_adviceHyp_of_not_collapseAt`, and so by the Table 3
discussion, is about the hierarchy of the scale itself — the quantifiers range over the whole
budget `s.Q` of the scale, i.e. over exponentially long strings at the exponential scale.  This
lemma is the (trivial) restatement that makes the reading explicit: changing the budget changes
the statement, and `CollapseAt (s.withQuant Q' h) 2` is a statement about the short-budget
hierarchy, not about `EXPH`. -/
theorem collapseAt_withQuant_iff (s : Scale) (Q' : ℕ → Word → Prop) (h : ∀ n, Q' n [])
    (hQ : ∀ n y, Q' n y ↔ s.Q n y) (k : ℕ) :
    CollapseAt (s.withQuant Q' h) k ↔ CollapseAt s k := by
  have hs : ∀ (j : ℕ) (L : Lang), SigmaLevel (s.withQuant Q' h) j L ↔ SigmaLevel s j L :=
    fun j L => sigmaLevel_congr_scale (s₁ := s.withQuant Q' h) (s₂ := s)
      (fun _ => Iff.rfl) hQ j L
  constructor
  · intro hc j L hL; exact (hs k L).1 (hc j L ((hs j L).2 hL))
  · intro hc j L hL; exact (hs k L).2 (hc j L ((hs j L).1 hL))

end Hier

end HTN
