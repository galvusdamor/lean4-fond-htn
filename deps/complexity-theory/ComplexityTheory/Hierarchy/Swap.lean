import ComplexityTheory.Hierarchy.Search
/-!
# The Karp–Lipton quantifier swap, with parameters

`KarpLipton.lean` performs the swap for one language, i.e. with no strings quantified before the
`∀∃` block.  The collapse of a *whole* hierarchy needs the swap inside a longer prefix, where the
strings quantified earlier are parameters of the block; this file states and proves that form.

* `HTN.Hier.SwapParams s` — **`Π₂ ⊆ Σ₂`, with parameters**: for every base relation `R` there is a
  base relation `R'` such that, for every input `x` and every admissible parameter list `ws`,

      (∀ y ∃ z. R x (ws ++ [y, z]))  ↔  (∃ c ∀ y. R' x (ws ++ [c, y])).

  This is the only complexity-theoretic input of the collapse theorem of `Collapse.lean`.
* `HTN.Hier.SearchClosure s` — the *structural* hypotheses under which the swap is available:
  every base relation has a witness bound whose words may all be quantified over, advice is
  guessable, and the base class contains the prefix-extension relation of each of its members and
  can run the bit-by-bit search.  None of them is a complexity-theoretic assumption.
* `HTN.Hier.SearchClosure.swapParams` — **the Karp–Lipton step, proved**: a `SearchClosure`
  together with the advice hypothesis `HTN.Hier.DecisionAdviceP` for every base relation — at the
  weak exponential scale, `NEXPTIME ⊆ EXPTIME/poly` — yields `SwapParams`.  The guessed string is
  the advice; the witness the swap needs is produced by `HTN.Hier.greedy`, and its correctness is
  `HTN.Hier.greedy_sound`.

Compare `KarpLipton.lean`, which carries the extractor as an unproved hypothesis
(`HTN.Hier.WitnessFromDecision`): the present file discharges that hypothesis, and — see the
discussion in `Search.lean` — does so at the weak exponential scale as well as at the polynomial
one.  What remains assumed is not search-to-decision but the closure of the base class under the
loop that performs it.
-/

namespace HTN

namespace Hier

/-- The relation the swap produces: on a parameter list followed by the guessed advice `c` and
the universally quantified `y`, it says that the extractor turns `c` into an admissible witness
for `y`. -/
def extRelP (s : Scale) (R : Rel) (ext : Word → Word → List Word → Word → Word) : Rel :=
  fun x ys => match ys.reverse with
    | y :: c :: rest =>
        s.Q x.length (ext c x rest.reverse y) ∧ R x (rest.reverse ++ [y, ext c x rest.reverse y])
    | _ => False

@[simp] theorem extRelP_apply (s : Scale) (R : Rel)
    (ext : Word → Word → List Word → Word → Word) (x : Word) (ws : List Word) (c y : Word) :
    extRelP s R ext x (ws ++ [c, y]) ↔
      s.Q x.length (ext c x ws y) ∧ R x (ws ++ [y, ext c x ws y]) := by
  have hrev : (ws ++ [c, y]).reverse = y :: c :: ws.reverse := by simp
  simp [extRelP, hrev]

/-- **`Π₂ ⊆ Σ₂`, with parameters.**  Every `∀∃` block over a base relation, inside an arbitrary
prefix of already quantified strings, is an `∃∀` block over a base relation. -/
def SwapParams (s : Scale) : Prop :=
  ∀ R, s.base R → ∃ R', s.base R' ∧ ∀ x ws, (∀ w ∈ ws, s.Q x.length w) →
    ((∀ y, s.Q x.length y → ∃ z, s.Q x.length z ∧ R x (ws ++ [y, z])) ↔
      (∃ c, s.Q x.length c ∧ ∀ y, s.Q x.length y → R' x (ws ++ [c, y])))

/-- **The structural hypotheses that make the Karp–Lipton swap available at a scale.**

They say that each base relation has a witness bound — the number of bits of the witnesses it is
worth searching for, which is the number of steps of the self-reduction — that every word within
a witness bound may be quantified over, that advice may be guessed, and that the base class
contains the prefix-extension relation of each of its members and can run the search of
`HTN.Hier.greedy`.  None of them is a complexity-theoretic assumption; the complexity-theoretic
input of the swap is the separate hypothesis `HTN.Hier.DecisionAdviceP`.

The bound is allowed to depend on the input and on the parameters, which is what lets the
quantifier budget of the scale be closed under pairing (`HTN.Hier.Closure`, `Collapse.lean`)
while each individual relation still has a bounded search. -/
structure SearchClosure (s : Scale) where
  /-- The witness bound of a relation, as a function of the input and the parameters. -/
  bnd : Rel → Word → List Word → ℕ
  /-- Every word within a witness bound may be quantified over. -/
  Q_of_le : ∀ R x ws (w : Word), w.length ≤ bnd R x ws → s.Q x.length w
  /-- A base relation with an admissible witness has one within its bound. -/
  witness_short : ∀ R, s.base R → ∀ x ws, (∃ z, s.Q x.length z ∧ R x (ws ++ [z])) →
    ∃ z, z.length ≤ bnd R x ws ∧ R x (ws ++ [z])
  /-- Advice is short enough to be guessed by an existential quantifier of the scale. -/
  A_Q : ∀ n c, s.A n c → s.Q n c
  /-- The base class contains the prefix-extension relation of each of its members. -/
  base_prefRel : ∀ R, s.base R → s.base (prefRel (bnd R) R)
  /-- The base class can run the bit-by-bit search against a base-class decision relation and
  check the witness it returns. -/
  base_greedy : ∀ R D : Rel, s.base R → s.base D →
    s.base (extRelP s R fun c x ws y => greedy D c x (ws ++ [y]) (bnd R x (ws ++ [y])) [])

namespace SearchClosure

variable {s : Scale}

/-- **The Karp–Lipton step at a scale with a search closure**: `Π₂ ⊆ Σ₂`, with parameters, from
the advice hypothesis alone.

The existential quantifier guesses the advice; the universal one runs the search
(`HTN.Hier.greedy`) and checks the witness it produces.  Soundness of the swap is free — a
guessed advice string is believed only when the witness it yields verifies — and completeness is
`HTN.Hier.greedy_sound` applied to the correct advice.

Read at the weak exponential scale: `NEXPTIME ⊆ EXPTIME/poly` implies `Π₂^EXP ⊆ Σ₂^EXP`, with
parameters. -/
theorem swapParams (sr : SearchClosure s) (hadv : ∀ R, s.base R → DecisionAdviceP s R) :
    SwapParams s := by
  intro R hR
  obtain ⟨a, ha, D, hD, hDec⟩ := hadv (prefRel (sr.bnd R) R) (sr.base_prefRel R hR)
  refine ⟨extRelP s R fun c x ws y =>
      greedy D c x (ws ++ [y]) (sr.bnd R x (ws ++ [y])) [], sr.base_greedy R D hR hD,
    fun x ws hws => ?_⟩
  -- the decision relation answers the prefix-extension questions, for every admissible `y`
  have key : ∀ y, s.Q x.length y → ∀ q : Word, q.length ≤ sr.bnd R x (ws ++ [y]) →
      (GoodPrefix R (sr.bnd R) x (ws ++ [y]) q ↔ D x (a x.length :: (ws ++ [y] ++ [q]))) := by
    intro y hy q hqlen
    have hadm : ∀ w ∈ ws ++ [y] ++ [q], s.Q x.length w := by
      intro w hw
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (hw | hw) | hw
      · exact hws w hw
      · exact hw ▸ hy
      · exact hw ▸ sr.Q_of_le R x (ws ++ [y]) q hqlen
    rw [← hDec x _ hadm]
    exact (exQ_prefRel (s := s) R x (ws ++ [y]) q
      (fun w hw => sr.Q_of_le R x (ws ++ [y]) w hw)).symm
  constructor
  · intro hall
    refine ⟨a x.length, sr.A_Q _ _ (ha _), fun y hy => ?_⟩
    have hex : ∃ z, s.Q x.length z ∧ R x (ws ++ [y] ++ [z]) := by
      obtain ⟨z, hz, hRz⟩ := hall y hy
      exact ⟨z, hz, by rw [List.append_assoc]; exact hRz⟩
    obtain ⟨z, hzlen, hRz⟩ := sr.witness_short R hR x (ws ++ [y]) hex
    have hgood : GoodPrefix R (sr.bnd R) x (ws ++ [y]) [] := goodPrefix_nil hzlen hRz
    have := greedy_sound (s := s) (R := R) (D := D) (bnd := sr.bnd R) (c := a x.length)
      (ws := ws ++ [y]) (fun w hw => sr.Q_of_le R x (ws ++ [y]) w hw) (key y hy)
      (sr.bnd R x (ws ++ [y])) [] (by simp) hgood
    rw [List.append_assoc] at this
    rw [extRelP_apply]
    exact ⟨this.1, this.2⟩
  · rintro ⟨c, -, hc⟩ y hy
    have := hc y hy
    rw [extRelP_apply] at this
    exact ⟨_, this.1, this.2⟩

end SearchClosure

end Hier

end HTN
