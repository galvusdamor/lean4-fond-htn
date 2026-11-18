import ComplexityTheory.Hierarchy.Collapse
/-!
# The Karp–Lipton swap from a window and concatenation

`Swap.lean` performs the quantifier swap from a `HTN.Hier.SearchClosure`, one of whose fields asks
the base class to contain the *prefix-extension relation* `HTN.Hier.prefRel` of each of its
members: a conjunction of a length check, a prefix check and the relation itself.  At a scale
defined by machines that conjunction is a machine construction.

This file offers a variant, `HTN.Hier.SearchClosureW`, in which that field is replaced by two
properties that a machine scale has for free:

* **a window**: every base relation ignores all but the first `bnd R x ws` bits of its last
  string (`window`) — a time-bounded machine cannot read further;
* **concatenation**: the base class contains `HTN.Hier.catRel R`, the relation `R` read after
  concatenating the last two strings — a linear-time preprocessing.

The prefix-extension question "is there a witness of the admissible length extending `q`?" then
becomes the existential question of `catRel R` with parameter `q`
(`HTN.Hier.goodPrefix_iff_exQ_catRel`), and the swap goes through as before
(`HTN.Hier.SearchClosureW.swapParams`, `HTN.Hier.collapseAt_two_of_decisionAdviceW`).
-/

namespace HTN

namespace Hier

variable {s : Scale}

/-- **Concatenate the last two strings of a list**; lists with fewer than two strings are left
alone. -/
def catList (ys : List Word) : List Word :=
  match ys.reverse with
  | z :: p :: rest => rest.reverse ++ [p ++ z]
  | _ => ys

@[simp] lemma catList_nil : catList [] = [] := rfl
@[simp] lemma catList_singleton (y : Word) : catList [y] = [y] := rfl

@[simp] lemma catList_append_pair (ws : List Word) (p z : Word) :
    catList (ws ++ [p, z]) = ws ++ [p ++ z] := by
  have hrev : (ws ++ [p, z]).reverse = z :: p :: ws.reverse := by simp
  simp [catList, hrev]

/-- **`R` read after concatenating the last two strings.** -/
def catRel (R : Rel) : Rel := fun x ys => R x (catList ys)

/-- **The structural hypotheses of the swap, in window form.**  As `HTN.Hier.SearchClosure`, with
the prefix-extension field replaced by a window of every base relation and by closure under
concatenating the last two strings. -/
structure SearchClosureW (s : Scale) where
  /-- The witness bound of a relation, as a function of the input and the parameters. -/
  bnd : Rel → Word → List Word → ℕ
  /-- Every word within a witness bound may be quantified over. -/
  Q_of_le : ∀ R x ws (w : Word), w.length ≤ bnd R x ws → s.Q x.length w
  /-- A base relation reads only the first `bnd R x ws` bits of its last string. -/
  window : ∀ R, s.base R → ∀ x ws z, (R x (ws ++ [z.take (bnd R x ws)]) ↔ R x (ws ++ [z]))
  /-- Advice is short enough to be guessed by an existential quantifier of the scale. -/
  A_Q : ∀ n c, s.A n c → s.Q n c
  /-- The base class is closed under concatenating the last two strings. -/
  base_catRel : ∀ R, s.base R → s.base (catRel R)
  /-- The base class can run the bit-by-bit search against a base-class decision relation and
  check the witness it returns. -/
  base_greedy : ∀ R D : Rel, s.base R → s.base D →
    s.base (extRelP s R fun c x ws y => greedy D c x (ws ++ [y]) (bnd R x (ws ++ [y])) [])

namespace SearchClosureW

/-- A witness, if there is one, can be cut to the window. -/
theorem witness_short (sr : SearchClosureW s) {R : Rel} (hR : s.base R) {x : Word}
    {ws : List Word} {z : Word} (hz : R x (ws ++ [z])) :
    ∃ z', z'.length ≤ sr.bnd R x ws ∧ R x (ws ++ [z']) :=
  ⟨z.take (sr.bnd R x ws), List.length_take_le _ _, (sr.window R hR x ws z).2 hz⟩

/-- **The prefix-extension question is the existential question of `catRel R`.** -/
theorem goodPrefix_iff_exQ_catRel (sr : SearchClosureW s) {R : Rel} (hR : s.base R) (x : Word)
    (ws : List Word) {q : Word} (hq : q.length ≤ sr.bnd R x ws) :
    GoodPrefix R (sr.bnd R) x ws q ↔ ExQ s (catRel R) x (ws ++ [q]) := by
  constructor
  · rintro ⟨z, hz, ⟨t, rfl⟩, hRz⟩
    refine ⟨t, sr.Q_of_le R x ws t ?_, ?_⟩
    · simp only [List.length_append] at hz; omega
    · show R x (catList (ws ++ [q] ++ [t]))
      simpa using hRz
  · rintro ⟨t, -, hRt⟩
    have hRt' : R x (ws ++ [q ++ t]) := by
      have : R x (catList (ws ++ [q] ++ [t])) := hRt
      simpa using this
    refine ⟨(q ++ t).take (sr.bnd R x ws), List.length_take_le _ _, ?_,
      (sr.window R hR x ws _).2 hRt'⟩
    rw [List.take_append, List.take_of_length_le hq]
    exact List.prefix_append _ _

/-- **The Karp–Lipton step, in window form**: `Π₂ ⊆ Σ₂`, with parameters, from the advice
hypothesis alone. -/
theorem swapParams (sr : SearchClosureW s) (hadv : ∀ R, s.base R → DecisionAdviceP s R) :
    SwapParams s := by
  intro R hR
  obtain ⟨a, ha, D, hD, hDec⟩ := hadv (catRel R) (sr.base_catRel R hR)
  refine ⟨extRelP s R fun c x ws y =>
      greedy D c x (ws ++ [y]) (sr.bnd R x (ws ++ [y])) [], sr.base_greedy R D hR hD,
    fun x ws hws => ?_⟩
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
    exact sr.goodPrefix_iff_exQ_catRel hR x (ws ++ [y]) hqlen
  constructor
  · intro hall
    refine ⟨a x.length, sr.A_Q _ _ (ha _), fun y hy => ?_⟩
    obtain ⟨z, -, hRz⟩ := hall y hy
    obtain ⟨z', hzlen, hRz'⟩ := sr.witness_short hR (ws := ws ++ [y]) (z := z)
      (by rw [List.append_assoc]; exact hRz)
    have hgood : GoodPrefix R (sr.bnd R) x (ws ++ [y]) [] := goodPrefix_nil hzlen hRz'
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

end SearchClosureW

/-- **The collapse from decision advice, in window form.** -/
theorem collapseAt_two_of_decisionAdviceW (c : Closure s) (sr : SearchClosureW s)
    (hadv : ∀ R, s.base R → DecisionAdviceP s R) : CollapseAt s 2 :=
  collapseAt_two_of_swapParams c (sr.swapParams hadv)

end Hier

end HTN
