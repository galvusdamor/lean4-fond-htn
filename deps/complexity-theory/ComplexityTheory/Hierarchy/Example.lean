import ComplexityTheory.Hierarchy.KarpLipton
/-!
# The structures are inhabited

The theorems of `Transfer.lean` and `KarpLipton.lean` are about abstract scales, so they would be
worthless if no scale, transfer or advice situation existed.  This file exhibits instances.

* `HTN.Hier.allScale` — the scale whose base class is *all* relations and whose budgets are *all*
  strings.  It is of course not a complexity class; it is the degenerate instance that shows the
  axioms of `HTN.Hier.Scale` are consistent.
* `HTN.Hier.expPadTransfer` — a `HTN.Hier.Transfer` between two copies of it along the genuine
  exponential padding `pad x = x 0^{2^{|x|}}`, with `padLen n = n + 2 ^ n`.  The padding data of
  the intended instance (`P` below, `EXPTIME` above) is therefore real; what the degenerate base
  class hides is exactly the complexity-theoretic content of `base_iff` — that a deterministic
  exponential-time computation on `x` is a polynomial-time computation on `pad x`.
* `HTN.Hier.witnessFromDecision_allScale` — the search-to-decision hypothesis holds in the
  degenerate scale, by choice.  This is the point of the whole discussion in reverse: the
  hypothesis is trivial as a statement about *sets*, and its entire content is that the extractor
  stays inside the base class and asks only questions whose advice is available.
-/

namespace HTN

namespace Hier

/-- The degenerate scale: every relation is in the base class, every string is admissible. -/
def allScale : Scale where
  base := fun _ => True
  Q := fun _ _ => True
  A := fun _ _ => True
  Q_nil := fun _ => trivial
  A_nil := fun _ => trivial

/-- The exponential padding `x ↦ x 0^{2^{|x|}}`. -/
def expPad (x : Word) : Word := x ++ List.replicate (2 ^ x.length) false

/-- The length of an exponentially padded word. -/
def expPadLen (n : ℕ) : ℕ := n + 2 ^ n

theorem expPad_length (x : Word) : (expPad x).length = expPadLen x.length := by
  simp [expPad, expPadLen]

theorem expPadLen_strictMono : StrictMono expPadLen := by
  intro a b h
  have : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h.le
  simp only [expPadLen]
  omega

theorem expPadLen_injective : Function.Injective expPadLen :=
  expPadLen_strictMono.injective

theorem expPad_injective : Function.Injective expPad := by
  intro x y h
  have hlen : expPadLen x.length = expPadLen y.length := by
    rw [← expPad_length, ← expPad_length, h]
  have hxy : x.length = y.length := expPadLen_injective hlen
  exact List.append_inj_left h hxy

/-- The exponential padding is a map of scales, between two copies of the degenerate scale.  The
padding data is the intended one; only the base classes are degenerate. -/
def expPadTransfer : Transfer allScale allScale where
  pad := expPad
  padLen := expPadLen
  pad_length := expPad_length
  pad_inj := expPad_injective
  padLen_inj := expPadLen_injective
  base_iff := fun _ => Iff.rfl
  base_restrict := fun _ _ => trivial
  Q_iff := fun _ _ => Iff.rfl
  A_iff := fun _ _ => Iff.rfl

/-- In the degenerate scale the advice hypothesis holds for every relation: the decision relation
may simply be the existential question itself. -/
theorem decisionAdvice_allScale (R : Rel) : DecisionAdvice allScale R := by
  refine ⟨fun _ => [], fun _ => trivial, fun x ys => ∃ z, R x [ys.getLast!, z], trivial,
    fun x y _ => ?_⟩
  simp [allScale]

/-- In the degenerate scale search reduces to decision, by choice.  The content of the hypothesis
at a real scale is not the existence of the extractor but its cost. -/
theorem witnessFromDecision_allScale (R : Rel) : WitnessFromDecision allScale R := by
  classical
  intro a D _ _
  refine ⟨fun _ x y => if h : ∃ z, R x [y, z] then h.choose else [], trivial, fun x y _ h => ?_⟩
  obtain ⟨z, -, hz⟩ := h
  have hex : ∃ z, R x [y, z] := ⟨z, hz⟩
  refine ⟨trivial, ?_⟩
  simpa [hex] using hex.choose_spec

/-- A smoke test of the Karp–Lipton step: in the degenerate scale every `∀∃` language lands at
level `2`, by the abstract argument of `KarpLipton.lean` — no hypothesis of that theorem is
contradictory. -/
theorem sigmaLevel_two_allScale (L : Lang) (R : Rel)
    (hL : ∀ x, L x ↔ ∀ y, allScale.Q x.length y → ∃ z, allScale.Q x.length z ∧ R x [y, z]) :
    SigmaLevel allScale 2 L :=
  sigmaLevel_two_of_decisionAdvice hL (fun _ _ _ => trivial) (decisionAdvice_allScale R)
    (witnessFromDecision_allScale R)

end Hier

end HTN
