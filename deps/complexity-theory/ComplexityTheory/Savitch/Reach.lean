import ComplexityTheory.Savitch.Rec
import ComplexityTheory.Collapse.Code
import ComplexityTheory.Space.Model
/-!
# Reachability of a nondeterministic machine as Savitch's recursion

`ComplexityTheory/Savitch/Rec.lean` states the halving recursion over an abstract one-step test
on bit strings of a fixed width.  This file connects it to the machine model of
`ComplexityTheory/Space/Model.lean`: a machine `M`, an input `x`, an advice `a` and a width
bound `W` give a one-step test `HTN.Savitch.stpM` on strings of width `2 * W`, and

    HTN.Savitch.accepts_iff :
      M.Accepts x a  ↔  ∃ two nodes of width 2 * W, initial and accepting after decoding,
                        with `Rec (stpM …) (2 * W) (2 * W)` true of them.

## The encoding

A configuration `c` of length at most `W` is padded to the fixed width `2 * W`:

    enc W c  =  (ones |c| ++ zeros (W - |c|))  ++  (c ++ zeros (W - |c|)),

the first half a unary record of the length, the second half the configuration itself.  The
decoding `dec W y` reads the length off the prefix of ones of the first half and cuts the second
half to it; it is defined on *every* string of width `2 * W`, and `dec W (enc W c) = c`.  Nothing
says that `enc W (dec W y) = y`, and nothing needs to: the recursion quantifies over all strings
of the width, and a string that is not an encoding simply decodes to some configuration.

The one-step test is reflexive by construction — a node may always stay where it is — which is
what lets a path of any length be padded to one of length exactly `2 ^ k`.
-/

namespace HTN

namespace Savitch

open PTime PSpace Space

/-! ### Padding a configuration to a fixed width -/

/-- **The decoding**: the length is read off the prefix of ones of the first half. -/
def dec (W : ℕ) (y : List Bool) : List Bool :=
  (y.drop W).take (onesPrefix (y.take W)).length

/-- **The encoding** of a configuration as a node of width `2 * W`. -/
def enc (W : ℕ) (c : List Bool) : List Bool :=
  (ones c.length ++ zeros (W - c.length)) ++ (c ++ zeros (W - c.length))

theorem onesPrefix_ones_zeros (m k : ℕ) : onesPrefix (ones m ++ zeros k) = ones m := by
  induction m with
  | zero =>
    rcases k with _ | k
    · rfl
    · simp [ones, zeros, List.replicate_succ, onesPrefix]
  | succ m ih => rw [ones_succ, List.cons_append, onesPrefix, ih]

theorem length_enc {W : ℕ} {c : List Bool} (hc : c.length ≤ W) : (enc W c).length = 2 * W := by
  simp only [enc, List.length_append, length_ones, length_zeros]
  omega

theorem dec_enc {W : ℕ} {c : List Bool} (hc : c.length ≤ W) : dec W (enc W c) = c := by
  have hfst : (ones c.length ++ zeros (W - c.length)).length = W := by
    simp only [List.length_append, length_ones, length_zeros]
    omega
  have htake : (enc W c).take W = ones c.length ++ zeros (W - c.length) :=
    take_eq_of_length _ _ hfst.symm
  have hdrop : (enc W c).drop W = c ++ zeros (W - c.length) :=
    drop_eq_of_length _ _ hfst.symm
  rw [dec, htake, hdrop, onesPrefix_ones_zeros, length_ones]
  simp

theorem length_dec_le (W : ℕ) (y : List Bool) : (dec W y).length ≤ W := by
  have h₁ : (onesPrefix (y.take W)).length ≤ (y.take W).length := length_onesPrefix_le _
  have h₂ : (y.take W).length ≤ W := by simp
  simp only [dec, List.length_take]
  omega

/-! ### The one-step test -/

variable (M : NSpace) (x a : List Bool) (W : ℕ)

/-- **The one-step test on nodes**: the two nodes decode to the same configuration, or the
machine may pass from the first to the second. -/
def stpM (u v : List Bool) : Bool :=
  decide (dec W u = dec W v) || M.stepB [dec W v, dec W u, x, a]

variable {M x a W}

theorem stpM_refl (u : List Bool) : stpM M x a W u u = true := by simp [stpM]

theorem stpM_of_step {c c' : List Bool} (hc : c.length ≤ W) (hc' : c'.length ≤ W)
    (h : M.Step x a c c') : stpM M x a W (enc W c) (enc W c') = true := by
  simp only [stpM, dec_enc hc, dec_enc hc', Bool.or_eq_true]
  exact Or.inr h

/-! ### Paths and runs -/

theorem PathN.eq_of_zero {stp : List Bool → List Bool → Bool} {E : ℕ} {u v : List Bool}
    (h : PathN stp E 0 u v) : u = v := by
  obtain ⟨f, h0, hn, -, -⟩ := h
  rw [← h0, hn]

theorem PathN.step_of_one {stp : List Bool → List Bool → Bool} {E : ℕ} {u v : List Bool}
    (h : PathN stp E 1 u v) : stp u v = true := by
  obtain ⟨f, h0, h1, -, hstep⟩ := h
  have := hstep 0 (by omega)
  rwa [h0, show (0 : ℕ) + 1 = 1 from rfl, h1] at this

/-- **A path of nodes is a run of the machine** on the decoded configurations. -/
theorem reach_of_pathN : ∀ (n : ℕ) {u v : List Bool},
    PathN (stpM M x a W) (2 * W) n u v → M.Reach x a (dec W u) (dec W v) := by
  intro n
  induction n with
  | zero =>
    intro u v h
    rw [h.eq_of_zero]
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro u v h
    obtain ⟨w, h₁, h₂⟩ := h.split
    have hstep := h₂.step_of_one
    refine Relation.ReflTransGen.trans (ih h₁) ?_
    rcases Bool.or_eq_true_iff.1 hstep with heq | hs
    · rw [of_decide_eq_true heq]
    · exact Relation.ReflTransGen.single hs

/-- **A run of the machine is a path of nodes** on the encoded configurations. -/
theorem exists_pathN_of_reach {c₀ c : List Bool} (h₀ : c₀.length ≤ W)
    (hb : ∀ d d', M.Step x a d d' → d'.length ≤ W) (h : M.Reach x a c₀ c) :
    ∃ n, PathN (stpM M x a W) (2 * W) n (enc W c₀) (enc W c) := by
  induction h with
  | refl => exact ⟨0, pathN_zero rfl (length_enc h₀)⟩
  | @tail d d' hreach hstep ih =>
    obtain ⟨n, hn⟩ := ih
    have hd : d.length ≤ W := by
      induction hreach with
      | refl => exact h₀
      | tail _ hs _ => exact hb _ _ hs
    have hd' : d'.length ≤ W := hb _ _ hstep
    exact ⟨n + 1, hn.trans (pathN_one (stpM_of_step hd hd' hstep) (length_enc hd)
      (length_enc hd'))⟩

/-! ### Acceptance as the recursion -/

/-- **Acceptance is the halving recursion** between two nodes of width `2 * W`, provided `W`
bounds the configurations the machine may visit. -/
theorem accepts_iff (M : NSpace) (x a : List Bool) {W : ℕ}
    (hW : M.bound.eval (x.length + a.length) ≤ W) :
    M.Accepts x a ↔ ∃ e₀ e : List Bool, e₀.length = 2 * W ∧ e.length = 2 * W ∧
      M.initB [dec W e₀, x, a] = true ∧ M.accB [dec W e, x, a] = true ∧
      Rec (stpM M x a W) (2 * W) (2 * W) e₀ e = true := by
  have hb : ∀ d d', M.Step x a d d' → d'.length ≤ W := fun d d' hs =>
    le_trans (M.stepB_length _ _ _ _ hs) hW
  constructor
  · rintro ⟨c₀, c, hinit, hreach, hacc⟩
    have h₀ : c₀.length ≤ W := le_trans (M.initB_length _ _ _ hinit) hW
    have hc : c.length ≤ W := le_trans (M.length_le_of_reach hinit hreach) hW
    obtain ⟨n, hpath⟩ := exists_pathN_of_reach h₀ hb hreach
    obtain ⟨m, hm, hpath'⟩ := exists_pathN_lt_two_pow hpath
    refine ⟨enc W c₀, enc W c, length_enc h₀, length_enc hc, ?_, ?_, ?_⟩
    · rwa [dec_enc h₀]
    · rwa [dec_enc hc]
    · refine (rec_eq_true_iff (2 * W) _ _ (length_enc h₀) (length_enc hc)).2 ?_
      exact hpath'.mono (fun y _ => stpM_refl y) (le_of_lt hm)
  · rintro ⟨e₀, e, he₀, he, hinit, hacc, hrec⟩
    exact ⟨dec W e₀, dec W e, hinit,
      reach_of_pathN _ ((rec_eq_true_iff (2 * W) _ _ he₀ he).1 hrec), hacc⟩

end Savitch

end HTN
