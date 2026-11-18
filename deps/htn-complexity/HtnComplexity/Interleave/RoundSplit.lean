import HtnComplexity.TMEnc.TMEncFixSchedule
/-!
# Cutting an interleaving along the rounds of one of its components

The soundness direction of the simulation argument has to *extract* a round (cell) decomposition
from an arbitrary plan: the plan is an interleaving of several streams, one of which — the tape —
is given as a stream of rounds, and the plan has to be cut into the corresponding rounds.  This
is the converse of `HTN.roundStream_sum`, and this file provides it:

* `HTN.Interleave.split_right` — an interleaving with a concatenation splits into two
  interleavings;
* `HTN.interleave_roundStream_split` — **an interleaving with a stream of `R` rounds is a stream
  of `R` rounds**, each round of the result being an interleaving of the corresponding rounds of
  the two components (up to a trailing rest, which is empty as soon as there is at least one
  round).
-/

namespace HTN

variable {α : Type}

namespace Interleave

/-- **An interleaving with a concatenation splits.**  If `zs` interleaves `xs` with `y₁ ++ y₂`,
then both `xs` and `zs` split accordingly. -/
lemma split_right : ∀ {xs y zs : List α}, Interleave xs y zs → ∀ {y₁ y₂ : List α},
    y = y₁ ++ y₂ → ∃ x₁ x₂ z₁ z₂, xs = x₁ ++ x₂ ∧ zs = z₁ ++ z₂ ∧
      Interleave x₁ y₁ z₁ ∧ Interleave x₂ y₂ z₂ := by
  intro xs y zs h
  induction h with
  | nil =>
      intro y₁ y₂ hy
      have hy₁ : y₁ = [] := by
        rcases List.append_eq_nil_iff.1 hy.symm with ⟨h₁, -⟩
        exact h₁
      have hy₂ : y₂ = [] := by
        rcases List.append_eq_nil_iff.1 hy.symm with ⟨-, h₂⟩
        exact h₂
      subst hy₁; subst hy₂
      exact ⟨[], [], [], [], rfl, rfl, Interleave.nil, Interleave.nil⟩
  | @left xs' ys' zs' a _ ih =>
      intro y₁ y₂ hy
      obtain ⟨x₁, x₂, z₁, z₂, hx, hz, h₁, h₂⟩ := ih hy
      exact ⟨a :: x₁, x₂, a :: z₁, z₂, by rw [hx]; rfl, by rw [hz]; rfl,
        Interleave.left a h₁, h₂⟩
  | @right xs' ys' zs' a hrec ih =>
      intro y₁ y₂ hy
      cases y₁ with
      | nil =>
          refine ⟨[], xs', [], a :: zs', rfl, rfl, Interleave.nil, ?_⟩
          simpa [hy] using Interleave.right a hrec
      | cons b y₁ =>
          have hb : b = a := by simpa using (List.cons.inj hy).1.symm
          have hys : ys' = y₁ ++ y₂ := by simpa using (List.cons.inj hy).2
          subst hb
          obtain ⟨x₁, x₂, z₁, z₂, hx, hz, h₁, h₂⟩ := ih hys
          exact ⟨x₁, x₂, b :: z₁, z₂, hx, by rw [hz]; rfl, Interleave.right b h₁, h₂⟩

end Interleave

/-- **An interleaving with a stream of rounds is a stream of rounds.**  If `z` interleaves `x`
with the stream `roundStream R s`, then `x` and `z` are themselves streams of `R` rounds — up to
a common trailing rest, which occurs only for `R = 0` — and round by round the rounds of `z`
interleave those of `x` with those of `s`. -/
lemma interleave_roundStream_split : ∀ (R : ℕ) {x z : List α} {s : ℕ → List α},
    Interleave x (roundStream R s) z →
    ∃ (xs zs : ℕ → List α) (rest : List α),
      x = roundStream R xs ++ rest ∧ z = roundStream R zs ++ rest ∧
        (0 < R → rest = []) ∧ ∀ r < R, Interleave (xs r) (s r) (zs r) := by
  intro R
  induction R with
  | zero =>
      intro x z s h
      refine ⟨fun _ => [], fun _ => [], x, by simp, ?_, by omega, by omega⟩
      simpa using h.eq_of_nil_right' rfl
  | succ R ih =>
      intro x z s h
      rw [roundStream_succ] at h
      obtain ⟨x₁, x₂, z₁, z₂, rfl, rfl, h₁, h₂⟩ := h.split_right rfl
      obtain ⟨xs, zs, rest, hx₁, hz₁, -, hall⟩ := ih h₁
      classical
      have hcx : (roundStream R fun r => if r = R then rest ++ x₂ else xs r) =
          roundStream R xs := roundStream_congr fun r hr => if_neg (Nat.ne_of_lt hr)
      have hcz : (roundStream R fun r => if r = R then rest ++ z₂ else zs r) =
          roundStream R zs := roundStream_congr fun r hr => if_neg (Nat.ne_of_lt hr)
      refine ⟨fun r => if r = R then rest ++ x₂ else xs r,
        fun r => if r = R then rest ++ z₂ else zs r, [], ?_, ?_, fun _ => rfl, ?_⟩
      · rw [roundStream_succ, hcx, hx₁]
        simp
      · rw [roundStream_succ, hcz, hz₁]
        simp
      · intro r hr
        rcases Nat.lt_or_ge r R with hrR | hrR
        · simpa [Nat.ne_of_lt hrR] using hall r hrR
        · have hrR' : r = R := by omega
          subst hrR'
          simpa using (Interleave.nil_right rest).append_append h₂

/-- **An interleaving with a non-empty stream of rounds is a stream of rounds.** -/
lemma interleave_roundStream_split_pos {R : ℕ} (hR : 0 < R) {x z : List α} {s : ℕ → List α}
    (h : Interleave x (roundStream R s) z) :
    ∃ xs zs : ℕ → List α, x = roundStream R xs ∧ z = roundStream R zs ∧
      ∀ r < R, Interleave (xs r) (s r) (zs r) := by
  obtain ⟨xs, zs, rest, hx, hz, hrest, hall⟩ := interleave_roundStream_split R h
  rw [hrest hR, List.append_nil] at hx hz
  exact ⟨xs, zs, hx, hz, hall⟩

end HTN
