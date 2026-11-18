import ComplexityTheory.Collapse.Code
import ComplexityTheory.Complexity.Basic
/-!
# Alternating machines with a polynomial memory

The source side of the Karp–Lipton cells is *alternating computation in polynomial space*: the
hardness families of `HtnComplexity/Complexity/RecMemUniform.lean` encode a machine whose
configurations are a control state together with polynomially many memory bits, whose branching
is existential or universal, and on which no bound is put on the number of steps.  By
Chandra–Kozen–Stockmeyer that class is `EXPTIME`; the identification is classical and is not
formalised here.

This file gives the model in the shape the advice-elimination argument needs — configurations
are bit strings of a fixed width, the three tests are predicates of Cobham's class:

* `HTN.PSpace.ASpace` — the machine;
* `HTN.PSpace.ASpace.accWithin` — the acceptance predicate *with a step counter*: the least
  fixpoint read off in `t` rounds.  The counter is what makes the predicate checkable: a claimed
  table of values which satisfies the local rule at every `(c, t)` is, by induction on `t`, the
  real one, whereas the rule alone has many solutions;
* `HTN.PSpace.ASpace.L` — the language, acceptance within `2 ^ (w + 1) - 1` rounds, the largest
  counter that fits into `w + 1` bits;
* `HTN.PSpace.ASpace.confLang` — the language of *configuration questions*, the auxiliary
  language the collapse argument applies its hypothesis to;
* `HTN.PSpace.InAPSpace` — the class.
-/

namespace HTN

namespace PSpace

open PTime

namespace ASpace

variable (M : ASpace)

@[simp] theorem accWithin_zero (x c : List Bool) : M.accWithin x 0 c = M.accB [c, x] := by
  rw [accWithin]

theorem accWithin_succ (x : List Bool) (t : ℕ) (c : List Bool) :
    M.accWithin x (t + 1) c = (M.accB [c, x] ||
      (if M.univB [c, x] = true then
          allLenB (M.w x) (fun c' => !M.stepB [c', c, x] || M.accWithin x t c')
        else anyLen (M.w x) (fun c' => M.stepB [c', c, x] && M.accWithin x t c'))) := by
  rw [accWithin]

/-- One more round never hurts. -/
theorem accWithin_succ_of (x : List Bool) : ∀ (t : ℕ) (c : List Bool),
    M.accWithin x t c = true → M.accWithin x (t + 1) c = true := by
  intro t
  induction t with
  | zero =>
    intro c hc
    rw [accWithin_succ]
    simp only [accWithin_zero] at hc
    simp [hc]
  | succ t ih =>
    intro c hc
    rw [accWithin_succ]
    rw [accWithin_succ] at hc
    rcases Bool.or_eq_true_iff.1 hc with hacc | hrest
    · simp [hacc]
    · refine Bool.or_eq_true_iff.2 (Or.inr ?_)
      by_cases hu : M.univB [c, x] = true
      · rw [if_pos hu] at hrest ⊢
        rw [allLenB_eq_true] at hrest ⊢
        intro c' hc'
        have h := hrest c' hc'
        rcases Bool.or_eq_true_iff.1 h with hstep | hacc'
        · simp [hstep]
        · simp [ih c' hacc']
      · rw [if_neg hu] at hrest ⊢
        rw [anyLen_eq_true] at hrest ⊢
        obtain ⟨c', hlen, hc'⟩ := hrest
        refine ⟨c', hlen, ?_⟩
        rcases Bool.and_eq_true_iff.1 hc' with ⟨hstep, hacc'⟩
        simp [hstep, ih c' hacc']

theorem accWithin_mono (x c : List Bool) {t t' : ℕ} (h : t ≤ t')
    (hc : M.accWithin x t c = true) : M.accWithin x t' c = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simpa using hc
  | succ d ih =>
    rw [show t + (d + 1) = (t + d) + 1 by omega]
    exact M.accWithin_succ_of x (t + d) c ih

/-- **The language of configuration questions**: the codes of triples `(c, t, x)` such that the
configuration `c` accepts within `t` rounds on `x`. -/
def confLang (z : List Bool) : Prop :=
  ∃ x c t : List Bool, c.length = M.w x ∧ t.length = M.w x + 1 ∧
    z = encS (ones (M.w x)) c t x ∧ M.accWithin x (val t) c = true

/-- **What a configuration question asks.** -/
theorem confLang_encS {x c t : List Bool} (hc : c.length = M.w x) (ht : t.length = M.w x + 1) :
    M.confLang (encS (ones (M.w x)) c t x) ↔ M.accWithin x (val t) c = true := by
  constructor
  · rintro ⟨x', c', t', hc', ht', hz, hacc⟩
    obtain ⟨-, rfl, rfl, rfl⟩ := encS_inj hc' ht' hc ht hz.symm
    exact hacc
  · intro h
    exact ⟨x, c, t, hc, ht, rfl, h⟩

/-- The length of a configuration question depends on the length of the input only. -/
theorem length_encS_conf {x c t : List Bool} (hc : c.length = M.w x) (ht : t.length = M.w x + 1) :
    (encS (ones (M.w x)) c t x).length = 3 * M.w x + 2 + x.length := by
  rw [length_encS, length_ones, hc, ht]
  omega

end ASpace

end PSpace

end HTN
