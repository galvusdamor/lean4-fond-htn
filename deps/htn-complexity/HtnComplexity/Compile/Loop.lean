import HtnComplexity.Compile.Round
/-!
# The loop of the compiled program is the acceptance of the machine

`HtnComplexity/Compile/Round.lean` describes one round of the loop.  This file iterates it:
from the head of the loop, with the memory carrying a configuration `c` of the machine's width,
the program accepts exactly when the machine accepts `c` within some number of rounds
(`HTN.Compile.Sim.loop_iff`).

The two directions are proved separately — the first by induction on the number of rounds of the
machine, the second by strong induction on the fuel of `HtnComplexity/Compile/Fuel.lean`,
which is what makes the recursion on a computation of a program with a loop well-founded.
-/

namespace HTN

namespace Compile

namespace Sim

open Syn PSpace PTime

variable {S : Sim} {x : List Bool}

/-! ### Padding a configuration to a full guess -/

/-- The guessed bits standing for a configuration. -/
def padN (S : Sim) (c : List Bool) : List Bool := c ++ List.replicate (S.NN - c.length) false

theorem length_padN {c : List Bool} (h : c.length ≤ S.NN) : (S.padN c).length = S.NN := by
  rw [padN, List.length_append, List.length_replicate]
  omega

theorem gcfg_padN {c : List Bool} (h : c.length = S.M.w x) : S.gcfg x (S.padN c) = c := by
  rw [gcfg, padN, ← h, List.take_left]

/-! ### A uniform bound over a finite list of configurations -/

/-- A finite list of configurations that all accept eventually all accept within one number of
rounds. -/
theorem exists_common_bound (M : ASpace) (y : List Bool) :
    ∀ l : List (List Bool), (∀ c ∈ l, ∃ t, M.accWithin y t c = true) →
      ∃ t, ∀ c ∈ l, M.accWithin y t c = true := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons a l ih =>
      intro h
      obtain ⟨ta, hta⟩ := h a List.mem_cons_self
      obtain ⟨tl, htl⟩ := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
      refine ⟨max ta tl, fun c hc => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact M.accWithin_mono y c (le_max_left _ _) hta
      · exact M.accWithin_mono y c (le_max_right _ _) (htl c hc')

/-! ### The loop -/

/-- **The program accepts at the head of the loop whenever the machine accepts the
configuration within some number of rounds.** -/
theorem loop_intro (hx : x.length = S.n) :
    ∀ (t : ℕ) (c : List Bool), c.length = S.M.w x → S.M.accWithin x t c = true →
      ∀ μ : ℕ → Bool, S.MemOk x c μ → Acc S.lay.prog x S.lay.lL μ := by
  have hxn : x.length ≤ S.NN := le_trans (le_of_eq hx) n_le_NN
  have hw : S.M.w x ≤ S.NN := w_le_NN (le_of_eq hx)
  intro t
  induction t with
  | zero =>
      intro c hc hacc μ h
      rw [ASpace.accWithin_zero] at hacc
      exact round_acc hxn (by omega) h hacc
  | succ t ih =>
      intro c hc hacc μ h
      have hcn : c.length ≤ S.NN := by omega
      by_cases hab : S.M.accB [c, x] = true
      · exact round_acc hxn hcn h hab
      have hab' : S.M.accB [c, x] = false := by simpa using hab
      rw [ASpace.accWithin_succ, hab'] at hacc
      simp only [Bool.false_or] at hacc
      by_cases hu : S.M.univB [c, x] = true
      · rw [if_pos hu, allLenB_eq_true] at hacc
        refine round_all hxn hcn hw h hab' hu ?_
        intro bs hbs hst
        have hlen : (S.gcfg x bs).length = S.M.w x := length_gcfg hbs hw
        have := hacc (S.gcfg x bs) hlen
        rw [hst] at this
        simp only [Bool.not_true, Bool.false_or] at this
        exact ih (S.gcfg x bs) hlen this _ (memOk_mC hbs hw h)
      · rw [if_neg hu, anyLen_eq_true] at hacc
        obtain ⟨c', hc', hboth⟩ := hacc
        rw [Bool.and_eq_true] at hboth
        obtain ⟨hst, hrec⟩ := hboth
        have hc'n : c'.length ≤ S.NN := by omega
        have hbs : (S.padN c').length = S.NN := length_padN hc'n
        have hg : S.gcfg x (S.padN c') = c' := gcfg_padN hc'
        refine round_ex hxn hcn hw h hab' (by simpa using hu) hbs (by rw [hg]; exact hst) ?_
        have hmem := memOk_mC (bs := S.padN c') hbs hw h
        rw [hg] at hmem
        exact ih c' hc' hrec _ hmem

/-- **If the program accepts at the head of the loop then the machine accepts the configuration
within some number of rounds.** -/
theorem loop_elim (hx : x.length = S.n) :
    ∀ (k : ℕ) (c : List Bool) (μ : ℕ → Bool), c.length = S.M.w x → S.MemOk x c μ →
      AccN S.lay.prog x k S.lay.lL μ → ∃ t, S.M.accWithin x t c = true := by
  have hxn : x.length ≤ S.NN := le_trans (le_of_eq hx) n_le_NN
  have hw : S.M.w x ≤ S.NN := w_le_NN (le_of_eq hx)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro c μ hc h hacc
    have hcn : c.length ≤ S.NN := by omega
    rcases round_elim hxn hcn hw h hacc with hab | ⟨hu, bs, hbs, hst, k', hk', hacc'⟩ |
      ⟨hu, hall⟩
    · exact ⟨0, by rw [ASpace.accWithin_zero]; exact hab⟩
    · -- the existential case
      have hlen : (S.gcfg x bs).length = S.M.w x := length_gcfg hbs hw
      obtain ⟨t, ht⟩ := ih k' hk' (S.gcfg x bs) (mC S x μ bs) hlen (memOk_mC hbs hw h) hacc'
      refine ⟨t + 1, ?_⟩
      rw [ASpace.accWithin_succ, if_neg (by simp [hu])]
      refine Bool.or_eq_true_iff.2 (Or.inr ?_)
      rw [anyLen_eq_true]
      exact ⟨S.gcfg x bs, hlen, by rw [hst, ht]; rfl⟩
    · -- the universal case
      set l := (allLen (S.M.w x)).filter fun c' => S.M.stepB [c', c, x] with hl
      have hmem : ∀ c' ∈ l, ∃ t, S.M.accWithin x t c' = true := by
        intro c' hc'
        rw [hl, List.mem_filter, mem_allLen] at hc'
        obtain ⟨hlen, hst⟩ := hc'
        have hbs : (S.padN c').length = S.NN := length_padN (by omega)
        have hg : S.gcfg x (S.padN c') = c' := gcfg_padN hlen
        obtain ⟨k', hk', hacc'⟩ := hall (S.padN c') hbs (by rw [hg]; simpa using hst)
        have hmemC := memOk_mC (bs := S.padN c') hbs hw h
        rw [hg] at hmemC
        exact ih k' hk' c' (mC S x μ (S.padN c')) hlen hmemC hacc'
      obtain ⟨t, ht⟩ := exists_common_bound S.M x l hmem
      refine ⟨t + 1, ?_⟩
      rw [ASpace.accWithin_succ, if_pos hu]
      refine Bool.or_eq_true_iff.2 (Or.inr ?_)
      rw [allLenB_eq_true]
      intro c' hlen
      by_cases hst : S.M.stepB [c', c, x] = true
      · have : c' ∈ l := by
          rw [hl, List.mem_filter, mem_allLen]
          exact ⟨hlen, hst⟩
        rw [ht c' this]
        simp
      · simp [show S.M.stepB [c', c, x] = false by simpa using hst]

/-- **The loop of the compiled program is the acceptance of the machine.** -/
theorem loop_iff (hx : x.length = S.n) {c : List Bool} (hc : c.length = S.M.w x)
    {μ : ℕ → Bool} (h : S.MemOk x c μ) :
    Acc S.lay.prog x S.lay.lL μ ↔ ∃ t, S.M.accWithin x t c = true := by
  constructor
  · intro hacc
    obtain ⟨k, hk⟩ := acc_iff_exists_accN.1 hacc
    exact loop_elim hx k c μ hc h hk
  · rintro ⟨t, ht⟩
    exact loop_intro hx t c hc ht μ h

end Sim

end Compile

end HTN
