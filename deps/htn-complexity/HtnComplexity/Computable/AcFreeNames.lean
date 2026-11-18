import HtnComplexity.Computable.AcSmall
/-!
# Fresh facts, actions and task names for the vocabulary-free wrapper

The compilation of a totally ordered problem into an acyclic one
(`HtnComplexity/Computable/AcSmall.lean`) compiles an *instance* description using the
vocabulary of the source domain: the initial state of `HTN.Syn.Ac.acInst facts q` lists one fact
per fact of the vocabulary and per memory cell, and its goal contains the closed-world part
`¬v⁰` for every vocabulary fact `v` outside the initial state of the source.  An instance
description does not know the vocabulary of the domain it will be used with, which is why the
cell `(TO-HTN, HTN-AC)` is proved there only for compilations *over a shared vocabulary*
(`HTN.Syn.CompSynVoc`).

This file is the first step of a construction that removes the vocabulary: the compiled domain —
which does know its vocabulary — performs the two jobs the compiled instance cannot, in two
extra phases put in front of and behind the body of the compiled initial task.  For that the
wrapper needs **fresh** facts, actions and compound task names, and this file provides them
together with the freshness proofs.

* `HTN.Syn.AcFree.fLic u`, `HTN.Syn.AcFree.fRes u` — the two fact families the compiled instance
  writes: the *licence* of a source fact (it holds initially in the source) and its *receipt*
  (its goal obligation is discharged).
* `HTN.Syn.AcFree.aBoot`, `…aSkip`, `…aChkN v`, `…aChkP v`, `…aEarn v` — the actions of the two
  phases.
* `HTN.Syn.AcFree.tPost`, `…tChk v`, `…tEarn v` — the compound task names of the second phase.

Freshness is proved against the *shape* of the numbering of
`HtnComplexity/Computable/AcNum.lean`: `HTN.Syn.AcFree.BaseFact`,
`HTN.Syn.AcFree.BaseAct` and `HTN.Syn.AcFree.BaseTask` are the residue conditions that every
fact, action and compound task name of the compiled acyclic domain satisfies, and none of the
new names does.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac

/-! ### The new facts -/

/-- **The licence of a source fact**: the compiled instance lists `fLic u` for every fact `u` of
the initial state of the source. -/
def fLic (u : ℕ) : ℕ := 6 * (u + 2) + 1

/-- **The receipt of a source fact**: the compiled instance lists `fRes u` for every fact `u` of
its initial state, and demands it for every goal fact.  The compiled domain deletes the receipts
of the facts of its own vocabulary, which therefore have to be earned again. -/
def fRes (u : ℕ) : ℕ := 6 * (u + 2) + 2

/-! ### The new actions -/

/-- The action establishing the initial state of the compiled problem. -/
def aBoot : ℕ := 13 * 2 + 8

/-- The action doing nothing. -/
def aSkip : ℕ := 13 * 3 + 8

/-- The action checking that the guessed initial value of `v` is *false*. -/
def aChkN (v : ℕ) : ℕ := 13 * (v + 2) + 9

/-- The action checking that the guessed initial value of `v` is *true* and licensed. -/
def aChkP (v : ℕ) : ℕ := 13 * (v + 2) + 10

/-- The action earning the receipt of `v` from its value in the final state. -/
def aEarn (v : ℕ) : ℕ := 13 * (v + 2) + 11

/-! ### The new compound task names -/

/-- The compound task of the verification phase. -/
def tPost : ℕ := 13 * 1 + 7

/-- The compound task checking the guessed initial value of `v`. -/
def tChk (v : ℕ) : ℕ := 13 * (v + 1) + 8

/-- The compound task earning the receipt of `v`. -/
def tEarn (v : ℕ) : ℕ := 13 * (v + 1) + 9

/-! ### The shapes of the numbering of the compiled acyclic domain -/

/-- **The shape of a fact of the compiled acyclic domain.**  Every fact its actions mention is
`key₀ = 0`, one of the four keys `1, 2, 7, 8`, or a number that is `3`, `4` or `5` modulo `6`
(a state fact `v^i`, its negation, or a stored task name). -/
def BaseFact (n : ℕ) : Prop :=
  n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 7 ∨ n = 8 ∨ 3 ≤ n % 6

/-- **The shape of an action of the compiled acyclic domain.** -/
def BaseAct (n : ℕ) : Prop := n % 13 ≤ 5 ∨ n % 13 = 12 ∨ n ≤ 24

/-- **The shape of a compound task name of the compiled acyclic domain.** -/
def BaseTask (n : ℕ) : Prop := n % 13 ≤ 5 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n ≤ 12

/-! ### The base shapes -/

lemma baseFact_fKey0 : BaseFact fKey0 := Or.inl rfl

lemma baseFact_fKey1 {x : ℕ} (hx : x ≤ 1) : BaseFact (fKey1 x) := by
  interval_cases x <;> simp [BaseFact, fKey1]

lemma baseFact_fKey2 {x : ℕ} (hx : x ≤ 1) : BaseFact (fKey2 x) := by
  interval_cases x <;> simp [BaseFact, fKey2]

lemma baseFact_fPos (v i : ℕ) : BaseFact (fPos v i) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
  simp [fPos]

lemma baseFact_fNeg (v i : ℕ) : BaseFact (fNeg v i) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
  simp [fNeg]

lemma baseFact_fTask (t : ℕ) : BaseFact (fTask t) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
  simp [fTask]

/-! ### The new names are fresh -/

lemma not_baseFact_fLic (u : ℕ) : ¬ BaseFact (fLic u) := by
  simp only [BaseFact, fLic, not_or, not_le]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  have : (6 * (u + 2) + 1) % 6 = 1 := by omega
  omega

lemma not_baseFact_fRes (u : ℕ) : ¬ BaseFact (fRes u) := by
  simp only [BaseFact, fRes, not_or, not_le]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  have : (6 * (u + 2) + 2) % 6 = 2 := by omega
  omega

lemma fLic_ne_fRes (u w : ℕ) : fLic u ≠ fRes w := by
  simp only [fLic, fRes]
  omega

lemma fLic_injective : Function.Injective fLic := by
  intro u w h
  simp only [fLic] at h
  omega

lemma fRes_injective : Function.Injective fRes := by
  intro u w h
  simp only [fRes] at h
  omega

lemma not_baseAct_aBoot : ¬ BaseAct aBoot := by
  simp only [BaseAct, aBoot, not_or, not_le]
  refine ⟨?_, ?_, by omega⟩ <;> norm_num

lemma not_baseAct_aSkip : ¬ BaseAct aSkip := by
  simp only [BaseAct, aSkip, not_or, not_le]
  refine ⟨?_, ?_, by omega⟩ <;> norm_num

lemma not_baseAct_aChkN (v : ℕ) : ¬ BaseAct (aChkN v) := by
  simp only [BaseAct, aChkN, not_or, not_le]
  have h : (13 * (v + 2) + 9) % 13 = 9 := by omega
  refine ⟨by omega, by omega, by omega⟩

lemma not_baseAct_aChkP (v : ℕ) : ¬ BaseAct (aChkP v) := by
  simp only [BaseAct, aChkP, not_or, not_le]
  have h : (13 * (v + 2) + 10) % 13 = 10 := by omega
  refine ⟨by omega, by omega, by omega⟩

lemma not_baseAct_aEarn (v : ℕ) : ¬ BaseAct (aEarn v) := by
  simp only [BaseAct, aEarn, not_or, not_le]
  have h : (13 * (v + 2) + 11) % 13 = 11 := by omega
  refine ⟨by omega, by omega, by omega⟩

lemma not_baseTask_tPost : ¬ BaseTask tPost := by
  simp only [BaseTask, tPost, not_or, not_le]
  refine ⟨by norm_num, by norm_num, by norm_num, by omega⟩

lemma not_baseTask_tChk (v : ℕ) : ¬ BaseTask (tChk v) := by
  simp only [BaseTask, tChk, not_or, not_le]
  have h : (13 * (v + 1) + 8) % 13 = 8 := by omega
  refine ⟨by omega, by omega, by omega, by omega⟩

lemma not_baseTask_tEarn (v : ℕ) : ¬ BaseTask (tEarn v) := by
  simp only [BaseTask, tEarn, not_or, not_le]
  have h : (13 * (v + 1) + 9) % 13 = 9 := by omega
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ### The new names are pairwise distinct -/

lemma aChkN_injective : Function.Injective aChkN := fun u w h => by
  simp only [aChkN] at h; omega

lemma aChkP_injective : Function.Injective aChkP := fun u w h => by
  simp only [aChkP] at h; omega

lemma aEarn_injective : Function.Injective aEarn := fun u w h => by
  simp only [aEarn] at h; omega

lemma tChk_injective : Function.Injective tChk := fun u w h => by
  simp only [tChk] at h; omega

lemma tEarn_injective : Function.Injective tEarn := fun u w h => by
  simp only [tEarn] at h; omega

lemma aBoot_ne_aSkip : aBoot ≠ aSkip := by simp [aBoot, aSkip]

lemma aBoot_ne_aChkN (v : ℕ) : aBoot ≠ aChkN v := by
  simp only [aBoot, aChkN]; omega

lemma aBoot_ne_aChkP (v : ℕ) : aBoot ≠ aChkP v := by
  simp only [aBoot, aChkP]; omega

lemma aBoot_ne_aEarn (v : ℕ) : aBoot ≠ aEarn v := by
  simp only [aBoot, aEarn]; omega

lemma aSkip_ne_aChkN (v : ℕ) : aSkip ≠ aChkN v := by
  simp only [aSkip, aChkN]; omega

lemma aSkip_ne_aChkP (v : ℕ) : aSkip ≠ aChkP v := by
  simp only [aSkip, aChkP]; omega

lemma aSkip_ne_aEarn (v : ℕ) : aSkip ≠ aEarn v := by
  simp only [aSkip, aEarn]; omega

lemma aChkN_ne_aChkP (v w : ℕ) : aChkN v ≠ aChkP w := by
  simp only [aChkN, aChkP]; omega

lemma aChkN_ne_aEarn (v w : ℕ) : aChkN v ≠ aEarn w := by
  simp only [aChkN, aEarn]; omega

lemma aChkP_ne_aEarn (v w : ℕ) : aChkP v ≠ aEarn w := by
  simp only [aChkP, aEarn]; omega

lemma tPost_ne_tChk (v : ℕ) : tPost ≠ tChk v := by
  simp only [tPost, tChk]; omega

lemma tPost_ne_tEarn (v : ℕ) : tPost ≠ tEarn v := by
  simp only [tPost, tEarn]; omega

lemma tChk_ne_tEarn (v w : ℕ) : tChk v ≠ tEarn w := by
  simp only [tChk, tEarn]; omega

end AcFree

end Syn

end HTN
