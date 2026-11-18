import HtnComplexity.Compile.Prog
/-!
# Acceptance of a program with a fuel

`HTN.Compile.Acc` is an inductive predicate, so a *derivation* of it is a well-founded object;
but a proof about a program with a **loop** has to recurse on that derivation, and a `Prop`
carries no measure one can recurse on.  This file adds the measure by hand: `HTN.Compile.AccN`
is acceptance *with a fuel*, a copy of `HTN.Compile.Acc` in which every rule but the accepting
one consumes one unit, and

    HTN.Compile.acc_iff_exists_accN : Acc P W pc μ ↔ ∃ k, AccN P W k pc μ.

The inversion lemmas come with the fuel strictly decreasing, which is what a loop invariant
is proved by induction on.
-/

namespace HTN

namespace Compile

open Syn

/-- **Acceptance of an alternating bit program with a fuel.** -/
inductive AccN (P : List Instr) (W : List Bool) : ℕ → ℕ → (ℕ → Bool) → Prop
  /-- The accepting instruction accepts, with no fuel. -/
  | acc {k pc : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iAcc) : AccN P W k pc μ
  /-- A `nand` writes and goes on. -/
  | nand {k pc i j d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iNand i j d)
      (h' : AccN P W k (pc + 1) (memUpd μ d (!(μ i && μ j)))) : AccN P W (k + 1) pc μ
  /-- A read writes the bit of the word and goes on. -/
  | rdIn {k pc p d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iRdIn p d)
      (h' : AccN P W k (pc + 1) (memUpd μ d (inBit W p))) : AccN P W (k + 1) pc μ
  /-- A taken branch. -/
  | brT {k pc i t : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iBrIf i t) (hi : μ i = true)
      (h' : AccN P W k t μ) : AccN P W (k + 1) pc μ
  /-- A branch that is not taken. -/
  | brF {k pc i t : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iBrIf i t) (hi : μ i = false)
      (h' : AccN P W k (pc + 1) μ) : AccN P W (k + 1) pc μ
  /-- A jump. -/
  | jmp {k pc t : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iJmp t) (h' : AccN P W k t μ) :
      AccN P W (k + 1) pc μ
  /-- An existential choice. -/
  | ex {k pc d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iEx d) (b : Bool)
      (h' : AccN P W k (pc + 1) (memUpd μ d b)) : AccN P W (k + 1) pc μ
  /-- A universal choice. -/
  | all {k pc d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iAll d)
      (h0 : AccN P W k (pc + 1) (memUpd μ d false))
      (h1 : AccN P W k (pc + 1) (memUpd μ d true)) : AccN P W (k + 1) pc μ
  /-- Clearing a bit. -/
  | set0 {k pc d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iSet0 d)
      (h' : AccN P W k (pc + 1) (memUpd μ d false)) : AccN P W (k + 1) pc μ
  /-- Setting a bit. -/
  | set1 {k pc d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iSet1 d)
      (h' : AccN P W k (pc + 1) (memUpd μ d true)) : AccN P W (k + 1) pc μ
  /-- Copying a bit. -/
  | copy {k pc s d : ℕ} {μ : ℕ → Bool} (h : P.getI pc = iCopy s d)
      (h' : AccN P W k (pc + 1) (memUpd μ d (μ s))) : AccN P W (k + 1) pc μ

namespace AccN

variable {P : List Instr} {W : List Bool} {k k' pc : ℕ} {μ : ℕ → Bool}

/-- More fuel never hurts. -/
theorem mono (h : AccN P W k pc μ) : ∀ {m}, k ≤ m → AccN P W m pc μ := by
  induction h with
  | acc h => exact fun _ => AccN.acc h
  | nand h _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.nand h (ih (by omega))
  | rdIn h _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.rdIn h (ih (by omega))
  | brT h hi _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.brT h hi (ih (by omega))
  | brF h hi _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.brF h hi (ih (by omega))
  | jmp h _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.jmp h (ih (by omega))
  | ex h b _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.ex h b (ih (by omega))
  | all h _ _ ih0 ih1 =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.all h (ih0 (by omega)) (ih1 (by omega))
  | set0 h _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.set0 h (ih (by omega))
  | set1 h _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.set1 h (ih (by omega))
  | copy h _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact AccN.copy h (ih (by omega))

/-- Forgetting the fuel. -/
theorem toAcc (h : AccN P W k pc μ) : Acc P W pc μ := by
  induction h with
  | acc h => exact Acc.acc h
  | nand h _ ih => exact Acc.nand h ih
  | rdIn h _ ih => exact Acc.rdIn h ih
  | brT h hi _ ih => exact Acc.brT h hi ih
  | brF h hi _ ih => exact Acc.brF h hi ih
  | jmp h _ ih => exact Acc.jmp h ih
  | ex h b _ ih => exact Acc.ex h b ih
  | all h _ _ ih0 ih1 => exact Acc.all h ih0 ih1
  | set0 h _ ih => exact Acc.set0 h ih
  | set1 h _ ih => exact Acc.set1 h ih
  | copy h _ ih => exact Acc.copy h ih

end AccN

/-- **Acceptance is acceptance with some fuel.** -/
theorem acc_iff_exists_accN {P : List Instr} {W : List Bool} {pc : ℕ} {μ : ℕ → Bool} :
    Acc P W pc μ ↔ ∃ k, AccN P W k pc μ := by
  constructor
  · intro h
    induction h with
    | acc h => exact ⟨0, AccN.acc h⟩
    | nand h _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.nand h hk⟩
    | rdIn h _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.rdIn h hk⟩
    | brT h hi _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.brT h hi hk⟩
    | brF h hi _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.brF h hi hk⟩
    | jmp h _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.jmp h hk⟩
    | ex h b _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.ex h b hk⟩
    | all h _ _ ih0 ih1 =>
        obtain ⟨k0, hk0⟩ := ih0
        obtain ⟨k1, hk1⟩ := ih1
        exact ⟨max k0 k1 + 1, AccN.all h (hk0.mono (le_max_left _ _)) (hk1.mono (le_max_right _ _))⟩
    | set0 h _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.set0 h hk⟩
    | set1 h _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.set1 h hk⟩
    | copy h _ ih => exact ih.elim fun k hk => ⟨k + 1, AccN.copy h hk⟩
  · rintro ⟨k, hk⟩
    exact hk.toAcc

/-! ### Inverting the fuelled semantics

Every rule but the accepting one consumes fuel, so each inversion lemma hands back a strictly
smaller fuel — which is what makes an induction on the fuel possible. -/

section Inversion

variable {P : List Instr} {W : List Bool} {k pc i j d p s t : ℕ} {μ : ℕ → Bool}

/-- A `nand`. -/
theorem accN_nand (hacc : AccN P W k pc μ) (h : P.getI pc = iNand i j d) :
    ∃ k' < k, AccN P W k' (pc + 1) (memUpd μ d (!(μ i && μ j))) := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iNand, iAcc] at h'
  | nand h' h'' =>
      rw [h] at h'
      simp only [iNand, Prod.mk.injEq] at h'
      obtain ⟨-, rfl, rfl, rfl⟩ := h'
      exact ⟨_, by omega, h''⟩
  | rdIn h' _ => rw [h] at h'; simp [iNand, iRdIn] at h'
  | brT h' _ _ => rw [h] at h'; simp [iNand, iBrIf] at h'
  | brF h' _ _ => rw [h] at h'; simp [iNand, iBrIf] at h'
  | jmp h' _ => rw [h] at h'; simp [iNand, iJmp] at h'
  | ex h' _ _ => rw [h] at h'; simp [iNand, iEx] at h'
  | all h' _ _ => rw [h] at h'; simp [iNand, iAll] at h'
  | set0 h' _ => rw [h] at h'; simp [iNand, iSet0] at h'
  | set1 h' _ => rw [h] at h'; simp [iNand, iSet1] at h'
  | copy h' _ => rw [h] at h'; simp [iNand, iCopy] at h'

/-- A read of the input word. -/
theorem accN_rdIn (hacc : AccN P W k pc μ) (h : P.getI pc = iRdIn p d) :
    ∃ k' < k, AccN P W k' (pc + 1) (memUpd μ d (inBit W p)) := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iRdIn, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iRdIn, iNand] at h'
  | rdIn h' h'' =>
      rw [h] at h'
      simp only [iRdIn, Prod.mk.injEq] at h'
      obtain ⟨-, rfl, -, rfl⟩ := h'
      exact ⟨_, by omega, h''⟩
  | brT h' _ _ => rw [h] at h'; simp [iRdIn, iBrIf] at h'
  | brF h' _ _ => rw [h] at h'; simp [iRdIn, iBrIf] at h'
  | jmp h' _ => rw [h] at h'; simp [iRdIn, iJmp] at h'
  | ex h' _ _ => rw [h] at h'; simp [iRdIn, iEx] at h'
  | all h' _ _ => rw [h] at h'; simp [iRdIn, iAll] at h'
  | set0 h' _ => rw [h] at h'; simp [iRdIn, iSet0] at h'
  | set1 h' _ => rw [h] at h'; simp [iRdIn, iSet1] at h'
  | copy h' _ => rw [h] at h'; simp [iRdIn, iCopy] at h'

/-- Copying a bit. -/
theorem accN_copy (hacc : AccN P W k pc μ) (h : P.getI pc = iCopy s d) :
    ∃ k' < k, AccN P W k' (pc + 1) (memUpd μ d (μ s)) := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iCopy, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iCopy, iNand] at h'
  | rdIn h' _ => rw [h] at h'; simp [iCopy, iRdIn] at h'
  | brT h' _ _ => rw [h] at h'; simp [iCopy, iBrIf] at h'
  | brF h' _ _ => rw [h] at h'; simp [iCopy, iBrIf] at h'
  | jmp h' _ => rw [h] at h'; simp [iCopy, iJmp] at h'
  | ex h' _ _ => rw [h] at h'; simp [iCopy, iEx] at h'
  | all h' _ _ => rw [h] at h'; simp [iCopy, iAll] at h'
  | set0 h' _ => rw [h] at h'; simp [iCopy, iSet0] at h'
  | set1 h' _ => rw [h] at h'; simp [iCopy, iSet1] at h'
  | copy h' h'' =>
      rw [h] at h'
      simp only [iCopy, Prod.mk.injEq] at h'
      obtain ⟨-, rfl, -, rfl⟩ := h'
      exact ⟨_, by omega, h''⟩

/-- Clearing a bit. -/
theorem accN_set0 (hacc : AccN P W k pc μ) (h : P.getI pc = iSet0 d) :
    ∃ k' < k, AccN P W k' (pc + 1) (memUpd μ d false) := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iSet0, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iSet0, iNand] at h'
  | rdIn h' _ => rw [h] at h'; simp [iSet0, iRdIn] at h'
  | brT h' _ _ => rw [h] at h'; simp [iSet0, iBrIf] at h'
  | brF h' _ _ => rw [h] at h'; simp [iSet0, iBrIf] at h'
  | jmp h' _ => rw [h] at h'; simp [iSet0, iJmp] at h'
  | ex h' _ _ => rw [h] at h'; simp [iSet0, iEx] at h'
  | all h' _ _ => rw [h] at h'; simp [iSet0, iAll] at h'
  | set0 h' h'' =>
      rw [h] at h'
      simp only [iSet0, Prod.mk.injEq] at h'
      obtain ⟨-, -, -, rfl⟩ := h'
      exact ⟨_, by omega, h''⟩
  | set1 h' _ => rw [h] at h'; simp [iSet0, iSet1] at h'
  | copy h' _ => rw [h] at h'; simp [iSet0, iCopy] at h'

/-- Setting a bit. -/
theorem accN_set1 (hacc : AccN P W k pc μ) (h : P.getI pc = iSet1 d) :
    ∃ k' < k, AccN P W k' (pc + 1) (memUpd μ d true) := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iSet1, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iSet1, iNand] at h'
  | rdIn h' _ => rw [h] at h'; simp [iSet1, iRdIn] at h'
  | brT h' _ _ => rw [h] at h'; simp [iSet1, iBrIf] at h'
  | brF h' _ _ => rw [h] at h'; simp [iSet1, iBrIf] at h'
  | jmp h' _ => rw [h] at h'; simp [iSet1, iJmp] at h'
  | ex h' _ _ => rw [h] at h'; simp [iSet1, iEx] at h'
  | all h' _ _ => rw [h] at h'; simp [iSet1, iAll] at h'
  | set0 h' _ => rw [h] at h'; simp [iSet1, iSet0] at h'
  | set1 h' h'' =>
      rw [h] at h'
      simp only [iSet1, Prod.mk.injEq] at h'
      obtain ⟨-, -, -, rfl⟩ := h'
      exact ⟨_, by omega, h''⟩
  | copy h' _ => rw [h] at h'; simp [iSet1, iCopy] at h'

/-- A branch that is taken. -/
theorem accN_brIf_true (hacc : AccN P W k pc μ) (h : P.getI pc = iBrIf i t) (hi : μ i = true) :
    ∃ k' < k, AccN P W k' t μ := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iBrIf, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iBrIf, iNand] at h'
  | rdIn h' _ => rw [h] at h'; simp [iBrIf, iRdIn] at h'
  | brT h' hi' h'' =>
      rw [h] at h'
      simp only [iBrIf, Prod.mk.injEq] at h'
      obtain ⟨-, rfl, rfl, -⟩ := h'
      exact ⟨_, by omega, h''⟩
  | brF h' hi' h'' =>
      rw [h] at h'
      simp only [iBrIf, Prod.mk.injEq] at h'
      obtain ⟨-, rfl, rfl, -⟩ := h'
      rw [hi] at hi'
      exact absurd hi' (by simp)
  | jmp h' _ => rw [h] at h'; simp [iBrIf, iJmp] at h'
  | ex h' _ _ => rw [h] at h'; simp [iBrIf, iEx] at h'
  | all h' _ _ => rw [h] at h'; simp [iBrIf, iAll] at h'
  | set0 h' _ => rw [h] at h'; simp [iBrIf, iSet0] at h'
  | set1 h' _ => rw [h] at h'; simp [iBrIf, iSet1] at h'
  | copy h' _ => rw [h] at h'; simp [iBrIf, iCopy] at h'

/-- A branch that is not taken. -/
theorem accN_brIf_false (hacc : AccN P W k pc μ) (h : P.getI pc = iBrIf i t) (hi : μ i = false) :
    ∃ k' < k, AccN P W k' (pc + 1) μ := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iBrIf, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iBrIf, iNand] at h'
  | rdIn h' _ => rw [h] at h'; simp [iBrIf, iRdIn] at h'
  | brT h' hi' h'' =>
      rw [h] at h'
      simp only [iBrIf, Prod.mk.injEq] at h'
      obtain ⟨-, rfl, rfl, -⟩ := h'
      rw [hi] at hi'
      exact absurd hi' (by simp)
  | brF h' hi' h'' =>
      rw [h] at h'
      simp only [iBrIf, Prod.mk.injEq] at h'
      obtain ⟨-, rfl, rfl, -⟩ := h'
      exact ⟨_, by omega, h''⟩
  | jmp h' _ => rw [h] at h'; simp [iBrIf, iJmp] at h'
  | ex h' _ _ => rw [h] at h'; simp [iBrIf, iEx] at h'
  | all h' _ _ => rw [h] at h'; simp [iBrIf, iAll] at h'
  | set0 h' _ => rw [h] at h'; simp [iBrIf, iSet0] at h'
  | set1 h' _ => rw [h] at h'; simp [iBrIf, iSet1] at h'
  | copy h' _ => rw [h] at h'; simp [iBrIf, iCopy] at h'

/-- A jump. -/
theorem accN_jmp (hacc : AccN P W k pc μ) (h : P.getI pc = iJmp t) :
    ∃ k' < k, AccN P W k' t μ := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iJmp, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iJmp, iNand] at h'
  | rdIn h' _ => rw [h] at h'; simp [iJmp, iRdIn] at h'
  | brT h' _ _ => rw [h] at h'; simp [iJmp, iBrIf] at h'
  | brF h' _ _ => rw [h] at h'; simp [iJmp, iBrIf] at h'
  | jmp h' h'' =>
      rw [h] at h'
      simp only [iJmp, Prod.mk.injEq] at h'
      obtain ⟨-, -, rfl, -⟩ := h'
      exact ⟨_, by omega, h''⟩
  | ex h' _ _ => rw [h] at h'; simp [iJmp, iEx] at h'
  | all h' _ _ => rw [h] at h'; simp [iJmp, iAll] at h'
  | set0 h' _ => rw [h] at h'; simp [iJmp, iSet0] at h'
  | set1 h' _ => rw [h] at h'; simp [iJmp, iSet1] at h'
  | copy h' _ => rw [h] at h'; simp [iJmp, iCopy] at h'

/-- An existential choice. -/
theorem accN_ex (hacc : AccN P W k pc μ) (h : P.getI pc = iEx d) :
    ∃ k' < k, ∃ b, AccN P W k' (pc + 1) (memUpd μ d b) := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iEx, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iEx, iNand] at h'
  | rdIn h' _ => rw [h] at h'; simp [iEx, iRdIn] at h'
  | brT h' _ _ => rw [h] at h'; simp [iEx, iBrIf] at h'
  | brF h' _ _ => rw [h] at h'; simp [iEx, iBrIf] at h'
  | jmp h' _ => rw [h] at h'; simp [iEx, iJmp] at h'
  | ex h' b h'' =>
      rw [h] at h'
      simp only [iEx, Prod.mk.injEq] at h'
      obtain ⟨-, -, -, rfl⟩ := h'
      exact ⟨_, by omega, b, h''⟩
  | all h' _ _ => rw [h] at h'; simp [iEx, iAll] at h'
  | set0 h' _ => rw [h] at h'; simp [iEx, iSet0] at h'
  | set1 h' _ => rw [h] at h'; simp [iEx, iSet1] at h'
  | copy h' _ => rw [h] at h'; simp [iEx, iCopy] at h'

/-- A universal choice. -/
theorem accN_all (hacc : AccN P W k pc μ) (h : P.getI pc = iAll d) :
    ∃ k' < k, AccN P W k' (pc + 1) (memUpd μ d false) ∧
      AccN P W k' (pc + 1) (memUpd μ d true) := by
  cases hacc with
  | acc h' => rw [h] at h'; simp [iAll, iAcc] at h'
  | nand h' _ => rw [h] at h'; simp [iAll, iNand] at h'
  | rdIn h' _ => rw [h] at h'; simp [iAll, iRdIn] at h'
  | brT h' _ _ => rw [h] at h'; simp [iAll, iBrIf] at h'
  | brF h' _ _ => rw [h] at h'; simp [iAll, iBrIf] at h'
  | jmp h' _ => rw [h] at h'; simp [iAll, iJmp] at h'
  | ex h' _ _ => rw [h] at h'; simp [iAll, iEx] at h'
  | all h' h0 h1 =>
      rw [h] at h'
      simp only [iAll, Prod.mk.injEq] at h'
      obtain ⟨-, -, -, rfl⟩ := h'
      exact ⟨_, by omega, h0, h1⟩
  | set0 h' _ => rw [h] at h'; simp [iAll, iSet0] at h'
  | set1 h' _ => rw [h] at h'; simp [iAll, iSet1] at h'
  | copy h' _ => rw [h] at h'; simp [iAll, iCopy] at h'

/-- The rejecting instruction rejects, with any fuel. -/
theorem not_accN_rej (h : P.getI pc = iRej) : ¬ AccN P W k pc μ := fun hacc =>
  not_acc_rej h hacc.toAcc

end Inversion

end Compile

end HTN
