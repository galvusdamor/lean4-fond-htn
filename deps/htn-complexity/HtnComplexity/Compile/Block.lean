import HtnComplexity.Compile.Fuel
/-!
# Straight-line blocks of an alternating bit program

Most of a compiled program is **straight line**: an instruction writes one memory bit from the
current memory and the word, and control falls through to the next one.  This file isolates that
pattern.

* `HTN.Compile.Simple` — the instruction is one of `nand`, `read`, `set`, `clear`, `copy`;
* `HTN.Compile.stepMem` — the memory after it;
* `HTN.Compile.runInstrs` — the memory after a list of them;
* `HTN.Compile.acc_block_iff` — a block of simple instructions is transparent: acceptance
  before it is acceptance after it with the memory it produces;
* `HTN.Compile.accN_block` — the same with a fuel, which is what an induction over a loop needs.

With this, a compiled block is described by a purely computational statement about
`HTN.Compile.runInstrs`, and no reasoning about acceptance is needed twice.
-/

namespace HTN

namespace Compile

open Syn

/-! ### Simple instructions -/

/-- The memory bit an instruction writes. -/
def wrIdx (I : Instr) : ℕ := I.2.2.2

/-- **A simple instruction**: it writes one bit and falls through. -/
def Simple (I : Instr) : Prop :=
  (∃ i j d, I = iNand i j d) ∨ (∃ p d, I = iRdIn p d) ∨ (∃ d, I = iSet0 d) ∨
    (∃ d, I = iSet1 d) ∨ (∃ s d, I = iCopy s d)

/-- The value a simple instruction writes. -/
def wrVal (W : List Bool) (μ : ℕ → Bool) (I : Instr) : Bool :=
  if I.1 = 1 then !(μ I.2.1 && μ I.2.2.1)
  else if I.1 = 2 then inBit W I.2.1
  else if I.1 = 8 then false
  else if I.1 = 9 then true
  else if I.1 = 10 then μ I.2.1
  else false

/-- The memory after a simple instruction. -/
def stepMem (W : List Bool) (μ : ℕ → Bool) (I : Instr) : ℕ → Bool :=
  memUpd μ (wrIdx I) (wrVal W μ I)

/-- The memory after a list of simple instructions. -/
def runInstrs (W : List Bool) (μ : ℕ → Bool) (Is : List Instr) : ℕ → Bool :=
  Is.foldl (stepMem W) μ

@[simp] theorem runInstrs_nil (W : List Bool) (μ : ℕ → Bool) : runInstrs W μ [] = μ := rfl

@[simp] theorem runInstrs_cons (W : List Bool) (μ : ℕ → Bool) (I : Instr) (Is : List Instr) :
    runInstrs W μ (I :: Is) = runInstrs W (stepMem W μ I) Is := rfl

theorem runInstrs_append (W : List Bool) (μ : ℕ → Bool) (Is Js : List Instr) :
    runInstrs W μ (Is ++ Js) = runInstrs W (runInstrs W μ Is) Js := List.foldl_append

@[simp] theorem wrIdx_iNand (i j d : ℕ) : wrIdx (iNand i j d) = d := rfl

@[simp] theorem wrIdx_iRdIn (p d : ℕ) : wrIdx (iRdIn p d) = d := rfl

@[simp] theorem wrIdx_iSet0 (d : ℕ) : wrIdx (iSet0 d) = d := rfl

@[simp] theorem wrIdx_iSet1 (d : ℕ) : wrIdx (iSet1 d) = d := rfl

@[simp] theorem wrIdx_iCopy (s d : ℕ) : wrIdx (iCopy s d) = d := rfl

@[simp] theorem simple_iNand (i j d : ℕ) : Simple (iNand i j d) := Or.inl ⟨i, j, d, rfl⟩

@[simp] theorem simple_iRdIn (p d : ℕ) : Simple (iRdIn p d) := Or.inr (Or.inl ⟨p, d, rfl⟩)

@[simp] theorem simple_iSet0 (d : ℕ) : Simple (iSet0 d) := Or.inr (Or.inr (Or.inl ⟨d, rfl⟩))

@[simp] theorem simple_iSet1 (d : ℕ) : Simple (iSet1 d) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))

@[simp] theorem simple_iCopy (s d : ℕ) : Simple (iCopy s d) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨s, d, rfl⟩)))

@[simp] theorem stepMem_iNand (W : List Bool) (μ : ℕ → Bool) (i j d : ℕ) :
    stepMem W μ (iNand i j d) = memUpd μ d (!(μ i && μ j)) := rfl

@[simp] theorem stepMem_iRdIn (W : List Bool) (μ : ℕ → Bool) (p d : ℕ) :
    stepMem W μ (iRdIn p d) = memUpd μ d (inBit W p) := rfl

@[simp] theorem stepMem_iSet0 (W : List Bool) (μ : ℕ → Bool) (d : ℕ) :
    stepMem W μ (iSet0 d) = memUpd μ d false := rfl

@[simp] theorem stepMem_iSet1 (W : List Bool) (μ : ℕ → Bool) (d : ℕ) :
    stepMem W μ (iSet1 d) = memUpd μ d true := rfl

@[simp] theorem stepMem_iCopy (W : List Bool) (μ : ℕ → Bool) (s d : ℕ) :
    stepMem W μ (iCopy s d) = memUpd μ d (μ s) := rfl

/-- A cell a simple instruction does not write keeps its value. -/
theorem stepMem_of_ne {W : List Bool} {μ : ℕ → Bool} {I : Instr} {a : ℕ} (h : a ≠ wrIdx I) :
    stepMem W μ I a = μ a := by
  rw [stepMem, memUpd, if_neg h]

/-- A cell no instruction of a block writes keeps its value. -/
theorem runInstrs_of_forall_ne {W : List Bool} {Is : List Instr} :
    ∀ {μ : ℕ → Bool} {a : ℕ}, (∀ I ∈ Is, a ≠ wrIdx I) → runInstrs W μ Is a = μ a := by
  induction Is with
  | nil => intro μ a _; rfl
  | cons I Is ih =>
      intro μ a h
      rw [runInstrs_cons, ih (fun J hJ => h J (by simp [hJ])),
        stepMem_of_ne (h I (by simp))]

/-! ### A block is transparent -/

section Block

variable {P : List Instr} {W : List Bool} {pc : ℕ} {μ : ℕ → Bool} {I : Instr}

/-- **One simple instruction.** -/
theorem acc_simple_iff (hs : Simple I) (h : P.getI pc = I) :
    Acc P W pc μ ↔ Acc P W (pc + 1) (stepMem W μ I) := by
  rcases hs with ⟨i, j, d, rfl⟩ | ⟨p, d, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩ | ⟨s, d, rfl⟩
  · rw [stepMem_iNand]; exact acc_nand_iff (W := W) (μ := μ) h
  · rw [stepMem_iRdIn]; exact acc_rdIn_iff (W := W) (μ := μ) h
  · rw [stepMem_iSet0]; exact acc_set0_iff (W := W) (μ := μ) h
  · rw [stepMem_iSet1]; exact acc_set1_iff (W := W) (μ := μ) h
  · rw [stepMem_iCopy]; exact acc_copy_iff (W := W) (μ := μ) h

/-- **One simple instruction**, with the fuel. -/
theorem accN_simple {k : ℕ} (hs : Simple I) (h : P.getI pc = I) (hacc : AccN P W k pc μ) :
    ∃ k' < k, AccN P W k' (pc + 1) (stepMem W μ I) := by
  rcases hs with ⟨i, j, d, rfl⟩ | ⟨p, d, rfl⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩ | ⟨s, d, rfl⟩
  · rw [stepMem_iNand]; exact accN_nand hacc h
  · rw [stepMem_iRdIn]; exact accN_rdIn hacc h
  · rw [stepMem_iSet0]; exact accN_set0 hacc h
  · rw [stepMem_iSet1]; exact accN_set1 hacc h
  · rw [stepMem_iCopy]; exact accN_copy hacc h

/-- **A straight-line block of simple instructions is transparent.** -/
theorem acc_block_iff : ∀ {Is : List Instr} {pc : ℕ} {μ : ℕ → Bool},
    (∀ t < Is.length, P.getI (pc + t) = Is.getI t) → (∀ I ∈ Is, Simple I) →
    (Acc P W pc μ ↔ Acc P W (pc + Is.length) (runInstrs W μ Is)) := by
  intro Is
  induction Is with
  | nil => intro pc μ _ _; simp
  | cons I Is ih =>
      intro pc μ hP hs
      have h0 : P.getI pc = I := by simpa using hP 0 (by simp)
      rw [acc_simple_iff (hs I (by simp)) h0]
      have hP' : ∀ t < Is.length, P.getI (pc + 1 + t) = Is.getI t := by
        intro t ht
        have h := hP (t + 1) (by simp; omega)
        rw [show pc + (t + 1) = pc + 1 + t by omega] at h
        simpa using h
      rw [ih hP' (fun J hJ => hs J (by simp [hJ])),
        show pc + (I :: Is).length = pc + 1 + Is.length by simp; omega]
      rfl

/-- **A straight-line block of simple instructions is transparent**, with the fuel. -/
theorem accN_block : ∀ {Is : List Instr} {pc : ℕ} {μ : ℕ → Bool} {k : ℕ},
    (∀ t < Is.length, P.getI (pc + t) = Is.getI t) → (∀ I ∈ Is, Simple I) →
    AccN P W k pc μ → ∃ k' ≤ k, AccN P W k' (pc + Is.length) (runInstrs W μ Is) := by
  intro Is
  induction Is with
  | nil => intro pc μ k _ _ hacc; exact ⟨k, le_rfl, by simpa using hacc⟩
  | cons I Is ih =>
      intro pc μ k hP hs hacc
      have h0 : P.getI pc = I := by simpa using hP 0 (by simp)
      obtain ⟨k₁, hk₁, hacc₁⟩ := accN_simple (hs I (by simp)) h0 hacc
      have hP' : ∀ t < Is.length, P.getI (pc + 1 + t) = Is.getI t := by
        intro t ht
        have h := hP (t + 1) (by simp; omega)
        rw [show pc + (t + 1) = pc + 1 + t by omega] at h
        simpa using h
      obtain ⟨k₂, hk₂, hacc₂⟩ := ih hP' (fun J hJ => hs J (by simp [hJ])) hacc₁
      refine ⟨k₂, by omega, ?_⟩
      rw [show pc + (I :: Is).length = pc + 1 + Is.length by simp; omega]
      exact hacc₂

end Block

/-! ### Assignment blocks

A block that writes a whole region at once — a copy of an area, the encoding of the input word,
the bits a circuit's outputs are read into — is a list of simple instructions whose destinations
are pairwise distinct and are read by none of them.  Such a block computes every one of its
values in the memory it started from, which is how a region is described in one step. -/

/-- The memory cells an instruction reads. -/
def rdIdx (I : Instr) : List ℕ :=
  if I.1 = 1 then [I.2.1, I.2.2.1] else if I.1 = 10 then [I.2.1] else []

@[simp] theorem rdIdx_iNand (i j d : ℕ) : rdIdx (iNand i j d) = [i, j] := rfl

@[simp] theorem rdIdx_iRdIn (p d : ℕ) : rdIdx (iRdIn p d) = [] := rfl

@[simp] theorem rdIdx_iSet0 (d : ℕ) : rdIdx (iSet0 d) = [] := rfl

@[simp] theorem rdIdx_iSet1 (d : ℕ) : rdIdx (iSet1 d) = [] := rfl

@[simp] theorem rdIdx_iCopy (s d : ℕ) : rdIdx (iCopy s d) = [s] := rfl

/-- The value written depends only on the cells the instruction reads. -/
theorem wrVal_congr {W : List Bool} {μ ν : ℕ → Bool} {I : Instr}
    (h : ∀ a ∈ rdIdx I, μ a = ν a) : wrVal W μ I = wrVal W ν I := by
  rcases I with ⟨op, x, y, z⟩
  simp only [rdIdx] at h
  simp only [wrVal]
  split_ifs with h1 h2 h8 h9 h10 <;> simp_all

/-- **An assignment block writes every one of its values, computed in the memory it started
from** — provided its destinations are pairwise distinct and read by none of its
instructions. -/
theorem runInstrs_assign {W : List Bool} : ∀ {Is : List Instr} {μ : ℕ → Bool},
    (∀ I ∈ Is, ∀ J ∈ Is, wrIdx I ∉ rdIdx J) →
    (List.Pairwise (fun I J => wrIdx I ≠ wrIdx J) Is) →
    ∀ I ∈ Is, runInstrs W μ Is (wrIdx I) = wrVal W μ I := by
  intro Is
  induction Is with
  | nil => intro μ _ _ I hI; exact absurd hI (by simp)
  | cons I Is ih =>
      intro μ hrd hpw J hJ
      have hpw' := List.pairwise_cons.1 hpw
      rcases List.mem_cons.1 hJ with rfl | hJ'
      · rw [runInstrs_cons, runInstrs_of_forall_ne ?_, stepMem, memUpd, if_pos rfl]
        intro K hK
        exact fun hc => hpw'.1 K hK hc
      · rw [runInstrs_cons,
          ih (fun A hA B hB => hrd A (by simp [hA]) B (by simp [hB])) hpw'.2 J hJ']
        refine wrVal_congr ?_
        intro a ha
        rw [stepMem_of_ne]
        exact fun hc => hrd I (by simp) J (by simp [hJ']) (hc ▸ ha)

/-! ### Reading a block off a program

A compiled program is a concatenation of blocks; this is how an instruction of one of them is
found at the program point it was placed at. -/

theorem getI_append_left {α : Type*} [Inhabited α] {l₁ l₂ : List α} {i : ℕ}
    (h : i < l₁.length) : (l₁ ++ l₂).getI i = l₁.getI i := List.getI_append _ _ _ h

theorem getI_append_right {α : Type*} [Inhabited α] (l₁ l₂ : List α) (i : ℕ) :
    (l₁ ++ l₂).getI (l₁.length + i) = l₂.getI i := by
  rw [List.getI_append_right _ _ _ (by omega)]
  congr 1
  omega

/-- The instructions of a block placed after a prefix are found at the points they were placed
at. -/
theorem getI_block {pre Is post : List Instr} {t : ℕ} (ht : t < Is.length) :
    (pre ++ Is ++ post).getI (pre.length + t) = Is.getI t := by
  rw [List.append_assoc, getI_append_right, getI_append_left ht]

/-- **A program written as a list of blocks**: the `i`-th block starts at the sum of the lengths
of the blocks before it. -/
theorem getI_flatten {α : Type*} [Inhabited α] {bs : List (List α)} {i : ℕ} (hi : i < bs.length)
    {t : ℕ} (ht : t < (bs.getI i).length) :
    bs.flatten.getI (((bs.take i).map List.length).sum + t) = (bs.getI i).getI t := by
  have hd : bs.drop i = bs.getI i :: bs.drop (i + 1) := by
    rw [List.getI_eq_getElem _ hi]
    exact (List.getElem_cons_drop hi).symm
  have hsplit : bs.flatten
      = (bs.take i).flatten ++ (bs.getI i ++ (bs.drop (i + 1)).flatten) := by
    conv_lhs => rw [← List.take_append_drop i bs, hd]
    rw [List.flatten_append]
    simp
  rw [hsplit, show ((bs.take i).map List.length).sum = (bs.take i).flatten.length from
    List.length_flatten.symm, getI_append_right, getI_append_left ht]

end Compile

end HTN
