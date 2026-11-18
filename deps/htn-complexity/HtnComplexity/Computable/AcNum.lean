import HtnComplexity.Computable.AcEnc
import HtnComplexity.Computable.GridDesc
/-!
# The compiled acyclic signature, spelled out as numbers

`HtnComplexity/Computable/AcEnc.lean` numbers the three inductive types of the compilation
`HtnComplexity/ToHtnAc/ToHtnAc.lean` by the functions `HTN.ToAc.encFact`, `HTN.ToAc.encAct` and
`HTN.ToAc.encTask`.  A *description* of the compiled domain has to write those numbers down
with numeric operations only, so that the translation is primitive recursive.

This file introduces one abbreviation per constructor — `HTN.Syn.Ac.fPos v i`,
`HTN.Syn.Ac.aSetV v i`, `HTN.Syn.Ac.tSELn n i`, … — and proves that they agree with the
numbering (`enc_*` lemmas, all definitional).  Everything downstream is phrased with these, so
that the description is manifestly built by arithmetic.

The names of the compiled signature are also *decoded* here, in the weak sense that is needed:
`HTN.Syn.Ac.tag`, the residue of a compiled task number modulo `13`, and
`HTN.Syn.Ac.payload`, its quotient, are computed for every constructor (`tag_*`,
`payload_*`).  That is what lets a function defined by a case distinction on `tag t` be
evaluated at `encTask f a c t`.
-/

namespace HTN

namespace Syn

namespace Ac

/-! ### The two channels -/

/-- The channel `R`, numbered. -/
def rwRead : ℕ := 0

/-- The channel `W`, numbered. -/
def rwWrite : ℕ := 1

/-! ### Source task names -/

/-- An action name of the source, as a task name of the source. -/
def nA (a : ℕ) : ℕ := 2 * a

/-- A compound task name of the source, as a task name of the source. -/
def nC (c : ℕ) : ℕ := 2 * c + 1

/-! ### The facts -/

/-- `key₀`, numbered. -/
def fKey0 : ℕ := 0

/-- `key₁^X`, numbered. -/
def fKey1 (x : ℕ) : ℕ := 6 * x + 1

/-- `key₂^X`, numbered. -/
def fKey2 (x : ℕ) : ℕ := 6 * x + 2

/-- `v^i`, numbered. -/
def fPos (v i : ℕ) : ℕ := 6 * (5 * v + i) + 3

/-- `¬v^i`, numbered. -/
def fNeg (v i : ℕ) : ℕ := 6 * (5 * v + i) + 4

/-- The stored task name, numbered. -/
def fTask (t : ℕ) : ℕ := 6 * t + 5

/-! ### The actions -/

/-- `setV_v^i`, numbered. -/
def aSetV (v i : ℕ) : ℕ := 13 * (5 * v + i)

/-- `delV_v^i`, numbered. -/
def aDelV (v i : ℕ) : ℕ := 13 * (5 * v + i) + 1

/-- `prePV_v^{i,j}`, numbered. -/
def aPrePV (v i j : ℕ) : ℕ := 13 * (25 * v + 5 * i + j) + 2

/-- `preNV_v^{i,j}`, numbered. -/
def aPreNV (v i j : ℕ) : ℕ := 13 * (25 * v + 5 * i + j) + 3

/-- `setC_t`, numbered. -/
def aSetC (t : ℕ) : ℕ := 13 * t + 4

/-- `preC_t`, numbered. -/
def aPreC (t : ℕ) : ℕ := 13 * t + 5

/-- `lock`, numbered. -/
def aLock : ℕ := 6

/-- `unlock`, numbered. -/
def aUnlock : ℕ := 7

/-- `ask_X`, numbered. -/
def aAsk (x : ℕ) : ℕ := 13 * x + 8

/-- `accept_X`, numbered. -/
def aAccept (x : ℕ) : ℕ := 13 * x + 9

/-- `done_X`, numbered. -/
def aDone (x : ℕ) : ℕ := 13 * x + 10

/-- `wait_X`, numbered. -/
def aWait (x : ℕ) : ℕ := 13 * x + 11

/-- `o²`, numbered. -/
def aOp2 (o : ℕ) : ℕ := 13 * o + 12

/-! ### The compound tasks -/

/-- `SEL^i`, numbered. -/
def tSEL (i : ℕ) : ℕ := 13 * i

/-- `SEL_n^i`, numbered. -/
def tSELn (n i : ℕ) : ℕ := 13 * (5 * n + i) + 1

/-- `EQ^{i,j}`, numbered. -/
def tEQ (i j : ℕ) : ℕ := 13 * (5 * i + j) + 2

/-- `EQ_n^{i,j}`, numbered. -/
def tEQn (n i j : ℕ) : ℕ := 13 * (25 * n + 5 * i + j) + 3

/-- `STATE_n^1`, numbered. -/
def tSTATE1 (n : ℕ) : ℕ := 13 * n + 4

/-- `STATE_n^3`, numbered. -/
def tSTATE3 (n : ℕ) : ℕ := 13 * n + 5

/-- `MEM`, numbered. -/
def tMEM : ℕ := 6

/-- `WRITE`, numbered. -/
def tWRITE : ℕ := 7

/-- `READ`, numbered. -/
def tREAD : ℕ := 8

/-- `TUPLE`, numbered. -/
def tTUPLE : ℕ := 9

/-- `𝔠̄^k_T`, numbered. -/
def tCnt (t k : ℕ) : ℕ := 13 * Nat.pair t k + 10

/-- `𝔠^k_T`, numbered. -/
def tCntPar (t k : ℕ) : ℕ := 13 * Nat.pair t k + 11

/-- `t_I`, numbered. -/
def tTI : ℕ := 12

/-! ### Agreement with the numbering of `AcEnc.lean` -/

section Agree

open ToAc

variable {F A C : Type} {f : F → ℕ} {a : A → ℕ} {c : C → ℕ}

@[simp] lemma enc_rwRead : encRW RW.read = rwRead := rfl
@[simp] lemma enc_rwWrite : encRW RW.write = rwWrite := rfl

@[simp] lemma enc_nA (x : A) : encName a c (Sum.inl x) = nA (a x) := rfl
@[simp] lemma enc_nC (y : C) : encName a c (Sum.inr y) = nC (c y) := rfl

@[simp] lemma enc_fKey0 : encFact f a c (AcFact.key0 : AcFact F A C) = fKey0 := rfl
@[simp] lemma enc_fKey1 (x : RW) :
    encFact f a c (AcFact.key1 x : AcFact F A C) = fKey1 (encRW x) := rfl
@[simp] lemma enc_fKey2 (x : RW) :
    encFact f a c (AcFact.key2 x : AcFact F A C) = fKey2 (encRW x) := rfl
@[simp] lemma enc_fPos (v : F) (i : Fin 5) :
    encFact f a c (AcFact.pos v i : AcFact F A C) = fPos (f v) i := rfl
@[simp] lemma enc_fNeg (v : F) (i : Fin 5) :
    encFact f a c (AcFact.neg v i : AcFact F A C) = fNeg (f v) i := rfl
@[simp] lemma enc_fTask (t : A ⊕ C) :
    encFact f a c (AcFact.task t : AcFact F A C) = fTask (encName a c t) := rfl

@[simp] lemma enc_aSetV (v : F) (i : Fin 5) :
    encAct f a c (AcAct.setV v i : AcAct F A C) = aSetV (f v) i := rfl
@[simp] lemma enc_aDelV (v : F) (i : Fin 5) :
    encAct f a c (AcAct.delV v i : AcAct F A C) = aDelV (f v) i := rfl
@[simp] lemma enc_aPrePV (v : F) (i j : Fin 5) :
    encAct f a c (AcAct.prePV v i j : AcAct F A C) = aPrePV (f v) i j := rfl
@[simp] lemma enc_aPreNV (v : F) (i j : Fin 5) :
    encAct f a c (AcAct.preNV v i j : AcAct F A C) = aPreNV (f v) i j := rfl
@[simp] lemma enc_aSetC (t : A ⊕ C) :
    encAct f a c (AcAct.setC t : AcAct F A C) = aSetC (encName a c t) := rfl
@[simp] lemma enc_aPreC (t : A ⊕ C) :
    encAct f a c (AcAct.preC t : AcAct F A C) = aPreC (encName a c t) := rfl
@[simp] lemma enc_aLock : encAct f a c (AcAct.lock : AcAct F A C) = aLock := rfl
@[simp] lemma enc_aUnlock : encAct f a c (AcAct.unlock : AcAct F A C) = aUnlock := rfl
@[simp] lemma enc_aAsk (x : RW) :
    encAct f a c (AcAct.ask x : AcAct F A C) = aAsk (encRW x) := rfl
@[simp] lemma enc_aAccept (x : RW) :
    encAct f a c (AcAct.accept x : AcAct F A C) = aAccept (encRW x) := rfl
@[simp] lemma enc_aDone (x : RW) :
    encAct f a c (AcAct.doneA x : AcAct F A C) = aDone (encRW x) := rfl
@[simp] lemma enc_aWait (x : RW) :
    encAct f a c (AcAct.waitA x : AcAct F A C) = aWait (encRW x) := rfl
@[simp] lemma enc_aOp2 (o : A) : encAct f a c (AcAct.op2 o : AcAct F A C) = aOp2 (a o) := rfl

@[simp] lemma enc_tSEL (i : Fin 5) :
    encTask f a c (AcTask.SEL i : AcTask F A C) = tSEL i := rfl
@[simp] lemma enc_tSELn (n : ℕ) (i : Fin 5) :
    encTask f a c (AcTask.SELn n i : AcTask F A C) = tSELn n i := rfl
@[simp] lemma enc_tEQ (i j : Fin 5) :
    encTask f a c (AcTask.EQ i j : AcTask F A C) = tEQ i j := rfl
@[simp] lemma enc_tEQn (n : ℕ) (i j : Fin 5) :
    encTask f a c (AcTask.EQn n i j : AcTask F A C) = tEQn n i j := rfl
@[simp] lemma enc_tSTATE1 (n : ℕ) :
    encTask f a c (AcTask.STATE1 n : AcTask F A C) = tSTATE1 n := rfl
@[simp] lemma enc_tSTATE3 (n : ℕ) :
    encTask f a c (AcTask.STATE3 n : AcTask F A C) = tSTATE3 n := rfl
@[simp] lemma enc_tMEM : encTask f a c (AcTask.MEM : AcTask F A C) = tMEM := rfl
@[simp] lemma enc_tWRITE : encTask f a c (AcTask.WRITE : AcTask F A C) = tWRITE := rfl
@[simp] lemma enc_tREAD : encTask f a c (AcTask.READ : AcTask F A C) = tREAD := rfl
@[simp] lemma enc_tTUPLE : encTask f a c (AcTask.TUPLE : AcTask F A C) = tTUPLE := rfl
@[simp] lemma enc_tCnt (t : AcTask F A C) (k : ℕ) :
    encTask f a c (AcTask.cnt t k) = tCnt (encTask f a c t) k := rfl
@[simp] lemma enc_tCntPar (t : AcTask F A C) (k : ℕ) :
    encTask f a c (AcTask.cntPar t k) = tCntPar (encTask f a c t) k := rfl
@[simp] lemma enc_tTI : encTask f a c (AcTask.tI : AcTask F A C) = tTI := rfl

end Agree

/-! ### The tag and the payload of a compiled task number -/

/-- The constructor tag of a compiled compound task number. -/
def tag (t : ℕ) : ℕ := t % 13

/-- The argument of a compiled compound task number. -/
def payload (t : ℕ) : ℕ := t / 13

private lemma tag_payload (x r : ℕ) (h : r < 13) : tag (13 * x + r) = r ∧
    payload (13 * x + r) = x := by
  constructor
  · simp [tag, Nat.mod_eq_of_lt h]
  · rw [payload, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt h, Nat.add_zero]

@[simp] lemma tag_tSEL (i : ℕ) : tag (tSEL i) = 0 := by
  simpa using (tag_payload i 0 (by norm_num)).1
@[simp] lemma payload_tSEL (i : ℕ) : payload (tSEL i) = i := by
  simpa using (tag_payload i 0 (by norm_num)).2
@[simp] lemma tag_tSELn (n i : ℕ) : tag (tSELn n i) = 1 := (tag_payload _ 1 (by norm_num)).1
@[simp] lemma payload_tSELn (n i : ℕ) : payload (tSELn n i) = 5 * n + i :=
  (tag_payload _ 1 (by norm_num)).2
@[simp] lemma tag_tEQ (i j : ℕ) : tag (tEQ i j) = 2 := (tag_payload _ 2 (by norm_num)).1
@[simp] lemma payload_tEQ (i j : ℕ) : payload (tEQ i j) = 5 * i + j :=
  (tag_payload _ 2 (by norm_num)).2
@[simp] lemma tag_tEQn (n i j : ℕ) : tag (tEQn n i j) = 3 := (tag_payload _ 3 (by norm_num)).1
@[simp] lemma payload_tEQn (n i j : ℕ) : payload (tEQn n i j) = 25 * n + 5 * i + j :=
  (tag_payload _ 3 (by norm_num)).2
@[simp] lemma tag_tSTATE1 (n : ℕ) : tag (tSTATE1 n) = 4 := (tag_payload _ 4 (by norm_num)).1
@[simp] lemma payload_tSTATE1 (n : ℕ) : payload (tSTATE1 n) = n :=
  (tag_payload _ 4 (by norm_num)).2
@[simp] lemma tag_tSTATE3 (n : ℕ) : tag (tSTATE3 n) = 5 := (tag_payload _ 5 (by norm_num)).1
@[simp] lemma payload_tSTATE3 (n : ℕ) : payload (tSTATE3 n) = n :=
  (tag_payload _ 5 (by norm_num)).2
@[simp] lemma tag_tMEM : tag tMEM = 6 := rfl
@[simp] lemma tag_tWRITE : tag tWRITE = 7 := rfl
@[simp] lemma tag_tREAD : tag tREAD = 8 := rfl
@[simp] lemma tag_tTUPLE : tag tTUPLE = 9 := rfl
@[simp] lemma tag_tCnt (t k : ℕ) : tag (tCnt t k) = 10 := (tag_payload _ 10 (by norm_num)).1
@[simp] lemma payload_tCnt (t k : ℕ) : payload (tCnt t k) = Nat.pair t k :=
  (tag_payload _ 10 (by norm_num)).2
@[simp] lemma tag_tCntPar (t k : ℕ) : tag (tCntPar t k) = 11 :=
  (tag_payload _ 11 (by norm_num)).1
@[simp] lemma payload_tCntPar (t k : ℕ) : payload (tCntPar t k) = Nat.pair t k :=
  (tag_payload _ 11 (by norm_num)).2
@[simp] lemma tag_tTI : tag tTI = 12 := rfl

end Ac

end Syn

end HTN
