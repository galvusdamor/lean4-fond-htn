import HtnComplexity.ToHtnAc.ToHtnAcStepPhase
import HtnComplexity.ToHtnAc.ToHtnAcPrimStep
/-!
# Positioning a proof step: which segment has been executed

`HtnComplexity/ToHtnAc/ToHtnAcStepPhase.lean` locates a proof step of the HTN-AC compilation
coarsely (untouched / in progress / finished).  For the soundness half of the correctness proof
the position has to be known exactly at the moments at which the step is waiting for an answer,
because that is where the state analysis of `HtnComplexity/ToHtnAc/ToHtnAcPrimStep.lean` and
`HtnComplexity/ToHtnAc/ToHtnAcCompoundStep.lean` is applied.

A proof step is a concatenation of *segments* separated by its handshakes
(`HtnComplexity/ToHtnAc/ToHtnAcTupleShape.lean`):

```
compound : lock ; SEL¹ ; SEL² ; SEL³ ; [ask_R ; wait_R] ; EQ ; EQ ; preC x ;
                  [ask_R ; wait_R] ; EQ ; EQ ; preC y ; setC c ;
                  [ask_W ; wait_W]^w ; unlock
primitive: lock ; SEL¹ ; SEL² ; SEL³ ; EQ ; o² ; EQ ; setC o ; [ask_W ; wait_W]^w ; unlock
```

and none of the segments contains a handshake action (`HTN.ToAc.countP_yieldSeq_SEL`,
`HTN.ToAc.countP_yieldSeq_EQ`).  So the four counters `#ask_R`, `#wait_R`, `#ask_W`, `#wait_W`
of the part already executed determine that part whenever a request of the step is open:

* `HTN.ToAc.compound_eq_of_read_pending` — while a compound step waits for a read answer it has
  executed either `lock ; SEL³ ; ask_R` or everything up to its second `ask_R`;
* `HTN.ToAc.compound_eq_of_write_pending` — while it waits for a write answer it has executed
  everything up to and including `setC c`, plus `k` completed write handshakes and the `ask_W`
  of the current one;
* `HTN.ToAc.prim_no_read_pending`, `HTN.ToAc.prim_eq_of_write_pending` — the same for a
  primitive step, which never reads.

The main consequence, `HTN.ToAc.step_write_pending_shape`, is the form in which the soundness
proof uses this: at a point at which a proof step has an *open write request* — which is
exactly the situation in which a memory cell may run its write phase and latch a triple — the
step has already executed its whole guessing and checking part, so the state analysis applies
and the latched triple is the one the step proves.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### The write requests -/

/-- The `w` write handshakes at the end of a proof step. -/
def writeReqs (w : ℕ) : List (AcAct F A C) :=
  (List.replicate w ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten

@[simp] lemma writeReqs_zero : writeReqs 0 = ([] : List (AcAct F A C)) := by simp [writeReqs]

lemma writeReqs_succ (w : ℕ) :
    writeReqs (F := F) (A := A) (C := C) (w + 1) =
      [AcAct.ask RW.write, AcAct.waitA RW.write] ++ writeReqs w := by
  simp [writeReqs, List.replicate_succ]

lemma writeReqs_add (k m : ℕ) :
    writeReqs (F := F) (A := A) (C := C) (k + m) = writeReqs k ++ writeReqs m := by
  induction k with
  | zero => simp
  | succ k ih =>
      have : k + 1 + m = (k + m) + 1 := by omega
      rw [this, writeReqs_succ, writeReqs_succ, ih, List.append_assoc]

lemma countP_writeReqs {p : AcAct F A C → Bool} (w : ℕ) :
    (writeReqs (F := F) (A := A) (C := C) w).countP p =
      w * ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C)).countP p := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [writeReqs_succ, List.countP_append, ih]
      ring

@[simp] lemma countP_isAsk_write_writeReqs (w : ℕ) :
    (writeReqs (F := F) (A := A) (C := C) w).countP (isAsk RW.write) = w := by
  rw [countP_writeReqs]
  simp [isAsk]

@[simp] lemma countP_isWait_write_writeReqs (w : ℕ) :
    (writeReqs (F := F) (A := A) (C := C) w).countP (isWait RW.write) = w := by
  rw [countP_writeReqs]
  simp [isWait]

/-- The write requests contain no read handshake, no `lock` and no `unlock`. -/
lemma countP_writeReqs_eq_zero {p : AcAct F A C → Bool} (w : ℕ)
    (h₁ : ¬ p (AcAct.ask RW.write)) (h₂ : ¬ p (AcAct.waitA RW.write)) :
    (writeReqs (F := F) (A := A) (C := C) w).countP p = 0 := by
  rw [countP_writeReqs]
  simp [h₁, h₂]

/-- **Where a prefix of the write requests ends**: after `k` complete handshakes, or after the
`ask_W` of the `k`-th one. -/
lemma prefix_writeReqs_cases : ∀ {w : ℕ} {q : List (AcAct F A C)}, q <+: writeReqs w →
    (∃ k, k ≤ w ∧ q = writeReqs k) ∨
      (∃ k, k < w ∧ q = writeReqs k ++ [AcAct.ask RW.write]) := by
  intro w
  induction w with
  | zero =>
      intro q hq
      rw [writeReqs_zero, List.prefix_nil] at hq
      exact Or.inl ⟨0, le_refl 0, by simp [hq]⟩
  | succ w ih =>
      intro q hq
      rw [writeReqs_succ] at hq
      rcases prefix_append_cases hq with h | ⟨r, rfl, hr⟩
      · -- a prefix of `[ask_W, wait_W]`
        cases q with
        | nil => exact Or.inl ⟨0, by omega, by simp⟩
        | cons a q' =>
            obtain ⟨rfl, hq'⟩ := List.cons_prefix_cons.1 h
            cases q' with
            | nil => exact Or.inr ⟨0, by omega, by simp⟩
            | cons b q'' =>
                obtain ⟨rfl, hq''⟩ := List.cons_prefix_cons.1 hq'
                rw [List.prefix_nil.1 hq'']
                exact Or.inl ⟨1, by omega, by simp [writeReqs_succ]⟩
      · rcases ih hr with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
        · exact Or.inl ⟨k + 1, by omega, by rw [writeReqs_succ]⟩
        · exact Or.inr ⟨k + 1, by omega, by rw [writeReqs_succ, List.append_assoc]⟩

/-! ### The segments of a proof step -/

/-- The part of a compound proof step before its first read request. -/
def compoundSeg0 (g₁ g₂ g₃ : List (AcAct F A C)) : List (AcAct F A C) :=
  AcAct.lock :: (g₁ ++ g₂ ++ g₃)

/-- The part of a compound proof step between its two read requests. -/
def compoundSeg1 (x : A ⊕ C) (e₁ e₂ : List (AcAct F A C)) : List (AcAct F A C) :=
  e₁ ++ e₂ ++ [AcAct.preC x]

/-- The part of a compound proof step between its second read request and its write requests. -/
def compoundSeg2 (c : C) (y : A ⊕ C) (e₃ e₄ : List (AcAct F A C)) : List (AcAct F A C) :=
  e₃ ++ e₄ ++ [AcAct.preC y, AcAct.setC (Sum.inr c)]

/-- The whole part of a compound proof step before its write requests. -/
def compoundPre (c : C) (x y : A ⊕ C) (g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)) :
    List (AcAct F A C) :=
  compoundSeg0 g₁ g₂ g₃ ++ [AcAct.ask RW.read, AcAct.waitA RW.read] ++ compoundSeg1 x e₁ e₂ ++
    [AcAct.ask RW.read, AcAct.waitA RW.read] ++ compoundSeg2 c y e₃ e₄

lemma tupleCompoundSeq_eq (c : C) (x y : A ⊕ C) (g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C))
    (w : ℕ) :
    tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w =
      compoundPre c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ ++ writeReqs w ++ [AcAct.unlock] := by
  simp [tupleCompoundSeq, compoundPre, compoundSeg0, compoundSeg1, compoundSeg2, writeReqs,
    List.append_assoc]

lemma tuplePrimitiveSeq_eq (o : A) (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)) (w : ℕ) :
    tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ w =
      primStepPrefix o g₁ g₂ g₃ e₁ e₂ ++ writeReqs w ++ [AcAct.unlock] := by
  simp [tuplePrimitiveSeq, primStepPrefix, writeReqs, List.append_assoc]

/-! ### The handshake actions of the segments -/

variable {p : AcAct F A C → Bool}

lemma countP_compoundSeg0 (hp : HandshakePred p)
    {g₁ g₂ g₃ : List (AcAct F A C)}
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃) :
    (compoundSeg0 g₁ g₂ g₃).countP p =
      ([AcAct.lock] : List (AcAct F A C)).countP p := by
  simp [compoundSeg0, List.countP_append, List.countP_cons,
    countP_yieldSeq_SEL hp hg₁, countP_yieldSeq_SEL hp hg₂, countP_yieldSeq_SEL hp hg₃]

lemma countP_compoundSeg1 (hp : HandshakePred p) {x : A ⊕ C} {e₁ e₂ : List (AcAct F A C)}
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂) :
    (compoundSeg1 x e₁ e₂).countP p = 0 := by
  simp [compoundSeg1, List.countP_append, countP_yieldSeq_EQ hp he₁, countP_yieldSeq_EQ hp he₂,
    hp.preC]

lemma countP_compoundSeg2 (hp : HandshakePred p) {c : C} {y : A ⊕ C}
    {e₃ e₄ : List (AcAct F A C)}
    (he₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃)
    (he₄ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄) :
    (compoundSeg2 c y e₃ e₄).countP p = 0 := by
  simp [compoundSeg2, List.countP_append, countP_yieldSeq_EQ hp he₃, countP_yieldSeq_EQ hp he₄,
    hp.preC, hp.setC]

lemma countP_primStepPrefix (hp : HandshakePred p) {o : A} {g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)}
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂) :
    (primStepPrefix o g₁ g₂ g₃ e₁ e₂).countP p =
      ([AcAct.lock] : List (AcAct F A C)).countP p := by
  simp [primStepPrefix, List.countP_append, List.countP_cons,
    countP_yieldSeq_SEL hp hg₁, countP_yieldSeq_SEL hp hg₂, countP_yieldSeq_SEL hp hg₃,
    countP_yieldSeq_EQ hp he₁, countP_yieldSeq_EQ hp he₂, hp.op2, hp.setC]

/-! ### Positioning a compound step -/

section Compound

variable {c : C} {x y : A ⊕ C} {g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)} {w : ℕ}
  {q : List (AcAct F A C)}
  (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
  (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
  (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
  (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁)
  (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂)
  (he₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃)
  (he₄ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄)

include hg₁ hg₂ hg₃ he₁ he₂ he₃ he₄

/-- **While a compound proof step waits for a read answer it stands at one of its two `ask_R`
actions.** -/
theorem compound_eq_of_read_pending
    (hq : q <+: tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w)
    (hpend : q.countP (isAsk RW.read) = q.countP (isWait RW.read) + 1) :
    q = compoundSeg0 g₁ g₂ g₃ ++ [AcAct.ask RW.read] ∨
      q = compoundSeg0 g₁ g₂ g₃ ++ [AcAct.ask RW.read, AcAct.waitA RW.read] ++
        compoundSeg1 x e₁ e₂ ++ [AcAct.ask RW.read] := by
  classical
  set L := tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w with hL
  set U₀ := compoundSeg0 (F := F) (A := A) (C := C) g₁ g₂ g₃ with hU₀
  set U₁ := U₀ ++ [AcAct.ask RW.read, AcAct.waitA RW.read] ++ compoundSeg1 x e₁ e₂ with hU₁
  -- the counters of the two prefixes ending at a read request
  have hask₀ : U₀.countP (isAsk RW.read) = 0 := by
    rw [hU₀, countP_compoundSeg0 (handshakePred_isAsk RW.read) hg₁ hg₂ hg₃]
    simp [isAsk]
  have hwait₀ : (U₀ ++ [AcAct.ask RW.read]).countP (isWait RW.read) = 0 := by
    rw [List.countP_append, hU₀, countP_compoundSeg0 (handshakePred_isWait RW.read) hg₁ hg₂ hg₃]
    simp [isWait]
  have hask₁ : U₁.countP (isAsk RW.read) = 1 := by
    rw [hU₁, List.countP_append, List.countP_append, hask₀,
      countP_compoundSeg1 (handshakePred_isAsk RW.read) he₁ he₂]
    simp [isAsk]
  have hwait₁ : (U₁ ++ [AcAct.ask RW.read]).countP (isWait RW.read) = 1 := by
    rw [List.countP_append, hU₁, List.countP_append, List.countP_append,
      countP_compoundSeg1 (handshakePred_isWait RW.read) he₁ he₂, hU₀,
      countP_compoundSeg0 (handshakePred_isWait RW.read) hg₁ hg₂ hg₃]
    simp [isWait]
  -- the two splittings of the step at a read request
  have hsplit₀ : L = U₀ ++ AcAct.ask RW.read :: AcAct.waitA RW.read ::
      (compoundSeg1 x e₁ e₂ ++ [AcAct.ask RW.read, AcAct.waitA RW.read] ++
        compoundSeg2 c y e₃ e₄ ++ writeReqs w ++ [AcAct.unlock]) := by
    rw [hL, tupleCompoundSeq_eq, compoundPre, hU₀]
    simp [List.append_assoc]
  have hsplit₁ : L = U₁ ++ AcAct.ask RW.read :: AcAct.waitA RW.read ::
      (compoundSeg2 c y e₃ e₄ ++ writeReqs w ++ [AcAct.unlock]) := by
    rw [hL, tupleCompoundSeq_eq, compoundPre, hU₁, hU₀]
    simp [List.append_assoc]
  -- how many read requests have been issued?
  have hle : q.countP (isAsk RW.read) ≤ 2 := by
    have hsub : q.countP (isAsk RW.read) ≤ L.countP (isAsk RW.read) := (hq.sublist).countP_le
    have : L.countP (isAsk RW.read) = 2 := by
      rw [hL, tupleCompoundSeq_eq, List.countP_append, List.countP_append, compoundPre]
      rw [List.countP_append, List.countP_append, List.countP_append, List.countP_append,
        countP_compoundSeg0 (handshakePred_isAsk RW.read) hg₁ hg₂ hg₃,
        countP_compoundSeg1 (handshakePred_isAsk RW.read) he₁ he₂,
        countP_compoundSeg2 (handshakePred_isAsk RW.read) he₃ he₄,
        countP_writeReqs_eq_zero w (by simp [isAsk]) (by simp [isAsk])]
      simp [isAsk]
    omega
  rcases Nat.lt_or_ge (q.countP (isWait RW.read)) 1 with hw | hw
  · -- no answer consumed yet: the step stands at its first `ask_R`
    refine Or.inl (eq_append_singleton_of_countP (p := isAsk RW.read) (p' := isWait RW.read)
      hsplit₀ (by simp [isWait]) hask₀ hwait₀ hq ?_ (by omega))
    omega
  · -- one answer consumed: the step stands at its second `ask_R`
    refine Or.inr ?_
    have hq2 : q.countP (isAsk RW.read) = 2 := by omega
    have : q = U₁ ++ [AcAct.ask RW.read] :=
      eq_append_singleton_of_countP (p := isAsk RW.read) (p' := isWait RW.read)
        hsplit₁ (by simp [isWait]) hask₁ hwait₁ hq (by omega) (by omega)
    rw [this, hU₁]

/-- **While a compound proof step waits for a write answer it has executed its whole guessing
and checking part**, together with `k` complete write handshakes and the `ask_W` of the current
one. -/
theorem compound_eq_of_write_pending
    (hq : q <+: tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w)
    (hpend : q.countP (isAsk RW.write) = q.countP (isWait RW.write) + 1) :
    ∃ k, k < w ∧
      q = compoundPre c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ ++ writeReqs k ++ [AcAct.ask RW.write] := by
  classical
  have hpre : ∀ p : AcAct F A C → Bool, HandshakePred p →
      ¬ p AcAct.lock → (compoundPre c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄).countP p =
        ([AcAct.ask RW.read, AcAct.waitA RW.read, AcAct.ask RW.read,
          AcAct.waitA RW.read] : List (AcAct F A C)).countP p := by
    intro p hp hlock
    rw [compoundPre, List.countP_append, List.countP_append, List.countP_append,
      List.countP_append, countP_compoundSeg0 hp hg₁ hg₂ hg₃, countP_compoundSeg1 hp he₁ he₂,
      countP_compoundSeg2 hp he₃ he₄]
    simp [hlock, List.countP_cons]
    omega
  have haskPre : (compoundPre c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄).countP (isAsk RW.write) = 0 := by
    rw [hpre _ (handshakePred_isAsk RW.write) (by simp [isAsk])]
    simp [isAsk]
  have hwaitPre : (compoundPre c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄).countP (isWait RW.write) = 0 := by
    rw [hpre _ (handshakePred_isWait RW.write) (by simp [isWait])]
    simp [isWait]
  rw [tupleCompoundSeq_eq] at hq
  rcases prefix_append_cases hq with h | ⟨r, rfl, hr⟩
  · -- the prefix ends inside `pre ++ writeReqs w`
    rcases prefix_append_cases h with h' | ⟨r, rfl, hr⟩
    · -- inside the guessing part: no write request at all
      have h₁ : q.countP (isAsk RW.write) = 0 := by
        have := (h'.sublist).countP_le (p := (isAsk RW.write : AcAct F A C → Bool))
        omega
      omega
    · rcases prefix_writeReqs_cases hr with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      · rw [List.countP_append, List.countP_append, haskPre, hwaitPre] at hpend
        simp at hpend
      · exact ⟨k, hk, by simp [List.append_assoc]⟩
  · -- the prefix ends inside `[unlock]`: then all write handshakes are complete
    have hcount : ((compoundPre c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ ++ writeReqs w) ++ r).countP
        (isAsk RW.write) =
        ((compoundPre c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ ++ writeReqs w) ++ r).countP
          (isWait RW.write) := by
      have hr' : r.countP (isAsk RW.write) = 0 ∧ r.countP (isWait RW.write) = 0 := by
        have := List.IsPrefix.sublist hr
        constructor <;>
          · refine List.countP_eq_zero.2 (fun a ha => ?_)
            have := this.mem ha
            simp at this
            subst this
            simp [isAsk, isWait]
      rw [List.countP_append, List.countP_append, List.countP_append, List.countP_append,
        haskPre, hwaitPre, hr'.1, hr'.2, countP_isAsk_write_writeReqs,
        countP_isWait_write_writeReqs]
    omega

end Compound

/-! ### Positioning a primitive step -/

section Primitive

variable {o : A} {g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)} {w : ℕ} {q : List (AcAct F A C)}
  (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
  (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
  (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
  (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁)
  (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂)

include hg₁ hg₂ hg₃ he₁ he₂

/-- A primitive proof step never has an open read request: it does not read. -/
theorem prim_no_read_pending (hq : q <+: tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ w) :
    q.countP (isAsk RW.read) = 0 := by
  classical
  have hsub := (hq.sublist).countP_le (p := (isAsk RW.read : AcAct F A C → Bool))
  have : (tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ w).countP (isAsk RW.read) = 0 := by
    rw [tuplePrimitiveSeq_eq, List.countP_append, List.countP_append,
      countP_primStepPrefix (handshakePred_isAsk RW.read) hg₁ hg₂ hg₃ he₁ he₂,
      countP_writeReqs_eq_zero w (by simp [isAsk]) (by simp [isAsk])]
    simp [isAsk]
  omega

/-- **While a primitive proof step waits for a write answer it has executed its whole guessing
and checking part**, together with `k` complete write handshakes and the `ask_W` of the current
one. -/
theorem prim_eq_of_write_pending (hq : q <+: tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ w)
    (hpend : q.countP (isAsk RW.write) = q.countP (isWait RW.write) + 1) :
    ∃ k, k < w ∧ q = primStepPrefix o g₁ g₂ g₃ e₁ e₂ ++ writeReqs k ++ [AcAct.ask RW.write] := by
  classical
  have haskPre : (primStepPrefix o g₁ g₂ g₃ e₁ e₂).countP (isAsk RW.write) = 0 := by
    rw [countP_primStepPrefix (handshakePred_isAsk RW.write) hg₁ hg₂ hg₃ he₁ he₂]
    simp [isAsk]
  have hwaitPre : (primStepPrefix o g₁ g₂ g₃ e₁ e₂).countP (isWait RW.write) = 0 := by
    rw [countP_primStepPrefix (handshakePred_isWait RW.write) hg₁ hg₂ hg₃ he₁ he₂]
    simp [isWait]
  rw [tuplePrimitiveSeq_eq] at hq
  rcases prefix_append_cases hq with h | ⟨r, rfl, hr⟩
  · rcases prefix_append_cases h with h' | ⟨r, rfl, hr⟩
    · have h₁ : q.countP (isAsk RW.write) = 0 := by
        have := (h'.sublist).countP_le (p := (isAsk RW.write : AcAct F A C → Bool))
        omega
      omega
    · rcases prefix_writeReqs_cases hr with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      · rw [List.countP_append, List.countP_append, haskPre, hwaitPre] at hpend
        simp at hpend
      · exact ⟨k, hk, by simp [List.append_assoc]⟩
  · have hr' : r.countP (isAsk RW.write) = 0 ∧ r.countP (isWait RW.write) = 0 := by
      have hsub := List.IsPrefix.sublist hr
      constructor <;>
        · refine List.countP_eq_zero.2 (fun a ha => ?_)
          have := hsub.mem ha
          simp at this
          subst this
          simp [isAsk, isWait]
    rw [List.countP_append, List.countP_append, List.countP_append, List.countP_append,
      haskPre, hwaitPre, hr'.1, hr'.2, countP_isAsk_write_writeReqs,
      countP_isWait_write_writeReqs] at hpend
    omega

end Primitive

/-! ### The shape of a proof step with an open write request -/

/-- **A proof step with an open write request has finished its guessing and checking part.**
This is the position at which a memory cell can run its write phase, so it is the position at
which the triple a cell latches is read off the state; the two shapes are those of
`HTN.ToAc.yieldSeq_TUPLE_shape`. -/
theorem step_write_pending_shape {σ q : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.TUPLE : AcTask F A C)] σ)
    (hq : q <+: σ)
    (hpend : q.countP (isAsk RW.write) = q.countP (isWait RW.write) + 1) :
    (∃ (c : C) (x y : A ⊕ C) (g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)) (w k : ℕ),
      D.SeqBody c [x, y] ∧ k < w ∧ w ≤ bound ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄ ∧
      σ = tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w ∧
      q = compoundPre c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ ++ writeReqs k ++ [AcAct.ask RW.write]) ∨
    (∃ (o : A) (g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)) (w k : ℕ),
      k < w ∧ w ≤ bound ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁ ∧
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂ ∧
      σ = tuplePrimitiveSeq o g₁ g₂ g₃ e₁ e₂ w ∧
      q = primStepPrefix o g₁ g₂ g₃ e₁ e₂ ++ writeReqs k ++ [AcAct.ask RW.write]) := by
  rcases yieldSeq_TUPLE_shape h with
    ⟨c, x, y, g₁, g₂, g₃, e₁, e₂, e₃, e₄, w, hmethod, hw, hg₁, hg₂, hg₃, he₁, he₂, he₃, he₄,
      rfl⟩ |
    ⟨o, g₁, g₂, g₃, e₁, e₂, w, hw, hg₁, hg₂, hg₃, he₁, he₂, rfl⟩
  · obtain ⟨k, hk, hqe⟩ :=
      compound_eq_of_write_pending hg₁ hg₂ hg₃ he₁ he₂ he₃ he₄ hq hpend
    exact Or.inl ⟨c, x, y, g₁, g₂, g₃, e₁, e₂, e₃, e₄, w, k, hmethod, hk, hw, hg₁, hg₂, hg₃,
      he₁, he₂, he₃, he₄, rfl, hqe⟩
  · obtain ⟨k, hk, hqe⟩ := prim_eq_of_write_pending hg₁ hg₂ hg₃ he₁ he₂ hq hpend
    exact Or.inr ⟨o, g₁, g₂, g₃, e₁, e₂, w, k, hk, hw, hg₁, hg₂, hg₃, he₁, he₂, rfl, hqe⟩

end ToAc

end HTN
