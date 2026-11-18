import HtnComplexity.Compile.Block
/-!
# Guessing a configuration

The loop of the compiled machine guesses a successor configuration, existentially or
universally according to the classification of the current one.  A configuration of width
`w ≤ N` is held as the cell encoding `HTN.Compile.encStr N`, so a guess must produce

* a presence bit equal to the **width mask** — the bit `MWb + i` says that the cell `i` is
  inside the configuration — and
* a value bit which is `false` wherever the mask is.

Guessing the bits freely and *forcing* them with the mask is what this file compiles: the group
of instructions for one cell guesses a bit into a scratch cell, ands it with the mask into the
value bit, and copies the mask into the presence bit.  Forcing rather than checking is what
makes the guess a bijection onto the configurations of the right width, with no validity test.

* `HTN.Compile.guessProg` — the block, existential or universal;
* `HTN.Compile.guessMem` — the memory it leaves, as a function of the guessed bits;
* `HTN.Compile.acc_guessEx`, `HTN.Compile.acc_guessAll` — what acceptance across the block is,
  and `HTN.Compile.accN_guessEx`, `HTN.Compile.accN_guessAll` the same with a fuel.
-/

namespace HTN

namespace Compile

open Syn

/-! ### The block -/

/-- The four instructions guessing the cell `i` of a configuration. -/
def guessGroup (uni : Bool) (Gb MWb Tb i : ℕ) : List Instr :=
  [ (if uni then iAll (Tb + 2 * i) else iEx (Tb + 2 * i)),
    iNand (Tb + 2 * i) (MWb + i) (Tb + 2 * i + 1),
    iNand (Tb + 2 * i + 1) (Tb + 2 * i + 1) (Gb + 2 * i + 1),
    iCopy (MWb + i) (Gb + 2 * i) ]

/-- The block guessing the cells `j, …, j + m - 1` of a configuration. -/
def guessProg (uni : Bool) (Gb MWb Tb j m : ℕ) : List Instr :=
  (List.range m).flatMap fun r => guessGroup uni Gb MWb Tb (j + r)

@[simp] theorem length_guessGroup (uni : Bool) (Gb MWb Tb i : ℕ) :
    (guessGroup uni Gb MWb Tb i).length = 4 := rfl

@[simp] theorem length_guessProg (uni : Bool) (Gb MWb Tb j m : ℕ) :
    (guessProg uni Gb MWb Tb j m).length = 4 * m := by
  rw [guessProg, List.length_flatMap]
  simp [mul_comm]

theorem guessProg_succ (uni : Bool) (Gb MWb Tb j m : ℕ) :
    guessProg uni Gb MWb Tb j (m + 1)
      = guessGroup uni Gb MWb Tb j ++ guessProg uni Gb MWb Tb (j + 1) m := by
  rw [guessProg, guessProg, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  congr 1
  refine List.flatMap_congr ?_
  intro r _
  show guessGroup uni Gb MWb Tb (j + (r + 1)) = guessGroup uni Gb MWb Tb (j + 1 + r)
  rw [show j + (r + 1) = j + 1 + r by omega]

/-! ### The memory the block leaves -/

/-- The memory after the group of one cell, from the guessed bit. -/
def guessStep (Gb MWb Tb i : ℕ) (μ : ℕ → Bool) (b : Bool) : ℕ → Bool :=
  memUpd (memUpd (memUpd (memUpd μ (Tb + 2 * i) b)
    (Tb + 2 * i + 1) (!(b && μ (MWb + i))))
    (Gb + 2 * i + 1) (b && μ (MWb + i)))
    (Gb + 2 * i) (μ (MWb + i))

/-- The memory after the block, from the guessed bits. -/
def guessMem (Gb MWb Tb : ℕ) : ℕ → (ℕ → Bool) → List Bool → (ℕ → Bool)
  | _, μ, [] => μ
  | j, μ, b :: bs => guessMem Gb MWb Tb (j + 1) (guessStep Gb MWb Tb j μ b) bs

@[simp] theorem guessMem_nil (Gb MWb Tb j : ℕ) (μ : ℕ → Bool) :
    guessMem Gb MWb Tb j μ [] = μ := rfl

@[simp] theorem guessMem_cons (Gb MWb Tb j : ℕ) (μ : ℕ → Bool) (b : Bool) (bs : List Bool) :
    guessMem Gb MWb Tb j μ (b :: bs)
      = guessMem Gb MWb Tb (j + 1) (guessStep Gb MWb Tb j μ b) bs := rfl

section Mem

variable {Gb MWb Tb NN : ℕ}

/-- The separation of the three regions the guess touches. -/
structure GuessSep (Gb MWb Tb NN : ℕ) : Prop where
  /-- The guessed configuration lies below the mask. -/
  gm : Gb + 2 * NN ≤ MWb
  /-- The mask lies below the scratch cells. -/
  mt : MWb + NN ≤ Tb

/-- A cell outside the three regions is untouched by one group. -/
theorem guessStep_of_ne {i : ℕ} {μ : ℕ → Bool} {b : Bool} {a : ℕ}
    (h1 : a ≠ Gb + 2 * i) (h2 : a ≠ Gb + 2 * i + 1) (h3 : a ≠ Tb + 2 * i)
    (h4 : a ≠ Tb + 2 * i + 1) : guessStep Gb MWb Tb i μ b a = μ a := by
  rw [guessStep, memUpd, if_neg h1, memUpd, if_neg h2, memUpd, if_neg h4, memUpd, if_neg h3]

/-- The mask is untouched by one group. -/
theorem guessStep_mask (hs : GuessSep Gb MWb Tb NN) {i i' : ℕ} (hi : i < NN) (hi' : i' < NN)
    {μ : ℕ → Bool} {b : Bool} :
    guessStep Gb MWb Tb i μ b (MWb + i') = μ (MWb + i') := by
  have := hs.gm; have := hs.mt
  exact guessStep_of_ne (by omega) (by omega) (by omega) (by omega)

/-- A cell outside the three regions is untouched by the block. -/
theorem guessMem_of_ne :
    ∀ {bs : List Bool} {j : ℕ} {μ : ℕ → Bool} {a : ℕ},
      (∀ i, j ≤ i → i < j + bs.length →
        a ≠ Gb + 2 * i ∧ a ≠ Gb + 2 * i + 1 ∧ a ≠ Tb + 2 * i ∧ a ≠ Tb + 2 * i + 1) →
      guessMem Gb MWb Tb j μ bs a = μ a := by
  intro bs
  induction bs with
  | nil => intro j μ a _; rfl
  | cons b bs ih =>
      intro j μ a ha
      obtain ⟨n1, n2, n3, n4⟩ := ha j (le_refl _) (by simp)
      rw [guessMem_cons, ih ?_, guessStep_of_ne n1 n2 n3 n4]
      intro i hi hi'
      exact ha i (by omega) (by simp at hi' ⊢; omega)

/-- The mask is untouched by the block. -/
theorem guessMem_mask (hs : GuessSep Gb MWb Tb NN) {bs : List Bool} {j : ℕ} {μ : ℕ → Bool}
    {i' : ℕ} (hj : j + bs.length ≤ NN) (hi' : i' < NN) :
    guessMem Gb MWb Tb j μ bs (MWb + i') = μ (MWb + i') := by
  refine guessMem_of_ne ?_
  have := hs.gm; have := hs.mt
  intro i _ hi2
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The presence bit of a guessed cell is the mask.** -/
theorem guessMem_pres (hs : GuessSep Gb MWb Tb NN) :
    ∀ {bs : List Bool} {j : ℕ} {μ : ℕ → Bool} {r : ℕ}, j + bs.length ≤ NN → r < bs.length →
      guessMem Gb MWb Tb j μ bs (Gb + 2 * (j + r)) = μ (MWb + (j + r)) := by
  intro bs
  induction bs with
  | nil => intro j μ r _ hr; exact absurd hr (by simp)
  | cons b bs ih =>
      intro j μ r hj hr
      have hgm := hs.gm
      have hmt := hs.mt
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · rw [guessMem_cons]
        have hstep : guessStep Gb MWb Tb j μ b (Gb + 2 * (j + 0)) = μ (MWb + j) := by
          rw [show j + 0 = j by omega, guessStep, memUpd, if_pos rfl]
        rw [guessMem_of_ne ?_, hstep]
        · simp
        · intro i hi hi2
          simp at hj hi2
          refine ⟨by omega, by omega, by omega, by omega⟩
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [guessMem_cons, show j + (r' + 1) = j + 1 + r' by omega,
          ih (by simp at hj ⊢; omega) (by simp at hr; omega),
          guessStep_mask hs (by simp at hj; omega) (by simp at hj hr; omega)]

/-- **The value bit of a guessed cell is the guess, masked.** -/
theorem guessMem_val (hs : GuessSep Gb MWb Tb NN) :
    ∀ {bs : List Bool} {j : ℕ} {μ : ℕ → Bool} {r : ℕ}, j + bs.length ≤ NN → r < bs.length →
      guessMem Gb MWb Tb j μ bs (Gb + 2 * (j + r) + 1)
        = (bs.getI r && μ (MWb + (j + r))) := by
  intro bs
  induction bs with
  | nil => intro j μ r _ hr; exact absurd hr (by simp)
  | cons b bs ih =>
      intro j μ r hj hr
      have hgm := hs.gm
      have hmt := hs.mt
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · rw [guessMem_cons]
        have hstep : guessStep Gb MWb Tb j μ b (Gb + 2 * (j + 0) + 1)
            = (b && μ (MWb + j)) := by
          rw [show j + 0 = j by omega, guessStep, memUpd, if_neg (by omega), memUpd, if_pos rfl]
        rw [guessMem_of_ne ?_, hstep]
        · simp
        · intro i hi hi2
          simp at hj hi2
          refine ⟨by omega, by omega, by omega, by omega⟩
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [guessMem_cons, show j + (r' + 1) = j + 1 + r' by omega,
          ih (by simp at hj ⊢; omega) (by simp at hr; omega),
          guessStep_mask hs (by simp at hj; omega) (by simp at hj hr; omega)]
        simp

end Mem

/-! ### Acceptance across the block -/

section Acc

variable {P : List Instr} {W : List Bool} {Gb MWb Tb NN : ℕ}

/-- The three instructions of a group after the guess. -/
private def guessTail (Gb MWb Tb i : ℕ) : List Instr :=
  [iNand (Tb + 2 * i) (MWb + i) (Tb + 2 * i + 1),
    iNand (Tb + 2 * i + 1) (Tb + 2 * i + 1) (Gb + 2 * i + 1),
    iCopy (MWb + i) (Gb + 2 * i)]

private theorem guessGroup_eq (uni : Bool) (Gb MWb Tb i : ℕ) :
    guessGroup uni Gb MWb Tb i
      = (if uni then iAll (Tb + 2 * i) else iEx (Tb + 2 * i)) :: guessTail Gb MWb Tb i := rfl

private theorem simple_guessTail (Gb MWb Tb i : ℕ) :
    ∀ I ∈ guessTail Gb MWb Tb i, Simple I := by
  intro I hI
  simp only [guessTail, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl <;> simp

/-- The three instructions of a group after the guess compute `HTN.Compile.guessStep`. -/
private theorem runInstrs_guessTail (hs : GuessSep Gb MWb Tb NN) {i : ℕ} (hi : i < NN)
    (μ : ℕ → Bool) (b : Bool) :
    runInstrs W (memUpd μ (Tb + 2 * i) b) (guessTail Gb MWb Tb i)
      = guessStep Gb MWb Tb i μ b := by
  have hgm := hs.gm
  have hmt := hs.mt
  funext a
  set μ0 : ℕ → Bool := memUpd μ (Tb + 2 * i) b with hμ0
  have hm0 : μ0 (MWb + i) = μ (MWb + i) := by rw [hμ0, memUpd, if_neg (by omega)]
  have hT0 : μ0 (Tb + 2 * i) = b := by rw [hμ0, memUpd, if_pos rfl]
  simp only [guessTail, runInstrs_cons, runInstrs_nil, stepMem_iNand, stepMem_iCopy]
  set μ1 : ℕ → Bool := memUpd μ0 (Tb + 2 * i + 1) (!(μ0 (Tb + 2 * i) && μ0 (MWb + i))) with hμ1
  have hμ1' : μ1 = memUpd μ0 (Tb + 2 * i + 1) (!(b && μ (MWb + i))) := by
    rw [hμ1, hm0, hT0]
  have h1T : μ1 (Tb + 2 * i + 1) = !(b && μ (MWb + i)) := by
    rw [hμ1', memUpd, if_pos rfl]
  set μ2 : ℕ → Bool := memUpd μ1 (Gb + 2 * i + 1) (!(μ1 (Tb + 2 * i + 1) && μ1 (Tb + 2 * i + 1)))
    with hμ2
  have hμ2' : μ2 = memUpd μ1 (Gb + 2 * i + 1) (b && μ (MWb + i)) := by
    rw [hμ2, h1T]
    cases hb : b <;> cases hm : μ (MWb + i) <;> simp
  have h2M : μ2 (MWb + i) = μ (MWb + i) := by
    rw [hμ2', memUpd, if_neg (by omega), hμ1', memUpd, if_neg (by omega), hm0]
  rw [h2M, hμ2', hμ1', hμ0, guessStep]

/-- The instructions of the block are found at the points they were placed at. -/
private theorem getI_guessProg_group {uni : Bool} {j m : ℕ} (hm : 0 < m) {t : ℕ} (ht : t < 4) :
    (guessProg uni Gb MWb Tb j m).getI t = (guessGroup uni Gb MWb Tb j).getI t := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [guessProg_succ, getI_append_left (by simpa using ht)]

/-- The instructions after the first group are the block of the remaining cells. -/
private theorem getI_guessProg_rest {uni : Bool} {j m pc : ℕ}
    (hP : ∀ t < 4 * (m + 1), P.getI (pc + t) = (guessProg uni Gb MWb Tb j (m + 1)).getI t) :
    ∀ t < 4 * m, P.getI (pc + 4 + t) = (guessProg uni Gb MWb Tb (j + 1) m).getI t := by
  intro t ht
  have h := hP (t + 4) (by omega)
  rw [show pc + (t + 4) = pc + 4 + t by omega] at h
  rw [h, guessProg_succ, show t + 4 = (guessGroup uni Gb MWb Tb j).length + t by simp; omega,
    getI_append_right]

/-- The instruction the guess itself is. -/
private theorem getI_guessProg_head {uni : Bool} {j m pc : ℕ} (hm : 0 < m)
    (hP : ∀ t < 4 * m, P.getI (pc + t) = (guessProg uni Gb MWb Tb j m).getI t) :
    P.getI pc = (if uni then iAll (Tb + 2 * j) else iEx (Tb + 2 * j)) := by
  have h := hP 0 (by omega)
  rw [getI_guessProg_group hm (by omega)] at h
  simpa [guessGroup_eq] using h

/-- The three instructions after the guess are where they were placed. -/
private theorem getI_guessTail {uni : Bool} {j m pc : ℕ} (hm : 0 < m)
    (hP : ∀ t < 4 * m, P.getI (pc + t) = (guessProg uni Gb MWb Tb j m).getI t) :
    ∀ t < (guessTail Gb MWb Tb j).length,
      P.getI (pc + 1 + t) = (guessTail Gb MWb Tb j).getI t := by
  intro t ht
  simp only [guessTail, List.length_cons, List.length_nil] at ht
  have h := hP (t + 1) (by omega)
  rw [getI_guessProg_group hm (by omega)] at h
  rw [show pc + 1 + t = pc + (t + 1) by omega, h, guessGroup_eq]
  interval_cases t <;> simp [guessTail]

/-- **Acceptance across the three instructions of a group after the guess.** -/
private theorem acc_guessTail_iff (hs : GuessSep Gb MWb Tb NN) {uni : Bool} {j m pc : ℕ}
    {μ : ℕ → Bool} (hj : j < NN) (hm : 0 < m)
    (hP : ∀ t < 4 * m, P.getI (pc + t) = (guessProg uni Gb MWb Tb j m).getI t) (b : Bool) :
    Acc P W (pc + 1) (memUpd μ (Tb + 2 * j) b)
      ↔ Acc P W (pc + 4) (guessStep Gb MWb Tb j μ b) := by
  rw [acc_block_iff (P := P) (W := W) (μ := memUpd μ (Tb + 2 * j) b)
      (Is := guessTail Gb MWb Tb j) (getI_guessTail hm hP) (simple_guessTail _ _ _ _),
    runInstrs_guessTail hs hj μ b,
    show pc + 1 + (guessTail Gb MWb Tb j).length = pc + 4 by simp [guessTail]]

/-- **Acceptance across the three instructions of a group after the guess**, with a fuel. -/
private theorem accN_guessTail (hs : GuessSep Gb MWb Tb NN) {uni : Bool} {j m pc k : ℕ}
    {μ : ℕ → Bool} (hj : j < NN) (hm : 0 < m)
    (hP : ∀ t < 4 * m, P.getI (pc + t) = (guessProg uni Gb MWb Tb j m).getI t) (b : Bool)
    (hacc : AccN P W k (pc + 1) (memUpd μ (Tb + 2 * j) b)) :
    ∃ k' ≤ k, AccN P W k' (pc + 4) (guessStep Gb MWb Tb j μ b) := by
  obtain ⟨k', hk', hacc'⟩ := accN_block (P := P) (W := W) (μ := memUpd μ (Tb + 2 * j) b)
    (Is := guessTail Gb MWb Tb j) (getI_guessTail hm hP) (simple_guessTail _ _ _ _) hacc
  refine ⟨k', hk', ?_⟩
  rw [runInstrs_guessTail hs hj μ b,
    show pc + 1 + (guessTail Gb MWb Tb j).length = pc + 4 by simp [guessTail]] at hacc'
  exact hacc'

/-- **Guessing existentially.** -/
theorem acc_guessEx (hs : GuessSep Gb MWb Tb NN) :
    ∀ {m j pc : ℕ} {μ : ℕ → Bool}, j + m ≤ NN →
      (∀ t < 4 * m, P.getI (pc + t) = (guessProg false Gb MWb Tb j m).getI t) →
      (Acc P W pc μ ↔ ∃ bs : List Bool, bs.length = m ∧
        Acc P W (pc + 4 * m) (guessMem Gb MWb Tb j μ bs)) := by
  intro m
  induction m with
  | zero =>
      intro j pc μ _ _
      constructor
      · intro h; exact ⟨[], rfl, by simpa using h⟩
      · rintro ⟨bs, hbs, h⟩
        rw [List.length_eq_zero_iff.1 hbs] at h
        simpa using h
  | succ m ih =>
      intro j pc μ hj hP
      have hEx : P.getI pc = iEx (Tb + 2 * j) := by
        simpa using getI_guessProg_head (by omega) hP
      have hTail := acc_guessTail_iff (W := W) (μ := μ) hs (by omega) (by omega) hP
      have hrest : ∀ b : Bool, (Acc P W (pc + 4) (guessStep Gb MWb Tb j μ b) ↔
          ∃ bs : List Bool, bs.length = m ∧
            Acc P W (pc + 4 + 4 * m)
              (guessMem Gb MWb Tb (j + 1) (guessStep Gb MWb Tb j μ b) bs)) :=
        fun b => ih (by omega) (getI_guessProg_rest hP)
      rw [acc_ex_iff (W := W) (μ := μ) hEx]
      constructor
      · rintro ⟨b, hb⟩
        rw [hTail b, hrest b] at hb
        obtain ⟨bs, hlen, hacc⟩ := hb
        exact ⟨b :: bs, by simp [hlen], by
          rw [guessMem_cons, show pc + 4 * (m + 1) = pc + 4 + 4 * m by omega]
          exact hacc⟩
      · rintro ⟨bs, hlen, hacc⟩
        obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
          cases bs with
          | nil => simp at hlen
          | cons b bs' => exact ⟨b, bs', rfl⟩
        refine ⟨b, ?_⟩
        rw [hTail b, hrest b]
        refine ⟨bs', by simpa using hlen, ?_⟩
        rw [show pc + 4 + 4 * m = pc + 4 * (m + 1) by omega]
        rw [guessMem_cons] at hacc
        exact hacc

/-- **Guessing universally.** -/
theorem acc_guessAll (hs : GuessSep Gb MWb Tb NN) :
    ∀ {m j pc : ℕ} {μ : ℕ → Bool}, j + m ≤ NN →
      (∀ t < 4 * m, P.getI (pc + t) = (guessProg true Gb MWb Tb j m).getI t) →
      (Acc P W pc μ ↔ ∀ bs : List Bool, bs.length = m →
        Acc P W (pc + 4 * m) (guessMem Gb MWb Tb j μ bs)) := by
  intro m
  induction m with
  | zero =>
      intro j pc μ _ _
      constructor
      · intro h bs hbs
        rw [List.length_eq_zero_iff.1 hbs]
        simpa using h
      · intro h
        have := h [] rfl
        simpa using this
  | succ m ih =>
      intro j pc μ hj hP
      have hAll : P.getI pc = iAll (Tb + 2 * j) := by
        simpa using getI_guessProg_head (by omega) hP
      have hTail := acc_guessTail_iff (W := W) (μ := μ) hs (by omega) (by omega) hP
      have hrest : ∀ b : Bool, (Acc P W (pc + 4) (guessStep Gb MWb Tb j μ b) ↔
          ∀ bs : List Bool, bs.length = m →
            Acc P W (pc + 4 + 4 * m)
              (guessMem Gb MWb Tb (j + 1) (guessStep Gb MWb Tb j μ b) bs)) :=
        fun b => ih (by omega) (getI_guessProg_rest hP)
      rw [acc_all_iff (W := W) (μ := μ) hAll]
      constructor
      · rintro ⟨h0, h1⟩ bs hlen
        obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
          cases bs with
          | nil => simp at hlen
          | cons b bs' => exact ⟨b, bs', rfl⟩
        have hb : Acc P W (pc + 1) (memUpd μ (Tb + 2 * j) b) := by
          cases b with
          | false => exact h0
          | true => exact h1
        rw [hTail b, hrest b] at hb
        rw [guessMem_cons, show pc + 4 * (m + 1) = pc + 4 + 4 * m by omega]
        exact hb bs' (by simpa using hlen)
      · intro h
        have key : ∀ b : Bool, Acc P W (pc + 1) (memUpd μ (Tb + 2 * j) b) := by
          intro b
          rw [hTail b, hrest b]
          intro bs' hlen
          have := h (b :: bs') (by simp [hlen])
          rw [guessMem_cons, show pc + 4 * (m + 1) = pc + 4 + 4 * m by omega] at this
          exact this
        exact ⟨key false, key true⟩

/-- **Guessing existentially**, with a fuel. -/
theorem accN_guessEx (hs : GuessSep Gb MWb Tb NN) :
    ∀ {m j pc k : ℕ} {μ : ℕ → Bool}, j + m ≤ NN →
      (∀ t < 4 * m, P.getI (pc + t) = (guessProg false Gb MWb Tb j m).getI t) →
      AccN P W k pc μ →
      ∃ k' ≤ k, ∃ bs : List Bool, bs.length = m ∧
        AccN P W k' (pc + 4 * m) (guessMem Gb MWb Tb j μ bs) := by
  intro m
  induction m with
  | zero =>
      intro j pc k μ _ _ hacc
      exact ⟨k, le_rfl, [], rfl, by simpa using hacc⟩
  | succ m ih =>
      intro j pc k μ hj hP hacc
      have hEx : P.getI pc = iEx (Tb + 2 * j) := by
        simpa using getI_guessProg_head (by omega) hP
      obtain ⟨k₁, hk₁, b, hacc₁⟩ := accN_ex hacc hEx
      obtain ⟨k₂, hk₂, hacc₂⟩ :=
        accN_guessTail (W := W) (μ := μ) hs (by omega) (by omega) hP b hacc₁
      obtain ⟨k₃, hk₃, bs, hlen, hacc₃⟩ :=
        ih (by omega) (getI_guessProg_rest hP) hacc₂
      refine ⟨k₃, by omega, b :: bs, by simp [hlen], ?_⟩
      rw [guessMem_cons, show pc + 4 * (m + 1) = pc + 4 + 4 * m by omega]
      exact hacc₃

/-- **Guessing universally**, with a fuel. -/
theorem accN_guessAll (hs : GuessSep Gb MWb Tb NN) :
    ∀ {m j pc k : ℕ} {μ : ℕ → Bool}, j + m ≤ NN →
      (∀ t < 4 * m, P.getI (pc + t) = (guessProg true Gb MWb Tb j m).getI t) →
      AccN P W k pc μ →
      ∃ k' ≤ k, ∀ bs : List Bool, bs.length = m →
        AccN P W k' (pc + 4 * m) (guessMem Gb MWb Tb j μ bs) := by
  intro m
  induction m with
  | zero =>
      intro j pc k μ _ _ hacc
      refine ⟨k, le_rfl, fun bs hbs => ?_⟩
      rw [List.length_eq_zero_iff.1 hbs]
      simpa using hacc
  | succ m ih =>
      intro j pc k μ hj hP hacc
      have hAll : P.getI pc = iAll (Tb + 2 * j) := by
        simpa using getI_guessProg_head (by omega) hP
      obtain ⟨k₁, hk₁, hacc0, hacc1⟩ := accN_all hacc hAll
      have key : ∀ b : Bool, ∃ k' ≤ k₁, ∀ bs : List Bool, bs.length = m →
          AccN P W k' (pc + 4 + 4 * m)
            (guessMem Gb MWb Tb (j + 1) (guessStep Gb MWb Tb j μ b) bs) := by
        intro b
        have hb : AccN P W k₁ (pc + 1) (memUpd μ (Tb + 2 * j) b) := by
          cases b with
          | false => exact hacc0
          | true => exact hacc1
        obtain ⟨k₂, hk₂, hacc₂⟩ :=
          accN_guessTail (W := W) (μ := μ) hs (by omega) (by omega) hP b hb
        obtain ⟨k₃, hk₃, hall⟩ := ih (by omega) (getI_guessProg_rest hP) hacc₂
        exact ⟨k₃, by omega, hall⟩
      obtain ⟨kf, hkf, hf⟩ := key false
      obtain ⟨kt, hkt, ht⟩ := key true
      refine ⟨max kf kt, by omega, fun bs hlen => ?_⟩
      obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
        cases bs with
        | nil => simp at hlen
        | cons b bs' => exact ⟨b, bs', rfl⟩
      rw [guessMem_cons, show pc + 4 * (m + 1) = pc + 4 + 4 * m by omega]
      cases b with
      | false => exact (hf bs' (by simpa using hlen)).mono (le_max_left _ _)
      | true => exact (ht bs' (by simpa using hlen)).mono (le_max_right _ _)

end Acc

end Compile

end HTN
