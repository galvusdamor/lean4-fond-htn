import HtnComplexity.ToHtnAc.ToHtnAcComplete
/-!
# The length of the gadget runs of the TO-HTN ⟶ HTN-AC compilation

To bound the length of a plan of the compiled problem one needs the length of each of its
pieces.  This file collects them.

* `HTN.ToAc.yieldSeq_SELn_length`, `HTN.ToAc.yieldSeq_SEL_length`,
  `HTN.ToAc.yieldSeq_EQn_length`, `HTN.ToAc.yieldSeq_EQ_length` — **every** refinement of a
  state guess `SEL^i` or of a comparison `EQ^{i,j}` consists of exactly `|vars|` actions (one
  per fact of the source signature); this is the only place where the length of a piece is not
  read off its definition.
* `HTN.ToAc.length_memWrite`, `length_memRead` — a phase of a memory cell has `2|vars| + 3`
  actions;
* `HTN.ToAc.length_readPhase`, `length_writePhase` — a handshake with the memory phase answering
  it spliced in has `2|vars| + 5` actions;
* `HTN.ToAc.length_compoundBlock_le`, `HTN.ToAc.length_primBlock_le` — one scheduled proof step
  filling `w` memory cells has at most `blockLen |vars| w = 11|vars| + 15 + w·(2|vars| + 5)`
  actions.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### The state guesses and the comparisons -/

/-- **A refinement of `SEL_n^i` consists of exactly `n` actions.** -/
theorem yieldSeq_SELn_length : ∀ {n : ℕ} {i : Fin 5} {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.SELn n i)] as → as.length = n := by
  intro n
  induction n with
  | zero =>
      intro i as h
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_SELn_zero_iff] at hbs
      subst hbs
      simp only [List.nil_append, yieldSeq_nil_iff] at hy
      subst hy
      rfl
  | succ n ih =>
      intro i as h
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_SELn_succ_iff] at hbs
      obtain ⟨v, -, hbs⟩ := hbs
      rcases hbs with rfl | rfl <;>
        (simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
         obtain ⟨as', rfl, hy⟩ := hy
         simp [ih hy])

/-- **A refinement of `SEL^i` has one action per fact of the source signature.** -/
theorem yieldSeq_SEL_length {i : Fin 5} {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL i)] as) :
    as.length = vars.length :=
  yieldSeq_SELn_length (yieldSeq_SEL_iff.1 h)

/-- **A refinement of `EQ_n^{i,j}` consists of exactly `n` actions.** -/
theorem yieldSeq_EQn_length : ∀ {n : ℕ} {i j : Fin 5} {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQn n i j)] as → as.length = n := by
  intro n
  induction n with
  | zero =>
      intro i j as h
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_EQn_zero_iff] at hbs
      subst hbs
      simp only [List.nil_append, yieldSeq_nil_iff] at hy
      subst hy
      rfl
  | succ n ih =>
      intro i j as h
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_EQn_succ_iff] at hbs
      obtain ⟨v, -, hbs⟩ := hbs
      rcases hbs with rfl | rfl <;>
        (simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
         obtain ⟨as', rfl, hy⟩ := hy
         simp [ih hy])

/-- **A refinement of `EQ^{i,j}` has one action per fact of the source signature.** -/
theorem yieldSeq_EQ_length {i j : Fin 5} {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ i j)] as) :
    as.length = vars.length :=
  yieldSeq_EQn_length (yieldSeq_EQ_iff.1 h)

/-! ### The phases of a memory cell -/

@[simp] lemma length_testsOf (i : Fin 5) (S : Set F) (vs : List F) :
    (testsOf (A := A) (C := C) i S vs).length = vs.length := by
  simp [testsOf]

@[simp] lemma length_writesOf (j : Fin 5) (S : Set F) (vs : List F) :
    (writesOf (A := A) (C := C) j S vs).length = vs.length := by
  simp [writesOf]

@[simp] lemma length_memWrite (S S' : Set F) (t : A ⊕ C) (vs : List F) :
    (memWrite S S' t vs).length = 2 * vs.length + 3 := by
  simp [memWrite]; omega

@[simp] lemma length_memRead (S S' : Set F) (t : A ⊕ C) (vs : List F) :
    (memRead S S' t vs).length = 2 * vs.length + 3 := by
  simp [memRead]; omega

@[simp] lemma length_readPhase (S S' : Set F) (t : A ⊕ C) (vs : List F) :
    (readPhase S S' t vs).length = 2 * vs.length + 5 := by
  simp [readPhase]

@[simp] lemma length_writePhase (S S' : Set F) (t : A ⊕ C) (vs : List F) (w : ℕ) :
    (writePhase S S' t vs w).length = w * (2 * vs.length + 5) := by
  induction w with
  | zero => simp
  | succ w ih => rw [writePhase_succ]; simp [ih]; ring

/-! ### One scheduled proof step -/

/-- The length of one scheduled proof step filling `w` memory cells, in terms of the number
`v` of facts of the source signature. -/
def blockLen (v w : ℕ) : ℕ := 11 * v + 15 + w * (2 * v + 5)

lemma blockLen_mono_w {v w w' : ℕ} (h : w ≤ w') : blockLen v w ≤ blockLen v w' := by
  unfold blockLen
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- **The length of a scheduled compound proof step.** -/
theorem length_compoundBlock_le {c : C} {x y : A ⊕ C} {S S'' S' : Set F}
    {g₁ g₂ g₃ e₁ e₂ e₃ e₄ : List (AcAct F A C)} {w : ℕ}
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 3)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 4)] e₂)
    (he₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 3)] e₃)
    (he₄ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 2 4)] e₄) :
    (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w).length =
      blockLen vars.length w := by
  have h₁ := yieldSeq_SEL_length hg₁
  have h₂ := yieldSeq_SEL_length hg₂
  have h₃ := yieldSeq_SEL_length hg₃
  have h₄ := yieldSeq_EQ_length he₁
  have h₅ := yieldSeq_EQ_length he₂
  have h₆ := yieldSeq_EQ_length he₃
  have h₇ := yieldSeq_EQ_length he₄
  have hwrite : (compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w).length =
      11 * vars.length + 15 + (writePhase S S' (Sum.inr c : A ⊕ C) vars w).length := by
    simp only [compoundBlock, List.length_cons, List.length_append, List.length_nil,
      length_readPhase, h₁, h₂, h₃, h₄, h₅, h₆, h₇]
    ring
  rw [hwrite, length_writePhase]
  unfold blockLen
  omega

/-- **The length of a scheduled primitive proof step.** -/
theorem length_primBlock_le {o : A} {S T : Set F} {g₁ g₂ g₃ e₁ e₂ : List (AcAct F A C)} {w : ℕ}
    (hg₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 0)] g₁)
    (hg₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 1)] g₂)
    (hg₃ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL 2)] g₃)
    (he₁ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 0 1)] e₁)
    (he₂ : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ 1 2)] e₂) :
    (primBlock o S T g₁ g₂ g₃ e₁ e₂ vars w).length ≤ blockLen vars.length w := by
  have h₁ := yieldSeq_SEL_length hg₁
  have h₂ := yieldSeq_SEL_length hg₂
  have h₃ := yieldSeq_SEL_length hg₃
  have h₄ := yieldSeq_EQ_length he₁
  have h₅ := yieldSeq_EQ_length he₂
  have hwrite : (primBlock o S T g₁ g₂ g₃ e₁ e₂ vars w).length =
      5 * vars.length + 4 + (writePhase S T (Sum.inl o : A ⊕ C) vars w).length := by
    simp only [primBlock, List.length_cons, List.length_append, List.length_nil, h₁, h₂, h₃,
      h₄, h₅]
    ring
  rw [hwrite, length_writePhase]
  unfold blockLen
  omega

/-! ### The arithmetic of the scheduling induction

The plan built for a proof list of `n` entries with `c` pending memory cells has at most
`(2n + c)·(2|vars| + 5) + n·(11|vars| + 15)` actions.  One step of the induction appends one
block, of length at most `blockLen |vars| w`, to the plan of a shorter list; the two lemmas
below are the corresponding arithmetic, with `a = 2|vars| + 5` and `b = 11|vars| + 15`. -/

/-- One step of the induction: the plan `x` of the shorter list carries `c₀` pending cells
(the `c` cells demanded, plus at most the two cells that a compound step reads), and the block
`y` appended for the new entry starts `w` further ones. -/
lemma sched_len_step {n c c₀ w a b x y : ℕ} (hc : c₀ ≤ c + 2)
    (hx : x ≤ (2 * n + c₀) * a + n * b) (hy : y ≤ b + w * a) :
    x + y ≤ (2 * (n + 1) + (w + c)) * a + (n + 1) * b := by
  have h1 : (2 * n + c₀) * a ≤ (2 * n + (c + 2)) * a :=
    Nat.mul_le_mul_right _ (by omega)
  have key : (2 * (n + 1) + (w + c)) * a + (n + 1) * b
      = ((2 * n + (c + 2)) * a + n * b) + (b + w * a) := by ring
  omega

end ToAc

end HTN
