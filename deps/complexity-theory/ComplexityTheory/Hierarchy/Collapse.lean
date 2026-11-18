import ComplexityTheory.Hierarchy.Swap
/-!
# From one quantifier swap to the collapse of the whole hierarchy

`Swap.lean` proves `Π₂ ⊆ Σ₂` with parameters (`HTN.Hier.SwapParams`).  Karp–Lipton is usually
quoted with the *hierarchy* as its conclusion, and getting from the one swap to the whole
hierarchy is a separate argument: every level is pushed down to the second one by induction,
using the swap inside a longer quantifier prefix, complementation to turn the existential
statement into the universal one, and a pairing to merge two adjacent quantifiers of the same
kind.

This file carries that argument out, at an arbitrary scale.

## Main definitions and results

* `HTN.Hier.qpreP` — the quantifier prefix with a list of parameters already fixed, and its
  unfolding lemmas;
* `HTN.Hier.notRel`, `HTN.Hier.qpre_notRel` — complementation commutes with the prefix, swapping
  the two sides of the hierarchy;
* `HTN.Hier.Closure` — the closure properties of the scale the induction uses: the base class is
  closed under complement, under ignoring the last quantified string, and under splitting a
  paired quantified string, and the quantifier budget has a pairing;
* `HTN.Hier.LevelTwo` — "every level-`k` block, with parameters, is a level-`2` block";
* `HTN.Hier.levelTwo_of_swapParams` — **the induction**: with the closure properties and the
  swap, `LevelTwo s k b` for every `k` and both sides;
* `HTN.Hier.collapseAt_two_of_swapParams` — **the collapse**: `CollapseAt s 2`.  Read at the weak
  exponential scale this is `EXPH = Σ₂^EXP`;
* `HTN.Hier.collapseAt_two_of_decisionAdvice` — the two halves together: the closure properties,
  the search closure of `Swap.lean` and the advice hypothesis give the collapse.  This is the
  Karp–Lipton theorem of the weak exponential hierarchy,
  `NEXPTIME ⊆ EXPTIME/poly ⟹ EXPH = Σ₂^EXP`, modulo the named closure properties of the scale.
-/

namespace HTN

namespace Hier

variable {s : Scale}

/-! ### The prefix with parameters -/

/-- **The quantifier prefix with parameters.**  `qpreP s R k b x ws` puts `k` alternating
quantifiers, starting with `∃` when `b = true`, in front of `R x (ws ++ …)`: the strings of `ws`
are already fixed, the new ones are appended to them in the order they are introduced. -/
def qpreP (s : Scale) (R : Rel) (k : ℕ) (b : Bool) (x : Word) (ws : List Word) : Prop :=
  qpre s R k b x ws.reverse

@[simp] theorem qpreP_zero (R : Rel) (b : Bool) (x : Word) (ws : List Word) :
    qpreP s R 0 b x ws ↔ R x ws := by
  simp [qpreP]

@[simp] theorem qpreP_succ_true (R : Rel) (k : ℕ) (x : Word) (ws : List Word) :
    qpreP s R (k + 1) true x ws ↔
      ∃ y, s.Q x.length y ∧ qpreP s R k false x (ws ++ [y]) := by
  simp [qpreP]

@[simp] theorem qpreP_succ_false (R : Rel) (k : ℕ) (x : Word) (ws : List Word) :
    qpreP s R (k + 1) false x ws ↔
      ∀ y, s.Q x.length y → qpreP s R k true x (ws ++ [y]) := by
  simp [qpreP]

theorem sigmaLevel_iff_qpreP (k : ℕ) (L : Lang) :
    SigmaLevel s k L ↔ ∃ R, s.base R ∧ ∀ x, L x ↔ qpreP s R k true x [] := by
  simp [SigmaLevel, qpreP]

/-! ### Complementation -/

/-- The complement of a relation. -/
def notRel (R : Rel) : Rel := fun x ys => ¬ R x ys

/-- **Complementation swaps the two sides of the hierarchy**: the prefix of the complement is the
complement of the opposite prefix. -/
theorem qpre_notRel (R : Rel) (x : Word) :
    ∀ (k : ℕ) (b : Bool) (ys : List Word),
      qpre s (notRel R) k b x ys ↔ ¬ qpre s R k (!b) x ys := by
  intro k
  induction k with
  | zero => intro b ys; simp [notRel]
  | succ k ih =>
      intro b ys
      cases b with
      | true =>
          simp only [qpre_succ_true, Bool.not_true, qpre_succ_false]
          constructor
          · rintro ⟨y, hy, h⟩ hall
            exact ((ih false (y :: ys)).1 h) (hall y hy)
          · intro hnot
            by_contra hex
            refine hnot fun y hy => ?_
            by_contra hcon
            exact hex ⟨y, hy, (ih false (y :: ys)).2 hcon⟩
      | false =>
          simp only [qpre_succ_false, Bool.not_false, qpre_succ_true]
          constructor
          · rintro hall ⟨y, hy, h⟩
            exact ((ih true (y :: ys)).1 (hall y hy)) h
          · intro hnot y hy
            exact (ih true (y :: ys)).2 fun hq => hnot ⟨y, hy, hq⟩

theorem qpreP_notRel (R : Rel) (k : ℕ) (b : Bool) (x : Word) (ws : List Word) :
    qpreP s (notRel R) k b x ws ↔ ¬ qpreP s R k (!b) x ws :=
  qpre_notRel R x k b ws.reverse

/-! ### Merging two adjacent quantifiers -/

/-- The relation obtained by splitting the second-to-last quantified string into a pair: it is
what merges two adjacent quantifiers of the same kind into one. -/
def unpairRel (fst snd : Word → Word) (R : Rel) : Rel := fun x ys =>
  match ys.reverse with
  | v :: t :: rest => R x (rest.reverse ++ [fst t, snd t, v])
  | _ => False

@[simp] theorem unpairRel_apply (fst snd : Word → Word) (R : Rel) (x : Word) (ws : List Word)
    (t v : Word) :
    unpairRel fst snd R x (ws ++ [t, v]) ↔ R x (ws ++ [fst t, snd t, v]) := by
  have hrev : (ws ++ [t, v]).reverse = v :: t :: ws.reverse := by simp
  simp [unpairRel, hrev]

/-- **The closure properties of the scale used by the collapse induction.**

The base class must be closed under complement (it is a *deterministic* class), under ignoring
the last quantified string (so that a short prefix can be padded to a longer one), and under
splitting a paired quantified string; and the quantifier budget must have a pairing.  All of them
hold at the polynomial scale and at the weak exponential scale, with the usual bit-doubling
pairing. -/
structure Closure (s : Scale) where
  /-- The base class is closed under complement. -/
  compl : ∀ R, s.base R → s.base (notRel R)
  /-- The base class is closed under ignoring the last quantified string. -/
  dropLast : ∀ R, s.base R → s.base fun x ys => R x ys.dropLast
  /-- The pairing of two quantified strings. -/
  pair : Word → Word → Word
  /-- The first component of a paired string. -/
  fst : Word → Word
  /-- The second component of a paired string. -/
  snd : Word → Word
  /-- The first component of a pair is the first string. -/
  fst_pair : ∀ u v, fst (pair u v) = u
  /-- The second component of a pair is the second string. -/
  snd_pair : ∀ u v, snd (pair u v) = v
  /-- A pair of admissible strings is admissible. -/
  Q_pair : ∀ n u v, s.Q n u → s.Q n v → s.Q n (pair u v)
  /-- The first component of an admissible string is admissible. -/
  Q_fst : ∀ n t, s.Q n t → s.Q n (fst t)
  /-- The second component of an admissible string is admissible. -/
  Q_snd : ∀ n t, s.Q n t → s.Q n (snd t)
  /-- The base class is closed under splitting the second-to-last quantified string. -/
  base_unpair : ∀ R, s.base R → s.base (unpairRel fst snd R)

/-! ### The induction -/

/-- **Every level-`k` block, with parameters, is a level-`2` block of the same side.**  For
`b = true` this is `Σ_k ⊆ Σ₂`, for `b = false` it is `Π_k ⊆ Π₂`, both with parameters. -/
def LevelTwo (s : Scale) (k : ℕ) (b : Bool) : Prop :=
  ∀ R, s.base R → ∃ R', s.base R' ∧ ∀ x ws, (∀ w ∈ ws, s.Q x.length w) →
    (qpreP s R k b x ws ↔ qpreP s R' 2 b x ws)

/-- The universal side follows from the existential one, by complementation. -/
theorem levelTwo_false_of_true (c : Closure s) {k : ℕ} (h : LevelTwo s k true) :
    LevelTwo s k false := by
  intro R hR
  obtain ⟨R₁, hR₁, hiff⟩ := h (notRel R) (c.compl R hR)
  refine ⟨notRel R₁, c.compl R₁ hR₁, fun x ws hws => ?_⟩
  have h1 : qpreP s (notRel R) k true x ws ↔ ¬ qpreP s R k false x ws :=
    qpreP_notRel R k true x ws
  have h2 : qpreP s (notRel R₁) 2 false x ws ↔ ¬ qpreP s R₁ 2 true x ws :=
    qpreP_notRel R₁ 2 false x ws
  rw [h2, ← hiff x ws hws, h1, not_not]

/-- Level `0`, with parameters, is a level-`2` block: two dummy quantifiers are added. -/
theorem levelTwo_zero (c : Closure s) : LevelTwo s 0 true := by
  intro R hR
  refine ⟨fun x ys => R x ys.dropLast.dropLast, c.dropLast _ (c.dropLast R hR),
    fun x ws _ => ?_⟩
  simp only [qpreP_zero, qpreP_succ_true, qpreP_succ_false]
  constructor
  · intro h
    refine ⟨[], s.Q_nil _, fun z _ => ?_⟩
    simpa [List.append_assoc] using h
  · rintro ⟨y, -, h⟩
    have := h [] (s.Q_nil _)
    simpa [List.append_assoc] using this

/-- The successor step: a level-`(k + 1)` block is a level-`2` block, given that the level-`k`
blocks of the opposite side are.  This is where the swap and the pairing are used. -/
theorem levelTwo_succ (c : Closure s) (hsw : SwapParams s) {k : ℕ}
    (h : LevelTwo s k false) : LevelTwo s (k + 1) true := by
  intro R hR
  obtain ⟨R₁, hR₁, h₁⟩ := h R hR
  obtain ⟨R₂, hR₂, h₂⟩ := hsw R₁ hR₁
  refine ⟨unpairRel c.fst c.snd R₂, c.base_unpair R₂ hR₂, fun x ws hws => ?_⟩
  have hadm : ∀ y, s.Q x.length y → ∀ w ∈ ws ++ [y], s.Q x.length w := by
    intro y hy w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · exact hws w hw
    · exact hw ▸ hy
  simp only [qpreP_succ_true, qpreP_succ_false, qpreP_zero]
  constructor
  · rintro ⟨y, hy, hblock⟩
    -- the block after `y` is a `Π₂` block over `R₁`, hence an `Σ₂` block over `R₂`
    have hPi : ∀ z, s.Q x.length z → ∃ w, s.Q x.length w ∧ R₁ x (ws ++ [y] ++ [z, w]) := by
      intro z hz
      have := (h₁ x (ws ++ [y]) (hadm y hy)).1 hblock
      simp only [qpreP_succ_false, qpreP_succ_true, qpreP_zero] at this
      obtain ⟨w, hw, hR⟩ := this z hz
      exact ⟨w, hw, by simpa [List.append_assoc] using hR⟩
    obtain ⟨cadv, hcadv, hswap⟩ := (h₂ x (ws ++ [y]) (hadm y hy)).1 hPi
    refine ⟨c.pair y cadv, c.Q_pair _ _ _ hy hcadv, fun z hz => ?_⟩
    have := hswap z hz
    simp only [List.append_assoc, List.cons_append, List.nil_append, unpairRel_apply,
      c.fst_pair, c.snd_pair]
    simpa [List.append_assoc] using this
  · rintro ⟨t, ht, hblock⟩
    refine ⟨c.fst t, c.Q_fst _ _ ht, ?_⟩
    refine (h₁ x (ws ++ [c.fst t]) (hadm _ (c.Q_fst _ _ ht))).2 ?_
    have hswap : ∃ d, s.Q x.length d ∧ ∀ z, s.Q x.length z →
        R₂ x (ws ++ [c.fst t] ++ [d, z]) := by
      refine ⟨c.snd t, c.Q_snd _ _ ht, fun z hz => ?_⟩
      have := hblock z hz
      simp only [List.append_assoc, List.cons_append, List.nil_append, unpairRel_apply] at this
      simpa [List.append_assoc] using this
    have := (h₂ x (ws ++ [c.fst t]) (hadm _ (c.Q_fst _ _ ht))).2 hswap
    simp only [qpreP_succ_false, qpreP_succ_true, qpreP_zero]
    intro z hz
    obtain ⟨w, hw, hR⟩ := this z hz
    exact ⟨w, hw, by simpa [List.append_assoc] using hR⟩

/-- **The induction.**  With the closure properties and the swap, every level of either side is a
level-`2` block of that side, with parameters. -/
theorem levelTwo_of_swapParams (c : Closure s) (hsw : SwapParams s) :
    ∀ k, LevelTwo s k true ∧ LevelTwo s k false := by
  intro k
  induction k with
  | zero =>
      have h := levelTwo_zero c
      exact ⟨h, levelTwo_false_of_true c h⟩
  | succ k ih =>
      have h := levelTwo_succ c hsw ih.2
      exact ⟨h, levelTwo_false_of_true c h⟩

/-- **The collapse of the hierarchy to its second level.**  Read at the weak exponential scale:
`EXPH = Σ₂^EXP`. -/
theorem collapseAt_two_of_swapParams (c : Closure s) (hsw : SwapParams s) : CollapseAt s 2 := by
  intro j L hL
  obtain ⟨R, hR, hLR⟩ := (sigmaLevel_iff_qpreP j L).1 hL
  obtain ⟨R', hR', hiff⟩ := (levelTwo_of_swapParams c hsw j).1 R hR
  refine (sigmaLevel_iff_qpreP 2 L).2 ⟨R', hR', fun x => ?_⟩
  rw [hLR x]
  exact hiff x [] (by simp)

/-- **The Karp–Lipton theorem of the weak exponential hierarchy**, at an arbitrary scale and with
every hypothesis named: from the advice hypothesis — at the weak exponential scale,
`NEXPTIME ⊆ EXPTIME/poly` — the hierarchy of the scale collapses to its second level,
`EXPH = Σ₂^EXP`.

Besides the advice hypothesis the proof uses only the closure properties of the scale: the search
closure of `Swap.lean`, which lets the base class run the bit-by-bit self-reduction, and the
`Closure` of this file.  Both hold at the polynomial scale and at the weak exponential scale; it
is the *strong* exponential hierarchy that fails to satisfy them, its outer machine being unable
even to read the strings it quantifies over (`Strong.lean`). -/
theorem collapseAt_two_of_decisionAdvice (c : Closure s) (sr : SearchClosure s)
    (hadv : ∀ R, s.base R → DecisionAdviceP s R) : CollapseAt s 2 :=
  collapseAt_two_of_swapParams c (sr.swapParams hadv)

end Hier

end HTN
