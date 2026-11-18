import HtnComplexity.UOSpace.TblSim
import HtnComplexity.Space.SeqGadget
/-!
# The action table for unordered HTN with an arbitrary (unordered) initial task network

The table `HTN.UOTbl.uoTbl d W` of `HtnComplexity/UOSpace/Table.lean` starts from a single
root fact.  For the unrooted class `UO-HTN` the initial task network is an arbitrary multiset of
tasks.  The machine for regular HTN with an initial task network
(`HtnComplexity/Space/ThrMachine.lean`) guesses and checks an initial configuration that
lists the tasks of the initial network in *slots* `0, 1, …, nIds - 1`: the fact "slot `p` carries
the task `x`", the fact "slot `p` carries a primitive task the domain does not mention", the fact
"there are `n` slots", and a sweep counter at `0`.  We reuse that machine and only replace the
table: `HTN.UOTbl.unTbl d W N` first **loads** the counters from the slots (one slot after the
other), then runs exactly the rows of `uoTbl` (with counters for the labels `labsU d`, which also
contain every primitive task the domain mentions).

The *input facts* (`fRoot c`, residue `3` modulo `4`) are

* `cLab p l` — slot `p` carries the task with label `l`;
* `cNop p` — slot `p` carries a primitive task unknown to the domain (a no-op);
* `cLen n` — there are `n` slots;
* `cCur 0` — the load has not started yet.

The load phase is controlled by the facts `fI (kCtl (kI d) p)` — the control facts of a method
number `kI d = d.methods.length` that does not exist — so the load rows are the `addRow`s of
`HtnComplexity/UOSpace/Table.lean` with one more precondition.

Input facts are never added by a row, so they only ever disappear; the rows of the main phase do
not mention them at all.  The simulation (`HtnComplexity/UOSpace/UnSim.lean`) therefore works
with the *stripped* state `strip s`, which forgets them.
-/

namespace HTN

namespace UOTbl

open Syn Space

/-! ### Labels and input facts -/

/-- **The labels with a counter**: the labels of the domain and all primitive tasks it
mentions. -/
def labsU (d : DomDesc) : List (Bool × ℕ) := labs d ++ (SeqG.vocA d).map (fun a => (false, a))

/-- The code of a label. -/
def lcode (l : Bool × ℕ) : ℕ := 2 * l.2 + cond l.1 1 0

theorem lcode_injective : Function.Injective lcode := by
  rintro ⟨b, n⟩ ⟨b', n'⟩ h
  simp only [lcode] at h
  cases b <;> cases b' <;> simp at h <;> first | (subst h; rfl) | omega

/-- Input fact code: slot `p` carries the label `l`. -/
def cLab (p : ℕ) (l : Bool × ℕ) : ℕ := 4 * Nat.pair p (lcode l)

/-- Input fact code: slot `p` carries an unknown primitive task. -/
def cNop (p : ℕ) : ℕ := 4 * p + 1

/-- Input fact code: there are `p` slots. -/
def cLen (p : ℕ) : ℕ := 4 * p + 2

/-- Input fact code: the sweep counter is at `p`. -/
def cCur (p : ℕ) : ℕ := 4 * p + 3

/-- The (non-existent) method number whose control facts run the load phase. -/
def kI (d : DomDesc) : ℕ := d.methods.length

/-! ### The load rows -/

/-- **Zero**: consume `cCur 0`, set every counter to zero, start loading slot `0`. -/
def zeroRow (L : List (Bool × ℕ)) (W k : ℕ) : Row :=
  ([fRoot (cCur 0)], fI (kCtl k 0) :: zerosAll L W, [fRoot (cCur 0)])

/-- **Load** slot `p`, carrying `l`: increment the counter of `l` (lowest zero bit `i`). -/
def labRow (k p : ℕ) (l : Bool × ℕ) (i : ℕ) : Row :=
  (fRoot (cLab p l) :: (addRow k p l i).1, (addRow k p l i).2.1, (addRow k p l i).2.2)

/-- **Skip** slot `p`, carrying an unknown primitive task. -/
def nopRow (k p : ℕ) : Row := ([fI (kCtl k p), fRoot (cNop p)], [fI (kCtl k (p + 1))], [fI (kCtl k p)])

/-- **Stop** loading: all `p` slots are loaded. -/
def doneRow (k p : ℕ) : Row := ([fI (kCtl k p), fRoot (cLen p)], [fI kIdle], [fI (kCtl k p)])

/-- The load rows, for at most `N` slots. -/
def initRows (d : DomDesc) (W N : ℕ) : List Row :=
  zeroRow (labsU d) W (kI d) ::
    ((List.range N).flatMap fun p => nopRow (kI d) p ::
      (labsU d).flatMap fun l => (List.range W).map (labRow (kI d) p l)) ++
    (List.range (N + 1)).map (doneRow (kI d))

/-- **The action table for unordered HTN with an initial task network of at most `N` tasks and
counters of `W` bits.** -/
def unTbl (d : DomDesc) (W N : ℕ) : List Row :=
  initRows d W N ++
    ((labsU d).filter (fun l => l.1 = false)).flatMap (fun l => (List.range W).map (exeRow d l)) ++
    d.methods.zipIdx.flatMap (methRows W) ++
    [finRow (labsU d) W]

theorem mem_unTbl {d : DomDesc} {W N : ℕ} {r : Row} :
    r ∈ unTbl d W N ↔ r = zeroRow (labsU d) W (kI d) ∨
      (∃ p < N, r = nopRow (kI d) p) ∨
      (∃ p < N, ∃ l ∈ labsU d, ∃ i < W, r = labRow (kI d) p l i) ∨
      (∃ p ≤ N, r = doneRow (kI d) p) ∨
      (∃ l ∈ labsU d, l.1 = false ∧ ∃ i < W, r = exeRow d l i) ∨
      (∃ k e, d.methods[k]? = some e ∧ ((∃ i < W, r = decRow k e i) ∨
        (∃ p l, (body e)[p]? = some l ∧ ∃ i < W, r = addRow k p l i) ∨
        r = endRow k (body e).length)) ∨
      r = finRow (labsU d) W := by
  simp only [unTbl, initRows, methRows, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_flatMap, List.mem_filter, List.mem_range,
    List.mem_zipIdx_iff_getElem?, decide_eq_true_eq, List.not_mem_nil, or_false]
  constructor
  · rintro (((((rfl | ⟨p, hp, rfl | ⟨l, hl, i, hi, rfl⟩⟩) | ⟨p, hp, rfl⟩) |
      ⟨l, ⟨hl, hl1⟩, i, hi, rfl⟩) |
      ⟨⟨e, k⟩, hk, ((⟨i, hi, rfl⟩ | ⟨⟨l, p⟩, hp, i, hi, rfl⟩) | rfl)⟩) | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, hp, l, hl, i, hi, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by omega, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, hl1, i, hi, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, e, hk, Or.inl ⟨i, hi, rfl⟩⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, e, hk, Or.inr (Or.inl ⟨p, l, hp, i, hi, rfl⟩)⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, e, hk, Or.inr (Or.inr rfl)⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · rintro (rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, l, hl, i, hi, rfl⟩ | ⟨p, hp, rfl⟩ |
      ⟨l, hl, hl1, i, hi, rfl⟩ | ⟨k, e, hk, (⟨i, hi, rfl⟩ | ⟨p, l, hp, i, hi, rfl⟩ | rfl)⟩ | rfl)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨p, hp, Or.inl rfl⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨p, hp, Or.inr ⟨l, hl, i, hi, rfl⟩⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨p, by omega, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨l, ⟨hl, hl1⟩, i, hi, rfl⟩))
    · exact Or.inl (Or.inr ⟨(e, k), hk, Or.inl (Or.inl ⟨i, hi, rfl⟩)⟩)
    · exact Or.inl (Or.inr ⟨(e, k), hk, Or.inl (Or.inr ⟨(l, p), hp, i, hi, rfl⟩)⟩)
    · exact Or.inl (Or.inr ⟨(e, k), hk, Or.inr rfl⟩)
    · exact Or.inr rfl

theorem labs_sub_labsU {d : DomDesc} {l : Bool × ℕ} (h : l ∈ labs d) : l ∈ labsU d :=
  List.mem_append_left _ h

theorem prim_mem_labsU {d : DomDesc} {a : ℕ} (h : a ∈ SeqG.vocA d) : (false, a) ∈ labsU d :=
  List.mem_append_right _ (List.mem_map_of_mem h)

/-! ### Residues -/

/-- An input fact. -/
def IsIn (f : ℕ) : Prop := f % 4 = 3

instance : DecidablePred IsIn := fun f => inferInstanceAs (Decidable (f % 4 = 3))

@[simp] theorem isIn_fRoot (c : ℕ) : IsIn (fRoot c) := by simp only [IsIn, fRoot]; omega
@[simp] theorem not_isIn_fSt (v : ℕ) : ¬ IsIn (fSt v) := by simp only [IsIn, fSt]; omega
@[simp] theorem not_isIn_fI (k : ℕ) : ¬ IsIn (fI k) := by simp only [IsIn, fI]; omega
@[simp] theorem not_isIn_fDone : ¬ IsIn fDone := by simp [IsIn, fDone]
@[simp] theorem not_isIn_bitF (l : Bool × ℕ) (i : ℕ) (b : Bool) : ¬ IsIn (bitF l i b) :=
  not_isIn_fI _

theorem isIn_iff {f : ℕ} : IsIn f ↔ ∃ c, f = fRoot c := by
  constructor
  · intro h; exact ⟨f / 4, by simp only [IsIn] at h; simp only [fRoot]; omega⟩
  · rintro ⟨c, rfl⟩; exact isIn_fRoot c

/-- **The stripped state**: the input facts forgotten. -/
def strip (s : List ℕ) : List ℕ := s.filter (fun f => decide (¬ IsIn f))

@[simp] theorem mem_strip {s : List ℕ} {f : ℕ} : f ∈ strip s ↔ f ∈ s ∧ ¬ IsIn f := by
  simp [strip]

theorem strip_post {r : Row} {s s' : List ℕ} (hadd : ∀ f ∈ r.2.1, ¬ IsIn f)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ r.2.1 ∨ (f ∈ s ∧ f ∉ r.2.2)) :
    ∀ f, f ∈ strip s' ↔ f ∈ r.2.1 ∨ (f ∈ strip s ∧ f ∉ r.2.2) := by
  intro f
  rw [mem_strip, mem_strip, hs']
  constructor
  · rintro ⟨h | h, hf⟩
    · exact Or.inl h
    · exact Or.inr ⟨⟨h.1, hf⟩, h.2⟩
  · rintro (h | h)
    · exact ⟨Or.inl h, hadd f h⟩
    · exact ⟨Or.inr ⟨h.1.1, h.2⟩, h.1.2⟩

theorem strip_applyRow {r : Row} {s : List ℕ} (hadd : ∀ f ∈ r.2.1, ¬ IsIn f) :
    ∀ f, f ∈ strip (applyRow r s) ↔ f ∈ r.2.1 ∨ (f ∈ strip s ∧ f ∉ r.2.2) :=
  strip_post hadd fun _ => mem_applyRow

theorem pre_strip {r : Row} {s : List ℕ} (hpre : ∀ f ∈ r.1, ¬ IsIn f)
    (h : ∀ f ∈ r.1, f ∈ s) : ∀ f ∈ r.1, f ∈ strip s :=
  fun f hf => mem_strip.2 ⟨h f hf, hpre f hf⟩

theorem pre_of_strip {r : Row} {s : List ℕ} (h : ∀ f ∈ r.1, f ∈ strip s) : ∀ f ∈ r.1, f ∈ s :=
  fun f hf => (mem_strip.1 (h f hf)).1

/-! ### No row adds an input fact; the main rows do not mention them -/

theorem not_isIn_lowF {l : Bool × ℕ} {i : ℕ} {v : Bool} : ∀ f ∈ lowF l i v, ¬ IsIn f := by
  intro f hf
  simp only [lowF, List.mem_map] at hf
  obtain ⟨j, -, rfl⟩ := hf
  exact not_isIn_bitF _ _ _

theorem not_isIn_decPre {l : Bool × ℕ} {i : ℕ} : ∀ f ∈ decPre l i, ¬ IsIn f := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  · exact not_isIn_bitF _ _ _
  · exact not_isIn_lowF f hf

theorem not_isIn_decAdd {l : Bool × ℕ} {i : ℕ} : ∀ f ∈ decAdd l i, ¬ IsIn f := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  · exact not_isIn_bitF _ _ _
  · exact not_isIn_lowF f hf

theorem not_isIn_zerosAll {L : List (Bool × ℕ)} {W : ℕ} : ∀ f ∈ zerosAll L W, ¬ IsIn f := by
  intro f hf
  obtain ⟨l, j, b, rfl⟩ := mem_zerosAll_shape hf
  exact not_isIn_bitF _ _ _

theorem not_isIn_map_fSt {xs : List ℕ} : ∀ f ∈ xs.map fSt, ¬ IsIn f := by
  intro f hf
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hf
  exact not_isIn_fSt v

/-- A row of the main phase. -/
def MainRow (d : DomDesc) (W : ℕ) (r : Row) : Prop :=
  (∃ l ∈ labsU d, l.1 = false ∧ ∃ i < W, r = exeRow d l i) ∨
    (∃ k e, d.methods[k]? = some e ∧ ((∃ i < W, r = decRow k e i) ∨
      (∃ p l, (body e)[p]? = some l ∧ ∃ i < W, r = addRow k p l i) ∨
      r = endRow k (body e).length)) ∨
    r = finRow (labsU d) W

/-- The rows of the main phase mention no input fact. -/
theorem mainRow_clean {d : DomDesc} {W : ℕ} {r : Row} (h : MainRow d W r) :
    (∀ f ∈ r.1, ¬ IsIn f) ∧ (∀ f ∈ r.2.1, ¬ IsIn f) := by
  rcases h with ⟨l, -, -, i, -, rfl⟩ | ⟨k, e, -, (⟨i, -, rfl⟩ | ⟨p, l, -, i, -, rfl⟩ | rfl)⟩ | rfl
  · refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simp only [exeRow, List.mem_cons, List.mem_append, or_assoc] at hf
      rcases hf with rfl | hf | hf
      · exact not_isIn_fI _
      · exact not_isIn_decPre f hf
      · exact not_isIn_map_fSt f hf
    · simp only [exeRow, List.mem_append] at hf
      rcases hf with hf | hf
      · exact not_isIn_decAdd f hf
      · exact not_isIn_map_fSt f hf
  · refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simp only [decRow, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact not_isIn_fI _
      · exact not_isIn_decPre f hf
    · simp only [decRow, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact not_isIn_fI _
      · exact not_isIn_decAdd f hf
  · refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simp only [addRow, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact not_isIn_fI _
      · exact not_isIn_decAdd f hf
    · simp only [addRow, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact not_isIn_fI _
      · exact not_isIn_decPre f hf
  · refine ⟨fun f hf => ?_, fun f hf => ?_⟩ <;> simp [endRow] at hf <;> subst hf <;> exact not_isIn_fI _
  · refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simp only [finRow, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact not_isIn_fI _
      · exact not_isIn_zerosAll f hf
    · simp [finRow] at hf; subst hf; exact not_isIn_fDone

/-- **No row of the table adds an input fact.** -/
theorem add_clean {d : DomDesc} {W N : ℕ} {r : Row} (hr : r ∈ unTbl d W N) :
    ∀ f ∈ r.2.1, ¬ IsIn f := by
  rcases mem_unTbl.1 hr with rfl | ⟨p, -, rfl⟩ | ⟨p, -, l, -, i, -, rfl⟩ | ⟨p, -, rfl⟩ | h | h | h
  · intro f hf
    simp only [zeroRow, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact not_isIn_fI _
    · exact not_isIn_zerosAll f hf
  · intro f hf; simp [nopRow] at hf; subst hf; exact not_isIn_fI _
  · intro f hf
    simp only [labRow, addRow, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact not_isIn_fI _
    · exact not_isIn_decPre f hf
  · intro f hf; simp [doneRow] at hf; subst hf; exact not_isIn_fI _
  · exact (mainRow_clean (Or.inl h)).2
  · exact (mainRow_clean (Or.inr (Or.inl h))).2
  · exact (mainRow_clean (Or.inr (Or.inr h))).2

/-! ### The load rows on represented states -/

theorem zero_post {s s' : List ℕ} {σ : Finset ℕ} {L : List (Bool × ℕ)} {W k : ℕ}
    (hs : ∀ f, f ∈ s ↔ StP σ f)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (zeroRow L W k).2.1 ∨ (f ∈ s ∧ f ∉ (zeroRow L W k).2.2)) :
    Rep L W σ 0 (· = fI (kCtl k 0)) s' := by
  refine rep_of (fun x hx => by simp at hx) (fun l' => by simp) (ctlOK_ctl k 0) (fun v => ?_)
    (fun l' j b => ?_) (fun f hf1 hf2 => ?_)
  · rw [hs']
    simp only [zeroRow, List.mem_cons, fSt_ne_fI, false_or, hs, stP_fSt, List.not_mem_nil,
      or_false, fSt_ne_fRoot, not_false_eq_true, and_true]
    constructor
    · rintro (hz | h)
      · obtain ⟨l, j, b, he⟩ := mem_zerosAll_shape hz
        exact absurd he (fSt_ne_bitF _ _ _ _)
      · exact h
    · exact Or.inr
  · rw [hs']
    simp only [zeroRow, List.mem_cons, bitF_eq_fI_iff, kBit_ne_kCtl, false_or, hs, stP_bitF,
      false_and, or_false, mem_zerosAll, Multiset.count_zero, Nat.zero_testBit]
  · rw [hs']
    have hz : f ∉ zerosAll L W := fun hz => by
      obtain ⟨l, j, b, rfl⟩ := mem_zerosAll_shape hz; exact hf2 l j b rfl
    simp only [zeroRow, List.mem_cons, hz, or_false, hs, not_stP hf1, false_and,
      List.not_mem_nil]

theorem lab_pre {L W σ M C s} (h : Rep L W σ M C (strip s)) (hC : CtlOK C) (k p : ℕ)
    (l : Bool × ℕ) (i : ℕ) :
    (∀ f ∈ (labRow k p l i).1, f ∈ s) ↔ fRoot (cLab p l) ∈ s ∧ C (fI (kCtl k p)) ∧
      (l ∈ L ∧ i < W ∧ (∀ j < i, (M.count l).testBit j = true) ∧
        (M.count l).testBit i = false) := by
  rw [← add_pre h hC k p l i]
  simp only [labRow, List.mem_cons, forall_eq_or_imp]
  apply and_congr Iff.rfl
  constructor
  · intro h' f hf
    refine mem_strip.2 ⟨h' f hf, ?_⟩
    simp only [addRow, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact not_isIn_fI _
    · exact not_isIn_decAdd f hf
  · intro h' f hf
    exact (mem_strip.1 (h' f hf)).1

theorem nop_pre {L W σ M C s} (h : Rep L W σ M C (strip s)) (k p : ℕ) :
    (∀ f ∈ (nopRow k p).1, f ∈ s) ↔ C (fI (kCtl k p)) ∧ fRoot (cNop p) ∈ s := by
  simp only [nopRow, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, or_false, forall_eq]
  rw [← h.mem_ctl k p, mem_strip]
  simp

theorem nop_post {L W σ M s s'} {k p : ℕ} (h : Rep L W σ M (· = fI (kCtl k p)) s)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (nopRow k p).2.1 ∨ (f ∈ s ∧ f ∉ (nopRow k p).2.2)) :
    Rep L W σ M (· = fI (kCtl k (p + 1))) s' := by
  refine rep_of h.1 h.2.1 (ctlOK_ctl k (p + 1)) (fun v => ?_) (fun l' j b => ?_)
    (fun f hf1 hf2 => ?_)
  · rw [hs']; simp [nopRow, h.mem_fSt (ctlOK_ctl k p)]
  · rw [hs']; simp [nopRow, h.mem_bitF (ctlOK_ctl k p)]
  · rw [hs']
    simp only [nopRow, List.mem_cons, List.not_mem_nil, or_false, h.mem_other hf1 hf2]
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact h1
      · exact absurd h1 h2
    · exact Or.inl

theorem done_pre {L W σ M C s} (h : Rep L W σ M C (strip s)) (k p : ℕ) :
    (∀ f ∈ (doneRow k p).1, f ∈ s) ↔ C (fI (kCtl k p)) ∧ fRoot (cLen p) ∈ s := by
  simp only [doneRow, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, or_false, forall_eq]
  rw [← h.mem_ctl k p, mem_strip]
  simp

theorem done_post {L W σ M s s'} {k p : ℕ} (h : Rep L W σ M (· = fI (kCtl k p)) s)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ (doneRow k p).2.1 ∨ (f ∈ s ∧ f ∉ (doneRow k p).2.2)) :
    Rep L W σ M (· = fI kIdle) s' :=
  end_post h (k := k) (n := p) (by simpa [doneRow, endRow] using hs')

theorem zero_pre {s : List ℕ} {L : List (Bool × ℕ)} {W k : ℕ} :
    (∀ f ∈ (zeroRow L W k).1, f ∈ s) ↔ fRoot (cCur 0) ∈ s := by
  simp [zeroRow]

end UOTbl

end HTN
