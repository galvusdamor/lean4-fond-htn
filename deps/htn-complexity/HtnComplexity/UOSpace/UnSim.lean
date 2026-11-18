import HtnComplexity.UOSpace.UnTable
/-!
# The unrooted unordered-HTN table simulates the abstract progression

The initial state `s₀` of the table `HTN.UOTbl.unTbl d W N` is described *abstractly* by a slot
labelling `lab : ℕ → Bool × ℕ` of `n₀` slots whose multiset of labels is the multiset of tasks of
the initial network (`hM`):

* `strip s₀` carries exactly the facts `fSt v` of the initial state (`hS`);
* (soundness) every input fact of `s₀` tells the truth about the slots (`HTN.UOTbl.InOK`);
* (completeness) `s₀` carries `cCur 0`, `cLen n₀`, the fact `cLab p (lab p)` for every slot with a
  label in `labsU d`, and `cNop p` for every slot carrying an unknown primitive task.

Then

* `HTN.UOTbl.solvable_of_solvableTblU` — reaching the goal `goalU q` in the table gives a plan;
* `HTN.UOTbl.solvableTblU_of_solvable` — a plan gives a run of the table, provided the counters
  are wide enough: `n₀ + uoBndP d q * maxBody d < 2 ^ W`, and `n₀ ≤ N`.
-/

namespace HTN

namespace UOTbl

open Syn Space UOAbs

/-! ### Unknown primitive tasks -/

/-- A label of a primitive task the domain does not mention. -/
def Unk (d : DomDesc) (l : Bool × ℕ) : Prop := l.1 = false ∧ l.2 ∉ SeqG.vocA d

instance (d : DomDesc) : DecidablePred (Unk d) := fun l =>
  inferInstanceAs (Decidable (l.1 = false ∧ l.2 ∉ SeqG.vocA d))

theorem actOf_unk {d : DomDesc} {a : ℕ} (h : a ∉ SeqG.vocA d) : actOf d a = ([], [], []) := by
  rw [actOf_eq]
  have : d.actions.lookup a = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    simp only [bne_iff_ne, ne_eq]
    intro hpa
    apply h
    simp only [SeqG.vocA, List.mem_append, List.mem_map]
    exact Or.inl ⟨p, hp, hpa.symm⟩
  simp [this]

theorem nxt_unk {d : DomDesc} {q : InstDesc} {a : ℕ} (h : a ∉ SeqG.vocA d) (σ : Finset ℕ) :
    (uoSys d q).nxt σ a = σ := by
  simp [uoSys, actOf_unk h]

theorem app_unk {d : DomDesc} {q : InstDesc} {a : ℕ} (h : a ∉ SeqG.vocA d) (σ : Finset ℕ) :
    (uoSys d q).app σ a := by
  simp [uoSys, actOf_unk h]

/-! ### Abstract runs: dropping no-ops, compound tasks need methods -/

section Abs

variable {d : DomDesc} {q : InstDesc}

theorem drop_unk {x : Bool × ℕ} (hx : Unk d x) {m : ℕ} {z y : Cfg}
    (hr : ReachIn (uoSys d q) m z y) (hg : IsGoal (uoSys d q) y) :
    ∀ σ M, z = (σ, x ::ₘ M) →
      ∃ m' ≤ m, ∃ y', ReachIn (uoSys d q) m' (σ, M) y' ∧ IsGoal (uoSys d q) y' := by
  induction hr with
  | refl z =>
    intro σ M hz
    subst hz
    exact absurd hg.1 (by simp)
  | @step n z w y hst _ ih =>
    intro σ M hz
    subst hz
    have hx1 : x.1 = false := hx.1
    cases hst with
    | dec _ _ c β hc hm =>
      have hne : (true, c) ≠ x := fun h => by rw [← h] at hx1; simp at hx1
      have hc' : (true, c) ∈ M := by
        rcases Multiset.mem_cons.1 hc with h | h
        · exact absurd h hne
        · exact h
      obtain ⟨m', hm', y', hy', hgy'⟩ := ih hg σ (M.erase (true, c) + β) (by
        rw [Multiset.erase_cons_tail_of_mem hc', Multiset.cons_add])
      exact ⟨m' + 1, by omega, y', ReachIn.step (Step.dec σ M c β hc' hm) hy', hgy'⟩
    | exe _ _ a ha happ =>
      by_cases hxa : x = (false, a)
      · subst hxa
        have hw : ReachIn (uoSys d q) n (σ, M) y := by
          have := ‹ReachIn (uoSys d q) n _ y›
          rwa [Multiset.erase_cons_head, nxt_unk hx.2] at this
        exact ⟨n, by omega, y, hw, hg⟩
      · have ha' : (false, a) ∈ M := by
          rcases Multiset.mem_cons.1 ha with h | h
          · exact absurd h.symm hxa
          · exact h
        obtain ⟨m', hm', y', hy', hgy'⟩ := ih hg _ (M.erase (false, a)) (by
          rw [Multiset.erase_cons_tail_of_mem ha'])
        exact ⟨m' + 1, by omega, y', ReachIn.step (Step.exe σ M a ha' happ) hy', hgy'⟩

theorem drop_unks {U : Multiset (Bool × ℕ)} (hU : ∀ x ∈ U, Unk d x) :
    ∀ {m : ℕ} {σ : Finset ℕ} {M : Multiset (Bool × ℕ)} {y : Cfg},
      ReachIn (uoSys d q) m (σ, M + U) y → IsGoal (uoSys d q) y →
      ∃ m' ≤ m, ∃ y', ReachIn (uoSys d q) m' (σ, M) y' ∧ IsGoal (uoSys d q) y' := by
  induction U using Multiset.induction_on with
  | empty => intro m σ M y hr hg; exact ⟨m, le_rfl, y, by simpa using hr, hg⟩
  | cons x U ih =>
    intro m σ M y hr hg
    have hx : Unk d x := hU x (Multiset.mem_cons_self _ _)
    obtain ⟨m1, hm1, y1, hr1, hg1⟩ := drop_unk hx hr hg σ (M + U) (by rw [Multiset.add_cons])
    obtain ⟨m2, hm2, y2, hr2, hg2⟩ := ih (fun z hz => hU z (Multiset.mem_cons_of_mem hz)) hr1 hg1
    exact ⟨m2, by omega, y2, hr2, hg2⟩

theorem method_of_goal {c : ℕ} {m : ℕ} {z y : Cfg} (hr : ReachIn (uoSys d q) m z y)
    (hg : IsGoal (uoSys d q) y) (hc : (true, c) ∈ z.2) : ∃ e ∈ d.methods, e.1 = c := by
  induction hr with
  | refl z => rw [hg.1] at hc; simp at hc
  | @step n z w y hst _ ih =>
    cases hst with
    | dec σ M c' β hc' hm =>
      by_cases hcc : c' = c
      · subst hcc
        obtain ⟨e, he, hec, -⟩ := hm
        exact ⟨e, he, hec⟩
      · refine ih hg ?_
        show (true, c) ∈ M.erase (true, c') + β
        refine Multiset.mem_add.2 (Or.inl ?_)
        exact (Multiset.mem_erase_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; exact fun h => hcc h.symm)).2 hc
    | exe σ M a ha happ =>
      refine ih hg ?_
      show (true, c) ∈ M.erase (false, a)
      exact (Multiset.mem_erase_of_ne (by simp)).2 hc

end Abs

/-! ### Slots -/

/-- The labels of the slots `p, p+1, …, n₀ - 1`. -/
def rest (lab : ℕ → Bool × ℕ) (n₀ p : ℕ) : Multiset (Bool × ℕ) :=
  ((List.range' p (n₀ - p)).map lab : List _)

theorem rest_zero (lab : ℕ → Bool × ℕ) (n₀ : ℕ) :
    rest lab n₀ 0 = ((List.range n₀).map lab : List _) := by
  simp [rest, List.range_eq_range']

theorem rest_succ (lab : ℕ → Bool × ℕ) {n₀ p : ℕ} (hp : p < n₀) :
    rest lab n₀ p = lab p ::ₘ rest lab n₀ (p + 1) := by
  simp only [rest]
  rw [show n₀ - p = (n₀ - (p + 1)) + 1 by omega, List.range'_succ]
  simp

theorem rest_self (lab : ℕ → Bool × ℕ) (n₀ : ℕ) : rest lab n₀ n₀ = 0 := by
  simp [rest]

/-- **The input facts tell the truth** about the slots. -/
structure InOK (d : DomDesc) (lab : ℕ → Bool × ℕ) (n₀ : ℕ) (s : List ℕ) : Prop where
  labOK : ∀ p l, fRoot (cLab p l) ∈ s → p < n₀ ∧ lab p = l
  nopOK : ∀ p, fRoot (cNop p) ∈ s → p < n₀ ∧ Unk d (lab p)
  lenOK : ∀ p, fRoot (cLen p) ∈ s → p = n₀

theorem inOK_step {d : DomDesc} {lab : ℕ → Bool × ℕ} {n₀ W N : ℕ} {s s' : List ℕ}
    (h : InOK d lab n₀ s) (hst : StepTbl (unTbl d W N) s s') : InOK d lab n₀ s' := by
  obtain ⟨r, hr, -, hs'⟩ := hst
  have hmono : ∀ c, fRoot c ∈ s' → fRoot c ∈ s := fun c hc => by
    rcases (hs' _).1 hc with h1 | h1
    · exact absurd (isIn_fRoot c) (add_clean hr _ h1)
    · exact h1.1
  exact ⟨fun p l hc => h.labOK p l (hmono _ hc), fun p hc => h.nopOK p (hmono _ hc),
    fun p hc => h.lenOK p (hmono _ hc)⟩

/-- The goal of the table problem. -/
def goalU (q : InstDesc) : List ℕ := q.goalList.map fSt ++ [fDone]

/-! ### Soundness -/

section Sound

variable {d : DomDesc} {q : InstDesc} {W N : ℕ} {lab : ℕ → Bool × ℕ} {n₀ : ℕ}

/-- Abstract reachability from the initial configuration. -/
def ARu (d : DomDesc) (q : InstDesc) (lab : ℕ → Bool × ℕ) (n₀ : ℕ) (z : Cfg) : Prop :=
  Relation.ReflTransGen (Step (uoSys d q))
    (q.initList.toFinset, ((List.range n₀).map lab : Multiset (Bool × ℕ))) z

/-- **The invariant of the reachable table states.** -/
def InvU (d : DomDesc) (q : InstDesc) (W : ℕ) (lab : ℕ → Bool × ℕ) (n₀ : ℕ) (s : List ℕ) : Prop :=
  InOK d lab n₀ s ∧
  ((∀ f, f ∈ strip s ↔ StP q.initList.toFinset f) ∨
   (fRoot (cCur 0) ∉ s ∧ ∃ M p, p ≤ n₀ ∧ ARu d q lab n₀ (q.initList.toFinset, M + rest lab n₀ p) ∧
      Rep (labsU d) W q.initList.toFinset M (· = fI (kCtl (kI d) p)) (strip s)) ∨
   (fRoot (cCur 0) ∉ s ∧ ∃ σ M, ARu d q lab n₀ (σ, M) ∧
      Rep (labsU d) W σ M (· = fI kIdle) (strip s)) ∨
   (fRoot (cCur 0) ∉ s ∧ ∃ σ M k e p, d.methods[k]? = some e ∧ p ≤ (body e).length ∧
      ARu d q lab n₀ (σ, M + ((body e).drop p : Multiset (Bool × ℕ))) ∧
      Rep (labsU d) W σ M (· = fI (kCtl k p)) (strip s)) ∨
   (fRoot (cCur 0) ∉ s ∧ ∃ σ, ARu d q lab n₀ (σ, 0) ∧
      Rep (labsU d) W σ 0 (· = fDone) (strip s)))

theorem kI_ne_of_getElem {k : ℕ} {e : MethodDesc} (hk : d.methods[k]? = some e) : kI d ≠ k := by
  intro h
  rw [← h, kI, List.getElem?_eq_none (le_refl _)] at hk
  exact absurd hk (by simp)

/-- Every row other than `zeroRow` needs a fact `fI k`. -/
theorem pre_fI {r : Row} (hr : r ∈ unTbl d W N) (hne : r ≠ zeroRow (labsU d) W (kI d)) :
    ∃ k, fI k ∈ r.1 := by
  rcases mem_unTbl.1 hr with rfl | ⟨p, -, rfl⟩ | ⟨p, -, l, -, i, -, rfl⟩ | ⟨p, -, rfl⟩ |
    ⟨l, -, -, i, -, rfl⟩ | ⟨k, e, -, (⟨i, -, rfl⟩ | ⟨p, l, -, i, -, rfl⟩ | rfl)⟩ | rfl
  · exact absurd rfl hne
  · exact ⟨kCtl (kI d) p, by simp [nopRow]⟩
  · exact ⟨kCtl (kI d) p, by simp [labRow, addRow]⟩
  · exact ⟨kCtl (kI d) p, by simp [doneRow]⟩
  · exact ⟨kIdle, by simp [exeRow]⟩
  · exact ⟨kIdle, by simp [decRow]⟩
  · exact ⟨kCtl k p, by simp [addRow]⟩
  · exact ⟨kCtl k (body e).length, by simp [endRow]⟩
  · exact ⟨kIdle, by simp [finRow]⟩

/-- In a state with a represented strip, the load rows need their control fact. -/
theorem load_ctl {L σ M C s} (hrep : Rep L W σ M C (strip s)) {r : Row}
    (hr : r ∈ unTbl d W N) (hpre : ∀ f ∈ r.1, f ∈ s) :
    (∀ p, r = nopRow (kI d) p → C (fI (kCtl (kI d) p))) ∧
    (∀ p l i, r = labRow (kI d) p l i → C (fI (kCtl (kI d) p))) ∧
    (∀ p, r = doneRow (kI d) p → C (fI (kCtl (kI d) p))) := by
  refine ⟨fun p hp => ?_, fun p l i hp => ?_, fun p hp => ?_⟩ <;> subst hp
  · exact (hrep.mem_ctl _ _).1 (mem_strip.2 ⟨hpre _ (by simp [nopRow]), not_isIn_fI _⟩)
  · exact (hrep.mem_ctl _ _).1 (mem_strip.2 ⟨hpre _ (by simp [labRow, addRow]), not_isIn_fI _⟩)
  · exact (hrep.mem_ctl _ _).1 (mem_strip.2 ⟨hpre _ (by simp [doneRow]), not_isIn_fI _⟩)

theorem cur_gone {s s' : List ℕ} {r : Row} (hr : r ∈ unTbl d W N) (h : fRoot (cCur 0) ∉ s)
    (hs' : ∀ f, f ∈ s' ↔ f ∈ r.2.1 ∨ (f ∈ s ∧ f ∉ r.2.2)) : fRoot (cCur 0) ∉ s' := by
  rw [hs']
  rintro (h1 | h1)
  · exact add_clean hr _ h1 (isIn_fRoot _)
  · exact h h1.1

theorem invU_step {s s' : List ℕ} (hs : InvU d q W lab n₀ s)
    (h : StepTbl (unTbl d W N) s s') : InvU d q W lab n₀ s' := by
  have hIn' := inOK_step hs.1 h
  obtain ⟨r, hr, hpre, hs'⟩ := h
  have hst' := strip_post (add_clean hr) hs'
  refine ⟨hIn', ?_⟩
  set σ0 := q.initList.toFinset
  rcases hs.2 with hs0 | ⟨hc, M, p, hp, har, hrep⟩ | ⟨hc, σ, M, har, hrep⟩ |
    ⟨hc, σ, M, k, e, p, hk, hp, har, hrep⟩ | ⟨hc, σ, har, hrep⟩
  · -- start: only `zeroRow` applies
    by_cases hz : r = zeroRow (labsU d) W (kI d)
    · subst hz
      refine Or.inr (Or.inl ⟨?_, 0, 0, Nat.zero_le _, ?_, zero_post hs0 hst'⟩)
      · rw [hs']
        rintro (h1 | h1)
        · exact add_clean hr _ h1 (isIn_fRoot _)
        · exact h1.2 (by simp [zeroRow])
      · rw [rest_zero, zero_add]
        exact Relation.ReflTransGen.refl
    · obtain ⟨k, hk⟩ := pre_fI hr hz
      have := (hs0 (fI k)).1 (mem_strip.2 ⟨hpre _ hk, not_isIn_fI _⟩)
      exact absurd this (not_stP fun v h => fI_ne_fSt _ _ h)
  · -- loading slot `p`
    have hcl := load_ctl hrep hr hpre
    have hc' := cur_gone hr hc hs'
    rcases mem_unTbl.1 hr with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', l, hl, i, hi, rfl⟩ |
      ⟨p', hp', rfl⟩ | ⟨l, hl, hl1, i, hi, rfl⟩ |
      ⟨k, e, hk, (⟨i, hi, rfl⟩ | ⟨p', l, hp', i, hi, rfl⟩ | rfl)⟩ | rfl
    · exact absurd (zero_pre.1 hpre) hc
    · have hC := hcl.1 p' rfl
      obtain rfl : p' = p := by simpa using hC
      have hnop := (nop_pre hrep (kI d) p').1 hpre
      obtain ⟨hpn, hunk⟩ := hs.1.nopOK p' hnop.2
      obtain ⟨a, ha⟩ : ∃ a, lab p' = (false, a) := ⟨(lab p').2, Prod.ext hunk.1 rfl⟩
      have ha2 : a ∉ SeqG.vocA d := by have := hunk.2; rw [ha] at this; exact this
      have hstep : Step (uoSys d q) (σ0, (false, a) ::ₘ (M + rest lab n₀ (p' + 1)))
          (σ0, M + rest lab n₀ (p' + 1)) := by
        have := Step.exe (S := uoSys d q) σ0 ((false, a) ::ₘ (M + rest lab n₀ (p' + 1))) a
          (Multiset.mem_cons_self _ _) (app_unk ha2 σ0)
        rwa [nxt_unk ha2, Multiset.erase_cons_head] at this
      refine Or.inr (Or.inl ⟨hc', M, p' + 1, hpn, ?_, nop_post hrep hst'⟩)
      rw [rest_succ lab hpn, ha, Multiset.add_cons] at har
      exact har.tail hstep
    · have hC := hcl.2.1 p' l i rfl
      obtain rfl : p' = p := by simpa using hC
      obtain ⟨hlab, -, hlL, hi', hlow, hb⟩ := (lab_pre hrep (ctlOK_ctl _ _) _ _ _ _).1 hpre
      obtain ⟨hpn, hlp⟩ := hs.1.labOK p' l hlab
      refine Or.inr (Or.inl ⟨hc', l ::ₘ M, p' + 1, hpn, ?_,
        add_post hrep hlL hi' hlow hb hst'⟩)
      rw [rest_succ lab hpn, hlp, Multiset.add_cons, ← Multiset.cons_add] at har
      exact har
    · have hC := hcl.2.2 p' rfl
      obtain rfl : p' = p := by simpa using hC
      have hdone := (done_pre hrep (kI d) p').1 hpre
      have hpn := hs.1.lenOK p' hdone.2
      subst hpn
      refine Or.inr (Or.inr (Or.inl ⟨hc', σ0, M, ?_, done_post hrep hst'⟩))
      simpa [rest_self] using har
    · have := (exe_pre hrep (ctlOK_ctl _ _) d l i).1
        (pre_strip (mainRow_clean (W := W) (Or.inl ⟨l, hl, hl1, i, hi, rfl⟩)).1 hpre)
      simp at this
    · have := (dec_pre hrep (ctlOK_ctl _ _) k e i).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl ⟨k, e, hk, Or.inl ⟨i, hi, rfl⟩⟩))).1 hpre)
      simp at this
    · have := (add_pre hrep (ctlOK_ctl _ _) k p' l i).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl
          ⟨k, e, hk, Or.inr (Or.inl ⟨p', l, hp', i, hi, rfl⟩)⟩))).1 hpre)
      have h2 : k = kI d := by
        have h1 := this.1
        simp only [fI_inj, kCtl_inj] at h1
        exact h1.1
      exact absurd h2.symm (kI_ne_of_getElem hk)
    · have h1 := (end_pre hrep k _).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl ⟨k, e, hk, Or.inr (Or.inr rfl)⟩))).1 hpre)
      simp only [fI_inj, kCtl_inj] at h1
      exact absurd h1.1.symm (kI_ne_of_getElem hk)
    · have := (fin_pre hrep (ctlOK_ctl _ _)).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inr rfl))).1 hpre)
      simp at this
  · -- idle
    have hcl := load_ctl hrep hr hpre
    have hc' := cur_gone hr hc hs'
    rcases mem_unTbl.1 hr with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', l, hl, i, hi, rfl⟩ |
      ⟨p', hp', rfl⟩ | ⟨⟨b, a⟩, hl, hl1, i, hi, rfl⟩ |
      ⟨k, e, hk, (⟨i, hi, rfl⟩ | ⟨p', l, hp', i, hi, rfl⟩ | rfl)⟩ | rfl
    · exact absurd (zero_pre.1 hpre) hc
    · have := hcl.1 p' rfl; simp at this
    · have := hcl.2.1 p' l i rfl; simp at this
    · have := hcl.2.2 p' rfl; simp at this
    · obtain rfl : b = false := hl1
      obtain ⟨-, ⟨hlL', hi', hlow, hb⟩, happ⟩ := (exe_pre hrep ctlOK_idle d (false, a) i).1
        (pre_strip (mainRow_clean (W := W) (Or.inl ⟨_, hl, rfl, i, hi, rfl⟩)).1 hpre)
      have hmem : (false, a) ∈ M := Multiset.count_pos.1 (count_pos_of_testBit hb)
      exact Or.inr (Or.inr (Or.inl ⟨hc', _, _, har.tail (Step.exe σ M a hmem happ),
        exe_post hrep d hlL' hi' hlow hb hst'⟩))
    · obtain ⟨-, hL, hi', hlow, hb⟩ := (dec_pre hrep ctlOK_idle k e i).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl ⟨k, e, hk, Or.inl ⟨i, hi, rfl⟩⟩))).1 hpre)
      have hmem : (true, e.1) ∈ M := Multiset.count_pos.1 (count_pos_of_testBit hb)
      have he : e ∈ d.methods := List.mem_of_getElem? hk
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hc', σ, _, k, e, 0, hk, Nat.zero_le _, ?_,
        dec_post hrep k e hL hi' hlow hb hst'⟩)))
      simpa using har.tail (Step.dec σ M e.1 _ hmem ⟨e, he, rfl, rfl⟩)
    · have := (add_pre hrep ctlOK_idle k p' l i).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl
          ⟨k, e, hk, Or.inr (Or.inl ⟨p', l, hp', i, hi, rfl⟩)⟩))).1 hpre)
      simp at this
    · have := (end_pre hrep k _).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl ⟨k, e, hk, Or.inr (Or.inr rfl)⟩))).1 hpre)
      simp at this
    · obtain ⟨-, hz⟩ := (fin_pre hrep ctlOK_idle).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inr rfl))).1 hpre)
      have hM : M = 0 := Multiset.eq_zero_of_forall_notMem fun x hx =>
        (Multiset.count_pos.2 hx).ne' (hz x (hrep.1 x hx))
      subst hM
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hc', σ, har, fin_post hrep hst'⟩)))
  · -- unfolding method `k`
    have hcl := load_ctl hrep hr hpre
    have hc' := cur_gone hr hc hs'
    rcases mem_unTbl.1 hr with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', l, hl, i, hi, rfl⟩ |
      ⟨p', hp', rfl⟩ | ⟨l, hl, hl1, i, hi, rfl⟩ |
      ⟨k', e', hk', (⟨i, hi, rfl⟩ | ⟨p', l, hp', i, hi, rfl⟩ | rfl)⟩ | rfl
    · exact absurd (zero_pre.1 hpre) hc
    · have := hcl.1 p' rfl
      obtain ⟨h2, -⟩ : kI d = k ∧ _ := by simpa using this
      exact absurd h2 (kI_ne_of_getElem hk)
    · have := hcl.2.1 p' l i rfl
      obtain ⟨h2, -⟩ : kI d = k ∧ _ := by simpa using this
      exact absurd h2 (kI_ne_of_getElem hk)
    · have := hcl.2.2 p' rfl
      obtain ⟨h2, -⟩ : kI d = k ∧ _ := by simpa using this
      exact absurd h2 (kI_ne_of_getElem hk)
    · have := (exe_pre hrep (ctlOK_ctl k p) d l i).1
        (pre_strip (mainRow_clean (W := W) (Or.inl ⟨l, hl, hl1, i, hi, rfl⟩)).1 hpre)
      simp at this
    · have := (dec_pre hrep (ctlOK_ctl k p) k' e' i).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl ⟨k', e', hk', Or.inl ⟨i, hi, rfl⟩⟩))).1 hpre)
      simp at this
    · obtain ⟨hC, hlL, hi', hlow, hb⟩ := (add_pre hrep (ctlOK_ctl k p) k' p' l i).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl
          ⟨k', e', hk', Or.inr (Or.inl ⟨p', l, hp', i, hi, rfl⟩)⟩))).1 hpre)
      obtain ⟨rfl, rfl⟩ : k' = k ∧ p' = p := by simpa using hC
      obtain rfl : e' = e := Option.some_injective _ (hk'.symm.trans hk)
      have hpl : p' < (body e').length := by
        by_contra hcon
        rw [List.getElem?_eq_none (by omega)] at hp'
        exact absurd hp' (by simp)
      have hl : (body e')[p'] = l := by
        rw [List.getElem?_eq_getElem hpl] at hp'
        exact Option.some_injective _ hp'
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hc', σ, _, k', e', p' + 1, hk', hpl, ?_,
        add_post hrep hlL hi' hlow hb hst'⟩)))
      rw [List.drop_eq_getElem_cons hpl, hl] at har
      have heq : M + ((l :: List.drop (p' + 1) (body e') : List _) : Multiset (Bool × ℕ)) =
          (l ::ₘ M) + (List.drop (p' + 1) (body e') : Multiset (Bool × ℕ)) := by
        rw [← Multiset.cons_coe, Multiset.add_cons, Multiset.cons_add]
      rwa [heq] at har
    · have hC := (end_pre hrep k' _).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl ⟨k', e', hk', Or.inr (Or.inr rfl)⟩))).1 hpre)
      obtain ⟨rfl, hpe⟩ : k' = k ∧ (body e').length = p := by simpa using hC
      obtain rfl : e' = e := Option.some_injective _ (hk'.symm.trans hk)
      rw [← hpe, List.drop_length] at har
      exact Or.inr (Or.inr (Or.inl ⟨hc', σ, M, by simpa using har, end_post (hpe ▸ hrep) hst'⟩))
    · have := (fin_pre hrep (ctlOK_ctl k p)).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inr rfl))).1 hpre)
      simp at this
  · -- final state: nothing applies
    exfalso
    have hcl := load_ctl hrep hr hpre
    rcases mem_unTbl.1 hr with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', l, hl, i, hi, rfl⟩ |
      ⟨p', hp', rfl⟩ | ⟨l, hl, hl1, i, hi, rfl⟩ |
      ⟨k, e, hk, (⟨i, hi, rfl⟩ | ⟨p', l, hp', i, hi, rfl⟩ | rfl)⟩ | rfl
    · exact hc (zero_pre.1 hpre)
    · exact fI_ne_fDone _ (hcl.1 p' rfl)
    · exact fI_ne_fDone _ (hcl.2.1 p' l i rfl)
    · exact fI_ne_fDone _ (hcl.2.2 p' rfl)
    · exact fI_ne_fDone _ ((exe_pre hrep ctlOK_done d l i).1
        (pre_strip (mainRow_clean (W := W) (Or.inl ⟨l, hl, hl1, i, hi, rfl⟩)).1 hpre)).1
    · exact fI_ne_fDone _ ((dec_pre hrep ctlOK_done k e i).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl ⟨k, e, hk, Or.inl ⟨i, hi, rfl⟩⟩))).1 hpre)).1
    · exact fI_ne_fDone _ ((add_pre hrep ctlOK_done k p' l i).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl
          ⟨k, e, hk, Or.inr (Or.inl ⟨p', l, hp', i, hi, rfl⟩)⟩))).1 hpre)).1
    · exact fI_ne_fDone _ ((end_pre hrep k _).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inl ⟨k, e, hk, Or.inr (Or.inr rfl)⟩))).1 hpre))
    · exact fI_ne_fDone _ ((fin_pre hrep ctlOK_done).1
        (pre_strip (mainRow_clean (W := W) (Or.inr (Or.inr rfl))).1 hpre)).1

theorem invU_reach {s₀ s : List ℕ} (h0 : InvU d q W lab n₀ s₀)
    (h : ReachTbl (unTbl d W N) s₀ s) : InvU d q W lab n₀ s := by
  induction h with
  | refl => exact h0
  | tail _ hst ih => exact invU_step ih hst

/-- **Soundness of the unrooted table.** -/
theorem solvable_of_solvableTblU (hd : d.MethodsUO) (hq : q.IsUO) {s₀ : List ℕ}
    (hM : uoAbs (initConfig q) = (q.initList.toFinset, ((List.range n₀).map lab : Multiset _)))
    (hS : ∀ f, f ∈ strip s₀ ↔ StP q.initList.toFinset f) (hIn : InOK d lab n₀ s₀)
    (h : SolvableTbl (unTbl d W N) s₀ (goalU q)) : Solvable d q := by
  obtain ⟨s, hr, hg⟩ := h
  have h0 : fDone ∈ strip s := mem_strip.2 ⟨hg fDone (by simp [goalU]), not_isIn_fDone⟩
  rcases (invU_reach (N := N) (W := W) ⟨hIn, Or.inl hS⟩ hr).2 with hs0 | ⟨-, M, p, -, -, hrep⟩ |
    ⟨-, σ, M, -, hrep⟩ | ⟨-, σ, M, k, e, p, -, -, -, hrep⟩ | ⟨-, σ, har, hrep⟩
  · exact absurd ((hs0 fDone).1 h0) (not_stP fun v h => fDone_ne_fSt _ h)
  · exact absurd (hrep.mem_done.1 h0) (fDone_ne_fI _)
  · exact absurd (hrep.mem_done.1 h0) (fDone_ne_fI _)
  · exact absurd (hrep.mem_done.1 h0) (fDone_ne_fI _)
  · have hgoal : IsGoal (uoSys d q) (σ, 0) := ⟨rfl, fun f hf =>
      (hrep.mem_fSt ctlOK_done f).1 (mem_strip.2 ⟨hg (fSt f) (by simp [goalU, hf]),
        not_isIn_fSt _⟩)⟩
    obtain ⟨m, hm⟩ := reachIn_of_rtg har
    rw [← hM] at hm
    obtain ⟨cs, hcs, -, hend⟩ := ppath_of_reachIn hd hm (uoInv_initConfig hq) rfl
    exact solvable_of_pReach (pReach_of_ppath hcs) (isGoalB_iff_uo.2 (hend ▸ hgoal))

end Sound

/-! ### Completeness -/

section Complete

variable {d : DomDesc} {q : InstDesc} {W N : ℕ}

theorem simU_add {k : ℕ} {e : MethodDesc} (hk : d.methods[k]? = some e) {σ : Finset ℕ}
    {M0 : Multiset (Bool × ℕ)} (hfin : ∀ l, (M0 + (body e : Multiset (Bool × ℕ))).count l < 2 ^ W) :
    ∀ n p, p + n = (body e).length → ∀ s,
      Rep (labsU d) W σ (M0 + ((body e).take p : Multiset (Bool × ℕ))) (· = fI (kCtl k p))
        (strip s) →
      ∃ s', ReachTbl (unTbl d W N) s s' ∧
        Rep (labsU d) W σ (M0 + (body e : Multiset (Bool × ℕ)))
          (· = fI (kCtl k (body e).length)) (strip s') := by
  have he : e ∈ d.methods := List.mem_of_getElem? hk
  intro n
  induction n with
  | zero =>
    intro p hp s hs
    have : p = (body e).length := by omega
    subst this
    exact ⟨s, Relation.ReflTransGen.refl, by simpa using hs⟩
  | succ n ih =>
    intro p hp s hs
    have hpl : p < (body e).length := by omega
    have hget : (body e)[p]? = some (body e)[p] := List.getElem?_eq_getElem hpl
    have htake : (((body e).take (p + 1) : List _) : Multiset (Bool × ℕ)) =
        (body e)[p] ::ₘ ((body e).take p : Multiset (Bool × ℕ)) := by
      rw [List.take_add_one, hget, Option.toList_some, ← Multiset.coe_add, add_comm]
      rfl
    have hlL : (body e)[p] ∈ labsU d := labs_sub_labsU (body_mem_labs he (List.getElem_mem hpl))
    have hcnt : ((M0 + ((body e).take p : Multiset (Bool × ℕ))).count (body e)[p]) + 1 < 2 ^ W := by
      have hle : (((body e).take (p + 1) : List _) : Multiset (Bool × ℕ)) ≤ (body e : Multiset _) :=
        Multiset.coe_le.2 (List.take_sublist _ _).subperm
      have h1 : (M0 + (((body e).take (p + 1) : List _) : Multiset (Bool × ℕ))).count (body e)[p]
          ≤ (M0 + (body e : Multiset (Bool × ℕ))).count (body e)[p] :=
        Multiset.count_le_of_le _ (by gcongr)
      rw [htake, Multiset.add_cons, Multiset.count_cons_self] at h1
      exact lt_of_le_of_lt h1 (hfin _)
    obtain ⟨i, hi, hlow, hb⟩ := Counter.exists_low_zero hcnt
    have hr : addRow k p (body e)[p] i ∈ unTbl d W N :=
      mem_unTbl.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, e, hk, Or.inr (Or.inl ⟨p, _, hget, i, hi, rfl⟩)⟩))))))
    have hpre := (add_pre hs (ctlOK_ctl k p) k p (body e)[p] i).2 ⟨rfl, hlL, hi, hlow, hb⟩
    have hpost := add_post hs hlL hi hlow hb (strip_applyRow (add_clean hr))
    rw [← Multiset.add_cons, ← htake] at hpost
    obtain ⟨s', hs', hrep⟩ := ih (p + 1) (by omega) _ hpost
    exact ⟨s', Relation.ReflTransGen.head (stepTbl_applyRow hr (pre_of_strip hpre)) hs', hrep⟩

theorem simU_step {σ σ' : Finset ℕ} {M M' : Multiset (Bool × ℕ)} {s : List ℕ}
    (h : Rep (labsU d) W σ M (· = fI kIdle) (strip s)) (hst : Step (uoSys d q) (σ, M) (σ', M'))
    (hcnt : ∀ l, M'.count l < 2 ^ W) :
    ∃ s', ReachTbl (unTbl d W N) s s' ∧ Rep (labsU d) W σ' M' (· = fI kIdle) (strip s') := by
  cases hst with
  | dec _ _ c β hc hm =>
    obtain ⟨e, he, rfl, rfl⟩ := hm
    obtain ⟨k, hk⟩ : ∃ k, d.methods[k]? = some e := List.mem_iff_getElem?.1 he
    have hpos : 0 < M.count (true, e.1) := Multiset.count_pos.2 hc
    obtain ⟨i, hi, hlow, hb⟩ := Counter.exists_low_one hpos (h.2.1 _)
    have hL := labs_sub_labsU (head_mem_labs he)
    have hr : decRow k e i ∈ unTbl d W N :=
      mem_unTbl.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, e, hk, Or.inl ⟨i, hi, rfl⟩⟩))))))
    have hpre := (dec_pre h ctlOK_idle k e i).2 ⟨rfl, hL, hi, hlow, hb⟩
    have h1 := dec_post h k e hL hi hlow hb (strip_applyRow (add_clean hr))
    have h1' : Rep (labsU d) W σ (M.erase (true, e.1) + (((body e).take 0 : List _) :
        Multiset (Bool × ℕ))) (· = fI (kCtl k 0)) (strip (applyRow (decRow k e i) s)) := by
      simpa using h1
    obtain ⟨s2, hs2, hrep2⟩ := simU_add (N := N) hk hcnt (body e).length 0 (by simp) _ h1'
    have hr2 : endRow k (body e).length ∈ unTbl d W N :=
      mem_unTbl.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, e, hk, Or.inr (Or.inr rfl)⟩))))))
    have hpre2 := (end_pre hrep2 k _).2 rfl
    have h3 := end_post hrep2 (strip_applyRow (add_clean hr2))
    exact ⟨_, (Relation.ReflTransGen.head (stepTbl_applyRow hr (pre_of_strip hpre)) hs2).tail
      (stepTbl_applyRow hr2 (pre_of_strip hpre2)), h3⟩
  | exe _ _ a ha happ =>
    have hpos : 0 < M.count (false, a) := Multiset.count_pos.2 ha
    obtain ⟨i, hi, hlow, hb⟩ := Counter.exists_low_one hpos (h.2.1 _)
    have hL := h.1 _ ha
    have hr : exeRow d (false, a) i ∈ unTbl d W N :=
      mem_unTbl.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hL, rfl, i, hi, rfl⟩)))))
    have hpre := (exe_pre h ctlOK_idle d (false, a) i).2 ⟨rfl, ⟨hL, hi, hlow, hb⟩, happ⟩
    exact ⟨_, Relation.ReflTransGen.single (stepTbl_applyRow hr (pre_of_strip hpre)),
      exe_post h d hL hi hlow hb (strip_applyRow (add_clean hr))⟩

theorem simU_run {m : ℕ} {x y : Cfg} (hr : ReachIn (uoSys d q) m x y) :
    ∀ s, Rep (labsU d) W x.1 x.2 (· = fI kIdle) (strip s) →
      Multiset.card x.2 + m * maxBody d < 2 ^ W →
      ∃ s', ReachTbl (unTbl d W N) s s' ∧ Rep (labsU d) W y.1 y.2 (· = fI kIdle) (strip s') := by
  induction hr with
  | refl x => exact fun s hs _ => ⟨s, Relation.ReflTransGen.refl, hs⟩
  | @step n x y z hst _ ih =>
    intro s hs hb
    have hcy : Multiset.card y.2 ≤ Multiset.card x.2 + 1 * maxBody d :=
      card_le_of_reachIn (closed_uoSys d q) (ReachIn.step hst (ReachIn.refl _))
    have hcnt : ∀ l, y.2.count l < 2 ^ W := fun l =>
      lt_of_le_of_lt (Multiset.count_le_card _ _) (by rw [Nat.succ_mul] at hb; omega)
    obtain ⟨s1, h1, r1⟩ := simU_step (N := N) hs hst hcnt
    obtain ⟨s2, h2, r2⟩ := ih s1 r1 (by rw [Nat.succ_mul] at hb; omega)
    exact ⟨s2, h1.trans h2, r2⟩

/-- The labels of the loaded slots among the first `p`. -/
def kept (d : DomDesc) (lab : ℕ → Bool × ℕ) (p : ℕ) : Multiset (Bool × ℕ) :=
  (((List.range p).filter (fun j => decide (¬ Unk d (lab j)))).map lab : List _)

/-- The labels of the skipped slots among the first `p`. -/
def skipped (d : DomDesc) (lab : ℕ → Bool × ℕ) (p : ℕ) : Multiset (Bool × ℕ) :=
  (((List.range p).filter (fun j => decide (Unk d (lab j)))).map lab : List _)

theorem kept_add_skipped (lab : ℕ → Bool × ℕ) (p : ℕ) :
    kept d lab p + skipped d lab p = ((List.range p).map lab : List _) := by
  simp only [kept, skipped, Multiset.coe_add, Multiset.coe_eq_coe]
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  convert List.filter_append_perm (fun j => decide (¬ Unk d (lab j))) (List.range p) using 2
  apply List.filter_congr
  intro x _
  simp

theorem kept_succ_unk {lab : ℕ → Bool × ℕ} {p : ℕ} (h : Unk d (lab p)) :
    kept d lab (p + 1) = kept d lab p := by
  simp [kept, List.range_succ, List.filter_append, h]

theorem kept_succ_known {lab : ℕ → Bool × ℕ} {p : ℕ} (h : ¬ Unk d (lab p)) :
    kept d lab (p + 1) = lab p ::ₘ kept d lab p := by
  simp only [kept, List.range_succ, List.filter_append, List.map_append]
  simp [h, ← Multiset.coe_add, add_comm]

theorem card_kept_le (lab : ℕ → Bool × ℕ) (p : ℕ) : Multiset.card (kept d lab p) ≤ p := by
  simp only [kept, Multiset.coe_card, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem mem_kept {lab : ℕ → Bool × ℕ} {p : ℕ} {x : Bool × ℕ} (h : x ∈ kept d lab p) :
    ∃ j < p, ¬ Unk d (lab j) ∧ lab j = x := by
  simp only [kept, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨j, ⟨hj, hu⟩, rfl⟩ := h
  exact ⟨j, hj, hu, rfl⟩

/-- **The load phase**, slot by slot. -/
theorem load_run {lab : ℕ → Bool × ℕ} {n₀ : ℕ} (hN : n₀ ≤ N) (hW : n₀ < 2 ^ W)
    {σ : Finset ℕ} {s₀ : List ℕ}
    (hlabs : ∀ p < n₀, ¬ Unk d (lab p) → lab p ∈ labsU d)
    (hcl : ∀ p < n₀, lab p ∈ labsU d → fRoot (cLab p (lab p)) ∈ s₀)
    (hcn : ∀ p < n₀, Unk d (lab p) → fRoot (cNop p) ∈ s₀) :
    ∀ n p, p + n = n₀ → ∀ s, (∀ f, IsIn f → f ∈ s₀ → f ∈ s) →
      Rep (labsU d) W σ (kept d lab p) (· = fI (kCtl (kI d) p)) (strip s) →
      ∃ s', ReachTbl (unTbl d W N) s s' ∧ (∀ f, IsIn f → f ∈ s₀ → f ∈ s') ∧
        Rep (labsU d) W σ (kept d lab n₀) (· = fI (kCtl (kI d) n₀)) (strip s') := by
  intro n
  induction n with
  | zero =>
    intro p hp s hin hs
    obtain rfl : p = n₀ := by omega
    exact ⟨s, Relation.ReflTransGen.refl, hin, hs⟩
  | succ n ih =>
    intro p hp s hin hs
    have hpn : p < n₀ := by omega
    by_cases hu : Unk d (lab p)
    · have hr : nopRow (kI d) p ∈ unTbl d W N :=
        mem_unTbl.2 (Or.inr (Or.inl ⟨p, by omega, rfl⟩))
      have hpre := (nop_pre hs (kI d) p).2 ⟨rfl, hin _ (isIn_fRoot _) (hcn p hpn hu)⟩
      have hpost := nop_post hs (strip_applyRow (add_clean hr))
      rw [← kept_succ_unk hu] at hpost
      have hin' : ∀ f, IsIn f → f ∈ s₀ → f ∈ applyRow (nopRow (kI d) p) s := by
        intro f hf hf0
        refine mem_applyRow.2 (Or.inr ⟨hin f hf hf0, ?_⟩)
        simp only [nopRow, List.mem_singleton]
        rintro rfl; exact not_isIn_fI _ hf
      obtain ⟨s', hs', hin'', hrep⟩ := ih (p + 1) (by omega) _ hin' hpost
      exact ⟨s', Relation.ReflTransGen.head (stepTbl_applyRow hr hpre) hs', hin'', hrep⟩
    · have hlL := hlabs p hpn hu
      have hcnt : (kept d lab p).count (lab p) + 1 < 2 ^ W := by
        have h1 : (kept d lab (p + 1)).count (lab p) ≤ p + 1 :=
          (Multiset.count_le_card _ _).trans (card_kept_le lab _)
        rw [kept_succ_known hu, Multiset.count_cons_self] at h1
        omega
      obtain ⟨i, hi, hlow, hb⟩ := Counter.exists_low_zero hcnt
      have hr : labRow (kI d) p (lab p) i ∈ unTbl d W N :=
        mem_unTbl.2 (Or.inr (Or.inr (Or.inl ⟨p, by omega, lab p, hlL, i, hi, rfl⟩)))
      have hpre := (lab_pre hs (ctlOK_ctl _ _) (kI d) p (lab p) i).2
        ⟨hin _ (isIn_fRoot _) (hcl p hpn hlL), rfl, hlL, hi, hlow, hb⟩
      have hpost := add_post hs hlL hi hlow hb
        (strip_applyRow (r := labRow (kI d) p (lab p) i) (s := s) (add_clean hr))
      rw [← kept_succ_known hu] at hpost
      have hin' : ∀ f, IsIn f → f ∈ s₀ → f ∈ applyRow (labRow (kI d) p (lab p) i) s := by
        intro f hf hf0
        refine mem_applyRow.2 (Or.inr ⟨hin f hf hf0, ?_⟩)
        simp only [labRow, addRow, List.mem_cons]
        rintro (rfl | h)
        · exact not_isIn_fI _ hf
        · exact not_isIn_decAdd f h hf
      obtain ⟨s', hs', hin'', hrep⟩ := ih (p + 1) (by omega) _ hin' hpost
      exact ⟨s', Relation.ReflTransGen.head (stepTbl_applyRow hr hpre) hs', hin'', hrep⟩

/-- **Completeness of the unrooted table.** -/
theorem solvableTblU_of_solvable (hd : d.MethodsUO) (hq : q.IsUO) {lab : ℕ → Bool × ℕ} {n₀ : ℕ}
    (hW : n₀ + uoBndP d q * maxBody d < 2 ^ W) (hN : n₀ ≤ N) {s₀ : List ℕ}
    (hM : uoAbs (initConfig q) = (q.initList.toFinset, ((List.range n₀).map lab : Multiset _)))
    (hS : ∀ f, f ∈ strip s₀ ↔ StP q.initList.toFinset f)
    (hc0 : fRoot (cCur 0) ∈ s₀) (hlen : fRoot (cLen n₀) ∈ s₀)
    (hcl : ∀ p < n₀, lab p ∈ labsU d → fRoot (cLab p (lab p)) ∈ s₀)
    (hcn : ∀ p < n₀, Unk d (lab p) → fRoot (cNop p) ∈ s₀)
    (h : Solvable d q) : SolvableTbl (unTbl d W N) s₀ (goalU q) := by
  set σ0 := q.initList.toFinset
  obtain ⟨m, hm, y, hy, hg⟩ := (solvable_iff_short_uo hd hq).1 h
  rw [hM, ← kept_add_skipped (d := d) lab n₀] at hy
  have hU : ∀ x ∈ skipped d lab n₀, Unk d x := by
    intro x hx
    simp only [skipped, Multiset.mem_coe, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨j, ⟨-, hu⟩, rfl⟩ := hx
    exact hu
  obtain ⟨m', hm', y', hy', hg'⟩ := drop_unks hU hy hg
  -- every kept label has a counter
  have hlabs : ∀ p < n₀, ¬ Unk d (lab p) → lab p ∈ labsU d := by
    intro p hp hu
    rcases hl : lab p with ⟨b, c⟩
    cases b with
    | true =>
      have hmem : (true, c) ∈ kept d lab n₀ := by
        rw [← hl]
        simp only [kept, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_range,
          decide_eq_true_eq]
        exact ⟨p, ⟨hp, hu⟩, rfl⟩
      obtain ⟨e, he, rfl⟩ := method_of_goal hy' hg' hmem
      exact labs_sub_labsU (head_mem_labs he)
    | false =>
      refine prim_mem_labsU ?_
      by_contra hc
      exact hu ⟨by rw [hl], by rw [hl]; exact hc⟩
  -- zero
  have hr0 : zeroRow (labsU d) W (kI d) ∈ unTbl d W N := mem_unTbl.2 (Or.inl rfl)
  have h0 := zero_post hS (strip_applyRow (s := s₀) (add_clean hr0))
  have hin0 : ∀ f, IsIn f → f ∈ s₀ → f ≠ fRoot (cCur 0) →
      f ∈ applyRow (zeroRow (labsU d) W (kI d)) s₀ := by
    intro f hf hf0 hne
    exact mem_applyRow.2 (Or.inr ⟨hf0, by simpa [zeroRow] using hne⟩)
  -- load
  have hkept0 : kept d lab 0 = 0 := by simp [kept]
  rw [← hkept0] at h0
  have hc0' : (cCur 0) ≠ cLab 0 (0, 0) := by simp [cCur, cLab]; omega
  obtain ⟨s1, hs1, hin1, hrep1⟩ := load_run (σ := σ0) (s₀ := applyRow (zeroRow (labsU d) W (kI d)) s₀)
    hN (by omega) hlabs
    (fun p hp hl => hin0 _ (isIn_fRoot _) (hcl p hp hl) (by
      simp only [ne_eq, fRoot_inj, cCur, cLab]; omega))
    (fun p hp hu => hin0 _ (isIn_fRoot _) (hcn p hp hu) (by
      simp only [ne_eq, fRoot_inj, cCur, cNop]; omega))
    n₀ 0 (by omega) _ (fun f _ hf => hf) h0
  -- done
  have hrd : doneRow (kI d) n₀ ∈ unTbl d W N := mem_unTbl.2 (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨n₀, hN, rfl⟩))))
  have hlen1 : fRoot (cLen n₀) ∈ s1 := hin1 _ (isIn_fRoot _) (hin0 _ (isIn_fRoot _) hlen (by
    simp only [ne_eq, fRoot_inj, cCur, cLen]; omega))
  have hpred := (done_pre hrep1 (kI d) n₀).2 ⟨rfl, hlen1⟩
  have hrep2 := done_post hrep1 (strip_applyRow (s := s1) (add_clean hrd))
  -- the main phase
  have hcard := card_kept_le (d := d) lab n₀
  have hmb : m' * maxBody d ≤ uoBndP d q * maxBody d := Nat.mul_le_mul_right _ (hm'.trans hm)
  obtain ⟨s3, hs3, hrep3⟩ := simU_run (N := N) hy' _ hrep2 (by simp only; omega)
  obtain ⟨hy0, hgy⟩ := hg'
  have hfpre := (fin_pre hrep3 ctlOK_idle).2 ⟨rfl, fun l _ => by simp [hy0]⟩
  have hrf : finRow (labsU d) W ∈ unTbl d W N :=
    mem_unTbl.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have hfin := fin_post hrep3 (strip_applyRow (s := s3) (add_clean hrf))
  refine ⟨_, ((((Relation.ReflTransGen.single (stepTbl_applyRow hr0 (zero_pre.2 hc0))).trans
    hs1).tail (stepTbl_applyRow hrd hpred)).trans hs3).tail
    (stepTbl_applyRow hrf (pre_of_strip hfpre)), ?_⟩
  intro f hf
  simp only [goalU, List.mem_append, List.mem_map, List.mem_singleton] at hf
  rcases hf with ⟨v, hv, rfl⟩ | rfl
  · exact (mem_strip.1 ((hfin.mem_fSt ctlOK_done v).2 (hgy v hv))).1
  · exact (mem_strip.1 (hfin.mem_done.2 rfl)).1

end Complete

end UOTbl

end HTN
