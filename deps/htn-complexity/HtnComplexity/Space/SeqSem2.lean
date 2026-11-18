import HtnComplexity.Space.SeqSem1
/-!
# What the gadget tests read off the code and the advice

The pieces of `HtnComplexity/Space/SeqTests.lean` that look into the code of the instance
(identifiers, ordering pairs, labels, initial facts) and into the advice (the two marker rows).
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### The marker rows of the advice -/

/-- The numeral announcing the primitive name `a` in the second marker row. -/
def vf (a : ℕ) : ℕ := natOfBits (serNat a ++ [true])

theorem bitsOfNat_vf (a : ℕ) : bitsOfNat (vf a) = serNat a ++ [true] :=
  isCanon_of_getLast (Or.inr (by simp))

theorem vf_injective : Function.Injective vf := by
  intro a a' h
  have := congrArg bitsOfNat h
  rw [bitsOfNat_vf, bitsOfNat_vf] at this
  exact (serNat_parse this).1

/-- **The two marker rows**: the root task of the gadget, and the primitive names the domain
mentions.  Both are no-ops. -/
def markRows (d : DomDesc) (K : ℕ) : List Row :=
  [([cRoot d], [], []), (((vocA d).filter fun a => decide ((bitsOfNat a).length ≤ K)).map vf, [], [])]

theorem instSer_split (q : InstDesc) :
    instSer q = blist (q.initList.map bitsOfNat) ++ (blist (q.goalList.map bitsOfNat) ++
      (blist (q.tnI.ids.map bitsOfNat) ++ (blist (q.tnI.ordList.map serPair) ++
        blist (q.tnI.lbl.map serLbl)))) := instSer_eq_blists q

theorem tblAdv_split (b : Bool) (tbl : List Row) :
    tblAdv b tbl = blist (idEnts tbl) ++ (blist (factEnts tbl) ++ [b]) := by
  simp [tblAdv]

theorem advOcc_iff (b : Bool) (tbl : List Row) (u : List Bool) :
    advOcc (tblAdv b tbl) (true :: bstr u) = true ↔ u ∈ factEnts tbl := by
  rw [advOcc, tblAdv_split, atL_succ, atL_zero, advOccBody, occB_iff]

theorem mkEnt_U0 (w : List Bool) :
    mkEnt tagPrec U0 (true :: bstr w) = true :: bstr (rowId 0 ++ tagPrec ++ w) := by
  rw [mkEnt]; simp [U0, rowId, tagPrec, bstr_eq_dbl, dbl_append, dbl_cons, dbl]

/-- **The root test**: an entry passes it exactly when it is the root task of the gadget. -/
theorem kRoot_iff (d : DomDesc) (K : ℕ) (b : Bool) (T : List Row) {w : List Bool} (hw : IsCanon w) :
    kRoot (true :: bstr w) (tblAdv b (markRows d K ++ T)) = true ↔ natOfBits w = cRoot d := by
  rw [kRoot, mkEnt_U0, advOcc_iff]
  have : rowId 0 ++ tagPrec ++ w = factEnt 0 tagPrec (natOfBits w) := by rw [factEnt, hw]
  rw [this, mem_factEnts_prec (by simp [markRows])]
  simp [rowOf, markRows]

theorem markA_eq (a0 : ℕ) :
    markA ++ (dbl (serNat a0) ++ ttf) = true :: bstr (factEnt 1 tagPrec (vf a0)) := by
  rw [factEnt, bitsOfNat_vf, bstr_eq_dbl]
  simp [markA, rowId, tagPrec, dbl_append, dbl_cons, dbl, ttf]

theorem advOcc_markA (d : DomDesc) (K : ℕ) (b : Bool) (T : List Row) (a0 : ℕ) :
    advOcc (tblAdv b (markRows d K ++ T)) (markA ++ (dbl (serNat a0) ++ ttf)) = true ↔
      a0 ∈ vocA d ∧ (bitsOfNat a0).length ≤ K := by
  rw [markA_eq, advOcc_iff, mem_factEnts_prec (by simp [markRows])]
  simp only [rowOf, markRows, List.cons_append, List.getD_cons_succ, List.getD_cons_zero,
    List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨a, ha, h⟩ => vf_injective h ▸ ha, fun h => ⟨a0, h, rfl⟩⟩

theorem dbl_lblBits_inl (a : ℕ) : dbl (lblBits (Sum.inl a)) = [true, false] ++ dbl (serNat a) := by
  simp [lblBits, dbl_cons]

theorem dbl_lblBits_inr (c : ℕ) : dbl (lblBits (Sum.inr c)) = [true, true] ++ dbl (serNat c) := by
  simp [lblBits, dbl_cons]

/-- **The unknown-primitive test** on a label entry. -/
theorem unknownD_iff (d : DomDesc) (K : ℕ) (b : Bool) (T : List Row) (p : ℕ) (x : ℕ ⊕ ℕ) :
    unknownD (true :: bstr (bitsOfNat (cfG (.lab p x)))) (tblAdv b (markRows d K ++ T)) = true ↔
      ∃ a0, x = Sum.inl a0 ∧ ¬ (a0 ∈ vocA d ∧ (bitsOfNat a0).length ≤ K) := by
  have hE : (true :: bstr (bitsOfNat (cfG (.lab p x)))).drop 13 =
      dbl (unary p) ++ (dbl (lblBits x) ++ ttf) := by rw [entG_lab, drop_kp rfl]
  rw [unknownD, tailsE_posD hE (fun _ t a => decide ([true, false] <+: t) &&
    !advOcc a (markA ++ t.drop 2)) (fun _ _ _ => by simp [unknownBody, Bool.and_assoc])]
  rcases x with a0 | c
  · rw [dbl_lblBits_inl]
    simp only [List.append_assoc, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    have hd : ([true, false] ++ (dbl (serNat a0) ++ ttf)).drop 2 = dbl (serNat a0) ++ ttf := rfl
    rw [hd, Bool.eq_false_iff, ne_eq, advOcc_markA]
    simp
  · rw [dbl_lblBits_inr]
    simp

/-! ### Reading the code -/

theorem witId_iff (E : List Bool) (q : InstDesc) :
    witId E (instSer q) = true ↔ ∃ i ∈ q.tnI.ids, witNode E (dbl (serNat i)) = true := by
  rw [witId, instSer_split, atL_succ, atL_succ, atL_zero, anyE_iff]
  simp [witIdBody, serNat]

theorem bstr_serPair (e : ℕ × ℕ) :
    bstr (serPair e) = dbl (bstr (bitsOfNat e.1)) ++ (dbl (bstr (bitsOfNat e.2)) ++ [false]) := by
  rw [serPair, bstr_eq_dbl, dbl_append]; simp [serNat]

theorem witFst_iff (E : List Bool) (e : ℕ × ℕ) :
    witFst E (true :: bstr (serPair e)) = true ↔ witNode E (dbl (serNat e.1)) = true := by
  rw [witFst, List.tail_cons, tailsE_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [witFstBody, Bool.and_eq_true] at h
    obtain ⟨u, hu⟩ := (isBD_iff _).1 h.1
    have hsplit : cutAt (bstr (serPair e)) s ++ s = bstr (serPair e) := suffix_take_append hs
    rw [hu, bstr_serPair] at hsplit
    obtain ⟨rfl, -⟩ := dbl_bstr_parse hsplit
    show witNode E (dbl (bstr (bitsOfNat e.1))) = true
    rw [← hu]; exact h.2
  · intro h
    refine ⟨dbl (bstr (bitsOfNat e.2)) ++ [false], ?_, ?_⟩
    · rw [bstr_serPair]; exact List.suffix_append _ _
    · rw [witFstBody, bstr_serPair, cutAt_append, Bool.and_eq_true]
      exact ⟨(isBD_iff _).2 ⟨_, rfl⟩, h⟩

theorem witSnd_iff (E : List Bool) (e : ℕ × ℕ) :
    witSnd E (true :: bstr (serPair e)) = true ↔ witNode E (dbl (serNat e.2)) = true := by
  rw [witSnd, List.tail_cons, tailsE_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    simp only [witSndBody, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨u1, hu1⟩ := (isBD_iff _).1 h1
    obtain ⟨u2, hu2⟩ := (isBD_iff _).1 h2
    have hs' : s = s.take (s.length - 1) ++ [false] := (suffix_take_append h3).symm
    have hsplit : cutAt (bstr (serPair e)) s ++ s = bstr (serPair e) := suffix_take_append hs
    rw [hu1, hs', hu2, bstr_serPair] at hsplit
    obtain ⟨-, h5⟩ := dbl_bstr_parse hsplit
    obtain ⟨rfl, -⟩ := dbl_bstr_parse h5
    show witNode E (dbl (bstr (bitsOfNat e.2))) = true
    rw [← hu2]; exact h4
  · intro h
    refine ⟨dbl (bstr (bitsOfNat e.2)) ++ [false], ?_, ?_⟩
    · rw [bstr_serPair]; exact List.suffix_append _ _
    · have ht : (dbl (bstr (bitsOfNat e.2)) ++ [false]).take
          ((dbl (bstr (bitsOfNat e.2)) ++ [false]).length - 1) = dbl (bstr (bitsOfNat e.2)) := by
        simp
      simp only [witSndBody, bstr_serPair, cutAt_append, ht, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨(isBD_iff _).2 ⟨_, rfl⟩, (isBD_iff _).2 ⟨_, rfl⟩⟩, List.suffix_append _ _⟩, h⟩

theorem witAny_iff (E : List Bool) (q : InstDesc) :
    witAny E (instSer q) = true ↔ ∃ a ∈ wnodes q.tnI, witNode E (dbl (serNat a)) = true := by
  rw [witAny, Bool.or_eq_true, witId_iff]
  have h2 : atL 3 (anyE witPairBody) (instSer q) E [] [] = true ↔
      ∃ e ∈ q.tnI.ordList, witNode E (dbl (serNat e.1)) = true ∨
        witNode E (dbl (serNat e.2)) = true := by
    rw [instSer_split, atL_succ, atL_succ, atL_succ, atL_zero, anyE_iff]
    simp [witPairBody, witFst_iff, witSnd_iff]
  rw [h2]
  simp only [wnodes, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨e, he, h | h⟩)
    · exact ⟨i, Or.inl hi, h⟩
    · exact ⟨e.1, Or.inr ⟨e, he, Or.inl rfl⟩, h⟩
    · exact ⟨e.2, Or.inr ⟨e, he, Or.inr rfl⟩, h⟩
  · rintro ⟨a, hi | ⟨e, he, rfl | rfl⟩, h⟩
    · exact Or.inl ⟨a, hi, h⟩
    · exact Or.inr ⟨e, he, Or.inl h⟩
    · exact Or.inr ⟨e, he, Or.inr h⟩

theorem kInst_iff (E : List Bool) (q : InstDesc) :
    kInst E (instSer q) = true ↔ ∃ v ∈ q.initList, E = true :: bstr (tagI3 ++ bitsOfNat v) := by
  rw [kInst, instSer_split, anyE_iff]
  simp [kInstBody, preEnt_eq]

theorem pInst_iff (S : List (List Bool)) (q : InstDesc) :
    pInst (blist S) (instSer q) = true ↔ ∀ v ∈ q.initList, tagI3 ++ bitsOfNat v ∈ S := by
  rw [pInst, instSer_split, allE_iff]
  simp [pInstBody, preEnt_eq, occB_blist]

theorem goal_iff (S : List (List Bool)) (q : InstDesc) :
    atL 1 (allE pInstBody) (instSer q) (blist S) [] [] = true ↔
      ∀ v ∈ q.goalList, tagI3 ++ bitsOfNat v ∈ S := by
  rw [instSer_split, atL_succ, atL_zero, allE_iff]
  simp [pInstBody, preEnt_eq, occB_blist]

/-! ### Labels -/

theorem firstLblD_iff (l : List (List Bool)) (w K : List Bool) :
    firstLblD (blist l) w (dbl K) = true ↔
      ∃ l₁ l₂, l = l₁ ++ (w ++ K) :: l₂ ∧ ∀ v' ∈ l₁, ¬ (w <+: v') := by
  rw [firstLblD, tailsE_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    simp only [lblTestD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨hent, hpre⟩, hocc⟩ := h
    obtain ⟨a, ha⟩ := entriesB_iff.1 hent
    have hsplit : entriesEnc a ++ t = blist l ++ [] := by
      rw [← ha, List.append_nil]; exact suffix_take_append ht
    obtain ⟨l₂, hl, hr⟩ := entriesEnc_align a t l [] hsplit
    rw [List.append_nil] at hr
    cases l₂ with
    | nil => rw [hr] at hpre; obtain ⟨_, h⟩ := hpre; simp at h
    | cons v l₂' =>
      rw [hr, blist_cons] at hpre
      have hpre' : bstr (w ++ K) <+: bstr v ++ blist l₂' := by
        obtain ⟨s, hs⟩ := hpre
        refine ⟨s, ?_⟩
        simp only [List.cons_append, List.cons.injEq, true_and] at hs
        rw [bstr_eq_dbl, dbl_append]; simpa using hs
      rw [bstr_prefix_iff] at hpre'
      refine ⟨a, l₂', by rw [hl, hpre'], ?_⟩
      intro v' hv' hvw
      have hpre2 : cutAt (blist l) t ++ [false] = blist a := by
        rw [ha, blist_eq_entriesEnc]
      rw [hpre2] at hocc
      have : occB (blist a ++ []) (true :: dbl w) = true := (occB_key_iff a [] w).2 ⟨v', hv', hvw⟩
      rw [List.append_nil, hocc] at this
      exact absurd this (by simp)
  · rintro ⟨l₁, l₂, hl, hno⟩
    have hy : blist l = entriesEnc l₁ ++ blist ((w ++ K) :: l₂) := by rw [hl, blist_append_eq]
    refine ⟨blist ((w ++ K) :: l₂), ⟨entriesEnc l₁, hy.symm⟩, ?_⟩
    simp only [lblTestD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    have hcut : cutAt (blist l) (blist ((w ++ K) :: l₂)) = entriesEnc l₁ := by
      rw [hy, cutAt_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hcut]; exact entriesB_iff.2 ⟨l₁, rfl⟩
    · rw [blist_cons, bstr_eq_dbl, dbl_append]
      exact ⟨blist l₂, by simp⟩
    · rw [hcut, ← blist_eq_entriesEnc]
      have : ¬ (occB (blist l₁ ++ []) (true :: dbl w) = true) := by
        rw [occB_key_iff]
        rintro ⟨v', hv', hvw⟩
        exact hno v' hv' hvw
      simpa using this

theorem serNat_prefix_serLbl_iff (i j : ℕ) (b : Bool) (n : ℕ) :
    serNat i <+: serLbl (j, b, n) ↔ i = j := bstr_prefix_serLbl_iff i j b n

theorem serNat_append_eq_serLbl_iff (i j : ℕ) (b : Bool) (n : ℕ) (K : List Bool) :
    serNat i ++ K = serLbl (j, b, n) ↔ i = j ∧ K = b :: serNat n := by
  rw [serLbl]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := serNat_parse h
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem exact_first_iff (lbl : List (ℕ × Bool × ℕ)) (i : ℕ) (K : List Bool) :
    (∃ l₁ l₂, lbl.map serLbl = l₁ ++ (serNat i ++ K) :: l₂ ∧ ∀ v' ∈ l₁, ¬ (serNat i <+: v')) ↔
      ∃ b n, lbl.lookup i = some (b, n) ∧ K = b :: serNat n := by
  induction lbl with
  | nil =>
    constructor
    · rintro ⟨l₁, l₂, hl, -⟩; cases l₁ <;> simp at hl
    · rintro ⟨b, n, h, -⟩; simp at h
  | cons e rest ih =>
    obtain ⟨j, b, n⟩ := e
    by_cases hij : j = i
    · subst hij
      rw [show ((j, b, n) :: rest).lookup j = some (b, n) by simp]
      constructor
      · rintro ⟨l₁, l₂, hl, hno⟩
        cases l₁ with
        | nil =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at hl
          exact ⟨b, n, rfl, ((serNat_append_eq_serLbl_iff j j b n K).1 hl.1.symm).2⟩
        | cons v' l₁' =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at hl
          exact absurd ((serNat_prefix_serLbl_iff j j b n).2 rfl) (hl.1 ▸ hno v' (by simp))
      · rintro ⟨b', n', h, rfl⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rest.map serLbl, by simp [serLbl], by simp⟩
    · have hne : ((j, b, n) :: rest).lookup i = rest.lookup i := by
        have hb : (i == j) = false := by simp [Ne.symm hij]
        simp only [List.lookup, hb]
      rw [hne, ← ih]
      constructor
      · rintro ⟨l₁, l₂, hl, hno⟩
        cases l₁ with
        | nil =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at hl
          exact absurd ((serNat_append_eq_serLbl_iff i j b n K).1 hl.1.symm).1 (Ne.symm hij)
        | cons v' l₁' =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at hl
          exact ⟨l₁', l₂, hl.2, fun v'' hv'' => hno v'' (by simp [hv''])⟩
      · rintro ⟨l₁, l₂, hl, hno⟩
        refine ⟨serLbl (j, b, n) :: l₁, l₂, by simp [hl], ?_⟩
        intro v'' hv''
        rcases List.mem_cons.1 hv'' with rfl | hv''
        · exact fun hc => hij ((serNat_prefix_serLbl_iff i j b n).1 hc).symm
        · exact hno v'' hv''

theorem lookup_ne_none_iff {β : Type} (l : List (ℕ × β)) (i : ℕ) :
    l.lookup i ≠ none ↔ ∃ e ∈ l, e.1 = i := by
  rw [ne_eq, List.lookup_eq_none_iff]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h fun e he => by simpa [bne_iff_ne] using (hc e he).symm
  · rintro ⟨e, he, rfl⟩ h
    have := h e he
    simp at this

theorem lblBits_label (t : TnDesc) (i : ℕ) :
    lblBits (t.label i) = match t.lbl.lookup i with
      | some (b, n) => b :: serNat n
      | none => [false, false] := by
  unfold TnDesc.label
  rcases h : t.lbl.lookup i with _ | ⟨b, n⟩
  · simp [lblBits, serNat]
  · cases b <;> rfl

/-- **The label test**: the doubled label read off an entry is the label of the identifier. -/
theorem labelD_iff (t : TnDesc) (i : ℕ) (DK : List Bool) :
    labelD (blist (t.lbl.map serLbl)) (serNat i) DK = true ↔ DK = dbl (lblBits (t.label i)) := by
  rw [labelD, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, lblBits_label]
  have hkey : occB (blist (t.lbl.map serLbl)) (true :: dbl (serNat i)) = true ↔
      t.lbl.lookup i ≠ none := by
    rw [show blist (t.lbl.map serLbl) = blist (t.lbl.map serLbl) ++ [] by simp, occB_key_iff,
      lookup_ne_none_iff]
    simp only [List.mem_map]
    constructor
    · rintro ⟨v, ⟨⟨j, b, n⟩, he, rfl⟩, hv⟩
      exact ⟨(j, b, n), he, ((serNat_prefix_serLbl_iff i j b n).1 hv).symm⟩
    · rintro ⟨⟨j, b, n⟩, he, hj⟩
      exact ⟨_, ⟨_, he, rfl⟩, (serNat_prefix_serLbl_iff i j b n).2 hj.symm⟩
  constructor
  · rintro ⟨hdbl, h⟩
    obtain ⟨K, rfl⟩ := (isDblD_iff _).1 hdbl
    rcases h with h | ⟨hno, h⟩
    · obtain ⟨b, n, hl, rfl⟩ := (exact_first_iff t.lbl i K).1 ((firstLblD_iff _ _ K).1 h)
      rw [hl]
    · have hnone : t.lbl.lookup i = none := by
        by_contra hc; exact absurd (hkey.2 hc) (by rw [hno]; simp)
      rw [hnone, h]; rfl
  · intro h
    refine ⟨(isDblD_iff _).2 ⟨_, h⟩, ?_⟩
    rcases hl : t.lbl.lookup i with _ | ⟨b, n⟩
    · rw [hl] at h
      refine Or.inr ⟨?_, h⟩
      by_contra hc
      exact (hkey.1 (by simpa using hc)) hl
    · rw [hl] at h
      refine Or.inl ?_
      rw [h, firstLblD_iff]
      exact (exact_first_iff t.lbl i _).2 ⟨b, n, hl, rfl⟩

theorem zOf_wit (p i : ℕ) :
    zOf (true :: bstr (bitsOfNat (cfG (.wit p i)))) (true :: bstr (bitsOfNat i)) = dbl (unary p) := by
  rw [zOf, entG_wit, drop_kp rfl, List.tail_cons]
  exact cutAt_append _ _

/-- **The label-entry test**: for the witness entry of `(p, i)`, an entry passes exactly when it is
the label fact of position `p` with the label of `i`. -/
theorem labOk_iff (E : List Bool) (t : TnDesc) (p i : ℕ) :
    labOk E (true :: bstr (bitsOfNat (cfG (.wit p i)))) (true :: bstr (bitsOfNat i))
      (blist (t.lbl.map serLbl)) = true ↔
      E = true :: bstr (bitsOfNat (cfG (.lab p (t.label i)))) := by
  rw [labOk, zOf_wit, Bool.and_eq_true, decide_eq_true_eq, List.tail_cons,
    show bstr (bitsOfNat i) = serNat i from rfl, labelD_iff, entG_lab]
  constructor
  · rintro ⟨hE, hDK⟩
    rw [hE, hDK]; simp
  · intro hE
    have hDK : dkOf E (dbl (unary p)) = dbl (lblBits (t.label i)) := by
      rw [dkOf, hE, drop_kp rfl, List.drop_left]
      exact cutAt_append _ _
    refine ⟨?_, hDK⟩
    rw [hDK, hE]; simp

theorem labOkX_eq (E E' I : List Bool) (q : InstDesc) :
    labOkX E E' I (instSer q) = labOk E E' I (blist (q.tnI.lbl.map serLbl)) := by
  rw [labOkX, instSer_split, atL_succ, atL_succ, atL_succ, atL_succ, atL_zero]; rfl

end SeqM

end Space

end HTN
