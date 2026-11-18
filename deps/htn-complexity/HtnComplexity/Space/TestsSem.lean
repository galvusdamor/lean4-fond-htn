import HtnComplexity.Space.Tests
/-!
# What the tests of the target-side machine mean

This file reads the tests defined in `HtnComplexity/Space/Tests.lean` on well-formed
strings: a configuration that is a serialised list of canonical numerals, an input that is the
initial state and the goal of a table problem, and an advice that is an action table written by
`HTN.Space.tblAdv`.  The last four lemmas — `HTN.Space.stepCoreB_iff`,
`HTN.Space.initCoreB_iff`, `HTN.Space.accCoreB_iff` and `HTN.Space.wfB_iff` — are what the
correctness proof of the machine (`HtnComplexity/Space/TblMachine.lean`) runs on: they say
that the transition test *is* the transition relation of the action table the advice carries,
that the initial test *is* "the configuration carries the facts of the initial state", and that
the accepting test *is* "the flag is set and the goal is reached".
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### The suffix after the leading serialised list -/

/-- **The suffix is the one that follows the leading serialised list.** -/
theorem afterB_iff (p : Args → Bool) (l : List (List Bool)) (z v₁ v₂ v₃ : List Bool) :
    afterB p (blist l ++ z) v₁ v₂ v₃ = true ↔ p [z, v₁, v₂, v₃] = true := by
  rw [afterB, Bool.not_eq_true', ← Bool.not_eq_true, anyTailsB_eq_true]
  constructor
  · intro h
    by_contra hp
    refine h ⟨z, ⟨blist l, rfl⟩, ?_⟩
    simp only [afterTest, List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨?_, by simpa using hp⟩
    rw [cutAt_append]
    exact blistB_iff.2 ⟨l, rfl⟩
  · rintro hp ⟨s, hs, hst⟩
    simp only [afterTest, List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at hst
    obtain ⟨hb, hpf⟩ := hst
    obtain ⟨l', hl'⟩ := blistB_iff.1 hb
    have hsplit : blist l' ++ s = blist l ++ z := by
      rw [← hl', cutAt]
      exact suffix_take_append hs
    obtain ⟨-, rfl⟩ := blist_parse hsplit
    rw [hp] at hpf
    simp at hpf

/-! ### Reading and building the entries of the advice -/

theorem length_dbl (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [dbl_cons]; simp [ih]; omega

theorem init_entry (u : List Bool) :
    (true :: bstr u).take ((true :: bstr u).length - 1) = true :: dbl u := by
  rw [bstr_eq_dbl]
  simp [length_dbl]

theorem extB_iff (u w : List Bool) : extB (true :: bstr u) (true :: bstr w) = true ↔ u <+: w := by
  rw [extB, init_entry]
  simp only [decide_eq_true_eq, List.cons_prefix_cons, true_and]
  rw [bstr_eq_dbl]
  exact dbl_prefix_iff u w []

theorem restOf_eq (u y : List Bool) :
    restOf (true :: bstr u) (true :: bstr (u ++ y)) = bstr y := by
  rw [restOf, bstr_eq_dbl (u ++ y), bstr_eq_dbl y, dbl_append]
  simp [length_dbl, List.append_assoc]

theorem tagIsB_iff {t t' : List Bool} (ht : t.length = 2) (ht' : t'.length = 2)
    (u v : List Bool) :
    tagIsB t (true :: bstr u) (true :: bstr (u ++ t' ++ v)) = true ↔ t = t' := by
  rw [tagIsB, List.append_assoc, restOf_eq, bstr_eq_dbl]
  simp only [decide_eq_true_eq]
  rw [dbl_prefix_iff]
  constructor
  · intro h
    have h2 : t = (t' ++ v).take t.length := List.prefix_iff_eq_take.1 h
    rw [ht, ← ht'] at h2
    rwa [List.take_left] at h2
  · rintro rfl
    exact List.prefix_append _ _

theorem factOf_eq {t : List Bool} (ht : t.length = 2) (u v : List Bool) :
    factOf (true :: bstr u) (true :: bstr (u ++ t ++ v)) = true :: bstr v := by
  rw [factOf, List.append_assoc, restOf_eq, bstr_eq_dbl (t ++ v), dbl_append,
    List.append_assoc, ← bstr_eq_dbl]
  simp [length_dbl, ht]

theorem mkEnt_eq (t u v : List Bool) :
    mkEnt t (true :: bstr u) (true :: bstr v) = true :: bstr (u ++ t ++ v) := by
  rw [mkEnt, bstr_eq_dbl (u ++ t ++ v), dbl_append, dbl_append]
  simp [bstr_eq_dbl, length_dbl, List.append_assoc]

/-! ### Canonical entries, and well-formed configurations -/

theorem canonEntB_iff (w : List Bool) : canonEntB (true :: bstr w) = true ↔ IsCanon w := by
  rw [canonEntB, isCanon_iff_getLast]
  rcases List.eq_nil_or_concat w with rfl | ⟨w', b, rfl⟩
  · simp [bstr]
  · rw [List.concat_eq_append]
    have hb : bstr (w' ++ [b]) = dbl w' ++ [true, b, false] := by
      rw [bstr_eq_dbl, dbl_append]
      simp [dbl_cons]
    have hlast : (w' ++ [b]).getLast? = some b := by simp
    have hnil : w' ++ [b] ≠ [] := by simp
    rw [hb, hlast]
    have hlen : (true :: (dbl w' ++ [true, b, false])) ≠ [true, false] := by
      intro hc
      have := congrArg List.length hc
      simp [length_dbl] at this
    simp only [hlen, decide_false, Bool.false_or, decide_eq_true_eq, hnil, false_or,
      Option.some.injEq]
    constructor
    · rintro ⟨q, hq⟩
      have hq' : q ++ [true, true, false] = (true :: dbl w') ++ [true, b, false] := by
        rw [hq]; simp
      obtain ⟨-, h2⟩ := List.append_inj' hq' rfl
      simpa using h2
    · rintro rfl
      exact ⟨true :: dbl w', by simp⟩

/-- **A configuration passes the well-formedness test exactly when it is a serialised list of
canonical numerals of the allowed length.** -/
theorem wfB_iff {c bnd : List Bool} :
    wfB c bnd = true ↔
      ∃ S, c = blist S ∧ (∀ w ∈ S, IsCanon w) ∧ c.length ≤ bnd.length := by
  rw [wfB]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hb, hall⟩, hlen⟩
    obtain ⟨S, rfl⟩ := blistB_iff.1 hb
    refine ⟨S, rfl, fun w hw => ?_, hlen⟩
    rw [← List.append_nil (blist S)] at hall
    have := (allEntB_iff _ S [] [] [] []).1 hall w hw
    simpa [canonEntB_iff] using this
  · rintro ⟨S, rfl, hcan, hlen⟩
    refine ⟨⟨blistB_iff.2 ⟨S, rfl⟩, ?_⟩, hlen⟩
    rw [← List.append_nil (blist S)]
    refine (allEntB_iff _ S [] [] [] []).2 fun w hw => ?_
    simpa [canonEntB_iff] using hcan w hw

/-! ### Membership in a configuration -/

theorem occB_blist (S : List (List Bool)) (w : List Bool) :
    occB (blist S) (true :: bstr w) = true ↔ w ∈ S := by
  simpa using occB_iff S [] w

theorem occB_decSt {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (f : ℕ) :
    occB (blist S) (true :: bstr (bitsOfNat f)) = true ↔ f ∈ decSt S := by
  rw [occB_blist, mem_decSt_iff hS]

/-! ### The four conditions of a transition -/

theorem bool_imp {a b : Bool} : ((!a) || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

theorem bool_post {x y z : Bool} :
    (x || (y && !z)) = true ↔ (x = true ∨ (y = true ∧ ¬ z = true)) := by
  cases x <;> cases y <;> cases z <;> simp

/-- **The precondition test**: every fact of the list of the row marked by `t` is in the state
the configuration carries. -/
theorem inOkB_iff {tbl : List Row} {i : ℕ} {t : List Bool} (ht : t.length = 2) {L : List ℕ}
    (hL : ∀ f : ℕ, factEnt i t f ∈ factEnts tbl ↔ f ∈ L) {T : List (List Bool)}
    (hT : ∀ w ∈ T, IsCanon w) (b : Bool) :
    inOkB t (true :: bstr (rowId i)) (blist (factEnts tbl) ++ [b]) (blist T) = true ↔
      ∀ f ∈ L, f ∈ decSt T := by
  rw [inOkB, allEntB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ, bool_imp, Bool.and_eq_true]
  constructor
  · intro h f hf
    have hmem : factEnt i t f ∈ factEnts tbl := (hL f).2 hf
    have hw := h _ hmem
    have hshape : factEnt i t f = rowId i ++ t ++ bitsOfNat f := rfl
    rw [hshape] at hw
    have hext : extB (true :: bstr (rowId i))
        (true :: bstr (rowId i ++ t ++ bitsOfNat f)) = true := by
      rw [extB_iff, List.append_assoc]
      exact List.prefix_append _ _
    have htag : tagIsB t (true :: bstr (rowId i))
        (true :: bstr (rowId i ++ t ++ bitsOfNat f)) = true := (tagIsB_iff ht ht _ _).2 rfl
    have hfin := hw ⟨hext, htag⟩
    rwa [factOf_eq ht, occB_decSt hT] at hfin
  · intro h w hw hguard
    obtain ⟨j, t', f', hj, ht', rfl⟩ := mem_factEnts_shape hw
    obtain ⟨hext, htag⟩ := hguard
    have hshape : factEnt j t' f' = rowId j ++ t' ++ bitsOfNat f' := rfl
    have hij : i = j := by
      rw [extB_iff] at hext
      exact (rowId_prefix_factEnt_iff i j t' f').1 hext
    subst hij
    rw [hshape, tagIsB_iff ht ht'] at htag
    subst htag
    rw [hshape, factOf_eq ht, occB_decSt hT]
    exact h f' ((hL f').1 hw)

/-- **The \"nothing is lost\" test**: every fact of the configuration is deleted by the row or
survives into the successor. -/
theorem keepOkB_iff {tbl : List Row} {i : ℕ} {D : List ℕ}
    (hD : ∀ f : ℕ, factEnt i tagDel f ∈ factEnts tbl ↔ f ∈ D) {S S' : List (List Bool)}
    (hS : ∀ w ∈ S, IsCanon w) (hS' : ∀ w ∈ S', IsCanon w) (b : Bool) :
    keepOkB (true :: bstr (rowId i)) (blist (factEnts tbl) ++ [b]) (blist S) (blist S') = true ↔
      ∀ f ∈ decSt S, f ∈ D ∨ f ∈ decSt S' := by
  rw [keepOkB, ← List.append_nil (blist S), allEntB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.or_eq_true]
  constructor
  · intro h f hf
    have hb : bitsOfNat f ∈ S := (mem_decSt_iff hS f).1 hf
    have hw := h _ hb
    rw [mkEnt_eq, occB_iff, occB_decSt hS'] at hw
    exact hw.imp (fun hx => (hD f).1 hx) id
  · intro h w hw
    have hwb : w = bitsOfNat (natOfBits w) := (hS w hw).symm
    rw [hwb, mkEnt_eq, occB_iff, occB_decSt hS']
    exact (h _ (List.mem_map.2 ⟨w, hw, rfl⟩)).imp (fun hx => (hD _).2 hx) id

/-- **The \"nothing is invented\" test**: every fact of the successor is added by the row, or was
there and is not deleted. -/
theorem postOkB_iff {tbl : List Row} {i : ℕ} {A D : List ℕ}
    (hA : ∀ f : ℕ, factEnt i tagAdd f ∈ factEnts tbl ↔ f ∈ A)
    (hD : ∀ f : ℕ, factEnt i tagDel f ∈ factEnts tbl ↔ f ∈ D) {S S' : List (List Bool)}
    (hS : ∀ w ∈ S, IsCanon w) (hS' : ∀ w ∈ S', IsCanon w) (b : Bool) :
    postOkB (true :: bstr (rowId i)) (blist (factEnts tbl) ++ [b]) (blist S) (blist S') = true ↔
      ∀ f ∈ decSt S', f ∈ A ∨ (f ∈ decSt S ∧ f ∉ D) := by
  rw [postOkB, ← List.append_nil (blist S'), allEntB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ, bool_post]
  constructor
  · intro h f hf
    have hb : bitsOfNat f ∈ S' := (mem_decSt_iff hS' f).1 hf
    have hw := h _ hb
    rw [mkEnt_eq, mkEnt_eq, occB_iff, occB_iff, occB_decSt hS] at hw
    exact hw.imp (fun hx => (hA f).1 hx) (fun hx => ⟨hx.1, fun hc => hx.2 ((hD f).2 hc)⟩)
  · intro h w hw
    have hwb : w = bitsOfNat (natOfBits w) := (hS' w hw).symm
    rw [hwb, mkEnt_eq, mkEnt_eq, occB_iff, occB_iff, occB_decSt hS]
    exact (h _ (List.mem_map.2 ⟨w, hw, rfl⟩)).imp (fun hx => (hA _).2 hx)
      (fun hx => ⟨hx.1, fun hc => hx.2 ((hD _).1 hc)⟩)

/-! ### One transition, and the transition relation -/

/-- **The transition test for one row of the table is the transition relation of that row.** -/
theorem rowStepB_iff {tbl : List Row} {i : ℕ} (hi : i < tbl.length) {S S' : List (List Bool)}
    (hS : ∀ w ∈ S, IsCanon w) (hS' : ∀ w ∈ S', IsCanon w) (b : Bool) :
    rowStepB (true :: bstr (rowId i)) (blist (factEnts tbl) ++ [b]) (blist S) (blist S') = true ↔
      ((∀ f ∈ (rowOf tbl i).1, f ∈ decSt S) ∧
        ∀ f, f ∈ decSt S' ↔ f ∈ (rowOf tbl i).2.1 ∨ (f ∈ decSt S ∧ f ∉ (rowOf tbl i).2.2)) := by
  rw [rowStepB]
  simp only [Bool.and_eq_true]
  rw [inOkB_iff rfl (fun f => mem_factEnts_prec hi) hS b,
    inOkB_iff rfl (fun f => mem_factEnts_add hi) hS' b,
    keepOkB_iff (fun f => mem_factEnts_del hi) hS hS' b,
    postOkB_iff (fun f => mem_factEnts_add hi) (fun f => mem_factEnts_del hi) hS hS' b]
  constructor
  · rintro ⟨⟨⟨hprec, hadd⟩, hkeep⟩, hpost⟩
    refine ⟨hprec, fun f => ⟨fun hf => hpost f hf, ?_⟩⟩
    rintro (hf | ⟨hf, hnd⟩)
    · exact hadd f hf
    · rcases hkeep f hf with hd | hs
      · exact absurd hd hnd
      · exact hs
  · rintro ⟨hprec, hiff⟩
    refine ⟨⟨⟨hprec, fun f hf => (hiff f).2 (Or.inl hf)⟩, fun f hf => ?_⟩,
      fun f hf => (hiff f).1 hf⟩
    by_cases hd : f ∈ (rowOf tbl i).2.2
    · exact Or.inl hd
    · exact Or.inr ((hiff f).2 (Or.inr ⟨hf, hd⟩))

/-- **The transition test is the transition relation of the action table the advice carries.** -/
theorem stepCoreB_iff {tbl : List Row} {S S' : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w)
    (hS' : ∀ w ∈ S', IsCanon w) (b : Bool) :
    stepCoreB (tblAdv b tbl) (blist S) (blist S') = true ↔ StepTbl tbl (decSt S) (decSt S') := by
  rw [stepCoreB, tblAdv, show blist (idEnts tbl) ++ blist (factEnts tbl) ++ [b]
      = blist (idEnts tbl) ++ (blist (factEnts tbl) ++ [b]) from List.append_assoc _ _ _,
    afterB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [anyEntB_iff]
  constructor
  · rintro ⟨u, hu, hstep⟩
    obtain ⟨i, hi, rfl⟩ := mem_idEnts_iff.1 hu
    obtain ⟨hprec, hiff⟩ := (rowStepB_iff hi hS hS' b).1 hstep
    exact ⟨rowOf tbl i, rowOf_mem hi, hprec, hiff⟩
  · rintro ⟨row, hrow, hprec, hiff⟩
    obtain ⟨i, hi, rfl⟩ := exists_rowOf hrow
    exact ⟨rowId i, mem_idEnts_iff.2 ⟨i, hi, rfl⟩, (rowStepB_iff hi hS hS' b).2 ⟨hprec, hiff⟩⟩

/-! ### The initial and the accepting test -/

/-- **The initial test**: the configuration carries exactly the facts of the initial state. -/
theorem initCoreB_iff {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (s g : List ℕ) :
    initCoreB (blist S) (encProblem s g) = true ↔ ∀ f, f ∈ decSt S ↔ f ∈ s := by
  rw [initCoreB, ← encState_decSt hS, encProblem, ← List.append_nil (encState (decSt S))]
  simp only [Bool.and_eq_true]
  rw [subEntB_encState, subEntB_encState]
  constructor
  · rintro ⟨h1, h2⟩ f
    exact ⟨fun h => h1 f h, fun h => h2 f h⟩
  · intro h
    exact ⟨fun f hf => (h f).1 hf, fun f hf => (h f).2 hf⟩

/-- **The accepting test**: the flag bit of the advice is set and the goal is reached. -/
theorem accCoreB_iff {S : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w) (s g : List ℕ) (b : Bool)
    (tbl : List Row) :
    accCoreB (blist S) (encProblem s g) (tblAdv b tbl) = true ↔
      (b = true ∧ ∀ f ∈ g, f ∈ decSt S) := by
  rw [accCoreB]
  have hrev : ((tblAdv b tbl).reverse.headD false) = b := by simp [tblAdv]
  rw [hrev]
  simp only [Bool.and_eq_true]
  refine and_congr Iff.rfl ?_
  rw [encProblem, encState, afterB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [← List.append_nil (encState g), ← encState_decSt hS, ← List.append_nil (encState (decSt S)),
    subEntB_encState]

end Space

end HTN
