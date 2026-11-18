import ComplexityTheory.Space.AltModel
import HtnComplexity.Space.AltTbl
import HtnComplexity.Space.InstMachine
/-!
# The tests of the alternating target-side machine

The alternating machine of `HtnComplexity/Space/AltMachine.lean` reads the same advice as
the nondeterministic machine of the tail-recursive case — an action table written out as
`HTN.Space.tblAdv` — but distinguishes three kinds of rows by a marker in their delete lists
(`HTN.Space.AReach`): the marker `1` makes a row a push row, the marker `5` a return row.  This
file provides the three transition tests, each with a semantic lemma and a closure lemma:

* `HTN.Space.plainStepB` — some plain row (no marker) leads from one state to the other;
* `HTN.Space.pushStepB` — the row named by a given entry is a push row, it is followed by another
  row, and it leads from one state to the other;
* `HTN.Space.retStepB` — the row after the one named by a given entry leads from one state to the
  other.

A row is named by the encoded entry `true :: bstr (rowId i)`; the next row is named by prefixing
two `true` bits (`HTN.Space.nxtId`), since `rowId (i + 1) = true :: rowId i`.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### Markers and names -/

/-- The marker of push rows. -/
def kPush : ℕ := 1

/-- The marker of return rows. -/
def kRet : ℕ := 5

/-- The encoded entry of a numeral. -/
def natEnt (n : ℕ) : List Bool := true :: bstr (bitsOfNat n)

/-- The encoded name of the `i`-th row. -/
def idEnt (i : ℕ) : List Bool := true :: bstr (rowId i)

/-- The name of the next row. -/
def nxtId (U : List Bool) : List Bool := true :: true :: U

theorem nxtId_idEnt (i : ℕ) : nxtId (idEnt i) = idEnt (i + 1) := by
  simp [nxtId, idEnt, rowId, List.replicate_succ, bstr]

theorem idEnt_injective : Function.Injective idEnt := by
  intro i j h
  simp only [idEnt, List.cons.injEq, true_and] at h
  have h1 := (bstr_parse (r := []) (s := []) (by simpa using h)).1
  have := congrArg List.length h1
  simpa [rowId] using this

/-! ### The tests -/

/-- The row named by `U` carries the marker `k` in its delete list (`y`: the fact entries). -/
def markB (k : ℕ) (U y : List Bool) : Bool := occB y (mkEnt tagDel U (natEnt k))

/-- The row named by `U` is plain. -/
def plainOkB (U y : List Bool) : Bool := !markB kPush U y && !markB kRet U y

/-- **Some plain row leads from `c` to `c'`.** -/
def plainStepB (a c c' : List Bool) : Bool :=
  afterB (fun args =>
    anyEntB (fun args2 => plainOkB (args2.getD 0 []) (args2.getD 1 []) &&
      rowStepB (args2.getD 0 []) (args2.getD 1 []) (args2.getD 2 []) (args2.getD 3 []))
      (args.getD 1 []) (args.getD 0 []) (args.getD 2 []) (args.getD 3 []))
    a a c c'

/-- `U` is the name of a row of the advice. -/
def isIdB (a U : List Bool) : Bool :=
  anyEntB (fun args => decide (args.getD 0 [] = args.getD 1 [])) a U [] []

/-- **The row named by `U` is a push row followed by another row, and leads from `c` to `c'`.** -/
def pushStepB (a U c c' : List Bool) : Bool :=
  isIdB a U && isIdB a (nxtId U) &&
    afterB (fun args => markB kPush (args.getD 1 []) (args.getD 0 []) &&
      rowStepB (args.getD 1 []) (args.getD 0 []) (args.getD 2 []) (args.getD 3 [])) a U c c'

/-- **The row after the one named by `U` leads from `c` to `c'`.** -/
def retStepB (a U c c' : List Bool) : Bool :=
  isIdB a U && isIdB a (nxtId U) &&
    afterB (fun args => rowStepB (nxtId (args.getD 1 [])) (args.getD 0 []) (args.getD 2 [])
      (args.getD 3 [])) a U c c'

/-! ### What the tests mean -/

/-- The set of facts a configuration carries. -/
def dset (S : List (List Bool)) : Set ℕ := {f | f ∈ decSt S}

theorem tblAdv_eq (b : Bool) (tbl : List Row) :
    tblAdv b tbl = blist (idEnts tbl) ++ (blist (factEnts tbl) ++ [b]) := by
  rw [tblAdv, List.append_assoc]

theorem markB_iff {tbl : List Row} {i : ℕ} (hi : i < tbl.length) (k : ℕ) (b : Bool) :
    markB k (idEnt i) (blist (factEnts tbl) ++ [b]) = true ↔ k ∈ (rowOf tbl i).2.2 := by
  rw [markB, idEnt, natEnt, mkEnt_eq, occB_iff]
  exact mem_factEnts_del hi

theorem isIdB_iff (b : Bool) (tbl : List Row) (U : List Bool) :
    isIdB (tblAdv b tbl) U = true ↔ ∃ i < tbl.length, U = idEnt i := by
  rw [isIdB, tblAdv_eq, anyEntB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, hwU⟩
    obtain ⟨i, hi, rfl⟩ := mem_idEnts_iff.1 hw
    exact ⟨i, hi, hwU.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨rowId i, mem_idEnts_iff.2 ⟨i, hi, rfl⟩, rfl⟩

theorem rowStep_iff_set {tbl : List Row} {i : ℕ} (hi : i < tbl.length) {S S' : List (List Bool)}
    (hS : ∀ w ∈ S, IsCanon w) (hS' : ∀ w ∈ S', IsCanon w) (b : Bool) :
    rowStepB (idEnt i) (blist (factEnts tbl) ++ [b]) (blist S) (blist S') = true ↔
      RowOk (rowOf tbl i) (dset S) ∧ dset S' = rowApp (rowOf tbl i) (dset S) := by
  rw [idEnt, rowStepB_iff hi hS hS' b]
  refine and_congr Iff.rfl ?_
  rw [Set.ext_iff]
  rfl

/-- **The plain transition test.** -/
theorem plainStepB_iff {tbl : List Row} {S S' : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w)
    (hS' : ∀ w ∈ S', IsCanon w) (b : Bool) :
    plainStepB (tblAdv b tbl) (blist S) (blist S') = true ↔
      ∃ i < tbl.length, kPush ∉ (rowOf tbl i).2.2 ∧ kRet ∉ (rowOf tbl i).2.2 ∧
        RowOk (rowOf tbl i) (dset S) ∧ dset S' = rowApp (rowOf tbl i) (dset S) := by
  rw [plainStepB, tblAdv_eq, afterB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [anyEntB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
  constructor
  · rintro ⟨u, hu, ⟨hplain, hstep⟩⟩
    obtain ⟨i, hi, rfl⟩ := mem_idEnts_iff.1 hu
    rw [plainOkB, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at hplain
    have h1 : ¬ markB kPush (idEnt i) (blist (factEnts tbl) ++ [b]) = true := by
      simpa [idEnt] using hplain.1
    have h2 : ¬ markB kRet (idEnt i) (blist (factEnts tbl) ++ [b]) = true := by
      simpa [idEnt] using hplain.2
    rw [markB_iff hi] at h1 h2
    exact ⟨i, hi, h1, h2, (rowStep_iff_set hi hS hS' b).1 hstep⟩
  · rintro ⟨i, hi, h1, h2, hstep⟩
    refine ⟨rowId i, mem_idEnts_iff.2 ⟨i, hi, rfl⟩, ?_, (rowStep_iff_set hi hS hS' b).2 hstep⟩
    rw [← markB_iff hi kPush b] at h1
    rw [← markB_iff hi kRet b] at h2
    simp only [plainOkB, Bool.and_eq_true, Bool.not_eq_true']
    simp only [idEnt, Bool.not_eq_true] at h1 h2
    exact ⟨h1, h2⟩

/-- **The push test.** -/
theorem pushStepB_iff {tbl : List Row} {U : List Bool} {S S' : List (List Bool)}
    (hS : ∀ w ∈ S, IsCanon w) (hS' : ∀ w ∈ S', IsCanon w) (b : Bool) :
    pushStepB (tblAdv b tbl) U (blist S) (blist S') = true ↔
      ∃ i, i + 1 < tbl.length ∧ U = idEnt i ∧ kPush ∈ (rowOf tbl i).2.2 ∧
        RowOk (rowOf tbl i) (dset S) ∧ dset S' = rowApp (rowOf tbl i) (dset S) := by
  rw [pushStepB, Bool.and_eq_true, Bool.and_eq_true, isIdB_iff, isIdB_iff]
  conv_lhs => rw [tblAdv_eq, afterB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨i, hi, rfl⟩, ⟨j, hj, hij⟩⟩, hmark, hstep⟩
    rw [nxtId_idEnt] at hij
    have hji : j = i + 1 := (idEnt_injective hij).symm
    subst hji
    rw [markB_iff hi] at hmark
    exact ⟨i, hj, rfl, hmark, (rowStep_iff_set hi hS hS' b).1 hstep⟩
  · rintro ⟨i, hi, rfl, hmark, hstep⟩
    have hi' : i < tbl.length := by omega
    refine ⟨⟨⟨i, hi', rfl⟩, ⟨i + 1, hi, nxtId_idEnt i⟩⟩, (markB_iff hi' _ b).2 hmark,
      (rowStep_iff_set hi' hS hS' b).2 hstep⟩

/-- **The return test.** -/
theorem retStepB_iff {tbl : List Row} {U : List Bool} {S S' : List (List Bool)}
    (hS : ∀ w ∈ S, IsCanon w) (hS' : ∀ w ∈ S', IsCanon w) (b : Bool) :
    retStepB (tblAdv b tbl) U (blist S) (blist S') = true ↔
      ∃ i, i + 1 < tbl.length ∧ U = idEnt i ∧
        RowOk (rowOf tbl (i + 1)) (dset S) ∧ dset S' = rowApp (rowOf tbl (i + 1)) (dset S) := by
  rw [retStepB, Bool.and_eq_true, Bool.and_eq_true, isIdB_iff, isIdB_iff]
  conv_lhs => rw [tblAdv_eq, afterB_iff]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  constructor
  · rintro ⟨⟨⟨i, hi, rfl⟩, ⟨j, hj, hij⟩⟩, hstep⟩
    rw [nxtId_idEnt] at hij hstep
    have hji : j = i + 1 := (idEnt_injective hij).symm
    subst hji
    exact ⟨i, hj, rfl, (rowStep_iff_set hj hS hS' b).1 hstep⟩
  · rintro ⟨i, hi, rfl, hstep⟩
    have hi' : i < tbl.length := by omega
    refine ⟨⟨⟨i, hi', rfl⟩, ⟨i + 1, hi, nxtId_idEnt i⟩⟩, ?_⟩
    rw [nxtId_idEnt]
    exact (rowStep_iff_set hi hS hS' b).2 hstep

/-! ### The tests are predicates of Cobham's class -/

theorem cobham_natEnt (k : ℕ) : Cobham fun _ : Args => natEnt k := cobham_const _

theorem cobhamB_markB (k : ℕ) {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => markB k (a args) (b args) :=
  (cobhamB_occB hb (cobham_mkEnt tagDel ha (cobham_natEnt k))).of_eq fun _ => rfl

theorem cobhamB_plainOkB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => plainOkB (a args) (b args) :=
  ((cobhamB_markB kPush ha hb).not.and (cobhamB_markB kRet ha hb).not).of_eq fun _ => rfl

theorem cobhamB_plainStepB {a b c : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => plainStepB (a args) (b args) (c args) := by
  have hrow : CobhamB fun args2 : Args =>
      plainOkB (args2.getD 0 []) (args2.getD 1 []) &&
      rowStepB (args2.getD 0 []) (args2.getD 1 []) (args2.getD 2 []) (args2.getD 3 []) :=
    ((cobhamB_plainOkB (Cobham.proj 0) (Cobham.proj 1)).and
      (cobhamB_rowStepB (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2) (Cobham.proj 3))).of_eq
      fun args => by simp [proj]
  have hany : CobhamB fun args : Args =>
      anyEntB (fun args2 => plainOkB (args2.getD 0 []) (args2.getD 1 []) &&
        rowStepB (args2.getD 0 []) (args2.getD 1 []) (args2.getD 2 []) (args2.getD 3 []))
        (args.getD 1 []) (args.getD 0 []) (args.getD 2 []) (args.getD 3 []) :=
    (cobhamB_anyEntB hrow (Cobham.proj 1) (Cobham.proj 0) (Cobham.proj 2)
      (Cobham.proj 3)).of_eq fun args => by simp [proj]
  exact (cobhamB_afterB hany ha ha hb hc).of_eq fun _ => rfl

theorem cobhamB_isIdB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => isIdB (a args) (b args) := by
  have heq : CobhamB fun args : Args => decide (args.getD 0 [] = args.getD 1 []) :=
    (cobhamB_eqStr (Cobham.proj 0) (Cobham.proj 1)).of_eq fun args => by simp [proj]
  exact (cobhamB_anyEntB heq ha hb Cobham.empty Cobham.empty).of_eq fun _ => rfl

theorem cobham_nxtId {a : Fn} (ha : Cobham a) : Cobham fun args => nxtId (a args) :=
  (cobham_consT (cobham_consT ha)).of_eq' fun _ => rfl

theorem cobhamB_pushStepB {a u b c : Fn} (ha : Cobham a) (hu : Cobham u) (hb : Cobham b)
    (hc : Cobham c) : CobhamB fun args => pushStepB (a args) (u args) (b args) (c args) := by
  have hin : CobhamB fun args : Args =>
      markB kPush (args.getD 1 []) (args.getD 0 []) &&
      rowStepB (args.getD 1 []) (args.getD 0 []) (args.getD 2 []) (args.getD 3 []) :=
    ((cobhamB_markB kPush (Cobham.proj 1) (Cobham.proj 0)).and
      (cobhamB_rowStepB (Cobham.proj 1) (Cobham.proj 0) (Cobham.proj 2) (Cobham.proj 3))).of_eq
      fun args => by simp [proj]
  exact (((cobhamB_isIdB ha hu).and (cobhamB_isIdB ha (cobham_nxtId hu))).and
    (cobhamB_afterB hin ha hu hb hc)).of_eq fun _ => rfl

theorem cobhamB_retStepB {a u b c : Fn} (ha : Cobham a) (hu : Cobham u) (hb : Cobham b)
    (hc : Cobham c) : CobhamB fun args => retStepB (a args) (u args) (b args) (c args) := by
  have hin : CobhamB fun args : Args =>
      rowStepB (nxtId (args.getD 1 [])) (args.getD 0 []) (args.getD 2 []) (args.getD 3 []) :=
    (cobhamB_rowStepB (cobham_nxtId (Cobham.proj 1)) (Cobham.proj 0) (Cobham.proj 2)
      (Cobham.proj 3)).of_eq fun args => by simp [proj]
  exact (((cobhamB_isIdB ha hu).and (cobhamB_isIdB ha (cobham_nxtId hu))).and
    (cobhamB_afterB hin ha hu hb hc)).of_eq fun _ => rfl

end Space

end HTN
