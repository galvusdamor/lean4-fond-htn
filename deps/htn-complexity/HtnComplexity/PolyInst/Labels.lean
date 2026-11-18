import HtnComplexity.PolyInst.Enum
import HtnComplexity.Computable.Rooted
/-!
# Reading compound names off a serialised instance, in polynomial time

Several instance translations need the **compound task names of the initial task network**,

    compoundNames t = t.ids.flatMap (labelList true t.lbl)

(the name of every identifier whose first label is compound, in the order of the identifier
list), or just the first of them, the **root name** `rootName q`.  This file emits them as
functions of Cobham's class:

* `HTN.Syn.PolyInst.lblName pre w y` — at every entry of the label list `y` that is the *first*
  entry for the identifier with numeral `w` and carries a compound name, the string `pre`
  followed by the numeral of the name (`HTN.Syn.PolyInst.lblName_eq`);
* `HTN.Syn.PolyInst.cnList pre x` — the same for every identifier of the serialised instance
  `x`, in order: `cnList pre (instSer q) = compoundNames.flatMap (pre ++ serNat ·)`
  (`HTN.Syn.PolyInst.cnList_instSer`);
* `HTN.Syn.PolyInst.rootSer x` — the numeral of the root name
  (`HTN.Syn.PolyInst.rootSer_instSer : rootSer (instSer q) = serNat (rootName q)`).
-/

namespace HTN

namespace Syn

namespace PolyInst

open PTime Compress TOPlan

/-! ### The first compound label of an identifier -/

/-- The chunk at the position `t` of the label list `y` for the identifier with numeral `w`. -/
def nameAt (pre w y t : List Bool) : List Bool :=
  if (entPos y t && (decide ((true :: dbl (w ++ [true])) <+: t) &&
      !occB (cutS y t ++ [false]) (true :: dbl w))) = true
  then pre ++ undbl (dpre (t.drop (2 * w.length + 3))) else []

/-- The chunks over all positions of the label list. -/
def lblName (pre w y : List Bool) : List Bool := y.tails.flatMap (nameAt pre w y)

/-- The first matching entry of a label list, as a `flatMap` over its decompositions. -/
theorem flatMap_splits_first (G : ℕ → List Bool) (i : ℕ) :
    ∀ lbl : List (ℕ × Bool × ℕ),
      ((splits lbl).flatMap fun p =>
        if p.2.1.1 = i ∧ p.2.1.2.1 = true ∧ ∀ e ∈ p.1, e.1 ≠ i then G p.2.1.2.2 else []) =
      (TnDesc.labelList true lbl i).flatMap G := by
  intro lbl
  induction lbl with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨j, b, n⟩ := e
    simp only [splits, List.flatMap_cons, List.flatMap_map, List.not_mem_nil, false_imp_iff,
      imp_true_iff, and_true, List.mem_cons, forall_eq_or_imp]
    by_cases hj : j = i
    · subst hj
      have hrest : ((splits rest).flatMap fun p =>
          if p.2.1.1 = j ∧ p.2.1.2.1 = true ∧ (j ≠ j ∧ ∀ e ∈ p.1, e.1 ≠ j) then
            G p.2.1.2.2 else []) = [] := by
        simp
      rw [hrest]
      cases b <;> simp [TnDesc.labelList]
    · have hfirst : (if j = i ∧ b = true then G n else []) = [] := by simp [hj]
      rw [hfirst, List.nil_append]
      have : TnDesc.labelList true ((j, b, n) :: rest) i = TnDesc.labelList true rest i := by
        simp [TnDesc.labelList, hj]
      rw [this, ← ih]
      refine List.flatMap_congr fun p _ => ?_
      simp only [ne_eq, hj, not_false_eq_true, true_and]

theorem dbl_length (u : List Bool) : (dbl u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [dbl_cons, ih]; ring

/-- **The label lookup, emitted**: for the numeral of `i`, the chunks over the label list are
`pre` and the numeral of the compound name of `i`, if its first label is compound. -/
theorem lblName_eq (pre : List Bool) (lbl : List (ℕ × Bool × ℕ)) (i : ℕ) (z : List Bool) :
    lblName pre (serNat i) (blist (lbl.map serLbl) ++ z) =
      (TnDesc.labelList true lbl i).flatMap fun n => pre ++ serNat n := by
  set y := blist (lbl.map serLbl) ++ z with hy
  set w := serNat i with hw
  set H : List Bool → List Bool := fun t =>
    if (decide ((true :: dbl (w ++ [true])) <+: t) &&
      !occB (cutS y t ++ [false]) (true :: dbl w)) = true
    then pre ++ undbl (dpre (t.drop (2 * w.length + 3))) else [] with hH
  have hn : ∀ t, nameAt pre w y t = if entPos y t = true then H t else [] := by
    intro t
    simp only [nameAt, hH]
    cases entPos y t <;> simp
  rw [lblName, List.flatMap_congr (fun t _ => hn t), hy, flatMap_entPos,
    ← flatMap_splits_first]
  refine List.flatMap_congr fun p hp => ?_
  obtain ⟨l₁, e, l₂⟩ := p
  obtain ⟨j, b, n⟩ := e
  have hl := mem_splits.1 hp
  simp only at hl
  have hcut : cutS y (blist (((j, b, n) :: l₂).map serLbl) ++ z) = entriesEnc (l₁.map serLbl) :=
    cutS_entry serLbl hl z
  have hocc : occB (entriesEnc (l₁.map serLbl) ++ [false]) (true :: dbl w) = true ↔
      ∃ e ∈ l₁, e.1 = i := by
    rw [← blist_eq_entriesEnc, show blist (l₁.map serLbl) = blist (l₁.map serLbl) ++ [] from
      (List.append_nil _).symm, occB_key_iff]
    simp only [List.mem_map, exists_exists_and_eq_and]
    refine exists_congr fun e => and_congr_right fun _ => ?_
    obtain ⟨j', b', n'⟩ := e
    rw [hw, serNat, bstr_prefix_serLbl_iff]
    exact eq_comm
  have hkey : (true :: dbl (w ++ [true])) <+: blist (((j, b, n) :: l₂).map serLbl) ++ z ↔
      i = j ∧ b = true := by
    rw [key_prefix_iff]
    constructor
    · rintro ⟨v, l', h, hv⟩
      simp only [List.map_cons, List.cons.injEq] at h
      rw [← h.1, hw, serNat, bstr_append_prefix_serLbl_iff] at hv
      refine ⟨hv.1, ?_⟩
      have := hv.2
      simp only [List.cons_prefix_cons] at this
      exact this.1.symm
    · rintro ⟨rfl, rfl⟩
      refine ⟨_, _, rfl, ?_⟩
      rw [hw, serNat, bstr_append_prefix_serLbl_iff]
      simp [List.cons_prefix_cons]
  simp only [hH, hcut]
  by_cases hc : i = j ∧ b = true
  · obtain ⟨rfl, rfl⟩ := hc
    have hno : (∃ e ∈ l₁, e.1 = i) ↔ ¬ ∀ e ∈ l₁, e.1 ≠ i :=
      ⟨fun ⟨e, he, h⟩ hall => hall e he h, fun h => by push_neg at h; exact h⟩
    by_cases hall : ∀ e ∈ l₁, e.1 ≠ i
    · have hocc' : occB (entriesEnc (l₁.map serLbl) ++ [false]) (true :: dbl w) = false := by
        rcases h : occB (entriesEnc (l₁.map serLbl) ++ [false]) (true :: dbl w)
        · rfl
        · exact absurd (hno.1 (hocc.1 h)) (not_not.2 hall)
      have hk := (hkey.2 ⟨rfl, rfl⟩)
      simp only [hk, hocc', decide_true, Bool.not_false, Bool.and_self, if_true, hall, and_self,
        true_and]
      rw [if_pos hall]
      congr 1
      -- the name part of the entry
      have hent : blist (((i, true, n) :: l₂).map serLbl) ++ z =
          true :: (dbl (w ++ [true]) ++ (dbl (bstr (bitsOfNat n)) ++
            (false :: (blist (l₂.map serLbl) ++ z)))) := by
        rw [List.map_cons, blist_cons, bstr_eq_dbl, serLbl_eq, hw, serNat]
        simp [dbl_append, dbl_cons, List.append_assoc]
      rw [hent]
      have hlen : 2 * w.length + 3 = (true :: dbl (w ++ [true])).length := by
        simp [dbl_length]; ring
      rw [hlen, ← List.cons_append, List.drop_left, dpre_dbl_bstr, undbl_dbl]
      rfl
    · have hocc' : occB (entriesEnc (l₁.map serLbl) ++ [false]) (true :: dbl w) = true :=
        hocc.2 (hno.2 hall)
      rw [if_neg (show ¬ (i = i ∧ true = true ∧ ∀ e ∈ l₁, e.1 ≠ i) from fun h => hall h.2.2)]
      simp [hocc']
  · have hk : decide ((true :: dbl (w ++ [true])) <+:
        blist (((j, b, n) :: l₂).map serLbl) ++ z) = false := by
      rw [decide_eq_false_iff_not, hkey]; exact hc
    have hc' : ¬ (j = i ∧ b = true) := fun h => hc ⟨h.1.symm, h.2⟩
    simp only [hk, Bool.false_and, Bool.false_eq_true, if_false]
    rw [if_neg (show ¬ (j = i ∧ b = true ∧ ∀ e ∈ l₁, e.1 ≠ i) from fun h => hc' ⟨h.1, h.2.1⟩)]

theorem cobham_nameAt {pre : List Bool} {w y t : Fn} (hw : Cobham w) (hy : Cobham y)
    (ht : Cobham t) : Cobham fun args => nameAt pre (w args) (y args) (t args) := by
  unfold nameAt
  have hp : CobhamB fun args => (entPos (y args) (t args) &&
      (decide ((true :: dbl (w args ++ [true])) <+: t args) &&
        !occB (cutS (y args) (t args) ++ [false]) (true :: dbl (w args)))) :=
    (cobhamB_entPos hy ht).and ((cobhamB_isPrefix (cobham_consTrue (cobham_dbl
      (PH.cobham_app hw (cobham_const [true])))) ht).and
      (cobhamB_occB (PH.cobham_app (cobham_cut hy ht) (cobham_const [false]))
        (cobham_consTrue (cobham_dbl hw))).not)
  refine (cobham_ifNil hp (PH.cobham_app (cobham_const pre) (cobham_undbl (cobham_dpre
    (cobham_drop (PH.cobham_app (cobham_const [true, true, true]) (cobham_dbl hw)) ht))))).of_eq'
    fun args => ?_
  · simp only [List.length_append, List.length_cons, List.length_nil, dbl_length]
    rw [show 0 + 1 + 1 + 1 + 2 * (w args).length = 2 * (w args).length + 3 by ring]

theorem cobham_lblName {pre : List Bool} {w y : Fn} (hw : Cobham w) (hy : Cobham y) :
    Cobham fun args => lblName pre (w args) (y args) :=
  (cobham_fmTailsC (G := fun args => nameAt pre (w args.tail) (y args.tail) (args.getD 0 []))
    (cobham_nameAt (cobham_tailArgs hw) (cobham_tailArgs hy) cobham_var0) hy).of_eq'
    fun args => by simp [fmTailsL, lblName]

/-! ### All compound names, and the root name -/

/-- The compound names of the initial task network of the serialised instance `x`, each written
as `pre` followed by its numeral. -/
def cnList (pre x : List Bool) : List Bool :=
  (yC x).tails.flatMap fun s => if idPos x s = true then lblName pre (nvAt s) (yE x) else []

theorem cnList_instSer (pre : List Bool) (q : InstDesc) :
    cnList pre (instSer q) = q.tnI.compoundNames.flatMap fun n => pre ++ serNat n := by
  unfold cnList idPos
  rw [yC_instSer, zC, flatMap_entPos]
  rw [show (q.tnI.compoundNames.flatMap fun n => pre ++ serNat n) =
      q.tnI.ids.flatMap fun u => (TnDesc.labelList true q.tnI.lbl u).flatMap fun n =>
        pre ++ serNat n by
    rw [TnDesc.compoundNames, List.flatMap_assoc]]
  rw [← flatMap_splits_entry q.tnI.ids]
  refine List.flatMap_congr fun p _ => ?_
  rw [nvAt_eq, yE_instSer, zE, ← lblName_eq pre q.tnI.lbl p.2.1 []]
  simp

theorem cobham_cnList (pre : List Bool) {x : Fn} (hx : Cobham x) :
    Cobham fun args => cnList pre (x args) := by
  unfold cnList
  exact (cobham_fmTailsC (G := fun args => if idPos (x args.tail) (args.getD 0 []) = true then
      lblName pre (nvAt (args.getD 0 [])) (yE (x args.tail)) else [])
    (cobham_ifNil (cobhamB_idPos (cobham_tailArgs hx) cobham_var0)
      (cobham_lblName (cobham_nvAt cobham_var0) (cobham_yE (cobham_tailArgs hx))))
    (cobham_yC hx)).of_eq' fun args => by simp [fmTailsL]

/-- The numeral of the root name of the serialised instance `x`. -/
def rootSer (x : List Bool) : List Bool :=
  if decide (cnList [] x = []) = true then serNat 0 else bpre (cnList [] x)

theorem rootSer_instSer (q : InstDesc) : rootSer (instSer q) = serNat (rootName q) := by
  rw [rootSer, cnList_instSer, rootName]
  rcases h : q.tnI.compoundNames with _ | ⟨c, cs⟩
  · simp
  · simp only [List.flatMap_cons, List.nil_append, List.headI_cons]
    have hne : serNat c ++ cs.flatMap (fun n => [] ++ serNat n) ≠ [] := by
      simp [serNat, bstr_eq_dbl]
    rw [if_neg (by simpa using hne), serNat, bpre_bstr]

theorem cobham_rootSer {x : Fn} (hx : Cobham x) : Cobham fun args => rootSer (x args) :=
  cobham_iteB (cobhamB_null (cobham_cnList [] hx)) (cobham_const _)
    (cobham_bpre (cobham_cnList [] hx))

end PolyInst

end Syn

end HTN
