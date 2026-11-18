import HtnComplexity.Article.NoHTNTOValid
/-!
# The steps of the plan, located

The `k`-th step of the plan by ranks: the task of rank `k` (`HTN.Article.NoHTNTO.stepIdxT`), its
label (`HTN.Article.NoHTNTO.lblIdxT`) and the description of its action
(`HTN.Article.NoHTNTO.actLoc`, `HTN.Article.NoHTNTO.at_actLoc`), all found by searching the input.
-/

namespace HTN

namespace Article

namespace NoHTNTO

open Cx Cx.LTerm Syn Syn.PolyDom Logspace NoHTN

/-! ### First matches -/

theorem firstIdx_congr {f g : ℕ → Bool} : ∀ {N : ℕ}, (∀ i < N, f i = g i) → firstIdx f N = firstIdx g N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    rw [firstIdx_succ, firstIdx_succ, ih (fun i hi => h i (by omega)), h N (by omega)]

theorem firstIdx_none {f : ℕ → Bool} {N : ℕ} (h : ∀ i < N, f i = false) : firstIdx f N = N := by
  have hle := firstIdx_le f N
  by_contra hne
  have := (firstIdx_spec f N).2 (by omega)
  rw [h _ (by omega)] at this; simp at this

theorem firstIdx_cons (f : ℕ → Bool) (N : ℕ) :
    firstIdx f (N + 1) = if f 0 then 0 else firstIdx (fun i => f (i + 1)) N + 1 := by
  by_cases h0 : f 0
  · rw [if_pos h0]; exact firstIdx_eq (by omega) h0 (fun i hi => by omega)
  · rw [if_neg h0]
    obtain ⟨h1, h2⟩ := firstIdx_spec (fun i => f (i + 1)) N
    have hle := firstIdx_le (fun i => f (i + 1)) N
    rcases Nat.lt_or_ge (firstIdx (fun i => f (i + 1)) N) N with h | h
    · refine firstIdx_eq (by omega) (h2 h) (fun i hi => ?_)
      rcases i with _ | i
      · simpa using h0
      · exact h1 i (by omega)
    · have he : firstIdx (fun i => f (i + 1)) N = N := by omega
      rw [he]
      apply firstIdx_none
      intro i hi
      rcases i with _ | i
      · simpa using h0
      · exact h1 i (by omega)

theorem find?_getD_eq {α : Type} [Inhabited α] (P : α → Bool) : ∀ l : List α,
    (l.find? P).getD default = l.getD (firstIdx (fun j => P (l.getD j default)) l.length) default
  | [] => by simp [firstIdx]
  | a :: l => by
    rw [List.length_cons, firstIdx_cons]
    by_cases h : P a
    · simp [List.find?_cons_of_pos h, h]
    · rw [List.find?_cons_of_neg (by simpa using h)]
      simp only [List.getD_cons_zero, h, Bool.false_eq_true, if_false, List.getD_cons_succ]
      exact find?_getD_eq P l

theorem filter_headI_eq {α : Type} [Inhabited α] (P : α → Bool) (l : List α) :
    (l.filter P).headI = (l.find? P).getD default := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : P a <;> simp [List.filter_cons, h, ih, List.find?_cons_of_neg]

/-- The label of a task id, by its first matching label. -/
theorem labelB_eq (t : TnDesc) (i : ℕ) :
    labelB t i = (t.lbl.getD (firstIdx (fun q => (t.lbl.getD q default).1 == i) t.lbl.length) default).2 := by
  rw [labelB, filter_headI_eq, find?_getD_eq]

theorem actOf_eq (p : ProbDesc) (a : ℕ) :
    actOf p a = p.actions.getD (firstIdx (fun j => (p.actions.getD j default).1 == a) p.actions.length) default := by
  rw [actOf, find?_getD_eq]

/-! ### Terms -/

/-- The ids of the initial task network. -/
abbrev IDS : LTerm := locTn
/-- Its ordering pairs. -/
abbrev ORD : LTerm := ordLoc 0 locTn
/-- Its labels. -/
abbrev LBL : LTerm := lblLoc 0 locTn

/-- The rank of the number at `(dx, X)`. -/
def rankT (dx : ℕ) (X : LTerm) : LTerm :=
  cntT (lenT 0 IDS) (pairMemT 1 (entryT 0 IDS (.var 0)) dx (lift 1 X) 0 ORD)

/-- The index of the task of rank `k`. -/
def stepIdxT (kT : LTerm) : LTerm :=
  firstB (lenT 0 IDS) (eq (rankT 1 (entryT 0 IDS (.var 0))) (lift 2 kT))

/-- The location of the task of rank `k`. -/
def stepLoc (kT : LTerm) : LTerm := entryT 0 IDS (stepIdxT kT)

/-- The index of its label. -/
def lblIdxT (kT : LTerm) : LTerm :=
  firstB (lenT 0 LBL) (natEqT 1 (entryT 0 LBL (.var 0)) 1 (lift 2 (stepLoc kT)))

/-- The location of the name of its action. -/
def nameLoc (kT : LTerm) : LTerm := sndT .bool 1 (sndT .nat 1 (entryT 0 LBL (lblIdxT kT)))

/-- The index of the description of its action. -/
def actIdxT (kT : LTerm) : LTerm :=
  firstB (lenT 0 (.lit 0)) (natEqT 1 (entryT 0 (.lit 0) (.var 0)) 1 (lift 2 (nameLoc kT)))

/-- **The location of the description of the action of step `k`.** -/
def actLoc (kT : LTerm) : LTerm := entryT 0 (.lit 0) (actIdxT kT)

/-- Its `prec⁺`, `prec⁻`, `eff⁺`, `eff⁻`. -/
def precPLoc (kT : LTerm) : LTerm := sndT .nat 1 (actLoc kT)
def precNLoc (kT : LTerm) : LTerm := sndT fNL 1 (precPLoc kT)
def effPLoc (kT : LTerm) : LTerm := sndT fNL 1 (precNLoc kT)
def effNLoc (kT : LTerm) : LTerm := sndT fNL 1 (effPLoc kT)

/-- The action names of the plan by ranks. -/
abbrev planActs (p : ProbDesc) : List ℕ := actsOf p.tnI (linOf p.tnI)

/-- The label of the task of rank `k`, by index. -/
def lblIdx (t : TnDesc) (k : ℕ) : ℕ := firstIdx (fun q => (t.lbl.getD q default).1 == stepId t k) t.lbl.length

/-- The index of the action of step `k`. -/
def actIdx (p : ProbDesc) (k : ℕ) : ℕ :=
  firstIdx (fun j => (p.actions.getD j default).1 == (planActs p).getD k 0) p.actions.length

theorem At.list_length_lt {y : List Bool} {d q : ℕ} {F : Fmt} {l : List F.ty} (h : At y d q (.list F) l) :
    l.length < y.length := by
  have h1 := LocS.length_le h
  have h2 := length_le_blist (l.map F.enc)
  rw [Fmt.enc_list] at h1
  simp at h2; omega

section Steps

variable {y : List Bool} {M : ℕ} (hM : y.length + 2 ≤ M) {p : ProbDesc} (hp : At y 0 0 fProb p)
include hM hp

theorem lenT_IDS (env : List ℕ) : eval y M env (lenT 0 IDS) = p.tnI.ids.length :=
  eval_lenT hM (at_ids hM (at_tn hM hp env))

theorem eval_rankT {dx : ℕ} {X : LTerm} {env : List ℕ} {x : ℕ} (hX : At y dx (eval y M env X) .nat x) :
    eval y M env (rankT dx X) = rank p.tnI x := by
  have hn := lenT_IDS hM hp env
  have hb := At.list_length_lt (at_ids hM (at_tn hM hp env))
  rw [rankT, eval_cntT _ _ (by rw [hn]; omega), hn, rank, cnt]
  congr 1
  apply List.filter_congr
  intro j hj
  rw [List.mem_range] at hj
  have he : At y 1 (eval y M (j :: env) (entryT 0 IDS (.var 0))) .nat p.tnI.ids[j] :=
    At.entry hM (at_ids hM (at_tn hM hp _)) hj (by simp [eval])
  have hX' : At y dx (eval y M (j :: env) (lift 1 X)) .nat x := by rwa [eval_lift1]
  simp only [eval_pairMemT hM he hX' (at_ord hM (at_tn hM hp _)), List.getD_eq_getElem _ _ hj]

variable (hv : p.Valid) (hto : TOL p.tnI)
include hv hto

theorem eval_stepIdxT {kT : LTerm} {env : List ℕ} {k : ℕ} (hk : eval y M env kT = k) :
    eval y M env (stepIdxT kT) = stepIdx p.tnI k := by
  rw [stepIdxT, eval_firstB, lenT_IDS hM hp env]
  change firstIdx _ _ = _
  apply firstIdx_congr
  intro i hi
  have he : At y 1 (eval y M (i :: p.tnI.ids.length :: env) (entryT 0 IDS (.var 0))) .nat p.tnI.ids[i] :=
    At.entry hM (at_ids hM (at_tn hM hp _)) hi (by simp [eval])
  rw [eval_eq _ _ _ (by omega), eval_rankT hM hp he, eval_lift2, hk, List.getD_eq_getElem _ _ hi]
  by_cases h : rank p.tnI p.tnI.ids[i] = k <;> simp [h]

theorem at_stepLoc {kT : LTerm} {env : List ℕ} {k : ℕ} (hk : eval y M env kT = k) (hkn : k < p.tnI.ids.length) :
    At y 1 (eval y M env (stepLoc kT)) .nat (stepId p.tnI k) := by
  obtain ⟨h1, -, -⟩ := stepId_spec hv.tnI hto hkn
  have := At.entry hM (at_ids hM (at_tn hM hp env)) h1 (eval_stepIdxT hM hp hv hto hk)
  rwa [stepId, List.getD_eq_getElem _ _ h1]

omit hM hp in
theorem lblIdx_lt {k : ℕ} (hkn : k < p.tnI.ids.length) : lblIdx p.tnI k < p.tnI.lbl.length := by
  obtain ⟨-, hmem, -⟩ := stepId_spec hv.tnI hto hkn
  have : stepId p.tnI k ∈ p.tnI.lbl.map Prod.fst := hv.tnI.lbl_perm.symm.subset hmem
  obtain ⟨q, hq, hq1⟩ := List.mem_map.1 this
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  have hle := firstIdx_le (fun q => (p.tnI.lbl.getD q default).1 == stepId p.tnI k) p.tnI.lbl.length
  by_contra hge
  have := (firstIdx_spec (fun q => (p.tnI.lbl.getD q default).1 == stepId p.tnI k) p.tnI.lbl.length).1 j
    (by unfold lblIdx at hge; omega)
  rw [List.getD_eq_getElem _ _ hj, hq1] at this; simp at this

theorem eval_lblIdxT {kT : LTerm} {env : List ℕ} {k : ℕ} (hk : eval y M env kT = k)
    (hkn : k < p.tnI.ids.length) : eval y M env (lblIdxT kT) = lblIdx p.tnI k := by
  have hL := at_lbl hM (at_tn hM hp env)
  rw [lblIdxT, eval_firstB, eval_lenT hM hL]
  change firstIdx _ _ = _
  apply firstIdx_congr
  intro q hq
  have he : At y 1 (eval y M (q :: p.tnI.lbl.length :: env) (entryT 0 LBL (.var 0)))
      (.pair .nat (.pair .bool .nat)) p.tnI.lbl[q] :=
    At.entry hM (at_lbl hM (at_tn hM hp (q :: p.tnI.lbl.length :: env))) hq (by simp [eval])
  have h2 : At y 1 (eval y M (q :: p.tnI.lbl.length :: env) (lift 2 (stepLoc kT))) .nat (stepId p.tnI k) := by
    rw [eval_lift2]; exact at_stepLoc hM hp hv hto hk hkn
  simp only [ne0_natEqT hM (At.p1 he) h2, List.getD_eq_getElem _ _ hq, Bool.beq_eq_decide_eq]

theorem at_nameLoc {kT : LTerm} {env : List ℕ} {k : ℕ} (hk : eval y M env kT = k)
    (hkn : k < p.tnI.ids.length) :
    At y 1 (eval y M env (nameLoc kT)) .nat ((planActs p).getD k 0) := by
  have hL := at_lbl hM (at_tn hM hp env)
  have hlt := lblIdx_lt hv hto hkn
  have he := At.entry hM hL hlt (eval_lblIdxT hM hp hv hto hk hkn)
  have := At.p2 hM (At.p2 hM he)
  have hk' : k < (planActs p).length := by simp [planActs, actsOf, linOf, hkn]
  rw [List.getD_eq_getElem _ _ hk']
  simp only [planActs, actsOf, linOf, List.getElem_map, List.getElem_range, labelB_eq]
  change At y 1 _ .nat (p.tnI.lbl.getD (lblIdx p.tnI k) default).2.2
  rw [List.getD_eq_getElem _ _ hlt]
  exact this

omit hM hp hto in
theorem actIdx_lt (hn : ∀ q ∈ p.tnI.lbl, q.2.1 = false) (hto : TOL p.tnI) {k : ℕ}
    (hkn : k < p.tnI.ids.length) : actIdx p k < p.actions.length := by
  have hlt := lblIdx_lt hv hto hkn
  have hq := List.getElem_mem hlt
  have hdecl := hv.tnI.prim_ok _ hq (hn _ hq)
  have hk' : k < (planActs p).length := by simp [planActs, actsOf, linOf, hkn]
  have hname : (planActs p).getD k 0 = (p.tnI.lbl[lblIdx p.tnI k]'hlt).2.2 := by
    rw [List.getD_eq_getElem _ _ hk']
    simp only [planActs, actsOf, linOf, List.getElem_map, List.getElem_range, labelB_eq]
    change (p.tnI.lbl.getD (lblIdx p.tnI k) default).2.2 = _
    rw [List.getD_eq_getElem _ _ hlt]
  rw [← hname] at hdecl
  obtain ⟨a, ha, hna⟩ := List.mem_map.1 hdecl
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hle := firstIdx_le (fun j => (p.actions.getD j default).1 == (planActs p).getD k 0) p.actions.length
  by_contra hge
  have := (firstIdx_spec (fun j => (p.actions.getD j default).1 == (planActs p).getD k 0)
    p.actions.length).1 j (by unfold actIdx at hge; omega)
  rw [List.getD_eq_getElem _ _ hj] at this
  simp [ActDesc.name] at hna
  simp [hna] at this

theorem eval_actIdxT {kT : LTerm} {env : List ℕ} {k : ℕ} (hk : eval y M env kT = k)
    (hkn : k < p.tnI.ids.length) : eval y M env (actIdxT kT) = actIdx p k := by
  have hA := at_acts hM hp env
  rw [actIdxT, eval_firstB, eval_lenT hM hA]
  change firstIdx _ _ = _
  apply firstIdx_congr
  intro j hj
  have he : At y 1 (eval y M (j :: p.actions.length :: env) (entryT 0 (.lit 0) (.var 0))) fAct p.actions[j] :=
    At.entry hM (at_acts hM hp (j :: p.actions.length :: env)) hj (by simp [eval])
  have h2 : At y 1 (eval y M (j :: p.actions.length :: env) (lift 2 (nameLoc kT))) .nat ((planActs p).getD k 0) := by
    rw [eval_lift2]; exact at_nameLoc hM hp hv hto hk hkn
  simp only [ne0_natEqT hM (At.p1 he) h2, List.getD_eq_getElem _ _ hj, Bool.beq_eq_decide_eq]

/-- **The description of the action of step `k`, located.** -/
theorem at_actLoc (hn : ∀ q ∈ p.tnI.lbl, q.2.1 = false) {kT : LTerm} {env : List ℕ} {k : ℕ}
    (hk : eval y M env kT = k) (hkn : k < p.tnI.ids.length) :
    At y 1 (eval y M env (actLoc kT)) fAct (actOf p ((planActs p).getD k 0)) := by
  have hlt := actIdx_lt hv hn hto hkn
  have := At.entry hM (at_acts hM hp env) hlt (eval_actIdxT hM hp hv hto hk hkn)
  rw [actOf_eq]
  change At y 1 _ fAct (p.actions.getD (actIdx p k) default)
  rw [List.getD_eq_getElem _ _ hlt]
  exact this

end Steps

end NoHTNTO

end Article

end HTN
