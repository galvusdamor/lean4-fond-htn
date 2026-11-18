import HtnComplexity.Article.SATNoHTN
import HtnComplexity.PT.NP
import HtnPlanning.Article.ToSyn
/-!
# Non-hierarchical HTN planning is in NP (Cor. 4.2.9)

A problem without compound tasks in its initial task network has exactly one task network
reachable by decomposition, the initial one; it has a solution iff some linearisation of it is
executable and reaches the goal.  The certificate is that linearisation (a list of task ids); it
is checked in polynomial time on the dual-rail translation `HTN.Article.toSynDom`,
`HTN.Article.toSynInst` (which handles negative preconditions and goals).

* `HTN.Article.NoHTN.solvable_iff_exists_cert` — for a well-formed non-hierarchical description,
  solvability is the existence of an accepted certificate;
* **`HTN.Article.cor_4_2_9`** — `PlanEx^noHTN_htn ∈ NP`;
* **`HTN.Article.thm_4_3_8_complete`** — together with Thm. 4.3.8: `PlanEx^noHTN_htn` is
  NP-complete.
-/

namespace HTN

namespace Article

namespace NoHTN

open Syn Syn.PolyDom PTime

/-! ### Executing an action sequence of a domain description -/

/-- The precondition, add and delete list of an action of a domain description, as lists. -/
def actLists (d : DomDesc) (a : ℕ) : List ℕ × List ℕ × List ℕ :=
  (d.actions.lookup a).elim ([], [], []) id

/-- One step of the execution check: applicability and the successor state. -/
def execStep (d : DomDesc) (s : Bool × List ℕ) (a : ℕ) : Bool × List ℕ :=
  (s.1 && (actLists d a).1.all (fun f => decide (f ∈ s.2)),
    s.2.filter (fun f => !decide (f ∈ (actLists d a).2.2)) ++ (actLists d a).2.1)

/-- **The execution check**: the sequence is executable from the initial state of `q` and ends in
a goal state. -/
def execB (d : DomDesc) (q : InstDesc) (as : List ℕ) : Bool :=
  let r := as.foldl (execStep d) (true, q.initList)
  r.1 && q.goalList.all fun f => decide (f ∈ r.2)

theorem prec_eq_actLists (d : DomDesc) (a : ℕ) : d.prec a = {f | f ∈ (actLists d a).1} := by
  unfold DomDesc.prec actLists; cases d.actions.lookup a <;> rfl

theorem add_eq_actLists (d : DomDesc) (a : ℕ) : d.add a = {f | f ∈ (actLists d a).2.1} := by
  unfold DomDesc.add actLists; cases d.actions.lookup a <;> rfl

theorem del_eq_actLists (d : DomDesc) (a : ℕ) : d.del a = {f | f ∈ (actLists d a).2.2} := by
  unfold DomDesc.del actLists; cases d.actions.lookup a <;> rfl

theorem execStep_state (d : DomDesc) (q : InstDesc) (b : Bool) (s : List ℕ) (a : ℕ) :
    {f | f ∈ (execStep d (b, s) a).2} = (problem d q).transition a {f | f ∈ s} := by
  ext f
  simp [execStep, ActionModel.transition, problem, Domain.mkProblem, DomDesc.toDomain,
    add_eq_actLists, del_eq_actLists]

theorem execStep_flag (d : DomDesc) (q : InstDesc) (b : Bool) (s : List ℕ) (a : ℕ) :
    (execStep d (b, s) a).1 = true ↔ b = true ∧ (problem d q).Applicable a {f | f ∈ s} := by
  simp [execStep, ActionModel.Applicable, problem, Domain.mkProblem, DomDesc.toDomain,
    prec_eq_actLists, Set.subset_def]

theorem foldl_execStep_state (d : DomDesc) (q : InstDesc) (as : List ℕ) :
    ∀ (b : Bool) (s : List ℕ), {f | f ∈ (as.foldl (execStep d) (b, s)).2} =
      (problem d q).transitionSeq as {f | f ∈ s} := by
  induction as with
  | nil => intro b s; rfl
  | cons a as ih =>
    intro b s
    simp only [List.foldl_cons, ActionModel.transitionSeq_cons]
    rw [ih, execStep_state d q b s a]

theorem foldl_execStep_flag (d : DomDesc) (q : InstDesc) (as : List ℕ) :
    ∀ (b : Bool) (s : List ℕ), (as.foldl (execStep d) (b, s)).1 = true ↔
      b = true ∧ (problem d q).SeqApplicable as {f | f ∈ s} := by
  induction as with
  | nil => intro b s; simp
  | cons a as ih =>
    intro b s
    simp only [List.foldl_cons, ActionModel.seqApplicable_cons]
    rw [ih, execStep_flag d q b s a, ← execStep_state d q b s a]
    tauto

/-- **The execution check is correct.** -/
theorem execB_iff (d : DomDesc) (q : InstDesc) (as : List ℕ) :
    execB d q as = true ↔ (problem d q).SeqApplicable as (problem d q).init ∧
      (problem d q).GoalState ((problem d q).transitionSeq as (problem d q).init) := by
  unfold execB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  rw [foldl_execStep_flag d q as true q.initList]
  simp only [true_and]
  refine and_congr Iff.rfl ?_
  show (∀ f ∈ q.goalList, f ∈ (List.foldl (execStep d) (true, q.initList) as).2) ↔
    {f | f ∈ q.goalList} ⊆ (problem d q).transitionSeq as {f | f ∈ q.initList}
  rw [← foldl_execStep_state d q as true q.initList]
  rfl

/-! ### Labels and linearisations -/

/-- The label of a task id, as `(compound?, name)`: the first listed label. -/
def labelB (t : TnDesc) (i : ℕ) : Bool × ℕ := ((t.lbl.filter fun q => q.1 == i).headI).2

theorem label_eq (t : TnDesc) (i : ℕ) :
    t.label i = if (labelB t i).1 then Sum.inr (labelB t i).2 else Sum.inl (labelB t i).2 := by
  unfold TnDesc.label labelB
  induction t.lbl with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨n, b, c⟩ := q
    by_cases h : n = i
    · subst h; cases b <;> simp [List.lookup]
    · have h' : (i == n) = false := by simpa using Ne.symm h
      simp only [List.lookup, h', List.filter_cons, show (n == i) = false by simpa using h]
      simpa using ih

/-- All tasks of the network are primitive. -/
def noHTNB (t : TnDesc) : Bool := t.ids.all fun i => !(labelB t i).1

/-- **The linearisation check.** -/
def linB (t : TnDesc) (l : List ℕ) : Bool :=
  nodupB l && permB l t.ids &&
    (List.range l.length).all fun i => (List.range l.length).all fun j =>
      !(decide (i < j)) || !(decide ((l.getI j, l.getI i) ∈ t.ordList))

theorem noHTNB_iff (t : TnDesc) : noHTNB t = true ↔ t.toTaskNetwork.IsPrimitive := by
  simp only [noHTNB, List.all_eq_true, Bool.not_eq_true', TaskNetwork.IsPrimitive,
    TaskNetwork.IsPrimitiveId, TnDesc.toTaskNetwork_T, List.mem_toFinset, TnDesc.toTaskNetwork_α,
    label_eq]
  refine forall_congr' fun i => imp_congr Iff.rfl ?_
  cases (labelB t i).1 <;> simp

theorem linB_iff {prim : ℕ → Prop} {t : TnDesc} (hv : TnValid prim t) (l : List ℕ) :
    linB t l = true ↔ t.toTaskNetwork.IsLinearization l := by
  simp only [linB, Bool.and_eq_true, nodupB_iff, permB_iff, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  constructor
  · rintro ⟨⟨hnd, hp⟩, hord⟩
    refine ⟨hnd, fun x => by rw [hp.mem_iff]; simp, ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij hc
    replace hc : (l[j], l[i]) ∈ t.ordList := hv.ordOf_iff.1 hc
    rcases hord i hi j hj with h | h
    · omega
    · rw [List.getI_eq_getElem _ hj, List.getI_eq_getElem _ hi] at h; exact h hc
  · rintro ⟨hnd, hmem, hpw⟩
    refine ⟨⟨hnd, (List.perm_ext_iff_of_nodup hnd hv.nodup).2 fun x => by
      rw [hmem x]; simp⟩, fun i hi j hj => ?_⟩
    by_cases hij : i < j
    · right
      rw [List.getI_eq_getElem _ hj, List.getI_eq_getElem _ hi]
      intro hc
      exact List.pairwise_iff_getElem.1 hpw i j hi hj hij
        ((TnDesc.toTaskNetwork_ord _ _ _).2 (hv.ordOf_iff.2 hc))
    · left; omega

/-! ### Decomposition from a primitive network -/

theorem decomposesTo_primitive {M : Set (Method ℕ ℕ ℕ)} {tn tn' : TaskNetwork ℕ ℕ ℕ}
    (h : HTN.DecomposesTo M tn tn') (hp : tn.IsPrimitive) : tn' = tn := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨t, m, -, ht, hlab, -⟩ := hs
    obtain ⟨a, ha⟩ := hp t ht
    rw [ha] at hlab
    exact absurd hlab (by simp)

/-! ### The certificate check -/

/-- The action sequence of a linearisation. -/
def actsOf (t : TnDesc) (l : List ℕ) : List ℕ := l.map fun i => (labelB t i).2

/-- **The certificate check** for non-hierarchical problems. -/
def certB (x : ProbDesc × List ℕ) : Bool :=
  validB x.1 && noHTNB x.1.tnI && linB x.1.tnI x.2 &&
    execB (toSynDom x.1) (toSynInst x.1) (actsOf x.1.tnI x.2)

/-- **Solvability of a well-formed non-hierarchical description is the existence of an accepted
certificate.** -/
theorem iff_exists_cert (p : ProbDesc) :
    (p.Valid ∧ p.toProblem.IsNoHTN ∧ p.toProblem.Solvable) ↔ ∃ l, certB (p, l) = true := by
  have htn : (problem (toSynDom p) (toSynInst p)).tnI = p.tnI.toTaskNetwork := rfl
  simp only [certB, Bool.and_eq_true, validB_iff, noHTNB_iff]
  constructor
  · rintro ⟨hv, hnh, hs⟩
    have hprim : p.tnI.toTaskNetwork.IsPrimitive := hnh
    rw [solvable_toSyn_iff] at hs
    obtain ⟨tn, hr, -, l, as, hl, has, happ, hgoal⟩ := hs
    obtain rfl := decomposesTo_primitive hr (by rw [htn]; exact hprim)
    rw [htn] at hl has
    refine ⟨l, ⟨⟨⟨hv, hprim⟩, (linB_iff hv.tnI l).2 hl⟩, (execB_iff _ _ _).2 ?_⟩⟩
    have hacts : actsOf p.tnI l = as := by
      have hmap : l.map (fun i => p.tnI.label i) = as.map Sum.inl := has
      apply List.map_injective_iff.2 Sum.inl_injective
      rw [← hmap, actsOf, List.map_map]
      refine List.map_congr_left fun i hi => ?_
      obtain ⟨a, ha⟩ := hprim i ((hl.2.1 i).1 hi)
      replace ha : p.tnI.label i = Sum.inl a := ha
      simp only [Function.comp_apply]
      rw [ha]
      rw [label_eq] at ha
      split_ifs at ha with hb <;> simp_all
    rw [hacts]; exact ⟨happ, hgoal⟩
  · rintro ⟨l, ⟨⟨⟨hv, hprim⟩, hlin⟩, hex⟩⟩
    refine ⟨hv, hprim, ?_⟩
    rw [solvable_toSyn_iff]
    have hl := (linB_iff hv.tnI l).1 hlin
    obtain ⟨happ, hgoal⟩ := (execB_iff _ _ _).1 hex
    refine ⟨_, Relation.ReflTransGen.refl, by rw [htn]; exact hprim, l, actsOf p.tnI l,
      by rw [htn]; exact hl, ?_, happ, hgoal⟩
    rw [htn]
    show l.map p.tnI.label = (actsOf p.tnI l).map Sum.inl
    rw [actsOf, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨a, ha⟩ := hprim i ((hl.2.1 i).1 hi)
    show p.tnI.label i = Sum.inl (labelB p.tnI i).2
    replace ha : p.tnI.label i = Sum.inl a := ha
    rw [ha]
    rw [label_eq] at ha
    split_ifs at ha with hb <;> simp_all

/-! ### Polynomial time -/

theorem sz_filter_le {β : Type} [BEnc β] (l : List β) (q : β → Bool) : sz (l.filter q) ≤ sz l := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : q a <;> simp [List.filter_cons, h, sz_cons] <;> omega

theorem sz_append_le {β : Type} [BEnc β] (l l' : List β) : sz (l ++ l') ≤ sz l + sz l' := by
  induction l with
  | nil => simp [sz_nil]
  | cons a l ih => simp only [List.cons_append, sz_cons]; omega

theorem sz_fst_le {β γ : Type} [BEnc β] [BEnc γ] (x : β × γ) : sz x.1 ≤ sz x := by
  rw [show sz x = sz x.1 + sz x.2 from sz_prod _ _]; omega

theorem sz_snd_le {β γ : Type} [BEnc β] [BEnc γ] (x : β × γ) : sz x.2 ≤ sz x := by
  rw [show sz x = sz x.1 + sz x.2 from sz_prod _ _]; omega

theorem sz_headI_le {β : Type} [BEnc β] [Inhabited β] (l : List β) :
    sz l.headI ≤ sz l + sz (default : β) := by
  cases l with
  | nil => simp
  | cons a l => simp only [List.headI_cons, sz_cons]; omega

theorem actLists_eq (d : DomDesc) (a : ℕ) :
    actLists d a = ((d.actions.filter fun x => x.1 == a).headI).2 := by
  unfold actLists
  induction d.actions with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x.1 = a
    · have h' : (a == x.1) = true := by simp [h]
      simp [List.lookup, h, h']
    · have h' : (a == x.1) = false := by simpa using Ne.symm h
      simp only [List.lookup, h', List.filter_cons, show (x.1 == a) = false by simpa using h]
      simpa using ih

theorem pt_actLists : PT fun x : DomDesc × ℕ => actLists x.1 x.2 := by
  refine (PT.snd.comp (PT.headI (PT.filter (p := fun (x : DomDesc × ℕ) (y : ActionDesc) =>
    y.1 == x.2) (PT.fst.comp PT.fst) (PT.beq (PT.fst.comp PT.snd) (PT.snd.comp PT.fst))))).of_eq
    fun x => (actLists_eq x.1 x.2).symm

theorem sz_actLists_le (d : DomDesc) (a : ℕ) : sz (actLists d a) ≤ sz d + sz (default : ActionDesc) := by
  rw [actLists_eq]
  have h1 := sz_headI_le (d.actions.filter fun x => x.1 == a)
  have h2 := sz_filter_le d.actions (fun x => x.1 == a)
  have h3 : sz d.actions ≤ sz d := sz_fst_le d
  have h4 := sz_snd_le (d.actions.filter fun x => x.1 == a).headI
  omega

theorem pt_execStep : PT fun x : (DomDesc × InstDesc × List ℕ) × (Bool × List ℕ) × ℕ =>
    execStep x.1.1 x.2.1 x.2.2 := by
  unfold execStep
  have hL : PT fun x : (DomDesc × InstDesc × List ℕ) × (Bool × List ℕ) × ℕ =>
      actLists x.1.1 x.2.2 := pt_actLists.comp (PT.pair (PT.fst.comp PT.fst) (PT.snd.comp PT.snd))
  have hs : PT fun x : (DomDesc × InstDesc × List ℕ) × (Bool × List ℕ) × ℕ => x.2.1.2 :=
    PT.snd.comp (PT.fst.comp PT.snd)
  refine PT.pair (PT.and (PT.fst.comp (PT.fst.comp PT.snd)) (PT.all (PT.fst.comp hL)
    (PT.elem (hs.comp PT.fst) PT.snd))) (PT.append ?_ (PT.fst.comp (PT.snd.comp hL)))
  exact PT.filter hs (PT.not (PT.elem (PT.snd.comp (PT.snd.comp (hL.comp PT.fst))) PT.snd))

theorem sz_execStep_le (d : DomDesc) (s : Bool × List ℕ) (a : ℕ) :
    sz (execStep d s a) ≤ sz s + sz d + sz (default : ActionDesc) := by
  have h1 := sz_actLists_le d a
  have h2 : sz (actLists d a).2.1 ≤ sz (actLists d a) :=
    (sz_fst_le (actLists d a).2).trans (sz_snd_le _)
  unfold execStep
  rw [sz_prod, sz_prod]
  have h3 := sz_filter_le s.2 (fun f => !decide (f ∈ (actLists d a).2.2))
  have h4 := sz_append_le (s.2.filter fun f => !decide (f ∈ (actLists d a).2.2)) (actLists d a).2.1
  have h5 : sz (s.1 && (actLists d a).1.all fun f => decide (f ∈ s.2)) = sz s.1 := rfl
  omega

theorem pt_execB : PT fun x : DomDesc × InstDesc × List ℕ => execB x.1 x.2.1 x.2.2 := by
  unfold execB
  have hf : PT fun x : DomDesc × InstDesc × List ℕ =>
      x.2.2.foldl (execStep x.1) (true, x.2.1.initList) :=
    PT.foldl (α := DomDesc × InstDesc × List ℕ) (β := ℕ) (σ := Bool × List ℕ)
      (g := fun x s a => execStep x.1 s a) (PT.snd.comp PT.snd)
      (PT.pair (PT.const true) (PT.fst.comp (PT.fst.comp PT.snd))) pt_execStep (c := 1)
      (d := 1 + sz (default : ActionDesc)) fun x s a _ => by
        have h := sz_execStep_le x.1 s a
        have : sz x.1 ≤ sz x := sz_fst_le x
        nlinarith
  exact PT.and (PT.fst.comp hf) (PT.all (PT.fst.comp (PT.snd.comp (PT.fst.comp PT.snd)))
    (PT.elem (PT.snd.comp (hf.comp PT.fst)) PT.snd))

theorem pt_map_posF {α : Type} [BEnc α] {f : α → List ℕ} (hf : PT f) :
    PT fun a => (f a).map posF :=
  PT.map hf ((PT.affine 2 0 PT.snd).of_eq fun _ => by simp [posF])

theorem pt_map_negF {α : Type} [BEnc α] {f : α → List ℕ} (hf : PT f) :
    PT fun a => (f a).map negF :=
  PT.map hf ((PT.affine 2 1 PT.snd).of_eq fun _ => by simp [negF])

theorem pt_filter_notMem {α : Type} [BEnc α] {f g : α → List ℕ} (hf : PT f) (hg : PT g) :
    PT fun a => (f a).filter fun x => x ∉ g a :=
  PT.filter (p := fun a x => decide (x ∉ g a)) hf
    ((PT.not (PT.elem (hg.comp PT.fst) PT.snd)).of_eq fun _ => by simp)

theorem pt_actToSyn : PT actToSyn := by
  unfold actToSyn delOnly
  have hpp : PT fun a : ActDesc => a.2.1 := PT.fst.comp PT.snd
  have hpn : PT fun a : ActDesc => a.2.2.1 := PT.fst.comp (PT.snd.comp PT.snd)
  have had : PT fun a : ActDesc => a.2.2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hde : PT fun a : ActDesc => a.2.2.2.2 := PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hdo := pt_filter_notMem hde had
  exact PT.pair PT.fst (PT.pair (PT.append (pt_map_posF hpp) (pt_map_negF hpn))
    (PT.pair (PT.append (pt_map_posF had) (pt_map_negF hdo))
      (PT.append (pt_map_negF had) (pt_map_posF hdo))))

theorem pt_toSynDom : PT toSynDom :=
  PT.pair (PT.map (PT.fst.comp PT.fst) (pt_actToSyn.comp PT.snd)) (PT.snd.comp PT.fst)

theorem pt_facts : PT ProbDesc.facts := by
  unfold ProbDesc.facts ProbDesc.init ProbDesc.goalPos ProbDesc.goalNeg ProbDesc.actions
  have hi : PT fun p : ProbDesc => p.2.1 := PT.fst.comp PT.snd
  have hgp : PT fun p : ProbDesc => p.2.2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hgn : PT fun p : ProbDesc => p.2.2.2.2 := PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hact : PT fun x : ProbDesc × ActDesc => x.2.2.1 ++ x.2.2.2.1 ++ x.2.2.2.2.1 ++ x.2.2.2.2.2 :=
    PT.append (PT.append (PT.append (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))))
      (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))
      (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))))
  exact PT.append (PT.append (PT.append hi hgp) hgn) (PT.flatMap (PT.fst.comp PT.fst) hact)

theorem pt_toSynInst : PT toSynInst := by
  unfold toSynInst
  have hi : PT fun p : ProbDesc => p.init := PT.fst.comp PT.snd
  have hgp : PT fun p : ProbDesc => p.goalPos := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hgn : PT fun p : ProbDesc => p.goalNeg := PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have htn : PT fun p : ProbDesc => p.tnI := PT.fst.comp (PT.snd.comp PT.snd)
  exact PT.pair (PT.append (pt_map_posF hi) (pt_map_negF (pt_filter_notMem pt_facts hi)))
    (PT.pair (PT.append (pt_map_posF hgp) (pt_map_negF hgn)) htn)

theorem pt_labelB : PT fun x : TnDesc × ℕ => labelB x.1 x.2 := by
  unfold labelB
  exact PT.snd.comp (PT.headI (PT.filter (p := fun (x : TnDesc × ℕ) (q : ℕ × Bool × ℕ) =>
    q.1 == x.2) (PT.snd.comp (PT.snd.comp PT.fst)) (PT.beq (PT.fst.comp PT.snd)
      (PT.snd.comp PT.fst))))

theorem pt_noHTNB : PT noHTNB := by
  unfold noHTNB
  exact PT.all PT.fst (PT.not (PT.fst.comp pt_labelB))

theorem pt_linB : PT fun x : TnDesc × List ℕ => linB x.1 x.2 := by
  unfold linB
  have hl : PT fun x : TnDesc × List ℕ => x.2 := PT.snd
  refine PT.and (PT.and (pt_nodupB hl) (pt_permB hl (PT.fst.comp PT.fst))) ?_
  refine PT.all (PT.rangeLength hl) (PT.all (PT.rangeLength (hl.comp PT.fst)) ?_)
  have hl2 : PT fun y : ((TnDesc × List ℕ) × ℕ) × ℕ => y.1.1.2 := PT.snd.comp (PT.fst.comp PT.fst)
  have hi : PT fun y : ((TnDesc × List ℕ) × ℕ) × ℕ => y.1.2 := PT.snd.comp PT.fst
  have hj : PT fun y : ((TnDesc × List ℕ) × ℕ) × ℕ => y.2 := PT.snd
  exact PT.or (PT.not (PT.lt hi hj)) (PT.not ((PT.elem
    (PT.fst.comp (PT.snd.comp (PT.fst.comp (PT.fst.comp PT.fst))))
    (PT.pair (PT.getI hl2 hj) (PT.getI hl2 hi))).of_eq fun _ => by congr))

theorem pt_certB : PT certB := by
  unfold certB actsOf
  have hp : PT fun x : ProbDesc × List ℕ => x.1 := PT.fst
  have htn : PT fun x : ProbDesc × List ℕ => x.1.tnI := PT.fst.comp (PT.snd.comp (PT.snd.comp hp))
  refine PT.and (PT.and (PT.and (pt_validB.comp hp) (pt_noHTNB.comp htn))
    (pt_linB.comp (PT.pair htn PT.snd))) ?_
  exact pt_execB.comp (PT.pair (pt_toSynDom.comp hp) (PT.pair (pt_toSynInst.comp hp)
    (PT.map (g := fun (x : ProbDesc × List ℕ) (i : ℕ) => (labelB x.1.tnI i).2) PT.snd
      (PT.snd.comp (pt_labelB.comp (PT.pair (htn.comp PT.fst) PT.snd))))))

/-! ### The size of a certificate -/

theorem sz_perm {l l' : List ℕ} (h : l.Perm l') : sz l = sz l' := by
  induction h with
  | nil => rfl
  | cons a _ ih => rw [sz_cons, sz_cons, ih]
  | swap a b l => rw [sz_cons, sz_cons, sz_cons, sz_cons]; ring
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem sz_ids_le (p : ProbDesc) : sz p.tnI.ids ≤ sz p :=
  (sz_fst_le p.tnI).trans ((sz_fst_le p.2.2).trans ((sz_snd_le p.2).trans (sz_snd_le p)))

end NoHTN

open NoHTN Syn.PolyDom

/-- **Corollary 4.2.9.** `PlanEx^noHTN_htn ∈ NP`. -/
theorem cor_4_2_9 : Cx.NP (PlanEx fun P => P.IsNoHTN) := by
  have h := Syn.PolyDom.inNP_codeLang (α := ProbDesc) (β := List ℕ)
    (Q := fun p => p.Valid ∧ p.toProblem.IsNoHTN ∧ p.toProblem.Solvable) pt_certB 1 fun p => by
      show _ ↔ _
      simp only []
      rw [iff_exists_cert]
      constructor
      · rintro ⟨l, hl⟩
        refine ⟨l, ?_, hl⟩
        simp only [certB, Bool.and_eq_true] at hl
        have hv := (validB_iff p).1 hl.1.1.1
        have hperm := ((linB_iff hv.tnI l).1 hl.1.2)
        have : l.Perm p.tnI.ids := (List.perm_ext_iff_of_nodup hperm.1 hv.tnI.nodup).2
          fun x => (hperm.2.1 x).trans (by simp)
        have h1 : (enc l).length = sz l := rfl
        have h2 : (enc p).length = sz p := rfl
        rw [h1, h2, pow_one, sz_perm this]
        have := sz_ids_le p
        omega
      · rintro ⟨l, -, hl⟩; exact ⟨l, hl⟩
  exact h

/-- **Corollary 4.2.9 with Thm. 4.3.8**: `PlanEx^noHTN_htn` is NP-complete. -/
theorem noHTN_npComplete : Cx.Complete Cx.NP (PlanEx fun P => P.IsNoHTN) :=
  ⟨cor_4_2_9, thm_4_3_8⟩



end Article

end HTN
