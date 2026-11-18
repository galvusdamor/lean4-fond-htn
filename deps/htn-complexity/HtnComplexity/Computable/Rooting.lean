import HtnPlanning.Computable.Bodies
import HtnComplexity.Computable.Rooted
/-!
# Rooting a totally ordered instance description

A *rooted* instance description (`HTN.Syn.InstDesc.IsRooted`) is one whose initial task network
is a single compound task.  Several of the compilations of the computable table are available
only for a rooted source instance, because the translation of the domain may not depend on the
instance, and a `STRIPS` instance description carries no task network.

For a **decision procedure** that restriction is irrelevant: a decider reads the domain
description *and* the instance description, so it may move the initial task network of the
instance into the domain.  This file does that:

* `HTN.Syn.rootDom d q` is `d` with one further method added, which decomposes a fresh compound
  name `HTN.Syn.freshRoot d q` into the initial task network of `q`;
* `HTN.Syn.rootInst d q` is `q` with the initial task network replaced by the single compound
  task `freshRoot d q`.

The translation is primitive recursive, it preserves the classes `TO-HTN`, `TO-HTN-AC` and
`TO-HTN-TR` (the fresh name gets a rank above all others, so *every* subtask of the new method
strictly decreases the rank), it produces a rooted instance, and it preserves and reflects
solvability (`HTN.Syn.solvable_root_iff`).  Consequently the deciders for the rooted classes of
`Computable/Deciders.lean` extend to the unrestricted classes `TO-HTN-AC` and `TO-HTN-TR`.

The proof of `solvable_root_iff` is the context-free reading of totally ordered HTN planning
(`HTN.Problem.solvable_iff_yieldSeq`): the refinements of the single fresh task are exactly the
refinements of the initial task sequence, because the fresh name occurs in no body of `d`.
-/

namespace HTN

namespace Syn

/-! ### The fresh compound name -/

/-- Every compound name a domain description mentions: the names its methods decompose, and the
compound names occurring in their subtask networks. -/
def DomDesc.compNames (d : DomDesc) : List ℕ :=
  d.methods.flatMap fun e => e.1 :: e.2.compoundNames

/-- A compound name that neither the domain description nor the initial task network of the
instance description mentions. -/
def freshRoot (d : DomDesc) (q : InstDesc) : ℕ :=
  (d.compNames ++ q.tnI.compoundNames).foldr (fun x m => x + 1 + m) 0

/-- Every member of a list is below the sum of the successors of its members. -/
theorem lt_foldr_succ_sum {l : List ℕ} {c : ℕ} (h : c ∈ l) :
    c < l.foldr (fun x m => x + 1 + m) 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | hx
    · omega
    · have := ih hx
      omega

/-- The values a function takes on a list are bounded by the fold of the maxima. -/
theorem le_foldr_max_map {l : List ℕ} {rk : ℕ → ℕ} {c : ℕ} (h : c ∈ l) :
    rk c ≤ (l.map rk).foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

theorem lt_freshRoot {d : DomDesc} {q : InstDesc} {c : ℕ}
    (h : c ∈ d.compNames ++ q.tnI.compoundNames) : c < freshRoot d q :=
  lt_foldr_succ_sum h

theorem ne_freshRoot {d : DomDesc} {q : InstDesc} {c : ℕ}
    (h : c ∈ d.compNames ++ q.tnI.compoundNames) : c ≠ freshRoot d q :=
  Nat.ne_of_lt (lt_freshRoot h)

/-- The name a method decomposes is mentioned by the description. -/
theorem mem_compNames_of_mem_methods {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) :
    e.1 ∈ d.compNames :=
  List.mem_flatMap.2 ⟨e, he, List.mem_cons_self⟩

/-- A compound name occurring in the subtask network of a listed method is mentioned. -/
theorem mem_compNames_of_mem_compoundNames {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods)
    {c : ℕ} (hc : c ∈ e.2.compoundNames) : c ∈ d.compNames :=
  List.mem_flatMap.2 ⟨e, he, List.mem_cons_of_mem _ hc⟩

/-! ### The construction -/

/-- The domain description `d`, extended by a method that decomposes the fresh compound name
into the initial task network of `q`. -/
def rootDom (d : DomDesc) (q : InstDesc) : DomDesc :=
  (d.actions, d.methods ++ [(freshRoot d q, q.tnI)])

/-- The instance description `q`, with the single fresh compound task as initial network. -/
def rootInst (d : DomDesc) (q : InstDesc) : InstDesc :=
  (q.initList, q.goalList, ([0], [], [(0, true, freshRoot d q)]))

variable {d : DomDesc} {q : InstDesc}

@[simp] theorem rootDom_actions : (rootDom d q).actions = d.actions := rfl

@[simp] theorem rootDom_methods :
    (rootDom d q).methods = d.methods ++ [(freshRoot d q, q.tnI)] := rfl

@[simp] theorem rootDom_prec : (rootDom d q).prec = d.prec := rfl

@[simp] theorem rootDom_add : (rootDom d q).add = d.add := rfl

@[simp] theorem rootDom_del : (rootDom d q).del = d.del := rfl

@[simp] theorem rootInst_initList : (rootInst d q).initList = q.initList := rfl

@[simp] theorem rootInst_goalList : (rootInst d q).goalList = q.goalList := rfl

theorem rootInst_tnI_T : (rootInst d q).tnI.toTaskNetwork.T = {0} := by
  simp [rootInst, InstDesc.tnI, TnDesc.toTaskNetwork, TnDesc.ids]

theorem rootInst_tnI_α : (rootInst d q).tnI.toTaskNetwork.α 0 = Sum.inr (freshRoot d q) := by
  simp [rootInst, InstDesc.tnI, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl]

theorem rootInst_isRooted : (rootInst d q).IsRooted :=
  ⟨0, freshRoot d q, rootInst_tnI_T, rootInst_tnI_α⟩

theorem rootInst_isTO : (rootInst d q).IsTO := rootInst_isRooted.isTO

/-! ### The classes are preserved -/

theorem rootDom_methodsTO (hd : d.MethodsTO) (hq : q.IsTO) : (rootDom d q).MethodsTO := by
  intro e he
  rw [rootDom_methods, List.mem_append] at he
  rcases he with he | he
  · exact hd e he
  · rw [List.mem_singleton.1 he]
    exact hq

theorem rootDom_isAcyclic (hd : d.IsAcyclic) : (rootDom d q).IsAcyclic := by
  obtain ⟨rk, hrk⟩ := hd
  classical
  set M : ℕ := (q.tnI.compoundNames.map rk).foldr max 0 with hM
  have hMle : ∀ c ∈ q.tnI.compoundNames, rk c ≤ M := fun _ hc => le_foldr_max_map hc
  refine ⟨fun c => if c = freshRoot d q then M + 1 else rk c, ?_⟩
  intro e he t ht c hc
  rw [rootDom_methods, List.mem_append] at he
  rcases he with he | he
  · have hhead : e.1 ≠ freshRoot d q :=
      ne_freshRoot (List.mem_append_left _ (mem_compNames_of_mem_methods he))
    have hsub : c ≠ freshRoot d q := by
      refine ne_freshRoot (List.mem_append_left _
        (mem_compNames_of_mem_compoundNames he ?_))
      exact TnDesc.mem_compoundNames.2 ⟨t, List.mem_toFinset.1 ht, hc⟩
    simp only [if_neg hhead, if_neg hsub]
    exact hrk e he t ht c hc
  · rw [List.mem_singleton.1 he] at ht hc ⊢
    have hmem : c ∈ q.tnI.compoundNames :=
      TnDesc.mem_compoundNames.2 ⟨t, List.mem_toFinset.1 ht, hc⟩
    have hsub : c ≠ freshRoot d q := ne_freshRoot (List.mem_append_right _ hmem)
    simp only [if_neg hsub, if_pos]
    exact Nat.lt_succ_of_le (hMle c hmem)

theorem rootDom_isTailRec (hd : d.IsTailRec) : (rootDom d q).IsTailRec := by
  obtain ⟨rk, hrk⟩ := hd
  classical
  set M : ℕ := (q.tnI.compoundNames.map rk).foldr max 0 with hM
  have hMle : ∀ c ∈ q.tnI.compoundNames, rk c ≤ M := fun _ hc => le_foldr_max_map hc
  refine ⟨fun c => if c = freshRoot d q then M + 1 else rk c, ?_⟩
  intro e he t ht c hc
  rw [rootDom_methods, List.mem_append] at he
  rcases he with he | he
  · have hhead : e.1 ≠ freshRoot d q :=
      ne_freshRoot (List.mem_append_left _ (mem_compNames_of_mem_methods he))
    have hsub : c ≠ freshRoot d q := by
      refine ne_freshRoot (List.mem_append_left _
        (mem_compNames_of_mem_compoundNames he ?_))
      exact TnDesc.mem_compoundNames.2 ⟨t, List.mem_toFinset.1 ht, hc⟩
    simp only [if_neg hhead, if_neg hsub]
    exact hrk e he t ht c hc
  · rw [List.mem_singleton.1 he] at ht hc ⊢
    have hmem : c ∈ q.tnI.compoundNames :=
      TnDesc.mem_compoundNames.2 ⟨t, List.mem_toFinset.1 ht, hc⟩
    have hsub : c ≠ freshRoot d q := ne_freshRoot (List.mem_append_right _ hmem)
    simp only [if_neg hsub, if_pos]
    exact ⟨fun _ => Nat.le_succ_of_le (hMle c hmem), fun _ => Nat.lt_succ_of_le (hMle c hmem)⟩

/-! ### The bodies of the extended description -/

/-- The compound names of a body of a totally ordered described network are among the compound
names of the description of that network. -/
theorem mem_compoundNames_of_mem_seqBody {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered)
    {c : ℕ} (hc : Sum.inr c ∈ TnDesc.seqBody t) : c ∈ t.compoundNames := by
  rw [TnDesc.seqBody, List.mem_map] at hc
  obtain ⟨i, hi, hlab⟩ := hc
  exact TnDesc.mem_compoundNames.2 ⟨i, (TnDesc.mem_lin hTO).1 hi, hlab⟩

/-- A body of `d` mentions no fresh name. -/
theorem ne_freshRoot_of_seqBody (hTO : d.MethodsTO) {c' : ℕ} {bs : List (ℕ ⊕ ℕ)}
    (h : d.toDomain.SeqBody c' bs) {c : ℕ} (hc : Sum.inr c ∈ bs) : c ≠ freshRoot d q := by
  obtain ⟨m, hm, -, rfl⟩ := (DomDesc.seqBody_iff hTO).1 h
  refine ne_freshRoot (List.mem_append_left _ (mem_compNames_of_mem_compoundNames
    (getI_mem_methods hm) ?_))
  exact mem_compoundNames_of_mem_seqBody (hTO _ (getI_mem_methods hm)) hc

/-- The name a body of `d` decomposes is not fresh. -/
theorem ne_freshRoot_of_seqBody_head (hTO : d.MethodsTO) {c : ℕ} {bs : List (ℕ ⊕ ℕ)}
    (h : d.toDomain.SeqBody c bs) : c ≠ freshRoot d q := by
  obtain ⟨m, hm, rfl, -⟩ := (DomDesc.seqBody_iff hTO).1 h
  exact ne_freshRoot (List.mem_append_left _ (mem_compNames_of_mem_methods (getI_mem_methods hm)))

/-- Every body of `d` is a body of the extended description. -/
theorem seqBody_rootDom_of {c : ℕ} {bs : List (ℕ ⊕ ℕ)} (h : d.toDomain.SeqBody c bs) :
    (rootDom d q).toDomain.SeqBody c bs := by
  obtain ⟨m, hm, hc, hbody⟩ := h
  obtain ⟨e, he, rfl⟩ := hm
  exact ⟨e.toMethod, ⟨e, by rw [rootDom_methods]; exact List.mem_append_left _ he, rfl⟩, hc, hbody⟩

/-- The fresh name decomposes into the initial task sequence of `q`. -/
theorem seqBody_rootDom_fresh (hq : q.IsTO) :
    (rootDom d q).toDomain.SeqBody (freshRoot d q) (TnDesc.seqBody q.tnI) := by
  have hmem : ((freshRoot d q, q.tnI) : MethodDesc) ∈ (rootDom d q).methods := by
    rw [rootDom_methods]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  exact ⟨MethodDesc.toMethod (freshRoot d q, q.tnI), ⟨_, hmem, rfl⟩, rfl,
    Method.hasSeqBody_of_isSeqNet (TnDesc.isSeqNet_lin hq)⟩

/-- **The bodies of the extended description**: those of `d`, and the initial task sequence for
the fresh name. -/
theorem seqBody_rootDom_iff (hTO : d.MethodsTO) (hq : q.IsTO) {c : ℕ} {bs : List (ℕ ⊕ ℕ)} :
    (rootDom d q).toDomain.SeqBody c bs ↔
      d.toDomain.SeqBody c bs ∨ (c = freshRoot d q ∧ bs = TnDesc.seqBody q.tnI) := by
  constructor
  · intro h
    obtain ⟨m, hm, hhd, hbd⟩ := (DomDesc.seqBody_iff (rootDom_methodsTO hTO hq)).1 h
    rw [rootDom_methods, List.length_append, List.length_singleton] at hm
    rcases Nat.lt_or_ge m d.methods.length with hlt | hge
    · have hget : (rootDom d q).methods.getI m = d.methods.getI m := by
        rw [rootDom_methods, List.getI_eq_getElem (l := d.methods ++ _) (by simp; omega),
          List.getI_eq_getElem (l := d.methods) hlt, List.getElem_append_left hlt]
      refine Or.inl ((DomDesc.seqBody_iff hTO).2 ⟨m, hlt, ?_, ?_⟩)
      · rw [DomDesc.hd, ← hget]; exact hhd
      · rw [DomDesc.bd, ← hget]; exact hbd
    · have hmeq : m = d.methods.length := by omega
      subst hmeq
      have hget : (rootDom d q).methods.getI d.methods.length = (freshRoot d q, q.tnI) := by
        rw [rootDom_methods, List.getI_eq_getElem (l := d.methods ++ _) (by simp),
          List.getElem_append_right (by omega)]
        simp
      refine Or.inr ⟨?_, ?_⟩
      · rw [← hhd, DomDesc.hd, hget]
      · rw [← hbd, DomDesc.bd, hget]
  · rintro (h | ⟨rfl, rfl⟩)
    · exact seqBody_rootDom_of h
    · exact seqBody_rootDom_fresh hq

/-! ### Refinements -/

open Domain in
/-- Every refinement of `d` is a refinement of the extended description. -/
theorem yieldSeq_rootDom_of {xs : List (ℕ ⊕ ℕ)} {as : List ℕ}
    (h : d.toDomain.YieldSeq xs as) : (rootDom d q).toDomain.YieldSeq xs as := by
  induction h with
  | nil => exact Domain.YieldSeq.nil
  | prim _ ih => exact Domain.YieldSeq.prim ih
  | comp hm _ ih => exact Domain.YieldSeq.comp (seqBody_rootDom_of hm) ih

/-- Conversely, a refinement of the extended description that starts from a task sequence
without the fresh name is a refinement of `d`. -/
theorem yieldSeq_of_rootDom (hTO : d.MethodsTO) (hq : q.IsTO) {xs : List (ℕ ⊕ ℕ)} {as : List ℕ}
    (h : (rootDom d q).toDomain.YieldSeq xs as)
    (hx : ∀ c, Sum.inr c ∈ xs → c ≠ freshRoot d q) : d.toDomain.YieldSeq xs as := by
  induction h with
  | nil => exact Domain.YieldSeq.nil
  | @prim a xs as _ ih =>
    exact Domain.YieldSeq.prim (ih fun c hc => hx c (List.mem_cons_of_mem _ hc))
  | @comp c bs xs as hm _ ih =>
    have hcne : c ≠ freshRoot d q := hx c List.mem_cons_self
    rcases (seqBody_rootDom_iff hTO hq).1 hm with hsrc | ⟨rfl, -⟩
    · refine Domain.YieldSeq.comp hsrc (ih fun c' hc' => ?_)
      rcases List.mem_append.1 hc' with hb | ht
      · exact ne_freshRoot_of_seqBody hTO hsrc hb
      · exact hx c' (List.mem_cons_of_mem _ ht)
    · exact absurd rfl hcne

/-! ### Solvability -/

/-- **Rooting preserves and reflects solvability.** -/
theorem solvable_root_iff (hTO : d.MethodsTO) (hq : q.IsTO) :
    Solvable (rootDom d q) (rootInst d q) ↔ Solvable d q := by
  have hseq : (problem d q).tnI.IsSeqNet (TnDesc.lin q.tnI) (TnDesc.seqBody q.tnI) :=
    TnDesc.isSeqNet_lin hq
  have hseq' : (problem (rootDom d q) (rootInst d q)).tnI.IsSeqNet [0]
      [Sum.inr (freshRoot d q)] := by
    have h := TaskNetwork.isSeqNet_singleton
      (problem_wf (rootDom d q) (rootInst d q)).tnI
      (show (problem (rootDom d q) (rootInst d q)).tnI.T = {0} from rootInst_tnI_T)
    have hα : (problem (rootDom d q) (rootInst d q)).tnI.α 0 = Sum.inr (freshRoot d q) :=
      rootInst_tnI_α
    rwa [hα] at h
  have hTOm : (problem d q).IsTO_M := (isTO_problem hTO hq).2
  have hTOm' : (problem (rootDom d q) (rootInst d q)).IsTO_M :=
    (isTO_problem (rootDom_methodsTO hTO hq) rootInst_isTO).2
  have hsrc : Solvable d q ↔ ∃ as : List ℕ,
      d.toDomain.YieldSeq (TnDesc.seqBody q.tnI) as ∧
      d.toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList} :=
    Problem.solvable_iff_yieldSeq (problem_wf d q) hTOm hseq
  have htgt : Solvable (rootDom d q) (rootInst d q) ↔ ∃ as : List ℕ,
      (rootDom d q).toDomain.YieldSeq [Sum.inr (freshRoot d q)] as ∧
      (rootDom d q).toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ (rootDom d q).toDomain.transitionSeq as {f | f ∈ q.initList} :=
    Problem.solvable_iff_yieldSeq (problem_wf (rootDom d q) (rootInst d q)) hTOm' hseq'
  have hmodel : (rootDom d q).toDomain.toActionModel = d.toDomain.toActionModel := rfl
  rw [hsrc, htgt]
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    refine ⟨as, ?_, happ, hgoal⟩
    cases hy with
    | comp hm hrest =>
      rcases (seqBody_rootDom_iff hTO hq).1 hm with hsrcb | ⟨-, rfl⟩
      · exact absurd rfl (ne_freshRoot_of_seqBody_head hTO hsrcb)
      · rw [List.append_nil] at hrest
        refine yieldSeq_of_rootDom hTO hq hrest fun c hc => ?_
        exact ne_freshRoot (List.mem_append_right _
          (mem_compoundNames_of_mem_seqBody hq hc))
  · rintro ⟨as, hy, happ, hgoal⟩
    refine ⟨as, ?_, happ, hgoal⟩
    refine Domain.YieldSeq.comp (seqBody_rootDom_fresh hq) ?_
    rw [List.append_nil]
    exact yieldSeq_rootDom_of hy

/-! ### Computability -/

theorem primrec_compNames : Primrec DomDesc.compNames := by
  refine Primrec.list_flatMap primrec_methods ?_
  exact Primrec₂.mk (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
    (primrec_compoundNames.comp (Primrec.snd.comp Primrec.snd)))

theorem primrec_freshRoot : Primrec₂ freshRoot := by
  have hlist : Primrec (fun p : DomDesc × InstDesc =>
      p.1.compNames ++ p.2.tnI.compoundNames) :=
    Primrec.list_append.comp (primrec_compNames.comp Primrec.fst)
      (primrec_compoundNames.comp (primrec_tnI.comp Primrec.snd))
  have hstep : Primrec₂ (fun (_ : DomDesc × InstDesc) (z : ℕ × ℕ) => z.1 + 1 + z.2) :=
    Primrec₂.mk (Primrec.nat_add.comp
      (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))
  exact Primrec₂.mk (Primrec.list_foldr hlist (Primrec.const 0) hstep)

theorem primrec_rootDom : Primrec₂ rootDom := by
  have hnew : Primrec (fun p : DomDesc × InstDesc =>
      [((freshRoot p.1 p.2, p.2.tnI) : MethodDesc)]) :=
    Primrec.list_cons.comp
      (Primrec.pair (primrec_freshRoot.comp Primrec.fst Primrec.snd)
        (primrec_tnI.comp Primrec.snd))
      (Primrec.const [])
  exact Primrec₂.mk (Primrec.pair (primrec_actions.comp Primrec.fst)
    (Primrec.list_append.comp (primrec_methods.comp Primrec.fst) hnew))

theorem primrec_rootInst : Primrec₂ rootInst := by
  have hlbl : Primrec (fun p : DomDesc × InstDesc =>
      [((0, true, freshRoot p.1 p.2) : ℕ × Bool × ℕ)]) :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const true) (primrec_freshRoot.comp Primrec.fst Primrec.snd)))
      (Primrec.const [])
  exact Primrec₂.mk (Primrec.pair (primrec_initList.comp Primrec.snd)
    (Primrec.pair (primrec_goalList.comp Primrec.snd)
      (Primrec.pair (Primrec.const [0])
        (Primrec.pair (Primrec.const []) hlbl))))

end Syn

end HTN
