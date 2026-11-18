import HtnComplexity.Computable.AcDom
import HtnPlanning.Computable.FiniteSig
import HtnPlanning.Computable.Bodies
import HtnComplexity.Computable.Rooted
/-!
# The compilation of a described totally ordered problem into an acyclic one

`HtnComplexity/Computable/AcDom.lean` lifts the construction of
`HtnComplexity/ToHtnAc/ToHtnAc.lean` to descriptions, but leaves the data it needs from the
source — the list of facts, the lists of names, the binary methods and the action model — as
parameters.  This file supplies them **from a description**, so that the compilation becomes a
function of a pair of descriptions:

* `HTN.Syn.Ac.acDom facts names bound d` — the description of the compiled acyclic domain,
* `HTN.Syn.Ac.acInst facts q` — the description of the compiled instance,

and proves `HTN.Syn.Ac.solvable_acDom_iff`: the described compiled problem is solvable exactly
when the compiled problem of the construction is, for the described problem moved to the finite
signature `(facts, names)` (`HtnPlanning/Computable/FiniteSig.lean`).

**The vocabulary.**  The two lists `facts` and `names` are the *shared signature* of the source
problem — the counterpart of the type-level signature `(F, A, C, I)` of the semantic
development, which the domain translation and the instance translation of a compilation scheme
both know.  They have to cover the source description
(`HTN.Syn.DomDesc.CoveredBy`, `HTN.Syn.InstDesc.CoveredBy`); the canonical choice
`(factsOf d q, namesOf d q)` always does (`HTN.Syn.coveredBy_canonical_dom`,
`…_inst`).  Keeping the vocabulary a parameter is what makes the compilation **modular**: the
compiled domain is a function of the vocabulary and the source *domain*, the compiled instance
one of the vocabulary and the source *instance*.

The source is assumed to be **totally ordered** (`HTN.Syn.DomDesc.MethodsTO`): this is what
makes the bodies of its methods the computable lists `HTN.Syn.DomDesc.bd`
(`HtnPlanning/Computable/Bodies.lean`), which is how the `TUPLE` methods of the
construction are enumerated.
-/

namespace HTN

namespace Syn

/-! ### Vocabularies -/

/-- **The vocabulary covers the domain description**: every fact its actions mention is listed
in `facts`, and every name its methods mention is listed in `names`. -/
structure DomDesc.CoveredBy (d : DomDesc) (facts names : List ℕ) : Prop where
  /-- The facts of an action are listed. -/
  acts : ∀ a : ℕ, d.prec a ⊆ {f | f ∈ facts} ∧ d.add a ⊆ {f | f ∈ facts} ∧
    d.del a ⊆ {f | f ∈ facts}
  /-- The names of a method are listed. -/
  methods : ∀ e ∈ d.methods, e.1 ∈ names ∧ e.2.namesOf ⊆ names

/-- **The vocabulary covers the instance description**. -/
structure InstDesc.CoveredBy (q : InstDesc) (facts names : List ℕ) : Prop where
  /-- The initial state is listed. -/
  init : ∀ f ∈ q.initList, f ∈ facts
  /-- The goal is listed. -/
  goal : ∀ f ∈ q.goalList, f ∈ facts
  /-- The names of the initial task network are listed. -/
  tnI : q.tnI.namesOf ⊆ names

/-- The canonical vocabulary covers the domain description. -/
theorem coveredBy_canonical_dom (d : DomDesc) (q : InstDesc) :
    d.CoveredBy (factsOf d q) (namesOf d q) :=
  ⟨prec_subset_factsOf d q, methods_names_subset_namesOf d q⟩

/-- The canonical vocabulary covers the instance description. -/
theorem coveredBy_canonical_inst (d : DomDesc) (q : InstDesc) :
    q.CoveredBy (factsOf d q) (namesOf d q) :=
  ⟨initList_subset_factsOf d q, goalList_subset_factsOf d q, tnI_names_subset_namesOf d q⟩

/-! ### Two more conditions on descriptions -/

namespace DomDesc

/-- **`BIN2` for descriptions**: every listed method has exactly two subtasks. -/
def IsBin2 (d : DomDesc) : Prop := ∀ m < d.methods.length, (d.bd m).length = 2

/-- **No operator adds and deletes the same fact.** -/
def NoAddDel (d : DomDesc) : Prop := ∀ a f : ℕ, f ∈ d.add a → f ∉ d.del a

end DomDesc

namespace Ac

open ToAc

/-! ### The finite signature of a vocabulary -/

/-- The facts of a vocabulary, as elements of the finite signature it spans. -/
def varsOf (facts : List ℕ) : List (SFact facts) :=
  facts.dedup.attach.map fun x => ⟨x.1, List.mem_dedup.1 x.2⟩

variable {facts names : List ℕ} {d : DomDesc} {q : InstDesc}

lemma map_val_varsOf : (varsOf facts).map Subtype.val = facts.dedup := by
  simp [varsOf, List.map_map, Function.comp_def]

lemma mem_varsOf (v : SFact facts) : v ∈ varsOf facts := by
  rw [varsOf, List.mem_map]
  exact ⟨⟨v.1, List.mem_dedup.2 v.2⟩, List.mem_attach _ _, rfl⟩

lemma nodup_varsOf : (varsOf facts).Nodup := by
  refine List.Nodup.map (fun x y h => ?_) (List.nodup_attach.2 (List.nodup_dedup _))
  exact Subtype.ext (by simpa using congrArg Subtype.val h)

/-- The small domain of a description, over the vocabulary. -/
def sDom (hn : 0 ∈ names) (facts : List ℕ) (d : DomDesc) :
    Domain (SFact facts) (SName names) (SName names) ℕ :=
  d.small hn facts

/-- The small instance of a description, over the vocabulary. -/
def sInst (hn : 0 ∈ names) (facts : List ℕ) (q : InstDesc) :
    Instance (SFact facts) (SName names) (SName names) ℕ :=
  q.small hn facts

lemma smallProblem_eq (hn : 0 ∈ names) : smallProblem d q hn facts =
    (sDom hn facts d).mkProblem (sInst hn facts q) := rfl

/-! ### The binary methods of a description -/

/-- A described task name, numbered as a task name of the compiled signature. -/
def encLbl : ℕ ⊕ ℕ → ℕ
  | Sum.inl u => nA u
  | Sum.inr u => nC u

/-- **The binary methods of a description**, numbered. -/
def tuplesOf (d : DomDesc) : List (ℕ × ℕ × ℕ) :=
  (List.range d.methods.length).filterMap fun m =>
    match d.bd m with
    | [x, y] => some (nC (d.hd m), encLbl x, encLbl y)
    | _ => none

lemma mem_tuplesOf {p : ℕ × ℕ × ℕ} :
    p ∈ tuplesOf d ↔ ∃ m, m < d.methods.length ∧ ∃ x y, d.bd m = [x, y] ∧
      p = (nC (d.hd m), encLbl x, encLbl y) := by
  simp only [tuplesOf, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨m, hm, hval⟩
    refine ⟨m, hm, ?_⟩
    rcases hb : d.bd m with _ | ⟨x, tl⟩
    · rw [hb] at hval; simp at hval
    · rcases tl with _ | ⟨y, tl'⟩
      · rw [hb] at hval; simp at hval
      · rcases tl' with _ | ⟨z, tl''⟩
        · rw [hb] at hval
          simp only [Option.some.injEq] at hval
          exact ⟨x, y, rfl, hval.symm⟩
        · rw [hb] at hval; simp at hval
  · rintro ⟨m, hm, x, y, hb, rfl⟩
    exact ⟨m, hm, by rw [hb]⟩

/-! ### The bodies of the small domain -/

/-- The small network of a described totally ordered network, presented as a sequence
network. -/
lemma isSeqNet_lin_small (hn : 0 ∈ names) {t : TnDesc}
    (hTO : t.toTaskNetwork.IsTotallyOrdered) :
    (t.small hn).IsSeqNet (TnDesc.lin t)
      ((TnDesc.seqBody t).map (Sum.map (nm hn) (nm hn))) := by
  obtain ⟨h1, h2, h3, h4⟩ := TnDesc.isSeqNet_lin (t := t) hTO
  refine ⟨h1, h2, ?_, h4⟩
  rw [← h3, List.map_map]
  rfl

lemma small_seqBody_iff (hn : 0 ∈ names) (hTO : d.MethodsTO) {c₀ : SName names} {bs} :
    (sDom hn facts d).SeqBody c₀ bs ↔ ∃ m, m < d.methods.length ∧
      nm hn (d.hd m) = c₀ ∧ (d.bd m).map (Sum.map (nm hn) (nm hn)) = bs := by
  constructor
  · rintro ⟨mm, ⟨e, he, rfl⟩, hc, hbody⟩
    obtain ⟨m, hm, hgm⟩ := List.mem_iff_getElem.1 he
    have hgetI : d.methods.getI m = e := by
      rw [List.getI_eq_getElem (l := d.methods) hm, hgm]
    refine ⟨m, hm, by rw [DomDesc.hd, hgetI]; exact hc, ?_⟩
    have hb := (Method.hasSeqBody_iff_of_isSeqNet
      (isSeqNet_lin_small hn (hTO _ (getI_mem_methods hm)))).1
        (show (MethodDesc.small hn (d.methods.getI m)).HasSeqBody bs by
          rw [hgetI]; exact hbody)
    rw [DomDesc.bd, hb]
  · rintro ⟨m, hm, rfl, rfl⟩
    exact ⟨MethodDesc.small hn (d.methods.getI m),
      ⟨_, getI_mem_methods hm, rfl⟩, rfl,
      Method.hasSeqBody_of_isSeqNet
        (isSeqNet_lin_small hn (hTO _ (getI_mem_methods hm)))⟩

/-! ### The names a listed method mentions -/

lemma hd_mem_names (hcov : d.CoveredBy facts names) {m : ℕ} (hm : m < d.methods.length) :
    d.hd m ∈ names :=
  (hcov.methods _ (getI_mem_methods hm)).1

lemma bd_names_mem (hcov : d.CoveredBy facts names) {m : ℕ} (hm : m < d.methods.length)
    {x : ℕ ⊕ ℕ} (hx : x ∈ d.bd m) :
    (∀ u, x = Sum.inl u → u ∈ names) ∧ (∀ u, x = Sum.inr u → u ∈ names) := by
  rw [DomDesc.bd, TnDesc.seqBody, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact label_mem_namesOf_of_mem (hcov.methods _ (getI_mem_methods hm)).2 i

lemma encName_map_nm (hn : 0 ∈ names) {x : ℕ ⊕ ℕ}
    (hx : (∀ u, x = Sum.inl u → u ∈ names) ∧ (∀ u, x = Sum.inr u → u ∈ names)) :
    encName (Subtype.val : SName names → ℕ) (Subtype.val : SName names → ℕ)
      (Sum.map (nm hn) (nm hn) x) = encLbl x := by
  cases x with
  | inl u => simp [encName, encLbl, nA, val_nm _ (hx.1 u rfl)]
  | inr u => simp [encName, encLbl, nC, val_nm _ (hx.2 u rfl)]

/-! ### The data of the compilation, read off a description -/

/-- The precondition list of a described action. -/
def precL (d : DomDesc) (x : ℕ) : List ℕ := (d.actions.lookup x).elim [] fun y => y.1

/-- The add list of a described action. -/
def addL (d : DomDesc) (x : ℕ) : List ℕ := (d.actions.lookup x).elim [] fun y => y.2.1

/-- The delete list of a described action. -/
def delL (d : DomDesc) (x : ℕ) : List ℕ := (d.actions.lookup x).elim [] fun y => y.2.2

/-- **The description of the compiled acyclic domain** of a described source domain, over the
vocabulary `(facts, names)`. -/
def acDom (facts names : List ℕ) (bound : ℕ) (d : DomDesc) : DomDesc :=
  acDomOf facts.dedup names.dedup names.dedup (tuplesOf d)
    (precL d) (addL d) (delL d) bound

/-- **The description of the compiled instance** of a described source instance, over the
vocabulary `facts`. -/
def acInst (facts : List ℕ) (q : InstDesc) : InstDesc :=
  acInstOf facts.dedup q.initList q.goalList (rootName q)

private lemma image_val_setOf {facts l : List ℕ} (hl : ∀ u ∈ l, u ∈ facts) :
    (Subtype.val : {v // v ∈ facts} → ℕ) '' {v | v.val ∈ l} = {u | u ∈ l} := by
  ext u
  exact ⟨by rintro ⟨v, hv, rfl⟩; exact hv, fun hu => ⟨⟨u, hl u hu⟩, hu, rfl⟩⟩

lemma mem_dedup_names {u : ℕ} : u ∈ names.dedup ↔ u ∈ names := List.mem_dedup

/-- **The source data of the compilation.** -/
lemma sourceData (hn : 0 ∈ names) (hcov : d.CoveredBy facts names) (hTO : d.MethodsTO) :
    SourceData (Subtype.val : SFact facts → ℕ)
      (Subtype.val : SName names → ℕ) (Subtype.val : SName names → ℕ)
      (sDom hn facts d) (varsOf facts) facts.dedup names.dedup names.dedup
      (tuplesOf d) where
  facts := map_val_varsOf.symm
  actions_mem := fun o => mem_dedup_names.2 o.2
  actions_onto := fun u hu => ⟨⟨u, mem_dedup_names.1 hu⟩, rfl⟩
  names_mem := fun y => mem_dedup_names.2 y.2
  names_onto := fun u hu => ⟨⟨u, mem_dedup_names.1 hu⟩, rfl⟩
  tuples_spec := by
    intro p
    rw [mem_tuplesOf]
    constructor
    · rintro ⟨m, hm, x, y, hb, rfl⟩
      have hxm : x ∈ d.bd m := by rw [hb]; simp
      have hym : y ∈ d.bd m := by rw [hb]; simp
      refine ⟨nm hn (d.hd m), Sum.map (nm hn) (nm hn) x, Sum.map (nm hn) (nm hn) y, ?_, ?_⟩
      · rw [small_seqBody_iff hn hTO]
        exact ⟨m, hm, rfl, by rw [hb]; simp⟩
      · rw [encName_map_nm hn (bd_names_mem hcov hm hxm),
          encName_map_nm hn (bd_names_mem hcov hm hym), val_nm _ (hd_mem_names hcov hm)]
    · rintro ⟨c₀, X, Y, hsb, rfl⟩
      rw [small_seqBody_iff hn hTO] at hsb
      obtain ⟨m, hm, rfl, hmap⟩ := hsb
      rcases hb : d.bd m with _ | ⟨x, _ | ⟨y, _ | ⟨z, w⟩⟩⟩ <;> rw [hb] at hmap <;>
        simp only [List.map_cons, List.map_nil] at hmap
      · exact absurd hmap (by simp)
      · exact absurd hmap (by simp)
      · simp only [List.cons.injEq, and_true] at hmap
        obtain ⟨hX, hY⟩ := hmap
        subst hX
        subst hY
        have hxm : x ∈ d.bd m := by rw [hb]; simp
        have hym : y ∈ d.bd m := by rw [hb]; simp
        refine ⟨m, hm, x, y, hb, ?_⟩
        rw [encName_map_nm hn (bd_names_mem hcov hm hxm),
          encName_map_nm hn (bd_names_mem hcov hm hym), val_nm _ (hd_mem_names hcov hm)]
      · exact absurd hmap (by simp)

/-- **The action data of the compilation.** -/
lemma actData (hn : 0 ∈ names) (hcov : d.CoveredBy facts names) :
    ActData (Subtype.val : SFact facts → ℕ)
      (Subtype.val : SName names → ℕ) (Subtype.val : SName names → ℕ)
      (sDom hn facts d) (varsOf facts) facts.dedup names.dedup names.dedup
      (precL d) (addL d) (delL d) where
  facts := map_val_varsOf.symm
  vars_all := mem_varsOf
  actions_mem := fun o => mem_dedup_names.2 o.2
  names_mem := fun y => mem_dedup_names.2 y.2
  names_onto := by
    intro u hu
    rcases List.mem_append.1 hu with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      exact ⟨Sum.inl ⟨w, mem_dedup_names.1 hw⟩, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      exact ⟨Sum.inr ⟨w, mem_dedup_names.1 hw⟩, rfl⟩
  act_inj := Subtype.val_injective
  name_inj := Subtype.val_injective
  pre_spec := fun o => (image_val_setOf (fun u hu => (hcov.acts o.val).1 hu)).symm
  add_spec := fun o => (image_val_setOf (fun u hu => (hcov.acts o.val).2.1 hu)).symm
  del_spec := fun o => (image_val_setOf (fun u hu => (hcov.acts o.val).2.2 hu)).symm

/-! ### Correctness -/

/-- **The described compilation is the compilation.** -/
theorem solvable_acDom_iff (hn : 0 ∈ names) (hdcov : d.CoveredBy facts names)
    (hqcov : q.CoveredBy facts names) (hTO : d.MethodsTO) (bound : ℕ) (tI0 : SName names)
    (hroot : (tI0 : ℕ) = rootName q) :
    Solvable (acDom facts names bound d) (acInst facts q) ↔
      (problem' (sDom hn facts d) (sInst hn facts q) (varsOf facts) bound tI0).Solvable :=
  solvable_acDesc_iff (sourceData hn hdcov hTO) (actData hn hdcov) Subtype.val_injective
    (image_val_setOf hqcov.init).symm (image_val_setOf hqcov.goal).symm hroot

end Ac

end Syn

end HTN
