import HtnComplexity.Computable.TokBlock
/-!
# The token gadget: correctness

Putting the three ingredients together:

* the source normal form `HTN.Problem.solvable_iff_derivesW` — a rooted regular problem is
  solvable exactly when some *derivation*, choosing one block of each method, is executable;
* the shape of the derivations of the compiled description (`HTN.Syn.derives_ctName`);
* the execution of one block (`HTN.Syn.seqApplicable_block`, `HTN.Syn.transitionSeq_block`),

the derivations of the two descriptions correspond
(`HTN.Syn.exists_derives_of_derivesW`, `HTN.Syn.exists_derivesW_of_derives`) and hence

    `HTN.Syn.solvable_tok_iff` :  Solvable d q ↔ Solvable (tokDom d) (tokInst q).
-/

namespace HTN

namespace Syn

variable {d : DomDesc} {q q' : InstDesc}

/-! ### Reading a listed method as an index -/

theorem exists_index_of_mem_methods {e : MethodDesc} (he : e ∈ d.methods) :
    ∃ i, i < d.methods.length ∧ d.methods.getI i = e := by
  obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.1 he
  exact ⟨i, hi, by rw [List.getI_eq_getElem (l := d.methods) hi, hval]⟩

theorem cOf_eq_of_getI {i : ℕ} {e : MethodDesc} (h : d.methods.getI i = e) : cOf d i = e.1 := by
  rw [cOf, h]

theorem tOf_eq_of_getI {i : ℕ} {e : MethodDesc} (h : d.methods.getI i = e) : tOf d i = e.2 := by
  rw [tOf, h]

/-- The method number `i`, as a semantic method. -/
theorem mem_methods_index {i : ℕ} (hi : i < d.methods.length) :
    MethodDesc.toMethod (cOf d i, tOf d i) ∈ (problem d q).methods :=
  ⟨d.methods.getI i, mem_methods_getI hi, by
    simp only [cOf, tOf]⟩

theorem isRegular_index {i : ℕ} (hreg : d.MethodsReg) (hi : i < d.methods.length) :
    (tOf d i).toTaskNetwork.IsRegular :=
  hreg (d.methods.getI i) (mem_methods_getI hi)

/-- An enumeration of the primitive part has as many elements as there are primitive
subtasks. -/
theorem length_eq_of_primLin {i : ℕ} {xs : List ℕ} (h : TnDesc.PrimLin (tOf d i) xs) :
    xs.length = (pOf d i).length := by
  have hperm : xs.Perm (pOf d i) :=
    (List.perm_ext_iff_of_nodup h.1 (TnDesc.primIds_nodup (tOf d i))).2 h.2.1
  exact hperm.length_eq

/-! ### From a source derivation to a compiled one -/

theorem block_append (i : ℕ) (xs rest : List ℕ) :
    strtA i :: (xs.map (doA i) ++ finA i :: rest) =
      (strtA i :: (xs.map (doA i) ++ [finA i])) ++ rest := by
  simp

/-- **Every source derivation is simulated by a compiled one.** -/
theorem exists_derives_of_derivesW (hreg : d.MethodsReg) {c : ℕ} {as : List ℕ}
    (hd : (problem d q).DerivesW c as) :
    ∀ s : Set ℕ, (problem d q).SeqApplicable as s →
      ∃ bs : List ℕ, (problem (tokDom d) q').Derives (ctName c) bs ∧
        (problem (tokDom d) q').SeqApplicable bs (stateF '' s) ∧
        (problem (tokDom d) q').transitionSeq bs (stateF '' s) =
          stateF '' ((problem d q).transitionSeq as s) := by
  induction hd with
  | @last c os m hm hc hb =>
      intro s happ
      obtain ⟨e, he, rfl⟩ := hm
      obtain ⟨i, hi, hgi⟩ := exists_index_of_mem_methods he
      have hct : cOf d i = c := by rw [cOf_eq_of_getI hgi]; exact hc
      have htt : tOf d i = e.2 := tOf_eq_of_getI hgi
      have hbe : (MethodDesc.toMethod (e.1, e.2)).HasBlock os none := hb
      obtain ⟨xs, hlin, rfl, htail⟩ :=
        (TnDesc.hasBlock_iff (t := e.2) (htt ▸ isRegular_index hreg hi) e.1).1 hbe
      rw [← htt] at hlin htail happ ⊢
      have hmem : ∀ x ∈ xs, x ∈ pOf d i := fun x hx => (hlin.2.1 x).1 hx
      have hcomp : ∀ x ∈ pOf d i, x ∈ xs := fun x hx => (hlin.2.1 x).2 hx
      refine ⟨strtA i :: (xs.map (doA i) ++ finA i :: []), ?_, ?_, ?_⟩
      · refine derives_ctName.2 ⟨i, hi, hct, xs, [], length_eq_of_primLin hlin, hmem, rfl, ?_⟩
        simp only [TailDer, ← htail]
      · rw [block_append, List.append_nil]
        exact (seqApplicable_block (q := q) hi s xs hmem).2 ⟨hlin, happ⟩
      · rw [block_append, List.append_nil]
        exact transitionSeq_block (q := q) hi s xs hmem hcomp
  | @cons c c' os rest m hm hc hb hder ih =>
      intro s happ
      rw [ActionModel.seqApplicable_append] at happ
      obtain ⟨e, he, rfl⟩ := hm
      obtain ⟨i, hi, hgi⟩ := exists_index_of_mem_methods he
      have hct : cOf d i = c := by rw [cOf_eq_of_getI hgi]; exact hc
      have htt : tOf d i = e.2 := tOf_eq_of_getI hgi
      have hbe : (MethodDesc.toMethod (e.1, e.2)).HasBlock os (some c') := hb
      obtain ⟨xs, hlin, rfl, htail⟩ :=
        (TnDesc.hasBlock_iff (t := e.2) (htt ▸ isRegular_index hreg hi) e.1).1 hbe
      rw [← htt] at hlin htail happ ⊢
      have hmem : ∀ x ∈ xs, x ∈ pOf d i := fun x hx => (hlin.2.1 x).1 hx
      have hcomp : ∀ x ∈ pOf d i, x ∈ xs := fun x hx => (hlin.2.1 x).2 hx
      obtain ⟨bs, hbder, hbapp, hbtr⟩ := ih _ happ.2
      refine ⟨strtA i :: (xs.map (doA i) ++ finA i :: bs), ?_, ?_, ?_⟩
      · refine derives_ctName.2 ⟨i, hi, hct, xs, bs, length_eq_of_primLin hlin, hmem, rfl, ?_⟩
        simp only [TailDer, ← htail]
        exact hbder
      · rw [block_append, ActionModel.seqApplicable_append]
        refine ⟨(seqApplicable_block (q := q) hi s xs hmem).2 ⟨hlin, happ.1⟩, ?_⟩
        rw [transitionSeq_block (q := q) hi s xs hmem hcomp]
        exact hbapp
      · rw [block_append, ActionModel.transitionSeq_append,
          transitionSeq_block (q := q) hi s xs hmem hcomp, hbtr,
          ActionModel.transitionSeq_append]

/-! ### From a compiled derivation to a source one -/

/-- **Every executable compiled derivation comes from a source derivation.** -/
theorem exists_derivesW_of_derives (hreg : d.MethodsReg) :
    ∀ (n : ℕ) (bs : List ℕ), bs.length ≤ n → ∀ (c : ℕ) (s : Set ℕ),
      (problem (tokDom d) q').Derives (ctName c) bs →
      (problem (tokDom d) q').SeqApplicable bs (stateF '' s) →
      ∃ as : List ℕ, (problem d q).DerivesW c as ∧ (problem d q).SeqApplicable as s ∧
        stateF '' ((problem d q).transitionSeq as s) =
          (problem (tokDom d) q').transitionSeq bs (stateF '' s) := by
  intro n
  induction n with
  | zero =>
      intro bs hlen c s hder _
      obtain ⟨i, hi, hci, xs, rest, hxlen, hmem, rfl, htail⟩ := derives_ctName.1 hder
      simp at hlen
  | succ n ih =>
      intro bs hlen c s hder happ
      obtain ⟨i, hi, hci, xs, rest, hxlen, hmem, rfl, htail⟩ := derives_ctName.1 hder
      rw [block_append, ActionModel.seqApplicable_append] at happ
      obtain ⟨hlin, hsrc⟩ := (seqApplicable_block (q := q) hi s xs hmem).1 happ.1
      have hcomp : ∀ x ∈ pOf d i, x ∈ xs := fun x hx => (hlin.2.1 x).2 hx
      have hblk := transitionSeq_block (q := q) (q' := q') hi s xs hmem hcomp
      have hmeth : MethodDesc.toMethod (cOf d i, tOf d i) ∈ (problem d q).methods :=
        mem_methods_index hi
      have hlenrest : rest.length ≤ n := by
        simp only [List.length_cons, List.length_append, List.length_map] at hlen
        omega
      rcases htailname : TnDesc.tailName (tOf d i) with _ | c'
      · have hrest : rest = [] := by
          simpa [TailDer, htailname] using htail
        subst hrest
        refine ⟨xs.map (TnDesc.actOf (tOf d i)), ?_, hsrc, ?_⟩
        · refine Problem.DerivesW.last hmeth (by simpa using hci) ?_
          exact (TnDesc.hasBlock_iff (isRegular_index hreg hi) (cOf d i)).2
            ⟨xs, hlin, rfl, htailname.symm⟩
        · exact hblk.symm
      · have hrest : (problem (tokDom d) q').Derives (ctName c') rest := by
          simpa [TailDer, htailname] using htail
        rw [hblk] at happ
        obtain ⟨as, hasd, hasapp, hastr⟩ :=
          ih rest hlenrest c' _ hrest happ.2
        refine ⟨xs.map (TnDesc.actOf (tOf d i)) ++ as, ?_, ?_, ?_⟩
        · refine Problem.DerivesW.cons hmeth (by simpa using hci) ?_ hasd
          exact (TnDesc.hasBlock_iff (isRegular_index hreg hi) (cOf d i)).2
            ⟨xs, hlin, rfl, htailname.symm⟩
        · rw [ActionModel.seqApplicable_append]
          exact ⟨hsrc, hasapp⟩
        · rw [ActionModel.transitionSeq_append, hastr, block_append,
            ActionModel.transitionSeq_append, hblk]

/-! ### Correctness of the compilation -/

theorem stateF_injective : Function.Injective stateF := fun _ _ h => stateF_inj.1 h

theorem setOf_mem_map_stateF (l : List ℕ) : {f | f ∈ l.map stateF} = stateF '' {v | v ∈ l} := by
  ext f
  simp [Set.mem_image]

theorem init_tokInst (q : InstDesc) :
    {f | f ∈ (tokInst q).initList} = stateF '' {v | v ∈ q.initList} :=
  setOf_mem_map_stateF q.initList

theorem goal_tokInst (q : InstDesc) :
    {f | f ∈ (tokInst q).goalList} = stateF '' {v | v ∈ q.goalList} :=
  setOf_mem_map_stateF q.goalList

/-- **Correctness of the token-gadget compilation.**  A regular description with a rooted
instance is solvable exactly when its totally ordered compilation is. -/
theorem solvable_tok_iff (hreg : d.MethodsReg) (hq : q.IsRooted) :
    Solvable d q ↔ Solvable (tokDom d) (tokInst q) := by
  obtain ⟨t₀, hT, hα⟩ := InstDesc.rootName_spec hq
  set c₀ := rootName q with hc₀
  have hsrc : Solvable d q ↔ ∃ as : List ℕ, (problem d q).DerivesW c₀ as ∧
      (problem d q).SeqApplicable as {v | v ∈ q.initList} ∧
      (problem d q).GoalState ((problem d q).transitionSeq as {v | v ∈ q.initList}) :=
    Problem.solvable_iff_derivesW (problem_wf d q) (isRegularM_problem hreg) hT hα
  have htgt : Solvable (tokDom d) (tokInst q) ↔ ∃ bs : List ℕ,
      (problem (tokDom d) (tokInst q)).Derives (ctName c₀) bs ∧
      (problem (tokDom d) (tokInst q)).SeqApplicable bs {f | f ∈ (tokInst q).initList} ∧
      (problem (tokDom d) (tokInst q)).GoalState
        ((problem (tokDom d) (tokInst q)).transitionSeq bs {f | f ∈ (tokInst q).initList}) :=
    Problem.solvable_iff_derives (problem_wf (tokDom d) (tokInst q))
      (isRegularM_problem (tokDom_methodsReg d))
      (isTO_problem (tokDom_methodsTO d) (tokInst_isRooted q).isTO).2
      (by simpa using tokInst_tnI_T q) (by simpa using tokInst_tnI_α q)
  rw [hsrc, htgt, init_tokInst q]
  constructor
  · rintro ⟨as, hd, happ, hgoal⟩
    obtain ⟨bs, hbd, hbapp, hbtr⟩ :=
      exists_derives_of_derivesW (q' := tokInst q) hreg hd _ happ
    refine ⟨bs, hbd, hbapp, ?_⟩
    rw [hbtr]
    show {f | f ∈ (tokInst q).goalList} ⊆ _
    rw [goal_tokInst q]
    exact Set.image_mono hgoal
  · rintro ⟨bs, hbd, hbapp, hbgoal⟩
    obtain ⟨as, hd, happ, htr⟩ :=
      exists_derivesW_of_derives (q := q) hreg bs.length bs le_rfl c₀ _ hbd hbapp
    refine ⟨as, hd, happ, ?_⟩
    have hg : {f | f ∈ (tokInst q).goalList} ⊆
        (problem (tokDom d) (tokInst q)).transitionSeq bs (stateF '' {v | v ∈ q.initList}) :=
      hbgoal
    rw [goal_tokInst q, ← htr] at hg
    exact (Set.image_subset_image_iff stateF_injective).1 hg

end Syn

end HTN
