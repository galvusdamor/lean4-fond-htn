import HtnComplexity.Computable.ParDom
/-!
# Correctness of the parallel product construction

The compiled domain of `HtnComplexity/Computable/ParDom.lean` performs one step of one
process of a configuration.  This file proves that it does exactly that:

* `HTN.Syn.parEntries_tail`, `HTN.Syn.parEntries_body_nil` — the pool of entries is closed under
  the two steps (for a **totally ordered regular** source domain the remaining part of a task
  that starts with a compound name is that compound name alone);
* `HTN.Syn.yieldSeq_parDom_iff` — **the refinements of a configuration name are exactly the
  parallel refinements of the configuration** (`HTN.Domain.ParYield`);
* `HTN.Syn.solvable_par_iff` — hence the compiled problem is solvable exactly when the source
  problem is, for a source instance whose initial task network is an unordered network of at
  most `k` compound tasks.

Neither translation looks at the other side: `parDom k d` reads only the domain description and
`parInst q` only the instance description, so the construction is a modular compilation.
-/

namespace HTN

namespace Syn

/-! ### Lists: replacing one entry -/

theorem getI_append_cons {α : Type} [Inhabited α] (L₁ : List α) (y : α) (L₂ : List α) :
    (L₁ ++ y :: L₂).getI L₁.length = y := by
  induction L₁ with
  | nil => rfl
  | cons u L₁ ih => simpa using ih

theorem set_append_cons {α : Type} (L₁ : List α) (y : α) (L₂ : List α) (v : α) :
    (L₁ ++ y :: L₂).set L₁.length v = L₁ ++ v :: L₂ := by
  induction L₁ with
  | nil => rfl
  | cons u L₁ ih => simp

theorem exists_append_cons_of_getI {α : Type} [Inhabited α] {L : List α} {i : ℕ}
    (hi : i < L.length) :
    ∃ L₁ L₂, L = L₁ ++ L.getI i :: L₂ ∧ L₁.length = i := by
  induction L generalizing i with
  | nil => simp at hi
  | cons u L ih =>
      match i with
      | 0 => exact ⟨[], L, rfl, rfl⟩
      | (i + 1) =>
          obtain ⟨L₁, L₂, hL, hlen⟩ := ih (by simpa using hi)
          exact ⟨u :: L₁, L₂, by rw [show (u :: L).getI (i + 1) = L.getI i from rfl,
            List.cons_append, ← hL], by simp [hlen]⟩

/-! ### The bodies of a totally ordered domain description -/

/-- **The bodies of a totally ordered domain description are the bodies of its listed
methods.** -/
theorem seqBody_iff_mem {d : DomDesc} (hTO : d.MethodsTO) {c : ℕ} {bs : List (ℕ ⊕ ℕ)} :
    d.toDomain.SeqBody c bs ↔ ∃ e ∈ d.methods, e.1 = c ∧ TnDesc.seqBody e.2 = bs := by
  rw [DomDesc.seqBody_iff hTO]
  constructor
  · rintro ⟨m, hm, hhd, hbd⟩
    exact ⟨d.methods.getI m, getI_mem_methods hm, hhd, hbd⟩
  · rintro ⟨e, he, hc, hbs⟩
    obtain ⟨m, hm, hgm⟩ := List.mem_iff_getElem.1 he
    have hgetI : d.methods.getI m = e := by
      rw [List.getI_eq_getElem (l := d.methods) hm, hgm]
    exact ⟨m, hm, by rw [DomDesc.hd, hgetI]; exact hc, by rw [DomDesc.bd, hgetI]; exact hbs⟩

/-! ### The pool of entries is closed under the two steps -/

/-- In the body of a **regular** totally ordered method a compound task comes last. -/
theorem seqBody_regular_last {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered)
    (hreg : t.toTaskNetwork.IsRegular) {j : ℕ} (hj : j < (TnDesc.seqBody t).length)
    {c : ℕ} (hc : (TnDesc.seqBody t)[j] = Sum.inr c) : j + 1 = (TnDesc.seqBody t).length := by
  have hlen : (TnDesc.seqBody t).length = (TnDesc.lin t).length := TnDesc.length_seqBody t
  have hj' : j < (TnDesc.lin t).length := by omega
  have hlbl : t.label ((TnDesc.lin t)[j]) = Sum.inr c := by
    have hmap : (TnDesc.seqBody t)[j] = t.label ((TnDesc.lin t)[j]'hj') := by
      simp only [TnDesc.seqBody, List.getElem_map]
    rw [← hmap]; exact hc
  have hmemT : (TnDesc.lin t)[j] ∈ t.toTaskNetwork.T :=
    (TnDesc.isSeqNet_lin hTO).mem_of_mem (List.getElem_mem hj')
  have habs : t.toTaskNetwork.IsAbstractId ((TnDesc.lin t)[j]) := ⟨c, hlbl⟩
  have hlast : t.toTaskNetwork.IsLastId ((TnDesc.lin t)[j]) :=
    ⟨hmemT, fun y hy hne => hreg.2 _ hmemT habs y hy hne⟩
  rw [hlen]
  exact (DomDesc.isLastId_lin_iff hTO hj').1 hlast

/-- A suffix of the body of a regular method that starts with a compound task is that compound
task alone. -/
theorem suffix_regular_cons_inr {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered)
    (hreg : t.toTaskNetwork.IsRegular) :
    ∀ {s : ParEntry}, s ∈ suffixesOf (TnDesc.seqBody t) → ∀ {c : ℕ} {xs : ParEntry},
      s = Sum.inr c :: xs → xs = [] := by
  have key : ∀ (l : List (ℕ ⊕ ℕ)), (∀ {j : ℕ} (hj : j < l.length) {c : ℕ},
      l[j] = Sum.inr c → j + 1 = l.length) →
      ∀ {s : ParEntry}, s ∈ suffixesOf l → ∀ {c : ℕ} {xs : ParEntry},
        s = Sum.inr c :: xs → xs = [] := by
    intro l
    induction l with
    | nil =>
        intro _ s hs c xs hsc
        rw [suffixesOf_nil, List.mem_singleton] at hs
        rw [hs] at hsc
        exact absurd hsc (by simp)
    | cons x l ih =>
        intro hlast s hs c xs hsc
        rw [suffixesOf_cons] at hs
        rcases List.mem_cons.1 hs with rfl | hmem
        · obtain ⟨hx, rfl⟩ := List.cons.inj hsc
          have h0 : (x :: l)[0] = Sum.inr c := by simpa using hx
          have hl := hlast (j := 0) (by simp) h0
          have hlen0 : l.length = 0 := by
            have hcons : (x :: l).length = l.length + 1 := rfl
            omega
          exact List.eq_nil_of_length_eq_zero hlen0
        · refine ih ?_ hmem hsc
          intro j hj c' hjc
          have := hlast (j := j + 1) (by simpa using hj) (by simpa using hjc)
          simpa using this
  intro s hs c xs hsc
  exact key (TnDesc.seqBody t) (fun {j} hj {c'} hjc => seqBody_regular_last hTO hreg hj hjc)
    hs hsc

/-- **The pool of entries is closed under executing a leading action.** -/
theorem parEntries_tail {d : DomDesc} {a : ℕ} {xs : ParEntry}
    (h : (Sum.inl a :: xs : ParEntry) ∈ parEntries d) : xs ∈ parEntries d := by
  simp only [parEntries, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_flatMap] at h ⊢
  rcases h with h | ⟨c, -, hc⟩ | ⟨e, he, hs⟩
  · exact absurd h (by simp)
  · exact absurd hc (by simp)
  · exact Or.inr (Or.inr ⟨e, he, tail_mem_suffixesOf hs⟩)

/-- **An entry that starts with a compound task is that compound task alone**, for a totally
ordered regular source domain. -/
theorem parEntries_cons_inr {d : DomDesc} (hTO : d.MethodsTO) (hreg : d.MethodsReg) {c : ℕ}
    {xs : ParEntry} (h : (Sum.inr c :: xs : ParEntry) ∈ parEntries d) : xs = [] := by
  simp only [parEntries, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_flatMap] at h
  rcases h with h | ⟨c', -, hc⟩ | ⟨e, he, hs⟩
  · exact absurd h (by simp)
  · exact (List.cons.inj hc.symm).2
  · exact suffix_regular_cons_inr (hTO e he) (hreg e he) hs rfl

/-- **The pool of entries contains the body of every listed method.** -/
theorem parEntries_body {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) :
    (TnDesc.seqBody e.2 : ParEntry) ∈ parEntries d :=
  mem_parEntries_body he (mem_suffixesOf_self _)

/-! ### The configurations are closed under the steps -/

theorem mem_parCfgs_set {k : ℕ} {d : DomDesc} {L : ParCfg} (hL : L ∈ parCfgs k d) {i : ℕ}
    {v : ParEntry} (hv : v ∈ parEntries d) : L.set i v ∈ parCfgs k d := by
  rw [parCfgs, mem_parTuplesLe] at hL ⊢
  refine ⟨by rw [List.length_set]; exact hL.1, fun x hx => ?_⟩
  rcases List.mem_or_eq_of_mem_set hx with hx' | rfl
  · exact hL.2 x hx'
  · exact hv

theorem mem_parEntries_of_mem_parCfgs {k : ℕ} {d : DomDesc} {L : ParCfg} (hL : L ∈ parCfgs k d)
    {x : ParEntry} (hx : x ∈ L) : x ∈ parEntries d := (mem_parTuplesLe.1 hL).2 x hx

/-! ### A primitive task sequence refines only into itself -/

theorem eq_of_yieldSeq_map_inl {D : Domain ℕ ℕ ℕ ℕ} :
    ∀ {xs : List (ℕ ⊕ ℕ)} {as : List ℕ}, D.YieldSeq xs as → ∀ pre, xs = pre.map Sum.inl →
      as = pre := by
  intro xs as h
  induction h with
  | nil => intro pre hpre; exact (List.map_eq_nil_iff.1 hpre.symm).symm
  | @prim a zs bs _ ih =>
      intro pre hpre
      rcases pre with _ | ⟨b, pre⟩
      · simp at hpre
      · have hb : a = b := by simpa using (List.cons.inj hpre).1
        have hz : zs = pre.map Sum.inl := (List.cons.inj hpre).2
        rw [hb, ih pre hz]
  | @comp c cs zs bs hm _ _ =>
      intro pre hpre
      rcases pre with _ | ⟨b, pre⟩
      · simp at hpre
      · exact absurd (List.cons.inj hpre).1 (by simp)

/-! ### The refinements of a configuration name -/

variable {k : ℕ} {d : DomDesc}

/-- **Every parallel refinement of a configuration is a refinement of its name.** -/
theorem yieldSeq_parDom_of_parYield (hTO : d.MethodsTO) (hreg : d.MethodsReg) :
    ∀ {L : ParCfg} {as : List ℕ}, Domain.ParYield d.toDomain L as → L ∈ parCfgs k d →
      (parDom k d).toDomain.YieldSeq [Sum.inr (parName L)] as := by
  intro L as h
  induction h with
  | @done L hL =>
      intro hmem
      have hm : ((parName L, TnDesc.nil) : MethodDesc) ∈ parMethods k d :=
        mem_parMethods_iff.2 ⟨L, hmem, mem_parMethodsOf_done hL⟩
      have hsb : (parDom k d).toDomain.SeqBody (parName L) [] :=
        (seqBody_iff_mem (parDom_methodsTO k d)).2 ⟨_, hm, rfl, rfl⟩
      exact Domain.YieldSeq.comp hsb (by simp)
  | @prim L₁ L₂ a xs as _ ih =>
      intro hmem
      have hi : L₁.length < (L₁ ++ (Sum.inl a :: xs) :: L₂).length := by simp
      have hget : (L₁ ++ (Sum.inl a :: xs) :: L₂).getI L₁.length = Sum.inl a :: xs :=
        getI_append_cons _ _ _
      have hset : (L₁ ++ (Sum.inl a :: xs) :: L₂).set L₁.length xs = L₁ ++ xs :: L₂ :=
        set_append_cons _ _ _ _
      have hxs : xs ∈ parEntries d :=
        parEntries_tail (mem_parEntries_of_mem_parCfgs hmem
          (List.mem_append_right _ List.mem_cons_self))
      have hmem' : L₁ ++ xs :: L₂ ∈ parCfgs k d := by
        rw [← hset]; exact mem_parCfgs_set hmem hxs
      have hm : ((parName (L₁ ++ (Sum.inl a :: xs) :: L₂),
          parStepTn a (parName (L₁ ++ xs :: L₂))) : MethodDesc) ∈ parMethods k d := by
        refine mem_parMethods_iff.2 ⟨_, hmem, ?_⟩
        have := mem_parMethodsOf_prim (d := d) hi hget
        rwa [hset] at this
      have hsb : (parDom k d).toDomain.SeqBody (parName (L₁ ++ (Sum.inl a :: xs) :: L₂))
          [Sum.inl a, Sum.inr (parName (L₁ ++ xs :: L₂))] :=
        (seqBody_iff_mem (parDom_methodsTO k d)).2 ⟨_, hm, rfl, rfl⟩
      exact Domain.YieldSeq.comp hsb (by
        simpa using Domain.YieldSeq.prim (ih hmem'))
  | @comp L₁ L₂ c bs xs as hsrc _ ih =>
      intro hmem
      obtain ⟨e, he, hc, hbs⟩ := (seqBody_iff_mem hTO).1 hsrc
      have hi : L₁.length < (L₁ ++ (Sum.inr c :: xs) :: L₂).length := by simp
      have hget : (L₁ ++ (Sum.inr c :: xs) :: L₂).getI L₁.length = Sum.inr c :: xs :=
        getI_append_cons _ _ _
      have hset : (L₁ ++ (Sum.inr c :: xs) :: L₂).set L₁.length (TnDesc.seqBody e.2 ++ xs) =
          L₁ ++ (TnDesc.seqBody e.2 ++ xs) :: L₂ := set_append_cons _ _ _ _
      have hbsmem : (bs ++ xs : ParEntry) ∈ parEntries d := by
        have hxs : xs = [] := parEntries_cons_inr hTO hreg
          (mem_parEntries_of_mem_parCfgs hmem (List.mem_append_right _ List.mem_cons_self))
        rw [hxs, List.append_nil, ← hbs]
        exact parEntries_body he
      have hmem' : L₁ ++ (bs ++ xs) :: L₂ ∈ parCfgs k d := by
        have := mem_parCfgs_set (i := L₁.length) (v := bs ++ xs) hmem hbsmem
        rwa [set_append_cons] at this
      have hm : ((parName (L₁ ++ (Sum.inr c :: xs) :: L₂),
          singleTn (parName (L₁ ++ (bs ++ xs) :: L₂))) : MethodDesc) ∈ parMethods k d := by
        refine mem_parMethods_iff.2 ⟨_, hmem, ?_⟩
        have := mem_parMethodsOf_comp (d := d) hi hget he hc
        rw [hset, hbs] at this
        exact this
      have hsb : (parDom k d).toDomain.SeqBody (parName (L₁ ++ (Sum.inr c :: xs) :: L₂))
          [Sum.inr (parName (L₁ ++ (bs ++ xs) :: L₂))] :=
        (seqBody_iff_mem (parDom_methodsTO k d)).2 ⟨_, hm, rfl, rfl⟩
      exact Domain.YieldSeq.comp hsb (by simpa using ih hmem')

/-! ### The converse: a refinement of a configuration name is a parallel refinement -/

/-- **The bodies the compiled domain offers for a configuration name.** -/
theorem seqBody_parDom_cases {L : ParCfg} {bs : List (ℕ ⊕ ℕ)}
    (h : (parDom k d).toDomain.SeqBody (parName L) bs) :
    (bs = [] ∧ ∀ xs ∈ L, xs = []) ∨
      (∃ i, i < L.length ∧ ∃ a xs, L.getI i = Sum.inl a :: xs ∧
        bs = [Sum.inl a, Sum.inr (parName (L.set i xs))]) ∨
      (∃ i, i < L.length ∧ ∃ c xs, L.getI i = Sum.inr c :: xs ∧ ∃ e ∈ d.methods, e.1 = c ∧
        bs = [Sum.inr (parName (L.set i (TnDesc.seqBody e.2 ++ xs)))]) := by
  rw [seqBody_iff_mem (parDom_methodsTO k d)] at h
  obtain ⟨m, hm, hhead, hbody⟩ := h
  obtain ⟨L₀, -, hmem⟩ := mem_parMethods_iff.1 hm
  rcases parMethodsOf_cases hmem with ⟨hm₀, hall⟩ | ⟨i, hi, a, xs, hget, hm₀⟩ |
    ⟨i, hi, c, xs, hget, e, he, hc, hm₀⟩
  · subst hm₀
    have hL : L₀ = L := parName_injective hhead
    subst hL
    exact Or.inl ⟨hbody.symm, hall⟩
  · subst hm₀
    have hL : L₀ = L := parName_injective hhead
    subst hL
    exact Or.inr (Or.inl ⟨i, hi, a, xs, hget, hbody.symm⟩)
  · subst hm₀
    have hL : L₀ = L := parName_injective hhead
    subst hL
    exact Or.inr (Or.inr ⟨i, hi, c, xs, hget, e, he, hc, hbody.symm⟩)

/-- The entry at a listed position belongs to the pool. -/
theorem getI_mem_parEntries {L : ParCfg} (hL : L ∈ parCfgs k d) {i : ℕ} (hi : i < L.length) :
    L.getI i ∈ parEntries d := by
  rw [List.getI_eq_getElem (l := L) hi]
  exact mem_parEntries_of_mem_parCfgs hL (List.getElem_mem hi)

/-- **Every refinement of a configuration name is a parallel refinement of the
configuration.**  The statement is generalised to the task sequences the bodies of the compiled
methods produce: a list of actions followed by one configuration task. -/
theorem parYield_of_yieldSeq_aux (hTO : d.MethodsTO) (hreg : d.MethodsReg) :
    ∀ {xs : List (ℕ ⊕ ℕ)} {as : List ℕ}, (parDom k d).toDomain.YieldSeq xs as →
      ∀ (pre : List ℕ) (L : ParCfg), L ∈ parCfgs k d →
        xs = pre.map Sum.inl ++ [Sum.inr (parName L)] →
        ∃ as', as = pre ++ as' ∧ Domain.ParYield d.toDomain L as' := by
  intro xs as h
  induction h with
  | nil =>
      intro pre L _ hxs
      rcases pre with _ | ⟨b, pre⟩ <;> simp at hxs
  | @prim a zs bs _ ih =>
      intro pre L hL hxs
      rcases pre with _ | ⟨b, pre⟩
      · rw [List.map_nil, List.nil_append] at hxs
        exact absurd (List.cons.inj hxs).1 (by simp)
      · obtain ⟨hab, hz⟩ := List.cons.inj hxs
        obtain ⟨as', has, hpar⟩ := ih pre L hL hz
        refine ⟨as', ?_, hpar⟩
        rw [has, List.cons_append]
        have : a = b := by simpa using hab
        rw [this]
  | @comp c cs zs bs hm _ ih =>
      intro pre L hL hxs
      rcases pre with _ | ⟨b, pre⟩
      · rw [List.map_nil, List.nil_append] at hxs
        obtain ⟨hc, hz⟩ := List.cons.inj hxs
        have hcL : c = parName L := by simpa using hc
        subst hcL
        subst hz
        rw [List.append_nil] at ih
        rcases seqBody_parDom_cases hm with ⟨rfl, hall⟩ | ⟨i, hi, a, xs, hget, rfl⟩ |
          ⟨i, hi, c', xs, hget, e, he, hce, rfl⟩
        · -- the finishing method
          refine ⟨bs, by simp, ?_⟩
          have hbs : bs = [] := by
            have := eq_of_yieldSeq_map_inl (D := (parDom k d).toDomain) ‹_› [] (by simp)
            simpa using this
          subst hbs
          exact Domain.ParYield.done hall
        · -- one action of the `i`-th process
          obtain ⟨L₁, L₂, hLsplit, hlen⟩ := exists_append_cons_of_getI hi
          rw [hget] at hLsplit
          have hxsmem : xs ∈ parEntries d :=
            parEntries_tail (by rw [← hget]; exact getI_mem_parEntries hL hi)
          have hset : L.set i xs = L₁ ++ xs :: L₂ := by
            rw [hLsplit, ← hlen, set_append_cons]
          have hL' : L.set i xs ∈ parCfgs k d := mem_parCfgs_set hL hxsmem
          obtain ⟨as', has, hpar⟩ := ih [a] (L.set i xs) hL' (by simp)
          refine ⟨a :: as', by simpa using has, ?_⟩
          rw [hLsplit]
          rw [hset] at hpar
          exact Domain.ParYield.prim hpar
        · -- one method application of the `i`-th process
          obtain ⟨L₁, L₂, hLsplit, hlen⟩ := exists_append_cons_of_getI hi
          rw [hget] at hLsplit
          have hxsnil : xs = [] :=
            parEntries_cons_inr hTO hreg (by rw [← hget]; exact getI_mem_parEntries hL hi)
          have hbody : (TnDesc.seqBody e.2 ++ xs : ParEntry) ∈ parEntries d := by
            rw [hxsnil, List.append_nil]
            exact parEntries_body he
          have hset : L.set i (TnDesc.seqBody e.2 ++ xs) =
              L₁ ++ (TnDesc.seqBody e.2 ++ xs) :: L₂ := by
            rw [hLsplit, ← hlen, set_append_cons]
          have hL' : L.set i (TnDesc.seqBody e.2 ++ xs) ∈ parCfgs k d :=
            mem_parCfgs_set hL hbody
          obtain ⟨as', has, hpar⟩ := ih [] (L.set i (TnDesc.seqBody e.2 ++ xs)) hL' (by simp)
          refine ⟨as', by simpa using has, ?_⟩
          rw [hLsplit]
          rw [hset] at hpar
          refine Domain.ParYield.comp ?_ hpar
          exact (seqBody_iff_mem hTO).2 ⟨e, he, hce, rfl⟩
      · rw [List.map_cons, List.cons_append] at hxs
        exact absurd (List.cons.inj hxs).1 (by simp)

/-- **The refinements of a configuration name are exactly the parallel refinements of the
configuration.** -/
theorem yieldSeq_parDom_iff (hTO : d.MethodsTO) (hreg : d.MethodsReg) {L : ParCfg}
    (hL : L ∈ parCfgs k d) {as : List ℕ} :
    (parDom k d).toDomain.YieldSeq [Sum.inr (parName L)] as ↔
      Domain.ParYield d.toDomain L as := by
  constructor
  · intro h
    obtain ⟨as', has, hpar⟩ := parYield_of_yieldSeq_aux hTO hreg h [] L hL (by simp)
    rw [has, List.nil_append]
    exact hpar
  · intro h
    exact yieldSeq_parDom_of_parYield hTO hreg h hL

/-! ### The correctness theorems -/

/-- **The compiled instance has exactly the refinements of the source instance**, as long as the
initial configuration is one of the configurations of the compiled domain. -/
theorem netYield_parInst_iff (hTO : d.MethodsTO) (hreg : d.MethodsReg) {q : InstDesc}
    (hq : q.IsParLe k)
    (hcfg : (q.tnI.compoundNames.map fun c => [Sum.inr c]) ∈ parCfgs k d) {as : List ℕ} :
    (parDom k d).toDomain.NetYield (parInst q).tnI.toTaskNetwork as ↔
      d.toDomain.NetYield q.tnI.toTaskNetwork as := by
  rw [parInst_tnI, netYield_singleTn_iff_yieldSeq (parDom_methodsTO k d),
    yieldSeq_parDom_iff hTO hreg hcfg]
  conv_rhs => rw [hq.1]
  rw [netYield_netTn_iff_parYield hTO]

/-- **Correctness of the parallel product construction**: for a totally ordered regular source
domain and a source instance whose initial task network is an unordered network of at most `k`
compound tasks, the compiled problem — a *rooted* problem over a totally ordered regular
domain — is solvable exactly when the source problem is. -/
theorem solvable_par_iff (hTO : d.MethodsTO) (hreg : d.MethodsReg) {q : InstDesc}
    (hq : q.IsParLe k) : Solvable (parDom k d) (parInst q) ↔ Solvable d q := by
  by_cases hcfg : (q.tnI.compoundNames.map fun c => [Sum.inr c]) ∈ parCfgs k d
  · rw [Solvable, Solvable, Problem.solvable_iff_netYield, Problem.solvable_iff_netYield]
    exact exists_congr fun as => and_congr (netYield_parInst_iff hTO hreg hq hcfg) Iff.rfl
  · -- the network names a compound task the source domain never decomposes
    obtain ⟨c, hcw, hcd⟩ := exists_dead_of_notMem_parCfgs hq.2 hcfg
    have hsrc : ¬ Solvable d q := by
      obtain ⟨i, hi, hlab⟩ := TnDesc.mem_compoundNames.1 hcw
      exact not_solvable_of_dead_task (t := i) (c := c)
        (by simpa using hi) (by simpa using hlab) hcd
    have htgt : ¬ Solvable (parDom k d) (parInst q) := by
      have hinst : parInst q = (q.initList, q.goalList,
          singleTn (parName (q.tnI.compoundNames.map fun c => [Sum.inr c]))) := rfl
      rw [hinst]
      refine not_solvable_of_rooted_dead (isRooted_singleTn _ _ _) ?_
      rw [rootName_singleTn]
      exact fun hmem => hcfg (mem_parCfgs_of_mem_heads hmem)
    exact iff_of_false htgt hsrc

/-- The compiled instance is rooted. -/
theorem isRooted_parInst (q : InstDesc) : (parInst q).IsRooted :=
  isRooted_singleTn _ _ _


end Syn

end HTN
