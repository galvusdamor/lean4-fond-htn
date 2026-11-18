import HtnComplexity.Complexity.TOPlan.Loop
/-!
# A totally ordered regular instance is a deterministic prefix and at most one compound task

For a domain description with totally ordered methods and a totally ordered, **regular**
instance description (the instances of `TO-HTN-REG`), the linearised initial task sequence is a
word of primitive tasks followed by at most one compound task
(`HTN.Syn.RegTO.seqBody_split`).  The primitive tasks act on states as partial *functions*, so
the automaton of `HtnComplexity/Complexity/TOPlan/Sem.lean` runs along the prefix
deterministically (`HTN.Syn.RegTO.run_optSet_prims`): its set of projected states stays empty
or a singleton, computed by `HTN.Syn.RegTO.exec`.

* `HTN.Syn.RegTO.solvable_iff_of_profile` — **solvability is a function of a short profile**:
  the projected state after the prefix (or the information that the prefix is not executable),
  which method head the final compound task carries (and whether there is one), the goal facts of
  the vocabulary, and the goal facts outside the vocabulary.
-/

namespace HTN

namespace Syn

namespace RegTO

open TOPlan Classical

variable {d : DomDesc}

/-- The precondition list of an action, as described (empty for an unmentioned action). -/
def precL (d : DomDesc) (a : ℕ) : List ℕ := (d.actions.lookup a).elim [] fun x => x.1

/-- The add list of an action. -/
def addL (d : DomDesc) (a : ℕ) : List ℕ := (d.actions.lookup a).elim [] fun x => x.2.1

/-- The delete list of an action. -/
def delL (d : DomDesc) (a : ℕ) : List ℕ := (d.actions.lookup a).elim [] fun x => x.2.2

/-- **Deterministic execution** of one letter on a projected state: a primitive task is executed
if it is applicable (otherwise the run dies), a compound task is ignored. -/
noncomputable def exec (d : DomDesc) : Option (Finset ℕ) → ℕ ⊕ ℕ → Option (Finset ℕ)
  | none, _ => none
  | some s, Sum.inl a =>
      if ∀ f ∈ precL d a, f ∈ s then some (s.filter (· ∉ delL d a) ∪ (addL d a).toFinset)
      else none
  | some s, Sum.inr _ => some s

/-- The set of projected states described by an optional state. -/
def optSet : Option (Finset ℕ) → Finset (Finset ℕ)
  | none => ∅
  | some s => {s}

theorem addL_subset_vocab (a : ℕ) : ∀ f ∈ addL d a, f ∈ vocab d := by
  intro f hf
  unfold addL at hf
  rcases h : d.actions.lookup a with _ | e
  · rw [h] at hf; simp at hf
  · rw [h] at hf
    exact mem_vocab_of_lookup h (by simp at hf ⊢; tauto)

theorem exec_subset {o : Option (Finset ℕ)} (ho : ∀ s, o = some s → s ⊆ vocab d) (x : ℕ ⊕ ℕ) :
    ∀ s, exec d o x = some s → s ⊆ vocab d := by
  intro s hs
  rcases o with _ | s0
  · simp [exec] at hs
  · rcases x with a | c
    · simp only [exec] at hs
      split_ifs at hs with h
      cases hs
      intro f hf
      rcases Finset.mem_union.1 hf with h1 | h1
      · exact ho s0 rfl (Finset.mem_filter.1 h1).1
      · exact addL_subset_vocab a f (List.mem_toFinset.1 h1)
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      exact ho s0 rfl

theorem transition_eq (a : ℕ) (s : Finset ℕ) :
    d.toDomain.toActionModel.transition a ↑s =
      ↑(s.filter (· ∉ delL d a) ∪ (addL d a).toFinset) := by
  ext f
  simp [ActionModel.transition, DomDesc.toDomain_del, DomDesc.toDomain_add, DomDesc.del,
    DomDesc.add, delL, addL]

/-- **The one-letter relation of a primitive task** is the partial function `exec`. -/
theorem rel_inl_iff (a : ℕ) (s u : Finset ℕ) :
    rel d (Sum.inl a) s u ↔ exec d (some s) (Sum.inl a) = some u := by
  rw [rel]
  have happ : d.toDomain.toActionModel.Applicable a ↑s ↔ ∀ f ∈ precL d a, f ∈ s := by
    simp [ActionModel.Applicable, DomDesc.toDomain_prec, DomDesc.prec, precL, Set.subset_def]
  constructor
  · intro h
    cases h with
    | prim hap hs =>
      rw [seqReach_nil_iff', transition_eq] at hs
      simp only [exec, if_pos (happ.1 hap)]
      exact congrArg some (Finset.coe_injective hs).symm
  · intro h
    simp only [exec] at h
    split_ifs at h with hp
    cases h
    refine .prim (happ.2 hp) ?_
    rw [transition_eq]
    exact .nil

theorem step_empty (x : ℕ ⊕ ℕ) : step d ∅ x = ∅ := by
  ext u; simp [step]

/-- **One primitive step of the automaton from an optional state.** -/
theorem step_optSet {o : Option (Finset ℕ)} (ho : ∀ s, o = some s → s ⊆ vocab d) (a : ℕ) :
    step d (optSet o) (Sum.inl a) = optSet (exec d o (Sum.inl a)) := by
  rcases o with _ | s
  · simp [optSet, exec, step_empty]
  · ext u
    simp only [step, optSet, Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
      exists_eq_left, rel_inl_iff]
    constructor
    · rintro ⟨-, h⟩
      rw [h]; simp
    · intro h
      rcases he : exec d (some s) (Sum.inl a) with _ | u'
      · rw [he] at h; simp at h
      · rw [he] at h
        simp only [Finset.mem_singleton] at h
        subst h
        exact ⟨exec_subset ho _ _ he, rfl⟩

/-- **The run along a primitive word is deterministic.** -/
theorem run_optSet_prims : ∀ (as : List ℕ) (o : Option (Finset ℕ)),
    (∀ s, o = some s → s ⊆ vocab d) →
      run d (optSet o) (as.map Sum.inl) = optSet ((as.map Sum.inl).foldl (exec d) o) := by
  intro as
  induction as with
  | nil => intro o _; rfl
  | cons a as ih =>
    intro o ho
    show run d (step d (optSet o) (Sum.inl a)) (as.map Sum.inl) = _
    rw [step_optSet ho]
    exact ih _ (exec_subset ho _)

/-! ### The shape of a totally ordered regular network -/

/-- **A totally ordered regular network linearises to a primitive word and at most one compound
task**, and the compound task (if any) is the only identifier carrying a compound label. -/
theorem seqBody_split {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered)
    (hreg : t.toTaskNetwork.IsRegular) :
    ∃ (as : List ℕ) (tl : List (ℕ ⊕ ℕ)), TnDesc.seqBody t = as.map Sum.inl ++ tl ∧
      (tl = [] ∨ ∃ c, tl = [Sum.inr c]) ∧
      ∀ c, (∃ u ∈ t.ids, t.label u = Sum.inr c) ↔ tl = [Sum.inr c] := by
  set L := TnDesc.lin t with hL
  have hlin := TnDesc.isLinearization_lin hTO
  have hmem : ∀ u, u ∈ L ↔ u ∈ t.ids := fun u => TnDesc.mem_lin hTO
  -- every compound identifier is the last element
  have hlast : ∀ i (hi : i < L.length), (∃ c, t.label L[i] = Sum.inr c) → i + 1 = L.length := by
    intro i hi ⟨c, hc⟩
    by_contra hne
    have hi1 : i + 1 < L.length := by omega
    have hab : t.toTaskNetwork.IsAbstractId L[i] := ⟨c, hc⟩
    have hTi : L[i] ∈ t.toTaskNetwork.T := (hlin.2.1 _).1 (List.getElem_mem hi)
    have hTj : L[i+1] ∈ t.toTaskNetwork.T := (hlin.2.1 _).1 (List.getElem_mem hi1)
    have hne' : L[i+1] ≠ L[i] := by
      intro h
      have := (hlin.1.getElem_inj_iff (hi := hi1) (hj := hi)).1 h
      omega
    have hord := hreg.2 _ hTi hab _ hTj hne'
    exact (List.pairwise_iff_getElem.1 hlin.2.2) i (i + 1) hi hi1 (by omega) hord
  -- the primitive word: all but possibly the last letter
  have hprim : ∀ u ∈ L.dropLast, ∃ a, t.label u = Sum.inl a := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hu
    rw [List.getElem_dropLast]
    have hi' : i < L.length := by simp at hi; omega
    rcases h : t.label L[i] with a | c
    · exact ⟨a, rfl⟩
    · have := hlast i hi' ⟨c, h⟩
      simp at hi; omega
  let actOf : ℕ ⊕ ℕ → ℕ := fun x => match x with | Sum.inl a => a | Sum.inr _ => 0
  have hpre : L.dropLast.map t.label = (L.dropLast.map (fun u => actOf (t.label u))).map Sum.inl := by
    rw [List.map_map]
    refine List.map_congr_left fun u hu => ?_
    obtain ⟨a, ha⟩ := hprim u hu
    simp [ha, actOf]
  rcases hLe : L.getLast? with _ | w
  · -- empty network
    have hL0 : L = [] := List.getLast?_eq_none_iff.1 hLe
    refine ⟨[], [], ?_, Or.inl rfl, fun c => ?_⟩
    · simp [TnDesc.seqBody, ← hL, hL0]
    · refine iff_of_false ?_ (by simp)
      rintro ⟨u, hu, -⟩
      have := (hmem u).2 hu
      rw [hL0] at this; simp at this
  · have hsplit : L = L.dropLast ++ [w] := (List.dropLast_append_getLast? (l := L) (a := w) hLe).symm
    have hw : w ∈ L := List.mem_of_getLast? hLe
    have hbody : TnDesc.seqBody t = L.dropLast.map t.label ++ [t.label w] := by
      simp only [TnDesc.seqBody, ← hL]
      conv_lhs => rw [hsplit]
      simp
    -- an identifier with a compound label is `w`
    have honly : ∀ u ∈ t.ids, ∀ c, t.label u = Sum.inr c → u = w := by
      intro u hu c hc
      have huL := (hmem u).2 hu
      rw [hsplit] at huL
      rcases List.mem_append.1 huL with h | h
      · obtain ⟨a, ha⟩ := hprim u h
        rw [ha] at hc; cases hc
      · exact List.mem_singleton.1 h
    rcases hwl : t.label w with a | c
    · refine ⟨L.dropLast.map (fun u => actOf (t.label u)) ++ [a], [], ?_, Or.inl rfl, fun c => ?_⟩
      · rw [hbody, hpre, hwl]; simp
      · refine iff_of_false ?_ (by simp)
        rintro ⟨u, hu, hc⟩
        have := honly u hu c hc
        subst this
        rw [hwl] at hc; cases hc
    · refine ⟨L.dropLast.map (fun u => actOf (t.label u)), [Sum.inr c], ?_, Or.inr ⟨c, rfl⟩,
        fun c' => ?_⟩
      · rw [hbody, hpre, hwl]
      · simp only [List.cons.injEq, Sum.inr.injEq, and_true]
        constructor
        · rintro ⟨u, hu, hc'⟩
          have := honly u hu c' hc'
          subst this
          rw [hwl] at hc'; cases hc'; rfl
        · rintro rfl
          exact ⟨w, (hmem w).1 hw, hwl⟩

/-! ### Solvability is a function of the profile -/

/-- The final optional projected state of an instance: the deterministic execution of its
linearised task sequence from the initial projected state (compound tasks are ignored). -/
noncomputable def finalOpt (d : DomDesc) (q : InstDesc) : Option (Finset ℕ) :=
  (TnDesc.seqBody q.tnI).foldl (exec d) (some (initProj d q))

theorem foldl_exec_none (xs : List (ℕ ⊕ ℕ)) : xs.foldl (exec d) none = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [exec] using ih

theorem initProj_subset (q : InstDesc) : ∀ s, some (initProj d q) = some s → s ⊆ vocab d := by
  intro s hs
  cases hs
  exact Finset.filter_subset _ _

theorem run_tail_eq {S : Finset (Finset ℕ)} {tl₁ tl₂ : List (ℕ ⊕ ℕ)}
    (h₁ : tl₁ = [] ∨ ∃ c, tl₁ = [Sum.inr c]) (h₂ : tl₂ = [] ∨ ∃ c, tl₂ = [Sum.inr c])
    (hnil : tl₁ = [] ↔ tl₂ = [])
    (hc : ∀ c ∈ heads d, (tl₁ = [Sum.inr c] ↔ tl₂ = [Sum.inr c])) :
    run d S tl₁ = run d S tl₂ := by
  rcases h₁ with rfl | ⟨c₁, rfl⟩
  · rw [hnil.1 rfl]
  · rcases h₂ with rfl | ⟨c₂, rfl⟩
    · exact absurd (hnil.2 rfl) (by simp)
    · by_cases hc₁ : c₁ ∈ heads d
      · have := (hc c₁ hc₁).1 rfl
        simp only [List.cons.injEq, Sum.inr.injEq, and_true] at this
        rw [this]
      · by_cases hc₂ : c₂ ∈ heads d
        · have := (hc c₂ hc₂).2 rfl
          simp only [List.cons.injEq, Sum.inr.injEq, and_true] at this
          exact absurd (this ▸ hc₂) hc₁
        · show step d S (Sum.inr c₁) = step d S (Sum.inr c₂)
          rw [← step_clsOf, ← step_clsOf (x := Sum.inr c₂)]
          simp [clsOf, hc₁, hc₂]

/-- **Solvability of a totally ordered regular instance is a function of its profile.** -/
theorem solvable_iff_of_profile (hTO : d.MethodsTO) {q₁ q₂ : InstDesc} (h₁ : q₁.IsTO)
    (h₁r : q₁.IsRegular) (h₂ : q₂.IsTO) (h₂r : q₂.IsRegular)
    (ho : finalOpt d q₁ = finalOpt d q₂)
    (hany : (∃ u ∈ q₁.tnI.ids, ∃ c, q₁.tnI.label u = Sum.inr c) ↔
      (∃ u ∈ q₂.tnI.ids, ∃ c, q₂.tnI.label u = Sum.inr c))
    (hc : ∀ c ∈ heads d, ((∃ u ∈ q₁.tnI.ids, q₁.tnI.label u = Sum.inr c) ↔
      (∃ u ∈ q₂.tnI.ids, q₂.tnI.label u = Sum.inr c)))
    (hg : ∀ f ∈ vocab d, (f ∈ q₁.goalList ↔ f ∈ q₂.goalList))
    (hout : OutOk d q₁ ↔ OutOk d q₂) :
    Solvable d q₁ ↔ Solvable d q₂ := by
  obtain ⟨as₁, tl₁, hb₁, ht₁, hct₁⟩ := seqBody_split h₁ h₁r
  obtain ⟨as₂, tl₂, hb₂, ht₂, hct₂⟩ := seqBody_split h₂ h₂r
  have hrun : ∀ (q : InstDesc) (as : List ℕ) (tl : List (ℕ ⊕ ℕ)),
      TnDesc.seqBody q.tnI = as.map Sum.inl ++ tl →
      run d {initProj d q} (TnDesc.seqBody q.tnI) =
        run d (optSet ((as.map Sum.inl).foldl (exec d) (some (initProj d q)))) tl := by
    intro q as tl hb
    rw [hb]
    show (as.map Sum.inl ++ tl).foldl (step d) {initProj d q} = _
    rw [List.foldl_append]
    show run d (run d (optSet (some (initProj d q))) (as.map Sum.inl)) tl = _
    rw [run_optSet_prims as _ (initProj_subset q)]
  have hfin : ∀ (q : InstDesc) (as : List ℕ) (tl : List (ℕ ⊕ ℕ)),
      TnDesc.seqBody q.tnI = as.map Sum.inl ++ tl → (tl = [] ∨ ∃ c, tl = [Sum.inr c]) →
      finalOpt d q = (as.map Sum.inl).foldl (exec d) (some (initProj d q)) := by
    intro q as tl hb ht
    rw [finalOpt, hb, List.foldl_append]
    rcases ht with rfl | ⟨c, rfl⟩
    · rfl
    · rcases ((as.map Sum.inl).foldl (exec d) (some (initProj d q))) with _ | s <;> rfl
  have hnil : tl₁ = [] ↔ tl₂ = [] := by
    constructor
    · intro h
      rcases ht₂ with h2 | ⟨c, rfl⟩
      · exact h2
      · exfalso
        obtain ⟨u, hu, hu'⟩ := (hct₂ c).2 rfl
        obtain ⟨u', hu'', c', hc'⟩ := hany.2 ⟨u, hu, c, hu'⟩
        have := (hct₁ c').1 ⟨u', hu'', hc'⟩
        rw [h] at this; cases this
    · intro h
      rcases ht₁ with h1 | ⟨c, rfl⟩
      · exact h1
      · exfalso
        obtain ⟨u, hu, hu'⟩ := (hct₁ c).2 rfl
        obtain ⟨u', hu'', c', hc'⟩ := hany.1 ⟨u, hu, c, hu'⟩
        have := (hct₂ c').1 ⟨u', hu'', hc'⟩
        rw [h] at this; cases this
  have hcc : ∀ c ∈ heads d, (tl₁ = [Sum.inr c] ↔ tl₂ = [Sum.inr c]) := fun c hcd => by
    rw [← hct₁, ← hct₂]; exact hc c hcd
  have hS : run d {initProj d q₁} (TnDesc.seqBody q₁.tnI) =
      run d {initProj d q₂} (TnDesc.seqBody q₂.tnI) := by
    rw [hrun q₁ as₁ tl₁ hb₁, hrun q₂ as₂ tl₂ hb₂, run_tail_eq ht₁ ht₂ hnil hcc,
      ← hfin q₁ as₁ tl₁ hb₁ ht₁, ← hfin q₂ as₂ tl₂ hb₂ ht₂, ho]
  rw [solvable_iff_run hTO h₁, solvable_iff_run hTO h₂, hS, hout]
  refine and_congr_left fun _ => ?_
  simp only [Accepts]
  refine exists_congr fun u => and_congr_right fun _ => ?_
  exact forall₂_congr fun f hf => imp_congr_left (hg f hf)

end RegTO

end Syn

end HTN
