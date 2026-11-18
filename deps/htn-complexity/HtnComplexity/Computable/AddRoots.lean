import HtnComplexity.Computable.AddRoot
import HtnComplexity.Computable.Window
/-!
# Adding a *family* of fresh root methods

`HtnComplexity/Computable/AddRoot.lean` adds one method for one fresh compound name, whose
body is fixed in advance.  A compilation whose source instance carries a task *network* — not a
single compound task — needs a whole family: the instance translation names the root by an
encoding of the network it has to root, and the domain translation, which does not see the
instance, supplies one method for **every** network that could arise.

This file provides that step:

* `HTN.Syn.addRootsDom L d` — the domain description `d` with the extra methods `L`;
* `HTN.Syn.solvable_addRoots_iff` — if the heads of `L` occur nowhere in `d` and in no body of
  `L`, and `L` lists only one method for `r`, then the problem rooted at `r` is solvable exactly
  when the problem whose initial task network is the body of `r` is.

The proof is the one of `HTN.Syn.solvable_addRoot_iff`, run once more at the level of the
family: from a rooted instance, the only reachable method whose head is one of the fresh names
is the method of the root itself, so all the other fresh methods may be dropped
(`HTN.Problem.solvable_withMethods_iff`) and the single-root theorem applies.
-/

namespace HTN

namespace Syn

/-- The domain description `d`, extended by the list of methods `L`. -/
def addRootsDom (L : List MethodDesc) (d : DomDesc) : DomDesc := (d.actions, d.methods ++ L)

variable {d : DomDesc} {L : List MethodDesc} {r : ℕ} {b : TnDesc} {I G : List ℕ}

@[simp] lemma addRootsDom_actions : (addRootsDom L d).actions = d.actions := rfl

@[simp] lemma addRootsDom_methods : (addRootsDom L d).methods = d.methods ++ L := rfl

/-- The fresh names the family introduces. -/
def rootHeads (L : List MethodDesc) : List ℕ := L.map Prod.fst

lemma mem_rootHeads {p : MethodDesc} (hp : p ∈ L) : p.1 ∈ rootHeads L :=
  List.mem_map_of_mem hp

/-- A method of the extension whose head is not a fresh name is a method of `d`. -/
lemma mem_of_notMem_rootHeads {e : MethodDesc} (he : e ∈ (addRootsDom L d).methods)
    (h : e.1 ∉ rootHeads L) : e ∈ d.methods := by
  rw [addRootsDom_methods, List.mem_append] at he
  rcases he with h1 | h2
  · exact h1
  · exact absurd (mem_rootHeads h2) h

lemma mem_rootHeads_of_root (hmem : (r, b) ∈ L) : r ∈ rootHeads L := mem_rootHeads hmem

/-- **Only the root's own method is reachable among the fresh ones.** -/
theorem reachableName_addRoots (hheads : ∀ e ∈ d.methods, e.1 ∉ rootHeads L)
    (hbodies : ∀ e ∈ d.methods, ∀ c ∈ rootHeads L, c ∉ e.2.compoundNames)
    (hroots : ∀ p ∈ L, ∀ c ∈ rootHeads L, c ∉ p.2.compoundNames)
    (huniq : ∀ p ∈ L, p.1 = r → p.2 = b) (hmem : (r, b) ∈ L) {c : ℕ}
    (hc : (problem (addRootsDom L d) (I, G, singleTn r)).ReachableName c) :
    c = r ∨ c ∉ rootHeads L := by
  induction hc with
  | @tnI t c ht hlab =>
    have hT : t ∈ ({0} : Finset ℕ) := by
      have h : t ∈ (singleTn r).toTaskNetwork.T := ht
      rwa [singleTn_toTaskNetwork_T] at h
    have ht0 : t = 0 := by simpa using hT
    subst ht0
    have h : (singleTn r).toTaskNetwork.α 0 = Sum.inr c := hlab
    rw [singleTn_toTaskNetwork_α] at h
    exact Or.inl (Sum.inr.inj h).symm
  | @method m t c hm _ ht hlab ih =>
    obtain ⟨e, he, rfl⟩ := hm
    have ht' : t ∈ e.2.ids := by
      have h : t ∈ e.2.toTaskNetwork.T := ht
      rwa [TnDesc.toTaskNetwork_T, List.mem_toFinset] at h
    have hlab' : e.2.label t = Sum.inr c := by
      have h : e.2.toTaskNetwork.α t = Sum.inr c := hlab
      rwa [TnDesc.toTaskNetwork_α] at h
    have hmemc : c ∈ e.2.compoundNames := TnDesc.mem_compoundNames.2 ⟨t, ht', hlab'⟩
    refine Or.inr ?_
    have h1 : e.1 = r ∨ e.1 ∉ rootHeads L := by simpa using ih
    rcases h1 with h1 | h1
    · -- the head of the method is the root, so the method is the root's own one
      have heL : e ∈ L := by
        rw [addRootsDom_methods, List.mem_append] at he
        rcases he with h | h
        · exact absurd (h1 ▸ mem_rootHeads_of_root hmem) (hheads e h)
        · exact h
      have hb : e.2 = b := huniq e heL h1
      intro hcr
      exact hroots e heL c hcr hmemc
    · have hed : e ∈ d.methods := mem_of_notMem_rootHeads he h1
      intro hcr
      exact hbodies e hed c hcr hmemc

/-- **The rooting theorem for a family of fresh methods.** -/
theorem solvable_addRoots_iff (hheads : ∀ e ∈ d.methods, e.1 ∉ rootHeads L)
    (hbodies : ∀ e ∈ d.methods, ∀ c ∈ rootHeads L, c ∉ e.2.compoundNames)
    (hroots : ∀ p ∈ L, ∀ c ∈ rootHeads L, c ∉ p.2.compoundNames)
    (huniq : ∀ p ∈ L, p.1 = r → p.2 = b) (hmem : (r, b) ∈ L) :
    Solvable (addRootsDom L d) (I, G, singleTn r) ↔ Solvable d (I, G, b) := by
  have hrmem : r ∈ rootHeads L := mem_rootHeads_of_root hmem
  have hhead' : ∀ e ∈ d.methods, e.1 ≠ r := fun e he hc => hheads e he (hc ▸ hrmem)
  have hbodies' : ∀ e ∈ d.methods, r ∉ e.2.compoundNames := fun e he => hbodies e he r hrmem
  have hb : r ∉ b.compoundNames := hroots (r, b) hmem r hrmem
  have hsub : {m : Method ℕ ℕ ℕ | ∃ e ∈ (addRootDom r b d).methods, e.toMethod = m} ⊆
      (problem (addRootsDom L d) (I, G, singleTn r)).methods := by
    rintro m ⟨e, he, rfl⟩
    rw [addRootDom_methods, List.mem_append] at he
    refine ⟨e, ?_, rfl⟩
    rw [addRootsDom_methods, List.mem_append]
    rcases he with h | h
    · exact Or.inl h
    · have : e = (r, b) := by simpa using h
      exact Or.inr (this ▸ hmem)
  have hreach : ∀ m, (problem (addRootsDom L d) (I, G, singleTn r)).ReachableMethod m →
      m ∈ {m : Method ℕ ℕ ℕ | ∃ e ∈ (addRootDom r b d).methods, e.toMethod = m} := by
    rintro m ⟨⟨e, he, rfl⟩, hrn⟩
    rcases reachableName_addRoots hheads hbodies hroots huniq hmem hrn with h | h
    · have heL : e ∈ L := by
        rw [addRootsDom_methods, List.mem_append] at he
        rcases he with h' | h'
        · have h1 : e.1 = r := by simpa using h
          exact absurd (h1 ▸ hrmem) (hheads e h')
        · exact h'
      have heq : e = (r, b) := by
        have h2 : e.2 = b := huniq e heL (by simpa using h)
        exact Prod.ext (by simpa using h) h2
      exact ⟨e, by rw [addRootDom_methods, List.mem_append]; exact Or.inr (by simp [heq]), rfl⟩
    · have hed : e ∈ d.methods := mem_of_notMem_rootHeads he (by simpa using h)
      exact ⟨e, by rw [addRootDom_methods, List.mem_append]; exact Or.inl hed, rfl⟩
  have h := Problem.solvable_withMethods_iff
    (P := problem (addRootsDom L d) (I, G, singleTn r)) hsub hreach
  have hp : (problem (addRootsDom L d) (I, G, singleTn r)).withMethods
      {m : Method ℕ ℕ ℕ | ∃ e ∈ (addRootDom r b d).methods, e.toMethod = m} =
      problem (addRootDom r b d) (I, G, singleTn r) := rfl
  rw [hp] at h
  have h2 : Solvable (addRootDom r b d) (addRootInst r ((I, G, singleTn r) : InstDesc)) ↔
      Solvable d (I, G, b) := solvable_addRoot_iff hhead' hbodies' hb
  have h3 : addRootInst r ((I, G, singleTn r) : InstDesc) = ((I, G, singleTn r) : InstDesc) := rfl
  rw [h3] at h2
  exact h.symm.trans h2

/-! ### A dead root -/

lemma isRooted_singleTn (I G : List ℕ) (r : ℕ) :
    InstDesc.IsRooted ((I, G, singleTn r) : InstDesc) :=
  ⟨0, r, singleTn_toTaskNetwork_T, singleTn_toTaskNetwork_α⟩

@[simp] lemma compoundNames_singleTn (r : ℕ) : (singleTn r).compoundNames = [r] := by
  simp [singleTn, TnDesc.compoundNames, TnDesc.ids, TnDesc.labelList, TnDesc.lbl]

@[simp] lemma rootName_singleTn (I G : List ℕ) (r : ℕ) :
    rootName ((I, G, singleTn r) : InstDesc) = r := by
  show (singleTn r).compoundNames.headI = r
  simp

@[simp] lemma addRootsDom_heads : (addRootsDom L d).heads = d.heads ++ rootHeads L := by
  simp [DomDesc.heads, rootHeads]

/-- A rooted instance whose root name heads no method of the extension is unsolvable. -/
theorem not_solvable_addRoots_of_dead (hr : r ∉ d.heads) (hrL : r ∉ rootHeads L) :
    ¬ Solvable (addRootsDom L d) (I, G, singleTn r) := by
  refine not_solvable_of_rooted_dead (isRooted_singleTn I G r) ?_
  rw [rootName_singleTn, addRootsDom_heads, List.mem_append]
  tauto

end Syn

end HTN
