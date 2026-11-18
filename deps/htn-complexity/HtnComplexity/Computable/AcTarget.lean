import HtnPlanning.Interleave.NetYield
import HtnComplexity.Computable.StripsTarget
/-!
# The doubling hierarchy: described acyclic totally ordered problems

A compilation into the class `TO-HTN-AC` cannot use a recursive hierarchy, so the number of
actions a plan may contain has to be bounded by the *depth* of the hierarchy.  The construction
of `HtnComplexity/ToHtnAc/StripsToAc.lean` — a hierarchy of `K` levels, each of which doubles the
number of tasks — is redone here for **descriptions**:

```
c_i ⟶ c_{i+1} c_{i+1}   (i < K)
c_K ⟶ a                 (for every offered action a)
c_K ⟶ ε
```

* `HTN.Syn.acDom acts K Acts` — the domain description with the actions `acts` and this
  hierarchy;
* `HTN.Syn.acDom_methodsTO`, `HTN.Syn.acDom_isAcyclic` — it belongs to the class `TO-HTN-AC`;
* `HTN.Syn.netYield_level` — the single compound task `c_i` refines into *every* sequence of at
  most `2 ^ (K - i)` offered actions;
* `HTN.Syn.solvable_acDom_of_plan` — hence the described problem is solvable whenever a short
  plan over the offered actions reaches the goal.

The refinement is built with the structural rules for refinements of a task network of
`HtnPlanning/Interleave/NetYield.lean`, which hold for an arbitrary type of task identifiers.
-/

namespace HTN

namespace Syn

open TaskNetwork

/-! ### The bodies of the hierarchy -/

/-- The described body `c c` of a splitting method. -/
def splitBody (c : ℕ) : TnDesc := ([0, 1], [(0, 1)], [(0, true, c), (1, true, c)])

/-- The described body consisting of the single action `a`. -/
def leafBody (a : ℕ) : TnDesc := ([0], [], [(0, false, a)])

/-- The task network with the single task `i` labelled `x`. -/
def unitNet (i : ℕ) (x : ℕ ⊕ ℕ) : TaskNetwork ℕ ℕ ℕ where
  T := {i}
  ord := fun _ _ => False
  α := fun _ => x

theorem unitNet_isSingle (i : ℕ) (x : ℕ ⊕ ℕ) : IsSingle (unitNet i x) i where
  memT := by intro y; simp [unitNet]
  ord := by intro a b h; exact h

theorem unitNet_wf (i : ℕ) (x : ℕ ⊕ ℕ) : (unitNet i x).WF where
  mem_left := by intro a b h; exact absurd h (by simp [unitNet])
  mem_right := by intro a b h; exact absurd h (by simp [unitNet])
  irrefl := by intro a h; exact h
  trans := by intro a b c h _; exact h

@[simp] theorem unitNet_α (i : ℕ) (x : ℕ ⊕ ℕ) (y : ℕ) : (unitNet i x).α y = x := rfl

/-- The leaf body is a single task labelled by its action. -/
theorem leafBody_isSingle (a : ℕ) : IsSingle (leafBody a).toTaskNetwork 0 where
  memT := by intro y; simp [leafBody, TnDesc.ids]
  ord := by
    intro x y h
    obtain ⟨-, -, hpre, -⟩ := h
    induction hpre with
    | single hxy => simp [TnDesc.listRel, leafBody, TnDesc.ordList] at hxy
    | tail _ hbc _ => simp [TnDesc.listRel, leafBody, TnDesc.ordList] at hbc

@[simp] theorem leafBody_α (a : ℕ) : (leafBody a).toTaskNetwork.α 0 = Sum.inl a := rfl

@[simp] theorem emptyBody_toTaskNetwork_T : emptyBody.toTaskNetwork.T = ∅ := rfl

/-- The ordering described by a splitting body. -/
theorem preOrd_splitBody {c x y : ℕ} : (splitBody c).preOrd x y ↔ (x = 0 ∧ y = 1) := by
  constructor
  · intro h
    induction h with
    | single hxy => simpa [TnDesc.listRel, splitBody, TnDesc.ordList, Prod.ext_iff] using hxy
    | tail _ hbc ih =>
      obtain ⟨rfl, rfl⟩ := ih
      simp [TnDesc.listRel, splitBody, TnDesc.ordList, Prod.ext_iff] at hbc
  · rintro ⟨rfl, rfl⟩
    exact Relation.TransGen.single (by simp [TnDesc.listRel, splitBody, TnDesc.ordList])

theorem splitBody_ord {c x y : ℕ} :
    (splitBody c).toTaskNetwork.ord x y ↔ (x = 0 ∧ y = 1) := by
  rw [TnDesc.toTaskNetwork_ord]
  constructor
  · rintro ⟨-, -, h, -⟩
    exact preOrd_splitBody.1 h
  · rintro ⟨rfl, rfl⟩
    refine ⟨by simp [splitBody, TnDesc.ids], by simp [splitBody, TnDesc.ids],
      preOrd_splitBody.2 ⟨rfl, rfl⟩, fun h => ?_⟩
    simpa using preOrd_splitBody.1 h

/-- **A splitting body is the sequential composition of two copies of the next level.** -/
theorem splitBody_isSeries (c : ℕ) :
    IsSeries (splitBody c).toTaskNetwork (unitNet 0 (Sum.inr c)) (unitNet 1 (Sum.inr c)) where
  disjoint := by simp [unitNet]
  memT := by intro t; simp [splitBody, TnDesc.ids, unitNet]
  α₁ := by
    intro t ht
    have : t = 0 := by simpa [unitNet] using ht
    subst this
    rfl
  α₂ := by
    intro t ht
    have : t = 1 := by simpa [unitNet] using ht
    subst this
    rfl
  ord := by
    intro a b
    rw [splitBody_ord]
    simp [unitNet]

/-! ### The hierarchy -/

/-- The methods of the doubling hierarchy of depth `K` over the actions `Acts`. -/
def acMethods (K : ℕ) (Acts : List ℕ) : List MethodDesc :=
  ((List.range K).map fun i => (i, splitBody (i + 1))) ++
    (K, emptyBody) :: Acts.map fun a => (K, leafBody a)

/-- **The doubling domain description.** -/
def acDom (acts : List ActionDesc) (K : ℕ) (Acts : List ℕ) : DomDesc := (acts, acMethods K Acts)

@[simp] theorem acDom_actions (acts : List ActionDesc) (K : ℕ) (Acts : List ℕ) :
    (acDom acts K Acts).actions = acts := rfl

@[simp] theorem acDom_methods (acts : List ActionDesc) (K : ℕ) (Acts : List ℕ) :
    (acDom acts K Acts).methods = acMethods K Acts := rfl

theorem splitMethod_mem {i K : ℕ} (h : i < K) (Acts : List ℕ) :
    ((i, splitBody (i + 1)) : MethodDesc) ∈ acMethods K Acts :=
  List.mem_append_left _ (List.mem_map_of_mem (by simpa using h))

theorem acEmptyMethod_mem (K : ℕ) (Acts : List ℕ) :
    ((K, emptyBody) : MethodDesc) ∈ acMethods K Acts :=
  List.mem_append_right _ (by simp)

theorem leafMethod_mem {a : ℕ} {Acts : List ℕ} (h : a ∈ Acts) (K : ℕ) :
    ((K, leafBody a) : MethodDesc) ∈ acMethods K Acts :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map_of_mem h))

/-- Every listed method of the doubling hierarchy is one of the three shapes. -/
theorem mem_acMethods {K : ℕ} {Acts : List ℕ} {e : MethodDesc} (he : e ∈ acMethods K Acts) :
    (∃ i < K, e = (i, splitBody (i + 1))) ∨ e = (K, emptyBody) ∨
      ∃ a ∈ Acts, e = (K, leafBody a) := by
  rcases List.mem_append.1 he with he | he
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
    exact Or.inl ⟨i, by simpa using hi, rfl⟩
  · rcases List.mem_cons.1 he with rfl | he
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
      exact Or.inr (Or.inr ⟨a, ha, rfl⟩)

/-! ### The doubling domain belongs to `TO-HTN-AC` -/

theorem acDom_methodsTO (acts : List ActionDesc) (K : ℕ) (Acts : List ℕ) :
    (acDom acts K Acts).MethodsTO := by
  intro e he
  rcases mem_acMethods he with ⟨i, -, rfl⟩ | rfl | ⟨a, -, rfl⟩
  · intro x hx y hy hxy
    have hx' : x = 0 ∨ x = 1 := by simpa [splitBody, TnDesc.ids] using hx
    have hy' : y = 0 ∨ y = 1 := by simpa [splitBody, TnDesc.ids] using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inl (splitBody_ord.2 ⟨rfl, rfl⟩)
    · exact Or.inr (splitBody_ord.2 ⟨rfl, rfl⟩)
    · exact absurd rfl hxy
  · intro x hx
    exact absurd hx (by simp [emptyBody, TnDesc.ids])
  · intro x hx y hy hxy
    have hx' : x = 0 := by simpa [leafBody, TnDesc.ids] using hx
    have hy' : y = 0 := by simpa [leafBody, TnDesc.ids] using hy
    exact absurd (hx'.trans hy'.symm) hxy

theorem acDom_isAcyclic (acts : List ActionDesc) (K : ℕ) (Acts : List ℕ) :
    (acDom acts K Acts).IsAcyclic := by
  refine ⟨fun c => K - c, ?_⟩
  intro e he t ht c hc
  rcases mem_acMethods he with ⟨i, hi, rfl⟩ | rfl | ⟨a, -, rfl⟩
  · have hci : c = i + 1 := by
      have : t = 0 ∨ t = 1 := by
        simpa [splitBody, TnDesc.ids] using ht
      rcases this with rfl | rfl <;> · rw [show (splitBody (i + 1)).toTaskNetwork.α _ =
        Sum.inr (i + 1) from rfl] at hc; exact (Sum.inr_injective hc).symm
    subst hci
    simp only
    omega
  · exact absurd ht (by simp [emptyBody, TnDesc.ids])
  · have ht' : t = 0 := by simpa [leafBody, TnDesc.ids] using ht
    subst ht'
    rw [leafBody_α] at hc
    exact absurd hc (by simp)

/-! ### What the doubling hierarchy refines into -/

section Yield

variable {acts : List ActionDesc} {K : ℕ} {Acts : List ℕ}

/-- Every described body is well formed. -/
theorem acDom_methods_wf :
    ∀ m ∈ (acDom acts K Acts).toDomain.methods, m.subtasks.WF := by
  rintro m ⟨e, -, rfl⟩
  exact e.2.toTaskNetwork_wf

/-- An empty network refines into the empty action sequence. -/
theorem netYieldN_empty {D : Domain ℕ ℕ ℕ ℕ} {tn : TaskNetwork ℕ ℕ ℕ} (h : tn.T = ∅) :
    D.NetYieldN 0 tn [] := by
  refine ⟨tn, StepsN.refl _, ?_, [], ⟨List.nodup_nil, ?_, List.Pairwise.nil⟩, rfl⟩
  · intro x hx
    rw [h] at hx
    exact absurd hx (by simp)
  · intro t
    rw [h]
    simp

/-- **The compound task of level `i` refines into every sequence of at most `2 ^ (K - i)`
offered actions.** -/
theorem netYield_level (n : ℕ) : ∀ i : ℕ, i ≤ K → K - i = n → ∀ as : List ℕ, as.length ≤ 2 ^ n →
    (∀ a ∈ as, a ∈ Acts) → ∀ {tn : TaskNetwork ℕ ℕ ℕ} {t : ℕ}, IsSingle tn t →
      tn.α t = Sum.inr i → (acDom acts K Acts).toDomain.NetYield tn as := by
  induction n with
  | zero =>
    intro i hiK' hi as hlen hus tn t hsingle hα
    have hiK : i = K := by omega
    subst hiK
    -- at the bottom level the plan has at most one action
    rcases as with _ | ⟨a, as⟩
    · refine ⟨1, ?_⟩
      rw [Domain.netYieldN_single_comp hsingle hα acDom_methods_wf]
      exact ⟨0, (⟨i, emptyBody.toTaskNetwork⟩ : Method ℕ ℕ ℕ),
        rfl, ⟨(i, emptyBody), acEmptyMethod_mem i Acts, rfl⟩, rfl, netYieldN_empty rfl⟩
    · have hnil : as = [] := by
        simp only [List.length_cons, pow_zero] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      refine ⟨1, ?_⟩
      rw [Domain.netYieldN_single_comp hsingle hα acDom_methods_wf]
      refine ⟨0, (⟨i, (leafBody a).toTaskNetwork⟩ : Method ℕ ℕ ℕ), rfl,
        ⟨(i, leafBody a), leafMethod_mem (hus a (by simp)) i, rfl⟩, rfl, ?_⟩
      exact (Domain.netYieldN_single_prim (leafBody_isSingle a) (leafBody_α a)).2 ⟨rfl, rfl⟩
  | succ n ih =>
    intro i hiK' hi as hlen hus tn t hsingle hα
    have hiK : i < K := by omega
    have hi' : K - (i + 1) = n := by omega
    -- split the plan in two halves
    obtain ⟨m₁, hy₁⟩ := ih (i + 1) (by omega) hi' (as.take (2 ^ n))
      (by simp only [List.length_take]; omega) (fun a ha => hus a (List.take_subset _ _ ha))
      (unitNet_isSingle 0 (Sum.inr (i + 1))) rfl
    obtain ⟨m₂, hy₂⟩ := ih (i + 1) (by omega) hi' (as.drop (2 ^ n))
      (by simp only [List.length_drop]; rw [pow_succ] at hlen; omega)
      (fun a ha => hus a (List.drop_subset _ _ ha))
      (unitNet_isSingle 1 (Sum.inr (i + 1))) rfl
    refine ⟨m₁ + m₂ + 1, ?_⟩
    rw [Domain.netYieldN_single_comp hsingle hα acDom_methods_wf]
    refine ⟨m₁ + m₂, (⟨i, (splitBody (i + 1)).toTaskNetwork⟩ : Method ℕ ℕ ℕ), rfl,
      ⟨(i, splitBody (i + 1)), splitMethod_mem hiK Acts, rfl⟩, rfl, ?_⟩
    rw [Domain.netYieldN_isSeries_iff (splitBody_isSeries (i + 1))
      (unitNet_wf 0 _) (unitNet_wf 1 _)]
    exact ⟨m₁, m₂, as.take (2 ^ n), as.drop (2 ^ n), rfl, (List.take_append_drop _ _).symm,
      hy₁, hy₂⟩

/-- **A short plan over the offered actions solves the described doubling problem.** -/
theorem solvable_acDom_of_plan (s g : List ℕ) {as : List ℕ} (hlen : as.length ≤ 2 ^ K)
    (hus : ∀ a ∈ as, a ∈ Acts)
    (happ : (acDom acts K Acts).toDomain.SeqApplicable as {f | f ∈ s})
    (hgoal : {f | f ∈ g} ⊆ (acDom acts K Acts).toDomain.transitionSeq as {f | f ∈ s}) :
    Solvable (acDom acts K Acts) (stripsInst s g) := by
  refine Problem.solvable_iff_netYield.2 ⟨as, ?_, happ, hgoal⟩
  have hsingle : IsSingle (problem (acDom acts K Acts) (stripsInst s g)).tnI 0 :=
    ⟨by intro y; simp [initTn, TnDesc.ids], fun x y h =>
      not_preOrd_of_ordList_nil (by rfl) x y h.2.2.1⟩
  exact netYield_level (K - 0) 0 (by omega) rfl as (by simpa using hlen) hus hsingle rfl

end Yield

end Syn

end HTN
