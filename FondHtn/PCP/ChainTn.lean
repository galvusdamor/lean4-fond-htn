import FondHtn.PCP.ChainNet
import FondHtn.Transfer.DetDesc
/-!
# Chain networks as descriptions

`FOND.PCP.chainTn xs oc`: the description of the chain network on the ids `0, …, n-1` with
primitive labels `xs`, followed by the compound label `oc` if any, totally ordered.
-/

namespace FOND

namespace PCP

open HTN HTN.Syn HTN.Article

/-- The listed order: all pairs `i < j < n`. -/
def ltPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range n).filterMap fun j => if i < j then some (i, j) else none

theorem mem_ltPairs {n : ℕ} {q : ℕ × ℕ} : q ∈ ltPairs n ↔ q.1 < q.2 ∧ q.2 < n := by
  obtain ⟨i, j⟩ := q
  simp only [ltPairs, List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, hab, rfl, rfl⟩; exact ⟨hab, hb⟩
  · rintro ⟨hij, hj⟩; exact ⟨i, by omega, j, hj, hij, rfl, rfl⟩

/-- The chain network description. -/
def chainTn (xs : List ℕ) (oc : Option ℕ) : TnDesc :=
  (List.range (xs.length + oc.toList.length), ltPairs (xs.length + oc.toList.length),
    (List.range xs.length).map (fun i => (i, false, xs.getD i 0)) ++
      oc.toList.map fun c => (xs.length, true, c))

theorem lookup_range_map {β : Type} (f : ℕ → β) (k i : ℕ) :
    ((List.range k).map fun j => (j, f j)).lookup i = if i < k then some (f i) else none := by
  induction k with
  | zero => simp [List.lookup]
  | succ k ih =>
    rw [List.range_succ, List.map_append, lookup_append, ih]
    by_cases h : i < k
    · simp [h, show i < k + 1 by omega]
    · by_cases h' : i = k
      · subst h'; simp [List.lookup]
      · have : (i == k) = false := by simp [h']
        simp [h, show ¬ i < k + 1 by omega, List.lookup, this]

theorem chainTn_valid {prim : ℕ → Prop} {xs : List ℕ} (oc : Option ℕ) (hx : ∀ x ∈ xs, prim x) :
    TnValid prim (chainTn xs oc) where
  nodup := List.nodup_range
  ord_mem q hq := by
    have := mem_ltPairs.1 hq
    simp only [chainTn, TnDesc.ids, List.mem_range]; omega
  irrefl a ha := by have := mem_ltPairs.1 ha; simp at this
  trans a b c hab hbc := by
    have h1 := mem_ltPairs.1 hab; have h2 := mem_ltPairs.1 hbc
    exact mem_ltPairs.2 ⟨by simp at h1 h2; omega, by simp at h2; omega⟩
  lbl_perm := by
    cases oc <;> simp [chainTn, TnDesc.lbl, TnDesc.ids, List.map_append, Function.comp_def,
      List.range_succ]
  prim_ok q hq hq' := by
    simp only [chainTn, TnDesc.lbl, List.mem_append, List.mem_map, List.mem_range] at hq
    rcases hq with ⟨i, hi, rfl⟩ | ⟨c, -, rfl⟩
    · exact hx _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)
    · simp at hq'

theorem chainTn_isChainNet (xs : List ℕ) (oc : Option ℕ) :
    IsChainNet (chainTn xs oc).toTaskNetwork xs oc where
  T := by
    ext x; simp [TnDesc.toTaskNetwork, chainTn, TnDesc.ids]
  ord i j := by
    show (chainTn xs oc).ordOf i j ↔ _
    rw [(chainTn_valid (prim := fun _ => True) oc (fun _ _ => trivial)).ordOf_iff]
    exact mem_ltPairs
  lab i hi := by
    show (chainTn xs oc).label i = _
    simp only [TnDesc.label, chainTn, TnDesc.lbl]
    rw [lookup_append, lookup_range_map (fun j => (false, xs.getD j 0)), if_pos hi]
    simp [List.getElem?_eq_getElem hi]
  labc c hc := by
    subst hc
    show (chainTn xs (some c)).label xs.length = _
    simp only [TnDesc.label, chainTn, TnDesc.lbl]
    rw [lookup_append, lookup_range_map (fun j => (false, xs.getD j 0)), if_neg (by omega)]
    simp [List.lookup]

/-- A chain network determines its labels. -/
theorem IsChainNet.unique {A C : Type} {tn : TaskNetwork ℕ A C} {xs xs' : List A}
    {oc oc' : Option C} (h : IsChainNet tn xs oc) (h' : IsChainNet tn xs' oc') :
    xs = xs' ∧ oc = oc' := by
  have hn : xs.length + oc.toList.length = xs'.length + oc'.toList.length := by
    have := congrArg Finset.card (h.T.symm.trans h'.T); simpa using this
  have hle : ∀ {xs xs' : List A} {oc oc' : Option C}, IsChainNet tn xs oc →
      IsChainNet tn xs' oc' → xs.length + oc.toList.length = xs'.length + oc'.toList.length →
      xs.length ≤ xs'.length := by
    intro xs xs' oc oc' h h' hn
    by_contra hlt
    push_neg at hlt
    cases oc' with
    | none => simp at hn; omega
    | some c =>
      have h1 := h'.labc c rfl
      have h2 := h.lab xs'.length hlt
      rw [h1] at h2; cases h2
  have hlen : xs.length = xs'.length := le_antisymm (hle h h' hn) (hle h' h hn.symm)
  have hxs : xs = xs' := by
    apply List.ext_getElem hlen
    intro i h1 h2
    have := (h.lab i h1).symm.trans (h'.lab i h2)
    exact Sum.inl_injective this
  subst hxs
  refine ⟨rfl, ?_⟩
  cases oc with
  | none => cases oc' with
    | none => rfl
    | some c => simp at hn
  | some c => cases oc' with
    | none => simp at hn
    | some c' =>
      have := (h.labc c rfl).symm.trans (h'.labc c' rfl)
      rw [Sum.inr_injective this]

end PCP

end FOND
