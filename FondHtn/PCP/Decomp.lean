import FondHtn.PCP.ChainNet
import FondHtn.FixedMethods
/-!
# Decompositions of chain problems

A *chain problem* has an initial task network of `r` unordered compound tasks (the roots) and
only chain methods (`FOND.PCP.IsChainNet`: some primitive tasks in a row, optionally followed by a
compound task).  Every task network reachable from `tn_I` is a disjoint union of `r` chains, the
`i`-th one being a partial derivation from root `i` (`FOND.PCP.Inv`).  Consequently
(`FOND.PCP.achievable_iff`) the achievable primitive networks are, up to the choice of ids,
exactly the disjoint unions of complete derivations, one per root.
-/

namespace FOND

namespace PCP

open HTN FOND.AcycHard

variable {F : Type} (P : Problem F ℕ ℕ ℕ)

/-- One method application in a chain: compound task `c` becomes `xs` followed by `oc`. -/
def MStep (c : ℕ) (xs : List ℕ) (oc : Option ℕ) : Prop :=
  ∃ m ∈ P.methods, m.abstractTask = c ∧ IsChainNet m.subtasks xs oc

/-- A derivation step on (word so far, pending compound task). -/
def PStep (x y : List ℕ × Option ℕ) : Prop :=
  ∃ c xs, x.2 = some c ∧ y.1 = x.1 ++ xs ∧ MStep P c xs y.2

/-- The chains of a network: chain `i` consists of the primitive tasks `ids i`, labelled with
`(st i).1`, followed by the pending compound task `pend i` labelled `(st i).2`; the order is
"earlier in the same chain". -/
structure Inv (tn : TaskNetwork ℕ ℕ ℕ) (r : ℕ) (root : ℕ → ℕ) (ids : ℕ → List ℕ)
    (pend : ℕ → Option ℕ) (st : ℕ → List ℕ × Option ℕ) : Prop where
  mem : ∀ x, x ∈ tn.T ↔ ∃ i < r, x ∈ ids i ++ (pend i).toList
  ord : ∀ x y, tn.ord x y ↔ ∃ i < r, Before (ids i ++ (pend i).toList) x y
  lab : ∀ i < r, (ids i).map tn.α = (st i).1.map Sum.inl
  pendSome : ∀ i < r, (pend i).isSome = (st i).2.isSome
  pendLab : ∀ i < r, ∀ p c, pend i = some p → (st i).2 = some c → tn.α p = Sum.inr c
  nodup : ∀ i < r, (ids i ++ (pend i).toList).Nodup
  disj : ∀ i j, i < r → j < r → i ≠ j → ∀ x ∈ ids i ++ (pend i).toList,
    x ∉ ids j ++ (pend j).toList
  der : ∀ i < r, Relation.ReflTransGen (PStep P) ([], some (root i)) (st i)

variable {P}

theorem mem_of_seq {tn : TaskNetwork ℕ ℕ ℕ} {r : ℕ} {root : ℕ → ℕ} {ids : ℕ → List ℕ}
    {pend : ℕ → Option ℕ} {st : ℕ → List ℕ × Option ℕ} (h : Inv P tn r root ids pend st)
    {i : ℕ} (hi : i < r) {x : ℕ} (hx : x ∈ ids i ++ (pend i).toList) : x ∈ tn.T :=
  (h.mem x).2 ⟨i, hi, hx⟩

/-- **One decomposition step preserves the chain structure.** -/
theorem Inv.step {tn tn' : TaskNetwork ℕ ℕ ℕ} {r : ℕ} {root : ℕ → ℕ} {ids : ℕ → List ℕ}
    {pend : ℕ → Option ℕ} {st : ℕ → List ℕ × Option ℕ} (h : Inv P tn r root ids pend st)
    {t : ℕ} {m : Method ℕ ℕ ℕ} (hs : DecompStep P.methods tn t m tn') {xs : List ℕ}
    {oc : Option ℕ} (hm : IsChainNet m.subtasks xs oc) :
    ∃ i < r, pend i = some t ∧ (st i).2 = some m.abstractTask ∧
      ∃ ids' pend', Inv P tn' r root ids' pend'
        (Function.update st i ((st i).1 ++ xs, oc)) ∧
        (∀ j, j ≠ i → ids' j = ids j ∧ pend' j = pend j) := by
  classical
  obtain ⟨hmM, ht, hαt, u, hu, huiso, hdisj, rfl⟩ := hs
  obtain ⟨i, hi, hti⟩ := (h.mem t).1 ht
  -- `t` is the pending task of chain `i`
  have htp : pend i = some t := by
    rcases List.mem_append.1 hti with htl | htp
    · exfalso
      have : tn.α t ∈ (st i).1.map Sum.inl := by rw [← h.lab i hi]; exact List.mem_map_of_mem htl
      obtain ⟨a, -, ha⟩ := List.mem_map.1 this
      rw [hαt] at ha; cases ha
    · simpa using htp
  obtain ⟨c, hc⟩ : ∃ c, (st i).2 = some c := by
    have := h.pendSome i hi; rw [htp] at this
    exact Option.isSome_iff_exists.1 this.symm
  have hcm : c = m.abstractTask := by
    have := h.pendLab i hi t c htp hc; rw [hαt] at this; cases this; rfl
  subst hcm
  obtain ⟨L, hLnd, hLlen, hLmem, hLord, hLlab, hLp, hLn⟩ := chain_of_iso hm hu huiso
  have htT : t ∉ ids i := by
    have := h.nodup i hi; rw [htp] at this
    exact fun h' => (List.nodup_append.1 this).2.2 t h' t (List.mem_singleton_self _) rfl
  have hdisjL : ∀ x ∈ L, x ∉ tn.T := fun x hx hxT =>
    Finset.disjoint_left.1 hdisj hxT ((hLmem x).2 hx)
  obtain ⟨optP, hLsplit, hoptS, hoptN⟩ : ∃ optP : Option ℕ,
      L = L.take xs.length ++ optP.toList ∧
      (∀ c', oc = some c' → ∃ p, optP = some p ∧ u.α p = Sum.inr c') ∧
      (oc = none → optP = none) := by
    cases oc with
    | none =>
      exact ⟨none, by simp [List.take_of_length_le (le_of_eq (hLn rfl))], by simp, fun _ => rfl⟩
    | some c' =>
      obtain ⟨p, hp, hpα⟩ := hLp c' rfl
      exact ⟨some p, hp, fun c'' h => by cases h; exact ⟨p, rfl, hpα⟩, by simp⟩
  set ids' : ℕ → List ℕ := Function.update ids i (ids i ++ L.take xs.length) with hids'
  set pend' : ℕ → Option ℕ := Function.update pend i optP with hpend'
  have hseq' : ids' i ++ (pend' i).toList = ids i ++ L := by
    simp only [ids', pend', Function.update_self, List.append_assoc]
    rw [← hLsplit]
  have hseqj : ∀ j, j ≠ i → ids' j ++ (pend' j).toList = ids j ++ (pend j).toList := by
    intro j hj; simp [ids', pend', Function.update_of_ne hj]
  have hseqi : ids i ++ (pend i).toList = ids i ++ [t] := by rw [htp]; rfl
  refine ⟨i, hi, htp, hc, ids', pend', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- membership
    intro x
    simp only [decomposeWith, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (⟨hxt, hxT⟩ | hxu)
      · obtain ⟨j, hj, hxj⟩ := (h.mem x).1 hxT
        refine ⟨j, hj, ?_⟩
        by_cases hji : j = i
        · subst hji; rw [hseq']; rw [hseqi] at hxj
          rcases List.mem_append.1 hxj with h1 | h1
          · exact List.mem_append_left _ h1
          · exact absurd (List.mem_singleton.1 h1) hxt
        · rw [hseqj j hji]; exact hxj
      · exact ⟨i, hi, by rw [hseq']; exact List.mem_append_right _ ((hLmem x).1 hxu)⟩
    · rintro ⟨j, hj, hxj⟩
      by_cases hji : j = i
      · subst hji; rw [hseq'] at hxj
        rcases List.mem_append.1 hxj with h1 | h1
        · refine Or.inl ⟨fun e => htT (e ▸ h1), mem_of_seq h hj (List.mem_append_left _ h1)⟩
        · exact Or.inr ((hLmem x).2 h1)
      · rw [hseqj j hji] at hxj
        refine Or.inl ⟨fun e => ?_, mem_of_seq h hj hxj⟩
        subst e
        exact h.disj i j hi hj (Ne.symm hji) x (by rw [hseqi]; simp) hxj
  · -- order
    intro x y
    simp only [decomposeWith]
    rw [hLord]
    have hord_t : ∀ a, tn.ord a t ↔ a ∈ ids i := by
      intro a
      rw [h.ord]
      constructor
      · rintro ⟨j, hj, hb⟩
        by_cases hji : j = i
        · subst hji; rw [hseqi, before_snoc_to htT] at hb; exact hb
        · exact absurd (by rw [hseqi]; simp) (h.disj j i hj hi hji t (before_mem hb).2)
      · intro ha; exact ⟨i, hi, by rw [hseqi, before_snoc_to htT]; exact ha⟩
    have hord_t' : ∀ b, ¬ tn.ord t b := by
      intro b hb
      rw [h.ord] at hb
      obtain ⟨j, hj, hb⟩ := hb
      by_cases hji : j = i
      · subst hji; rw [hseqi] at hb; exact before_snoc_last htT hb
      · exact h.disj j i hj hi hji t (before_mem hb).1 (by rw [hseqi]; simp)
    have hord_rest : ∀ a b, (tn.ord a b ∧ a ≠ t ∧ b ≠ t) ↔
        Before (ids i) a b ∨ ∃ j < r, j ≠ i ∧ Before (ids j ++ (pend j).toList) a b := by
      intro a b
      rw [h.ord]
      constructor
      · rintro ⟨⟨j, hj, hb⟩, hat, hbt⟩
        by_cases hji : j = i
        · subst hji; rw [hseqi, before_snoc_ne hbt] at hb; exact Or.inl hb
        · exact Or.inr ⟨j, hj, hji, hb⟩
      · rintro (hb | ⟨j, hj, hji, hb⟩)
        · have hat : a ≠ t := fun e => htT (e ▸ (before_mem hb).1)
          have hbt : b ≠ t := fun e => htT (e ▸ (before_mem hb).2)
          exact ⟨⟨i, hi, by rw [hseqi, before_snoc_ne hbt]; exact hb⟩, hat, hbt⟩
        · have hat : a ≠ t := fun e =>
            h.disj j i hj hi hji a (before_mem hb).1 (by rw [hseqi, e]; simp)
          have hbt : b ≠ t := fun e =>
            h.disj j i hj hi hji b (before_mem hb).2 (by rw [hseqi, e]; simp)
          exact ⟨⟨j, hj, hb⟩, hat, hbt⟩
    constructor
    · rintro (hb | ⟨ha, hb⟩ | ⟨ha, -⟩ | hb)
      · exact ⟨i, hi, by rw [hseq', before_append]; exact Or.inr (Or.inr hb)⟩
      · exact ⟨i, hi, by rw [hseq', before_append]; exact Or.inr (Or.inl
          ⟨(hord_t x).1 ha, (hLmem _).1 hb⟩)⟩
      · exact absurd ha (hord_t' _)
      · rcases (hord_rest x y).1 hb with hb | ⟨j, hj, hji, hb⟩
        · exact ⟨i, hi, by rw [hseq', before_append]; exact Or.inl hb⟩
        · exact ⟨j, hj, by rw [hseqj j hji]; exact hb⟩
    · rintro ⟨j, hj, hb⟩
      by_cases hji : j = i
      · subst hji
        rw [hseq', before_append] at hb
        rcases hb with hb | ⟨ha, hb⟩ | hb
        · exact Or.inr (Or.inr (Or.inr ((hord_rest x y).2 (Or.inl hb))))
        · exact Or.inr (Or.inl ⟨(hord_t x).2 ha, (hLmem y).2 hb⟩)
        · exact Or.inl hb
      · rw [hseqj j hji] at hb
        exact Or.inr (Or.inr (Or.inr ((hord_rest x y).2 (Or.inr ⟨j, hj, hji, hb⟩))))
  · -- labels
    intro j hj
    have hα : ∀ x ∈ tn.T, (decomposeWith tn t u).α x = tn.α x := fun x hx => by
      have hxu : x ∉ u.T := fun h' => hdisjL x ((hLmem x).1 h') hx
      simp [decomposeWith, hxu]
    by_cases hji : j = i
    · subst hji
      simp only [ids', Function.update_self, List.map_append]
      rw [List.map_congr_left (fun x hx => hα x (mem_of_seq h hj (List.mem_append_left _ hx))),
        h.lab j hj]
      have : (L.take xs.length).map (decomposeWith tn t u).α = xs.map Sum.inl := by
        rw [← hLlab]
        refine List.map_congr_left fun x hx => ?_
        have hxu : x ∈ u.T := (hLmem x).2 (List.mem_of_mem_take hx)
        simp [decomposeWith, hxu]
      rw [this]
    · simp only [ids', Function.update_of_ne hji]
      rw [List.map_congr_left (fun x hx => hα x (mem_of_seq h hj (List.mem_append_left _ hx))),
        h.lab j hj]
  · -- pending is some iff state pending
    intro j hj
    by_cases hji : j = i
    · subst hji
      simp only [pend', Function.update_self]
      cases oc with
      | none => rw [hoptN rfl]
      | some c' =>
        obtain ⟨p, hp, -⟩ := hoptS c' rfl
        rw [hp]; rfl
    · simp only [pend', Function.update_of_ne hji]; exact h.pendSome j hj
  · -- pending labels
    intro j hj p c' hp hc'
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self] at hc'
      simp only [pend', Function.update_self] at hp
      subst hc'
      obtain ⟨q, hq, hqα⟩ := hoptS _ rfl
      rw [hq] at hp; cases hp
      have hqu : p ∈ u.T := (hLmem p).2 (by rw [hLsplit, hq]; simp)
      simp [decomposeWith, hqu, hqα]
    · simp only [pend', Function.update_of_ne hji] at hp
      simp only [Function.update_of_ne hji] at hc'
      have hpT := mem_of_seq h hj (by rw [hp]; simp : p ∈ ids j ++ (pend j).toList)
      have hpu : p ∉ u.T := fun h' => hdisjL p ((hLmem p).1 h') hpT
      simp [decomposeWith, hpu, h.pendLab j hj p c' hp hc']
  · -- nodup
    intro j hj
    by_cases hji : j = i
    · subst hji
      rw [hseq']
      refine List.nodup_append.2 ⟨(List.nodup_append.1 (by rw [← hseqi]; exact h.nodup j hj)).1,
        hLnd, ?_⟩
      intro x hx y hy hxy
      subst hxy
      exact hdisjL x hy (mem_of_seq h hj (List.mem_append_left _ hx))
    · rw [hseqj j hji]; exact h.nodup j hj
  · -- disjointness
    intro j k hj hk hjk x hx hx'
    have side : ∀ a b, a < r → b < r → a ≠ b → a = i →
        ∀ y ∈ ids' a ++ (pend' a).toList, y ∉ ids' b ++ (pend' b).toList := by
      intro a b ha hb hab hai y hy hy'
      subst hai
      rw [hseq'] at hy
      rw [hseqj b (Ne.symm hab)] at hy'
      rcases List.mem_append.1 hy with hy | hy
      · exact h.disj a b ha hb hab y (by rw [hseqi]; exact List.mem_append_left _ hy) hy'
      · exact hdisjL y hy (mem_of_seq h hb hy')
    by_cases hji : j = i
    · exact side j k hj hk hjk hji x hx hx'
    · by_cases hki : k = i
      · exact side k j hk hj (Ne.symm hjk) hki x hx' hx
      · rw [hseqj j hji] at hx; rw [hseqj k hki] at hx'
        exact h.disj j k hj hk hjk x hx hx'
  · -- derivations
    intro j hj
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
      exact (h.der j hj).tail ⟨m.abstractTask, xs, hc, rfl, m, hmM, rfl, hm⟩
    · simp only [Function.update_of_ne hji]; exact h.der j hj
  · intro j hj
    exact ⟨by simp [ids', Function.update_of_ne hj], by simp [pend', Function.update_of_ne hj]⟩

/-! ## The initial network, reachability, primitive networks -/

/-- The initial network: `r` unordered roots. -/
structure IsRoots (tn : TaskNetwork ℕ ℕ ℕ) (r : ℕ) (root : ℕ → ℕ) : Prop where
  T : tn.T = Finset.range r
  ord : ∀ x y, ¬ tn.ord x y
  lab : ∀ i < r, tn.α i = Sum.inr (root i)

theorem inv_roots {tn : TaskNetwork ℕ ℕ ℕ} {r : ℕ} {root : ℕ → ℕ} (h : IsRoots tn r root) :
    Inv P tn r root (fun _ => []) some (fun i => ([], some (root i))) where
  mem x := by rw [h.T]; simp
  ord x y := by
    simp only [h.ord, false_iff, not_exists, not_and, List.nil_append, Option.toList_some]
    exact fun _ _ => not_before_singleton
  lab _ _ := rfl
  pendSome _ _ := rfl
  pendLab i hi p c hp hc := by cases hp; cases hc; exact h.lab i hi
  nodup _ _ := by simp
  disj i j _ _ hij x hx hx' := by simp at hx hx'; exact hij (hx.symm.trans hx')
  der _ _ := .refl

/-- Every method is a chain method. -/
def ChainMethods (P : Problem F ℕ ℕ ℕ) : Prop :=
  ∀ m ∈ P.methods, ∃ xs oc, IsChainNet m.subtasks xs oc

theorem inv_of_decomposesTo (hM : ChainMethods P) {r : ℕ} {root : ℕ → ℕ}
    (hI : IsRoots P.tnI r root) {tn : TaskNetwork ℕ ℕ ℕ} (h : P.DecomposesTo P.tnI tn) :
    ∃ ids pend st, Inv P tn r root ids pend st := by
  induction h with
  | refl => exact ⟨_, _, _, inv_roots hI⟩
  | tail _ hs ih =>
    obtain ⟨ids, pend, st, hinv⟩ := ih
    obtain ⟨t, m, hs⟩ := hs
    obtain ⟨xs, oc, hm⟩ := hM m hs.1
    obtain ⟨i, -, -, -, ids', pend', hinv', -⟩ := hinv.step hs hm
    exact ⟨ids', pend', _, hinv'⟩

theorem Inv.pend_none {tn : TaskNetwork ℕ ℕ ℕ} {r : ℕ} {root : ℕ → ℕ} {ids : ℕ → List ℕ}
    {pend : ℕ → Option ℕ} {st : ℕ → List ℕ × Option ℕ} (h : Inv P tn r root ids pend st)
    (hprim : tn.IsPrimitive) {i : ℕ} (hi : i < r) : pend i = none ∧ (st i).2 = none := by
  cases hp : pend i with
  | none =>
    have := h.pendSome i hi; rw [hp] at this
    exact ⟨rfl, Option.not_isSome_iff_eq_none.1 (by simpa using this.symm)⟩
  | some p =>
    exfalso
    obtain ⟨c, hc⟩ : ∃ c, (st i).2 = some c := by
      have := h.pendSome i hi; rw [hp] at this
      exact Option.isSome_iff_exists.1 this.symm
    obtain ⟨a, ha⟩ := hprim p (mem_of_seq h hi (by rw [hp]; simp))
    rw [h.pendLab i hi p c hp hc] at ha; cases ha

/-! ## Fresh copies of method networks -/

/-- The network `m` with all ids shifted by `N`. -/
def shiftNet {A C : Type} (m : TaskNetwork ℕ A C) (N : ℕ) : TaskNetwork ℕ A C where
  T := m.T.map (addRightEmbedding N)
  ord a b := N ≤ a ∧ N ≤ b ∧ m.ord (a - N) (b - N)
  α a := m.α (a - N)

theorem mem_shiftNet {A C : Type} {m : TaskNetwork ℕ A C} {N x : ℕ} :
    x ∈ (shiftNet m N).T ↔ N ≤ x ∧ x - N ∈ m.T := by
  simp only [shiftNet, Finset.mem_map, addRightEmbedding_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · rintro ⟨h1, h2⟩; exact ⟨x - N, h2, by omega⟩

theorem shiftNet_wf {A C : Type} {m : TaskNetwork ℕ A C} (hm : m.WF) (N : ℕ) :
    (shiftNet m N).WF where
  mem_left h := mem_shiftNet.2 ⟨h.1, hm.mem_left h.2.2⟩
  mem_right h := mem_shiftNet.2 ⟨h.2.1, hm.mem_right h.2.2⟩
  irrefl a h := hm.irrefl _ h.2.2
  trans h h' := ⟨h.1, h'.2.1, hm.trans h.2.2 h'.2.2⟩

theorem shiftNet_iso {A C : Type} (m : TaskNetwork ℕ A C) (N : ℕ) : (shiftNet m N).Iso m := by
  refine ⟨fun a => a - N, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx; exact (mem_shiftNet.1 hx).2
  · intro x hx y hy h
    have := (mem_shiftNet.1 hx).1; have := (mem_shiftNet.1 hy).1
    simp only at h; omega
  · intro y hy; exact ⟨y + N, mem_shiftNet.2 ⟨by omega, by simpa using hy⟩, by simp⟩
  · intro x hx y hy
    have := (mem_shiftNet.1 hx).1; have := (mem_shiftNet.1 hy).1
    simp only [shiftNet]
    constructor
    · exact fun h => h.2.2
    · exact fun h => ⟨by omega, by omega, h⟩
  · intro x _; rfl

/-- **The constructive step**: the pending task of a chain can be decomposed by any method
of its compound task. -/
theorem Inv.exists_step (hMwf : ∀ m ∈ P.methods, m.subtasks.WF) {tn : TaskNetwork ℕ ℕ ℕ}
    {r : ℕ} {root : ℕ → ℕ} {ids : ℕ → List ℕ} {pend : ℕ → Option ℕ}
    {st : ℕ → List ℕ × Option ℕ} (h : Inv P tn r root ids pend st) {i : ℕ} (hi : i < r)
    {c : ℕ} (hc : (st i).2 = some c) {xs : List ℕ} {oc : Option ℕ} (hms : MStep P c xs oc) :
    ∃ tn' ids' pend', DecompStep' P.methods tn tn' ∧
      Inv P tn' r root ids' pend' (Function.update st i ((st i).1 ++ xs, oc)) ∧
      (∀ j, j ≠ i → ids' j = ids j ∧ pend' j = pend j) := by
  obtain ⟨m, hmM, rfl, hm⟩ := hms
  obtain ⟨t, ht⟩ : ∃ t, pend i = some t := by
    have := h.pendSome i hi; rw [hc] at this
    exact Option.isSome_iff_exists.1 this
  have htT : t ∈ tn.T := mem_of_seq h hi (by rw [ht]; simp)
  set N := tn.T.sup id + 1
  have hlt : ∀ x ∈ tn.T, x < N := fun x hx => Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)
  have hs : DecompStep P.methods tn t m (decomposeWith tn t (shiftNet m.subtasks N)) := by
    refine ⟨hmM, htT, h.pendLab i hi t _ ht hc, shiftNet m.subtasks N, shiftNet_wf (hMwf m hmM) N,
      shiftNet_iso _ _, ?_, rfl⟩
    rw [Finset.disjoint_left]
    intro x hx hx'
    have := hlt x hx; have := (mem_shiftNet.1 hx').1; omega
  obtain ⟨i', hi', hti', hci', ids', pend', hinv', hothers⟩ := h.step hs hm
  have hii' : i' = i := by
    by_contra hne
    exact h.disj i' i hi' hi hne t (by rw [hti']; simp) (by rw [ht]; simp)
  subst hii'
  exact ⟨_, ids', pend', ⟨t, m, hs⟩, hinv', hothers⟩

/-- **Derivations can be carried out**: a derivation of chain `i` from its current state is
realised by decompositions. -/
theorem Inv.exists_run (hMwf : ∀ m ∈ P.methods, m.subtasks.WF) {r : ℕ} {root : ℕ → ℕ}
    {i : ℕ} (hi : i < r) {x y : List ℕ × Option ℕ} (hxy : Relation.ReflTransGen (PStep P) x y) :
    ∀ {tn : TaskNetwork ℕ ℕ ℕ} {ids : ℕ → List ℕ} {pend : ℕ → Option ℕ}
      {st : ℕ → List ℕ × Option ℕ}, Inv P tn r root ids pend st → st i = x →
      ∃ tn' ids' pend', P.DecomposesTo tn tn' ∧ Inv P tn' r root ids' pend' (Function.update st i y) ∧
        (∀ j, j ≠ i → ids' j = ids j ∧ pend' j = pend j) := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro tn ids pend st h hx
    refine ⟨tn, ids, pend, Relation.ReflTransGen.refl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    rw [← hx, Function.update_eq_self]; exact h
  | @head x z hxz _ ih =>
    intro tn ids pend st h hx
    obtain ⟨c, xs, hc, hz, hms⟩ := hxz
    obtain ⟨tn₁, ids₁, pend₁, hs₁, h₁, ho₁⟩ := h.exists_step hMwf hi (by rw [hx]; exact hc) hms
    have hz' : Function.update st i ((st i).1 ++ xs, z.2) i = z := by
      simp only [Function.update_self, hx]; ext <;> simp [hz]
    obtain ⟨tn₂, ids₂, pend₂, hs₂, h₂, ho₂⟩ := ih h₁ hz'
    refine ⟨tn₂, ids₂, pend₂, Relation.ReflTransGen.head hs₁ hs₂, ?_, fun j hj => ?_⟩
    · rw [Function.update_idem] at h₂; exact h₂
    · rw [(ho₂ j hj).1, (ho₁ j hj).1, (ho₂ j hj).2, (ho₁ j hj).2]; exact ⟨rfl, rfl⟩

end PCP

end FOND
