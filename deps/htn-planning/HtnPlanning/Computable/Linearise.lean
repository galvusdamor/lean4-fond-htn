import HtnPlanning.Computable.Reach
import HtnPlanning.Computable.MacroLists
import HtnPlanning.Regular.RegularNormalForm
/-!
# The order of a described task network, computably

`HtnPlanning/Computable/Reach.lean` decides the transitive closure of the listed
ordering pairs; on top of it this file computes, for a **totally ordered** described task
network, its unique linearisation and — if the network is in addition **regular** — the *body*
of the method it is the subtask network of: the sequence of its primitive tasks followed by the
optional compound task left open.

* `HTN.Syn.TnDesc.ordB` — the described ordering, as a `Bool` (`HTN.Syn.TnDesc.ordB_iff`);
* `HTN.Syn.TnDesc.rank t i` — the number of listed identifiers ordered before `i`;
* `HTN.Syn.TnDesc.lin t` — the identifiers of `t`, ordered by rank;
  `HTN.Syn.TnDesc.isLinearization_lin` proves that this is a linearisation of the described
  network as soon as the network is totally ordered;
* `HTN.Syn.TnDesc.bodyOf t` — the body, and `HTN.Syn.TnDesc.hasBody_bodyOf` its correctness in
  the sense of `HTN.Method.HasBody` of `HtnPlanning/Regular/RegularNormalForm.lean`.

All of them are primitive recursive.
-/

namespace HTN

namespace Syn

/-! ### Two lemmas on the length of a filtered list -/

theorem length_filter_le_of_imp {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    have ih' := ih fun x hx => hpq x (List.mem_cons_of_mem _ hx)
    by_cases hp : p y = true
    · have hq : q y = true := hpq y (by simp) hp
      simp only [List.filter_cons, hp, hq, if_pos, List.length_cons]
      omega
    · simp only [Bool.not_eq_true] at hp
      by_cases hq : q y = true
      · simp only [List.filter_cons, hp, hq, if_pos, List.length_cons]
        simp only [Bool.false_eq_true, if_false]
        omega
      · simp only [Bool.not_eq_true] at hq
        simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false]
        exact ih'

theorem length_filter_lt {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ x ∈ l, p x = true → q x = true) {x : α} (hx : x ∈ l) (hqx : q x = true)
    (hpx : p x = false) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    have hpq' : ∀ z ∈ ys, p z = true → q z = true := fun z hz => hpq z (List.mem_cons_of_mem _ hz)
    rcases List.mem_cons.1 hx with rfl | hx'
    · have hle := length_filter_le_of_imp (l := ys) hpq'
      simp only [List.filter_cons, hpx, hqx, Bool.false_eq_true, if_false, if_pos,
        List.length_cons]
      omega
    · have ih' := ih hpq' hx'
      by_cases hp : p y = true
      · have hq : q y = true := hpq y (by simp) hp
        simp only [List.filter_cons, hp, hq, if_pos, List.length_cons]
        omega
      · simp only [Bool.not_eq_true] at hp
        by_cases hq : q y = true
        · simp only [List.filter_cons, hp, hq, if_pos, Bool.false_eq_true, if_false,
            List.length_cons]
          omega
        · simp only [Bool.not_eq_true] at hq
          simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false]
          exact ih'

namespace TnDesc

/-! ### The described ordering as a `Bool` -/

/-- **The described ordering, decided**: `a` and `b` are listed identifiers, the listed pairs
lead from `a` to `b` and not back. -/
def ordB (t : TnDesc) (a b : ℕ) : Bool :=
  memB t.ids a && memB t.ids b && reachB t.ordList a b && !reachB t.ordList b a

theorem preOrd_iff_reachB {t : TnDesc} {a b : ℕ} :
    t.preOrd a b ↔ reachB t.ordList a b = true := reachB_iff.symm

theorem ordB_iff {t : TnDesc} {a b : ℕ} : ordB t a b = true ↔ t.toTaskNetwork.ord a b := by
  rw [toTaskNetwork_ord, ordB]
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, memB_iff,
    ← preOrd_iff_reachB]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun hc => ?_⟩
    rw [preOrd_iff_reachB] at hc
    rw [hc] at h4
    exact absurd h4 (by simp)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    rcases hb : reachB t.ordList b a with _ | _
    · rfl
    · exact absurd (preOrd_iff_reachB.2 hb) h4

/-! ### The rank of an identifier -/

/-- The number of listed identifiers ordered before `i`. -/
def rank (t : TnDesc) (i : ℕ) : ℕ := (t.ids.filter fun j => ordB t j i).length

theorem rank_le (t : TnDesc) (i : ℕ) : rank t i ≤ t.ids.length :=
  List.length_filter_le _ _

/-- The rank increases strictly along the described ordering. -/
theorem rank_lt_of_ord {t : TnDesc} {i j : ℕ} (h : t.toTaskNetwork.ord i j) :
    rank t i < rank t j := by
  have hwf := toTaskNetwork_wf t
  have hi : i ∈ t.ids := by
    have := hwf.mem_left h
    simpa using this
  refine length_filter_lt (x := i) ?_ hi (ordB_iff.2 h) ?_
  · intro x _ hx
    exact ordB_iff.2 (hwf.trans (ordB_iff.1 hx) h)
  · rcases hb : ordB t i i with _ | _
    · rfl
    · exact absurd (hwf.irrefl i (ordB_iff.1 hb)) (fun hc => hc)

/-- In a totally ordered network the rank determines the identifier. -/
theorem rank_inj {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered) {i j : ℕ}
    (hi : i ∈ t.ids) (hj : j ∈ t.ids) (h : rank t i = rank t j) : i = j := by
  by_contra hne
  have hiT : i ∈ t.toTaskNetwork.T := by simpa using hi
  have hjT : j ∈ t.toTaskNetwork.T := by simpa using hj
  rcases hTO i hiT j hjT hne with hord | hord
  · exact absurd (rank_lt_of_ord hord) (by omega)
  · exact absurd (rank_lt_of_ord hord) (by omega)

/-! ### The linearisation -/

/-- The identifiers of rank `k`. -/
def linAt (t : TnDesc) (k : ℕ) : List ℕ :=
  t.ids.filterMap fun i => if rank t i = k then some i else none

@[simp] theorem mem_linAt {t : TnDesc} {k i : ℕ} :
    i ∈ linAt t k ↔ i ∈ t.ids ∧ rank t i = k := by
  simp only [linAt, List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, hij⟩
    by_cases h : rank t j = k
    · rw [if_pos h] at hij
      have : j = i := by simpa using hij
      subst this
      exact ⟨hj, h⟩
    · rw [if_neg h] at hij
      exact absurd hij (by simp)
  · rintro ⟨hi, hk⟩
    exact ⟨i, hi, by simp [hk]⟩

/-- **The identifiers of a described network, in the order of their rank.**  For a totally
ordered network this is its unique linearisation (`isLinearization_lin`). -/
def lin (t : TnDesc) : List ℕ :=
  (List.range (t.ids.length + 1)).filterMap fun k => (linAt t k).head?

theorem mem_lin_of_head {t : TnDesc} {k i : ℕ} (h : (linAt t k).head? = some i) :
    i ∈ t.ids ∧ rank t i = k := mem_linAt.1 (List.mem_of_mem_head? h)

theorem mem_lin {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered) {i : ℕ} :
    i ∈ lin t ↔ i ∈ t.ids := by
  simp only [lin, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨k, -, hk⟩
    exact (mem_lin_of_head hk).1
  · intro hi
    refine ⟨rank t i, by have := rank_le t i; omega, ?_⟩
    rcases hh : (linAt t (rank t i)).head? with _ | j
    · have : i ∈ linAt t (rank t i) := mem_linAt.2 ⟨hi, rfl⟩
      rw [List.head?_eq_none_iff.1 hh] at this
      exact absurd this (by simp)
    · obtain ⟨hj, hjr⟩ := mem_lin_of_head hh
      have : j = i := rank_inj hTO hj hi hjr
      rw [this]

theorem pairwise_lin (t : TnDesc) : (lin t).Pairwise (fun x y => rank t x < rank t y) := by
  refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
  intro k k' hkk' b hb b' hb'
  obtain ⟨-, hbk⟩ := mem_lin_of_head hb
  obtain ⟨-, hbk'⟩ := mem_lin_of_head hb'
  omega

theorem nodup_lin (t : TnDesc) : (lin t).Nodup := by
  refine List.Pairwise.imp ?_ (pairwise_lin t)
  intro a b hab heq
  rw [heq] at hab
  omega

/-- **The computed order is the linearisation of a totally ordered described network.** -/
theorem isLinearization_lin {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered) :
    t.toTaskNetwork.IsLinearization (lin t) := by
  refine ⟨nodup_lin t, fun i => ?_, ?_⟩
  · rw [mem_lin hTO]
    simp
  · refine List.Pairwise.imp ?_ (pairwise_lin t)
    intro a b hab hord
    exact absurd (rank_lt_of_ord hord) (by omega)

theorem length_lin_le (t : TnDesc) : (lin t).length ≤ t.ids.length + 1 := by
  calc (lin t).length ≤ (List.range (t.ids.length + 1)).length :=
        List.length_filterMap_le _ _
    _ = t.ids.length + 1 := by simp

/-! ### The body of a method -/

/-- Is the identifier labelled with a compound task name? -/
def labelIsCompound (t : TnDesc) (i : ℕ) : Bool := !(labelList true t.lbl i).isEmpty

/-- The action labelling an identifier (junk for a compound one). -/
def actOf (t : TnDesc) (i : ℕ) : ℕ := (labelList false t.lbl i).headI

/-- The compound task name labelling an identifier (junk for a primitive one). -/
def compOf (t : TnDesc) (i : ℕ) : ℕ := (labelList true t.lbl i).headI

theorem actOf_eq {t : TnDesc} {i a : ℕ} (h : t.label i = Sum.inl a) : actOf t i = a := by
  rcases hl : t.lbl.lookup i with _ | ⟨b, n⟩
  · rw [label, hl] at h
    simp only [Sum.inl.injEq] at h
    simp [actOf, labelList_eq, hl, ← h]
  · cases b
    · rw [label, hl] at h
      simp only [Sum.inl.injEq] at h
      simp [actOf, labelList_eq, hl, h]
    · rw [label, hl] at h
      exact absurd h (by simp)

theorem compOf_eq {t : TnDesc} {i c : ℕ} (h : t.label i = Sum.inr c) : compOf t i = c := by
  rcases hl : t.lbl.lookup i with _ | ⟨b, n⟩
  · rw [label, hl] at h
    exact absurd h (by simp)
  · cases b
    · rw [label, hl] at h
      exact absurd h (by simp)
    · rw [label, hl] at h
      simp only [Sum.inr.injEq] at h
      simp [compOf, labelList_eq, hl, h]

theorem labelIsCompound_iff {t : TnDesc} {i : ℕ} :
    labelIsCompound t i = true ↔ ∃ c, t.label i = Sum.inr c := by
  rcases hl : t.lbl.lookup i with _ | ⟨b, n⟩
  · simp [labelIsCompound, labelList_eq, hl, label]
  · cases b
    · simp [labelIsCompound, labelList_eq, hl, label]
    · simp [labelIsCompound, labelList_eq, hl, label]

/-- **The body of a described subtask network**: the actions of its primitive tasks, in their
order, together with the compound task it leaves open. -/
def bodyOf (t : TnDesc) : List ℕ × Option ℕ :=
  match (lin t).reverse with
  | [] => ([], none)
  | z :: rest =>
      if labelIsCompound t z then (rest.reverse.map (actOf t), some (compOf t z))
      else ((lin t).map (actOf t), none)

theorem map_actOf_eq {t : TnDesc} {l : List ℕ} {os : List ℕ}
    (h : l.map t.toTaskNetwork.α = os.map Sum.inl) : l.map (actOf t) = os := by
  induction l generalizing os with
  | nil =>
    cases os with
    | nil => rfl
    | cons a as => simp at h
  | cons i is ih =>
    cases os with
    | nil => simp at h
    | cons a as =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨actOf_eq h1, ih h2⟩

/-- **Correctness of `bodyOf`.**  For a totally ordered and regular described network, `bodyOf`
computes the body of the method it is the subtask network of. -/
theorem hasBody_bodyOf {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered)
    (hreg : t.toTaskNetwork.IsRegular) (c : ℕ) :
    Method.HasBody (⟨c, t.toTaskNetwork⟩ : Method ℕ ℕ ℕ) (bodyOf t).1 (bodyOf t).2 := by
  obtain ⟨l, os, tail, hchain⟩ :=
    TaskNetwork.exists_isChain (toTaskNetwork_wf t) hreg hTO
  have hlin : lin t = TaskNetwork.chainIds l tail :=
    hchain.linearization_eq (isLinearization_lin hTO)
  cases tail with
  | none =>
    have hlin' : lin t = l := by simpa using hlin
    rcases hrev : (lin t).reverse with _ | ⟨z, rest⟩
    · have hnil : lin t = [] := by
        have := congrArg List.reverse hrev
        simpa using this
      have hl : l = [] := by rw [← hlin', hnil]
      subst hl
      have hos : os = [] := by
        have := hchain.labels
        simpa using this.symm
      subst hos
      have hb : bodyOf t = ([], none) := by simp only [bodyOf, hrev]
      rw [hb]
      exact ⟨[], none, hchain, rfl⟩
    · have hzprim : ∃ a, t.label z = Sum.inl a := by
        have hzmem : z ∈ lin t := by
          have := congrArg List.reverse hrev
          rw [List.reverse_reverse] at this
          rw [this]
          simp
        have hzl : z ∈ l := by rwa [hlin'] at hzmem
        have hmem : t.toTaskNetwork.α z ∈ l.map t.toTaskNetwork.α := List.mem_map_of_mem hzl
        rw [hchain.labels] at hmem
        obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
        exact ⟨a, ha.symm⟩
      have hnc : labelIsCompound t z = false := by
        rcases hb : labelIsCompound t z with _ | _
        · rfl
        · obtain ⟨cc, hcc⟩ := labelIsCompound_iff.1 hb
          obtain ⟨a, ha⟩ := hzprim
          rw [ha] at hcc
          exact absurd hcc (by simp)
      have hbody : bodyOf t = ((lin t).map (actOf t), none) := by
        simp only [bodyOf, hrev, hnc, Bool.false_eq_true, if_false]
      rw [hbody, hlin']
      refine ⟨l, none, ?_, rfl⟩
      have : l.map (actOf t) = os := map_actOf_eq hchain.labels
      rw [this]
      exact hchain
  | some p =>
    obtain ⟨z, cc⟩ := p
    have hlin' : lin t = l ++ [z] := by simpa using hlin
    have hrev : (lin t).reverse = z :: l.reverse := by rw [hlin']; simp
    have hzc : t.label z = Sum.inr cc := hchain.tailLabel (z, cc) rfl
    have hc : labelIsCompound t z = true := labelIsCompound_iff.2 ⟨cc, hzc⟩
    have hbody : bodyOf t = (l.map (actOf t), some (compOf t z)) := by
      simp only [bodyOf, hrev, hc, if_true, List.reverse_reverse]
    rw [hbody, compOf_eq hzc, map_actOf_eq hchain.labels]
    exact ⟨l, some (z, cc), hchain, rfl⟩

theorem length_bodyOf_le (t : TnDesc) : (bodyOf t).1.length ≤ t.ids.length + 1 := by
  rcases hrev : (lin t).reverse with _ | ⟨z, rest⟩
  · simp [bodyOf, hrev]
  · by_cases hc : labelIsCompound t z
    · have hb : bodyOf t = (rest.reverse.map (actOf t), some (compOf t z)) := by
        simp only [bodyOf, hrev, hc, if_true]
      have hlen : rest.length + 1 = (lin t).length := by
        have := congrArg List.length hrev
        simpa using this.symm
      have := length_lin_le t
      rw [hb]
      simp only [List.length_map, List.length_reverse]
      omega
    · have hb : bodyOf t = ((lin t).map (actOf t), none) := by
        simp only [bodyOf, hrev, hc, Bool.false_eq_true, if_false]
      rw [hb]
      simpa using length_lin_le t

/-! ### Computability -/

open Primrec

theorem primrec_ordB : Primrec fun p : TnDesc × ℕ × ℕ => ordB p.1 p.2.1 p.2.2 := by
  have hids : Primrec fun p : TnDesc × ℕ × ℕ => p.1.ids := primrec_ids.comp Primrec.fst
  have hord : Primrec fun p : TnDesc × ℕ × ℕ => p.1.ordList := primrec_ordList.comp Primrec.fst
  have ha : Primrec fun p : TnDesc × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hb : Primrec fun p : TnDesc × ℕ × ℕ => p.2.2 := Primrec.snd.comp Primrec.snd
  have h1 : Primrec fun p : TnDesc × ℕ × ℕ => memB p.1.ids p.2.1 := primrec_memB.comp hids ha
  have h2 : Primrec fun p : TnDesc × ℕ × ℕ => memB p.1.ids p.2.2 := primrec_memB.comp hids hb
  have h3 : Primrec fun p : TnDesc × ℕ × ℕ => reachB p.1.ordList p.2.1 p.2.2 :=
    primrec_reachB.comp (Primrec.pair hord ha) hb
  have h4 : Primrec fun p : TnDesc × ℕ × ℕ => reachB p.1.ordList p.2.2 p.2.1 :=
    primrec_reachB.comp (Primrec.pair hord hb) ha
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp h1 h2) h3) (Primrec.not.comp h4)

theorem primrec_rank : Primrec₂ rank := by
  have hfil : Primrec fun p : TnDesc × ℕ => p.1.ids.filterMap
      fun j => if ordB p.1 j p.2 = true then some j else none := by
    refine listFilterMap (β := ℕ) (σ := ℕ) (primrec_ids.comp Primrec.fst) ?_
    refine Primrec.ite ?_ (option_some.comp Primrec.snd) (Primrec.const none)
    refine PrimrecRel.comp Primrec.eq ?_ (Primrec.const true)
    exact primrec_ordB.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))
  refine Primrec.of_eq (Primrec.list_length.comp hfil) ?_
  rintro ⟨t, i⟩
  simp only [rank]
  congr 1
  rw [← List.filterMap_eq_filter]
  congr 1

theorem primrec_linAt : Primrec₂ linAt := by
  refine listFilterMap (β := ℕ) (σ := ℕ) (primrec_ids.comp Primrec.fst) ?_
  refine Primrec.ite ?_ (option_some.comp Primrec.snd) (Primrec.const none)
  exact PrimrecRel.comp Primrec.eq
    (primrec_rank.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (Primrec.snd.comp Primrec.fst)

theorem primrec_lin : Primrec lin := by
  have hrange : Primrec fun t : TnDesc => List.range (t.ids.length + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp primrec_ids))
  refine listFilterMap (β := ℕ) (σ := ℕ) hrange ?_
  exact Primrec.list_head?.comp (primrec_linAt.comp Primrec.fst Primrec.snd)

theorem primrec_labelIsCompound : Primrec₂ labelIsCompound := by
  have h : Primrec fun p : TnDesc × ℕ => labelList true p.1.lbl p.2 :=
    (primrec_labelList true).comp (primrec_lbl.comp Primrec.fst) Primrec.snd
  exact Primrec.not.comp (DomDesc.primrec_isEmptyList.comp h)

theorem primrec_actOf : Primrec₂ actOf :=
  Primrec.list_headI.comp
    ((primrec_labelList false).comp (primrec_lbl.comp Primrec.fst) Primrec.snd)

theorem primrec_compOf : Primrec₂ compOf :=
  Primrec.list_headI.comp
    ((primrec_labelList true).comp (primrec_lbl.comp Primrec.fst) Primrec.snd)

theorem primrec_bodyOf : Primrec bodyOf := by
  have hrev : Primrec fun t : TnDesc => (lin t).reverse :=
    Primrec.list_reverse.comp primrec_lin
  have hmain : Primrec₂ fun (t : TnDesc) (p : ℕ × List ℕ) =>
      (if labelIsCompound t p.1 then
        (p.2.reverse.map (actOf t), some (compOf t p.1))
      else ((lin t).map (actOf t), none) : List ℕ × Option ℕ) := by
    refine Primrec.ite (PrimrecRel.comp Primrec.eq (primrec_labelIsCompound.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)) (Primrec.const true)) ?_ ?_
    · refine Primrec.pair ?_ ?_
      · refine Primrec.list_map (Primrec.list_reverse.comp (Primrec.snd.comp Primrec.snd)) ?_
        exact primrec_actOf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
      · exact option_some.comp (primrec_compOf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    · refine Primrec.pair ?_ (Primrec.const none)
      refine Primrec.list_map (primrec_lin.comp Primrec.fst) ?_
      exact primrec_actOf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  refine Primrec.of_eq (Primrec.list_casesOn hrev (Primrec.const ([], none)) hmain) ?_
  intro t
  rcases h : (lin t).reverse with _ | ⟨z, rest⟩ <;> simp only [bodyOf, h]

end TnDesc

end Syn

end HTN
