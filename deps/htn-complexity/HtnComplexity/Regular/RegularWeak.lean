import HtnPlanning.Regular.RegularNormalForm
/-!
# Weak chains: the shape of the reachable networks of a *regular* problem

`HtnPlanning/Regular/RegularNormalForm.lean` analyses regular problems whose methods are
**totally ordered**: every reachable task network is then a *chain*, a linearly ordered
sequence of primitive tasks followed by at most one compound task, and it has exactly one
action sequence.

For a merely regular problem the reachable networks are **weak chains**: a set of primitive
tasks — arbitrarily ordered among themselves — all of which precede the at most one compound
task of the network.  A weak chain has in general *many* action sequences, one per
linearization of its primitive part, and this is exactly what makes the compilation of
`HTN-REG` into a totally ordered class non-trivial.

This file provides the task-network level of that analysis:

* `TaskNetwork.IsWeakChain tn tail` — `tn` is well formed, all its tasks except possibly `tail`
  are primitive, and `tail` (if present) is ordered after all of them;
* `TaskNetwork.Yields tn tail as` — some linearization of `tn` enumerates the primitive tasks
  with action sequence `as` and ends with `tail`;
* `TaskNetwork.Yields.split` and `TaskNetwork.Yields.compose` — decomposing the trailing
  compound task of a weak chain by a fresh copy of a weak chain yields a weak chain, and its
  action sequences are exactly the concatenations of an action sequence of the first with one
  of the second;
* `TaskNetwork.IsWeakChain.map`, `TaskNetwork.Yields.map` — both notions are transported along
  an isomorphism of task networks.

The normal form theorem built from these is in
`HtnComplexity/Regular/RegularWeakNormalForm.lean`.
-/

namespace HTN

universe u v w x

variable {A : Type v} {C : Type w} {I : Type x}

namespace TaskNetwork

section Weak

variable [DecidableEq I]

/-! ### Two list lemmas -/

omit [DecidableEq I] in
/-- A list in which no element failing `p` precedes an element satisfying `p` splits into the
elements satisfying `p` followed by the elements failing it. -/
lemma eq_filter_append_filter_not {α : Type*} {p : α → Bool} :
    ∀ {M : List α}, M.Pairwise (fun a b => p b = true → p a = true) →
      M = M.filter p ++ M.filter (fun x => ! p x) := by
  intro M
  induction M with
  | nil => simp
  | cons a M ih =>
      intro h
      rw [List.pairwise_cons] at h
      obtain ⟨hhead, htail⟩ := h
      by_cases ha : p a = true
      · simp [ha, ← ih htail]
      · simp only [Bool.not_eq_true] at ha
        have hM : ∀ b ∈ M, p b = false := by
          intro b hb
          by_contra hcon
          simp only [Bool.not_eq_false] at hcon
          simp [hhead b hb hcon] at ha
        have h1 : M.filter p = [] :=
          List.filter_eq_nil_iff.2 (by intro b hb; simp [hM b hb])
        have h2 : M.filter (fun x => ! p x) = M :=
          List.filter_eq_self.2 (by intro b hb; simp [hM b hb])
        simp [ha, h1, h2]

/-- A nodup list whose element `x` is preceded by all the others ends with `x`. -/
lemma eq_dropLast_append_last {M : List I} {x : I} (hnodup : M.Nodup) (hx : x ∈ M)
    (hlast : ∀ y ∈ M, y ≠ x → M.idxOf y < M.idxOf x) : M = M.dropLast ++ [x] := by
  classical
  have hxlt : M.idxOf x < M.length := List.idxOf_lt_length_of_mem hx
  have hidx : M.idxOf x = M.length - 1 := by
    by_contra hcon
    have hlt : M.idxOf x + 1 < M.length := by omega
    have hmem : M[M.idxOf x + 1]'hlt ∈ M := List.getElem_mem _
    have hidx' : M.idxOf (M[M.idxOf x + 1]'hlt) = M.idxOf x + 1 :=
      List.Nodup.idxOf_getElem hnodup _ hlt
    have hne : M[M.idxOf x + 1]'hlt ≠ x := by
      intro heq
      rw [heq] at hidx'
      omega
    have := hlast _ hmem hne
    rw [hidx'] at this
    omega
  have hne : M ≠ [] := by
    intro hcon
    rw [hcon] at hx
    simp at hx
  have hlen : M.length - 1 < M.length := by
    have := List.length_pos_of_ne_nil hne
    omega
  have hgl : M.getLast hne = x := by
    have hget : M.getLast hne = M[M.length - 1]'hlen := by rw [List.getLast_eq_getElem]
    rw [hget]
    have hidx' : M.idxOf (M[M.length - 1]'hlen) = M.length - 1 :=
      List.Nodup.idxOf_getElem hnodup _ hlen
    exact idxOf_inj_of_mem (List.getElem_mem hlen) hx (by rw [hidx', hidx])
  conv_lhs => rw [← List.dropLast_append_getLast hne, hgl]

/-- In a linearization, ordered tasks appear in the order of the ordering. -/
lemma idxOf_lt_of_ord {tn : TaskNetwork I A C} {M : List I} (hlin : tn.IsLinearization M)
    {x y : I} (hxy : tn.ord x y) (hx : x ∈ M) (hy : y ∈ M) (hne : x ≠ y) :
    M.idxOf x < M.idxOf y := by
  rcases lt_trichotomy (M.idxOf x) (M.idxOf y) with h | h | h
  · exact h
  · exact absurd (idxOf_inj_of_mem hx hy h) hne
  · exfalso
    have hpair := hlin.2.2
    rw [List.pairwise_iff_getElem] at hpair
    have hylt : M.idxOf y < M.length := List.idxOf_lt_length_of_mem hy
    have hxlt : M.idxOf x < M.length := List.idxOf_lt_length_of_mem hx
    have hkey := hpair (M.idxOf y) (M.idxOf x) hylt hxlt h
    rw [List.getElem_idxOf, List.getElem_idxOf] at hkey
    exact hkey hxy

/-! ### Weak chains -/

/-- **Weak chains.**  `tn.IsWeakChain tail` states that the task network `tn` consists of
primitive tasks — in an arbitrary partial order — followed by the optional compound task
`tail = some (t, c)`, which is ordered after all of them. -/
structure IsWeakChain (tn : TaskNetwork I A C) (tail : Option (I × C)) : Prop where
  /-- The network is well formed. -/
  wf : tn.WF
  /-- The trailing compound task belongs to the network. -/
  tailMem : ∀ p : I × C, tail = some p → p.1 ∈ tn.T
  /-- The trailing task is labelled by its compound task name. -/
  tailLabel : ∀ p : I × C, tail = some p → tn.α p.1 = Sum.inr p.2
  /-- Every other task precedes the trailing task. -/
  tailLast : ∀ p : I × C, tail = some p → ∀ x ∈ tn.T, x ≠ p.1 → tn.ord x p.1
  /-- All tasks but the trailing one are primitive. -/
  prim : ∀ x ∈ tn.T, (∀ p : I × C, tail = some p → x ≠ p.1) → tn.IsPrimitiveId x

/-- `tn.Yields tail as` states that some linearization of `tn` enumerates the primitive tasks
of `tn` with induced action sequence `as` and ends with the optional compound task `tail`. -/
def Yields (tn : TaskNetwork I A C) (tail : Option (I × C)) (as : List A) : Prop :=
  ∃ l : List I, tn.IsLinearization (chainIds l tail) ∧ tn.IsActionSeq l as ∧
    ∀ p : I × C, tail = some p → tn.α p.1 = Sum.inr p.2

omit [DecidableEq I] in
/-- A network that yields an action sequence without a trailing compound task is primitive. -/
lemma Yields.isPrimitive {tn : TaskNetwork I A C} {as : List A} (h : tn.Yields none as) :
    tn.IsPrimitive := by
  obtain ⟨l, hlin, hseq, -⟩ := h
  intro x hx
  have hxl : x ∈ l := by simpa using (hlin.2.1 x).2 hx
  have hmem : tn.α x ∈ l.map tn.α := List.mem_map_of_mem hxl
  rw [hseq] at hmem
  obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
  exact ⟨a, ha.symm⟩

namespace IsWeakChain

variable {tn : TaskNetwork I A C} {tail : Option (I × C)}

/-- Every linearization of a weak chain ends with its trailing compound task. -/
lemma linearization_eq (h : tn.IsWeakChain tail) {M : List I} (hlin : tn.IsLinearization M) :
    ∃ l : List I, M = chainIds l tail := by
  cases htail : tail with
  | none => exact ⟨M, rfl⟩
  | some p =>
      subst htail
      refine ⟨M.dropLast, ?_⟩
      rw [chainIds_some]
      have hpM : p.1 ∈ M := (hlin.2.1 p.1).2 (h.tailMem p rfl)
      refine eq_dropLast_append_last hlin.1 hpM ?_
      intro y hy hyp
      exact idxOf_lt_of_ord hlin (h.tailLast p rfl y ((hlin.2.1 y).1 hy) hyp) hy hpM hyp

omit [DecidableEq I] in
/-- A weak chain yields at least one action sequence. -/
lemma exists_yields (h : tn.IsWeakChain tail) : ∃ as : List A, tn.Yields tail as := by
  classical
  obtain ⟨M, hlin⟩ := exists_linearization h.wf
  obtain ⟨l, rfl⟩ := h.linearization_eq hlin
  have hprim : ∀ x ∈ l, tn.IsPrimitiveId x := by
    intro x hx
    have hxT : x ∈ tn.T := (hlin.2.1 x).1 (by cases tail <;> simp [hx])
    refine h.prim x hxT ?_
    rintro p rfl hxp
    have hnd := hlin.1
    rw [chainIds_some, List.nodup_append] at hnd
    exact hnd.2.2 x hx p.1 (by simp) hxp
  obtain ⟨as, has⟩ := exists_actionSeq hprim
  exact ⟨as, l, hlin, has, fun p hp => h.tailLabel p hp⟩

omit [DecidableEq I] in
/-- The trailing compound task of a weak chain is determined by the network. -/
lemma tail_eq_of_yields {tail' : Option (I × C)} {as : List A} (h : tn.IsWeakChain tail)
    (hy : tn.Yields tail' as) : tail = tail' := by
  obtain ⟨l, hlin, hseq, hlab⟩ := hy
  cases htail' : tail' with
  | none =>
      subst htail'
      cases htail : tail with
      | none => rfl
      | some p =>
          exfalso
          have hprim : tn.IsPrimitive := Yields.isPrimitive ⟨l, hlin, hseq, hlab⟩
          obtain ⟨a, ha⟩ := hprim p.1 (h.tailMem p htail)
          have := h.tailLabel p htail
          rw [ha] at this
          exact absurd this (by simp)
  | some q =>
      subst htail'
      have hqT : q.1 ∈ tn.T := (hlin.2.1 q.1).1 (by simp)
      have hqlab : tn.α q.1 = Sum.inr q.2 := hlab q rfl
      cases htail : tail with
      | none =>
          exfalso
          obtain ⟨a, ha⟩ := h.prim q.1 hqT (by simp [htail])
          rw [ha] at hqlab
          exact absurd hqlab (by simp)
      | some p =>
          have hne : ¬ (q.1 ≠ p.1) := by
            intro hne
            obtain ⟨a, ha⟩ := h.prim q.1 hqT (by
              rintro r hr
              rw [htail] at hr
              simp only [Option.some.injEq] at hr
              subst hr
              exact hne)
            rw [ha] at hqlab
            exact absurd hqlab (by simp)
          simp only [ne_eq, not_not] at hne
          have hplab := h.tailLabel p htail
          rw [← hne, hqlab] at hplab
          have hp2 : p.2 = q.2 := by simpa using hplab.symm
          exact congrArg some (Prod.ext hne.symm hp2)

omit [DecidableEq I] in
/-- Every well-formed regular task network is a weak chain. -/
lemma of_regular (hwf : tn.WF) (hreg : tn.IsRegular) :
    ∃ tail : Option (I × C), tn.IsWeakChain tail := by
  classical
  by_cases habs : ∃ t ∈ tn.T, tn.IsAbstractId t
  · obtain ⟨t, htT, c, hc⟩ := habs
    refine ⟨some (t, c), hwf, ?_, ?_, ?_, ?_⟩
    · rintro p ⟨rfl⟩; exact htT
    · rintro p ⟨rfl⟩; exact hc
    · rintro p ⟨rfl⟩ x hx hxt
      exact hreg.2 t htT ⟨c, hc⟩ x hx hxt
    · intro x hx hxp
      have hxt : x ≠ t := hxp (t, c) rfl
      rcases hcase : tn.α x with a | c'
      · exact ⟨a, hcase⟩
      · exact absurd (hreg.1 x hx t htT ⟨c', hcase⟩ ⟨c, hc⟩) hxt
  · push_neg at habs
    refine ⟨none, hwf, by rintro p ⟨⟩, by rintro p ⟨⟩, by rintro p ⟨⟩, ?_⟩
    intro x hx _
    rcases hcase : tn.α x with a | c'
    · exact ⟨a, hcase⟩
    · exact absurd ⟨c', hcase⟩ (habs x hx)

end IsWeakChain

/-! ### Transport along an isomorphism -/

section Iso

variable {tn tn' : TaskNetwork I A C} {σ : I → I} {tail : Option (I × C)}

omit [DecidableEq I] in
omit [DecidableEq I] in
/-- Weak chains are transported along an isomorphism of task networks. -/
lemma IsWeakChain.map (hbij : Set.BijOn σ (tn.T : Set I) (tn'.T : Set I))
    (hord : ∀ t ∈ tn.T, ∀ t' ∈ tn.T, (tn.ord t t' ↔ tn'.ord (σ t) (σ t')))
    (hα : ∀ t ∈ tn.T, tn.α t = tn'.α (σ t)) (hwf' : tn'.WF) (h : tn.IsWeakChain tail) :
    tn'.IsWeakChain (tail.map (fun p => (σ p.1, p.2))) := by
  have hmaps : ∀ x ∈ tn.T, σ x ∈ tn'.T := fun x hx => by simpa using hbij.mapsTo (by simpa using hx)
  refine ⟨hwf', ?_, ?_, ?_, ?_⟩
  · rintro p' hp'
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hp'
    exact hmaps _ (h.tailMem p hp)
  · rintro p' hp'
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hp'
    have := h.tailLabel p hp
    rw [hα p.1 (h.tailMem p hp)] at this
    exact this
  · rintro p' hp' x hx hxp
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hp'
    obtain ⟨y, hy, rfl⟩ := hbij.surjOn (by simpa using hx)
    have hyT : y ∈ tn.T := by simpa using hy
    have hyp : y ≠ p.1 := by
      intro hcon
      exact hxp (by rw [hcon])
    exact (hord y hyT p.1 (h.tailMem p hp)).1 (h.tailLast p hp y hyT hyp)
  · intro x hx hxp
    obtain ⟨y, hy, rfl⟩ := hbij.surjOn (by simpa using hx)
    have hyT : y ∈ tn.T := by simpa using hy
    obtain ⟨a, ha⟩ := h.prim y hyT (by
      rintro p hp hcon
      exact (hxp (σ p.1, p.2) (by simp [hp])) (by rw [hcon]))
    exact ⟨a, by rw [← hα y hyT]; exact ha⟩

omit [DecidableEq I] in
/-- Yielded action sequences are transported along an isomorphism of task networks. -/
lemma Yields.map (hbij : Set.BijOn σ (tn.T : Set I) (tn'.T : Set I))
    (hord : ∀ t ∈ tn.T, ∀ t' ∈ tn.T, (tn.ord t t' ↔ tn'.ord (σ t) (σ t')))
    (hα : ∀ t ∈ tn.T, tn.α t = tn'.α (σ t)) {as : List A} (h : tn.Yields tail as) :
    tn'.Yields (tail.map (fun p => (σ p.1, p.2))) as := by
  obtain ⟨l, hlin, hseq, hlab⟩ := h
  have hchainmap : chainIds (l.map σ) (tail.map (fun p => (σ p.1, p.2))) =
      (chainIds l tail).map σ := by cases tail <;> simp
  obtain ⟨hlin', -⟩ := Iso.map_isLinearization hbij hord hα hlin
  have hmemT : ∀ x ∈ l, x ∈ tn.T := by
    intro x hx
    exact (hlin.2.1 x).1 (by cases tail <;> simp [hx])
  refine ⟨l.map σ, by rw [hchainmap]; exact hlin', ?_, ?_⟩
  · have : (l.map σ).map tn'.α = l.map tn.α := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro x hx
      exact (hα x (hmemT x hx)).symm
    rw [IsActionSeq, this]
    exact hseq
  · rintro p' hp'
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hp'
    have hpT : p.1 ∈ tn.T := by
      refine (hlin.2.1 p.1).1 ?_
      rw [hp]; simp
    have := hlab p hp
    rw [hα p.1 hpT] at this
    exact this

end Iso

/-! ### Decomposing the trailing compound task of a weak chain -/

section Decompose

variable {tn₁ tn' : TaskNetwork I A C} {t : I} {c : C} {tail' : Option (I × C)}

/-- Every remaining old task precedes every inserted task. -/
lemma ord_old_new (h₁ : tn₁.IsWeakChain (some (t, c))) (hwf' : tn'.WF)
    (hdisj : Disjoint tn₁.T tn'.T) {x y : I} (hx : x ∈ tn₁.T) (hxt : x ≠ t) (hy : y ∈ tn'.T) :
    (decomposeWith tn₁ t tn').ord x y :=
  (decomposeWith_ord_old_new h₁.wf hwf' hdisj hx hy).2 (h₁.tailLast (t, c) rfl x hx hxt)

/-- No inserted task precedes a remaining old task. -/
lemma not_ord_new_old (h₁ : tn₁.IsWeakChain (some (t, c))) (hwf' : tn'.WF)
    (hdisj : Disjoint tn₁.T tn'.T) {x y : I} (hx : x ∈ tn'.T) (hy : y ∈ tn₁.T) (hyt : y ≠ t) :
    ¬ (decomposeWith tn₁ t tn').ord x y := by
  rw [decomposeWith_ord_new_old h₁.wf hwf' hdisj hx hy]
  intro hcon
  exact h₁.wf.asymm hcon (h₁.tailLast (t, c) rfl y hy hyt)

/-- The decomposed task does not survive the decomposition. -/
lemma not_mem_decomposeWith_self (h₁ : tn₁.IsWeakChain (some (t, c)))
    (hdisj : Disjoint tn₁.T tn'.T) : t ∉ (decomposeWith tn₁ t tn').T := by
  intro hcon
  rcases mem_decomposeWith_T.1 hcon with ⟨-, hne⟩ | hmem
  · exact hne rfl
  · exact (Finset.disjoint_left.1 hdisj (h₁.tailMem (t, c) rfl)) hmem

/-- **Decomposing the trailing compound task of a weak chain by a weak chain gives a weak
chain.** -/
theorem IsWeakChain.decompose (h₁ : tn₁.IsWeakChain (some (t, c)))
    (h' : tn'.IsWeakChain tail') (hdisj : Disjoint tn₁.T tn'.T) :
    (decomposeWith tn₁ t tn').IsWeakChain tail' := by
  have hwf₂ : (decomposeWith tn₁ t tn').WF := decomposeWith_wf h₁.wf h'.wf hdisj
  refine ⟨hwf₂, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact mem_decomposeWith_T.2 (Or.inr (h'.tailMem p hp))
  · intro p hp
    have hpT : p.1 ∈ tn'.T := h'.tailMem p hp
    simpa [decomposeWith_α, hpT] using h'.tailLabel p hp
  · intro p hp x hx hxp
    rcases mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx'
    · exact ord_old_new h₁ h'.wf hdisj hx₁ hxt (h'.tailMem p hp)
    · refine (decomposeWith_ord_new_new h₁.wf hdisj hx' (h'.tailMem p hp)).2 ?_
      exact h'.tailLast p hp x hx' hxp
  · intro x hx hxp
    rcases mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx'
    · have hxu : x ∉ tn'.T := Finset.disjoint_left.1 hdisj hx₁
      obtain ⟨a, ha⟩ := h₁.prim x hx₁ (by rintro q ⟨rfl⟩; exact hxt)
      exact ⟨a, by simpa [decomposeWith_α, hxu] using ha⟩
    · obtain ⟨a, ha⟩ := h'.prim x hx' hxp
      exact ⟨a, by simpa [decomposeWith_α, hx'] using ha⟩

/-- **The action sequences of a decomposed weak chain split.** -/
theorem Yields.split (h₁ : tn₁.IsWeakChain (some (t, c))) (h' : tn'.IsWeakChain tail')
    (hdisj : Disjoint tn₁.T tn'.T) {as₂ : List A}
    (h : (decomposeWith tn₁ t tn').Yields tail' as₂) :
    ∃ as os : List A, as₂ = as ++ os ∧ tn₁.Yields (some (t, c)) as ∧ tn'.Yields tail' os := by
  classical
  obtain ⟨l₂, hlin₂, hseq₂, hlab₂⟩ := h
  set M : List I := chainIds l₂ tail' with hMdef
  set p : I → Bool := fun x => decide (x ∈ tn₁.T) with hpdef
  have hMmem : ∀ x, x ∈ M ↔ x ∈ (decomposeWith tn₁ t tn').T := hlin₂.2.1
  have hMold : ∀ x, x ∈ M.filter p ↔ (x ∈ tn₁.T ∧ x ≠ t) := by
    intro x
    rw [List.mem_filter]
    constructor
    · rintro ⟨hxM, hpx⟩
      have hx₁ : x ∈ tn₁.T := by simpa [hpdef] using hpx
      rcases mem_decomposeWith_T.1 ((hMmem x).1 hxM) with ⟨-, hxt⟩ | hx'
      · exact ⟨hx₁, hxt⟩
      · exact absurd hx' (Finset.disjoint_left.1 hdisj hx₁)
    · rintro ⟨hx₁, hxt⟩
      exact ⟨(hMmem x).2 (mem_decomposeWith_T.2 (Or.inl ⟨hx₁, hxt⟩)), by simp [hpdef, hx₁]⟩
  have hMnew : ∀ x, x ∈ M.filter (fun x => ! p x) ↔ x ∈ tn'.T := by
    intro x
    rw [List.mem_filter]
    constructor
    · rintro ⟨hxM, hpx⟩
      have hx₁ : x ∉ tn₁.T := by simpa [hpdef] using hpx
      rcases mem_decomposeWith_T.1 ((hMmem x).1 hxM) with ⟨hx, -⟩ | hx'
      · exact absurd hx hx₁
      · exact hx'
    · intro hx'
      have hx₁ : x ∉ tn₁.T := fun hcon => (Finset.disjoint_left.1 hdisj hcon) hx'
      exact ⟨(hMmem x).2 (mem_decomposeWith_T.2 (Or.inr hx')), by simp [hpdef, hx₁]⟩
  -- the split of the linearization
  have hpair : M.Pairwise (fun a b => p b = true → p a = true) := by
    refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.and_mem.1 hlin₂.2.2)
    rintro a b ha hb ⟨-, -, hnord⟩ hpb
    by_contra hpa
    have hb₁ : b ∈ tn₁.T := by simpa [hpdef] using hpb
    have ha₁ : a ∉ tn₁.T := by simpa [hpdef] using hpa
    have ha' : a ∈ tn'.T := (hMnew a).1 (List.mem_filter.2 ⟨ha, by simp [hpdef, ha₁]⟩)
    have hbt : b ≠ t := ((hMold b).1 (List.mem_filter.2 ⟨hb, hpb⟩)).2
    exact hnord (ord_old_new h₁ h'.wf hdisj hb₁ hbt ha')
  have hsplit : M = M.filter p ++ M.filter (fun x => ! p x) :=
    eq_filter_append_filter_not hpair
  set Mold : List I := M.filter p with hMolddef
  set Mnew : List I := M.filter (fun x => ! p x) with hMnewdef
  have hnodupM : M.Nodup := hlin₂.1
  have hnodupOld : Mold.Nodup := hnodupM.filter _
  have hnodupNew : Mnew.Nodup := hnodupM.filter _
  have htM : t ∉ M := by
    intro hcon
    exact not_mem_decomposeWith_self h₁ hdisj ((hMmem t).1 hcon)
  have htOld : t ∉ Mold := fun hcon => htM (List.mem_of_mem_filter hcon)
  -- `Mold ++ [t]` is a linearization of `tn₁`
  have hlinOld : tn₁.IsLinearization (chainIds Mold (some (t, c))) := by
    rw [chainIds_some]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Nodup.append hnodupOld (by simp) (by
        intro x hx hx'
        simp only [List.mem_singleton] at hx'
        subst hx'
        exact htOld hx)
    · intro x
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (hx | hx)
        · exact ((hMold x).1 hx).1
        · rw [hx]; exact h₁.tailMem (t, c) rfl
      · intro hx
        by_cases hxt : x = t
        · exact Or.inr hxt
        · exact Or.inl ((hMold x).2 ⟨hx, hxt⟩)
    · refine List.pairwise_append.2 ⟨?_, by simp, ?_⟩
      · refine List.Pairwise.imp_of_mem ?_
          (List.Pairwise.and_mem.1 (List.Pairwise.filter p hlin₂.2.2))
        rintro a b ha hb ⟨-, -, hnord⟩ hcon
        obtain ⟨ha₁, hat⟩ := (hMold a).1 ha
        obtain ⟨hb₁, hbt⟩ := (hMold b).1 hb
        exact hnord ((decomposeWith_ord_old_old h'.wf hdisj hb₁ hbt ha₁ hat).2 hcon)
      · intro a ha b hb
        simp only [List.mem_singleton] at hb
        rw [hb]
        intro hcon
        obtain ⟨ha₁, hat⟩ := (hMold a).1 ha
        exact h₁.wf.asymm hcon (h₁.tailLast (t, c) rfl a ha₁ hat)
  -- `Mnew` is a linearization of `tn'`
  have hlinNew : tn'.IsLinearization Mnew := by
    refine ⟨hnodupNew, fun x => hMnew x, ?_⟩
    refine List.Pairwise.imp_of_mem ?_
      (List.Pairwise.and_mem.1 (List.Pairwise.filter (fun x => ! p x) hlin₂.2.2))
    rintro a b ha hb ⟨-, -, hnord⟩ hcon
    have ha' : a ∈ tn'.T := (hMnew a).1 ha
    have hb' : b ∈ tn'.T := (hMnew b).1 hb
    exact hnord ((decomposeWith_ord_new_new h₁.wf hdisj hb' ha').2 hcon)
  obtain ⟨l', hl'⟩ := h'.linearization_eq hlinNew
  -- the two halves of the id list
  have hl₂ : l₂ = Mold ++ l' := by
    have h1 : chainIds l₂ tail' = chainIds (Mold ++ l') tail' := by
      rw [chainIds_append, ← hl']
      exact hsplit
    cases tail' with
    | none => simpa using h1
    | some q =>
        simp only [chainIds_some] at h1
        exact List.append_inj_left' h1 rfl
  -- the two action sequences
  have hprimOld : ∀ x ∈ Mold, tn₁.IsPrimitiveId x := by
    intro x hx
    obtain ⟨hx₁, hxt⟩ := (hMold x).1 hx
    exact h₁.prim x hx₁ (by rintro q ⟨rfl⟩; exact hxt)
  have hprimNew : ∀ x ∈ l', tn'.IsPrimitiveId x := by
    intro x hx
    have hxN : x ∈ Mnew := by rw [hl']; cases tail' <;> simp [hx]
    refine h'.prim x ((hMnew x).1 hxN) ?_
    rintro q hq hxq
    have hnd := hnodupNew
    rw [hl', hq, chainIds_some, List.nodup_append] at hnd
    exact hnd.2.2 x hx q.1 (by simp) hxq
  obtain ⟨as, has⟩ := exists_actionSeq hprimOld
  obtain ⟨os, hos⟩ := exists_actionSeq hprimNew
  refine ⟨as, os, ?_, ⟨Mold, hlinOld, has, fun q hq => by
      simp only [Option.some.injEq] at hq; subst hq; exact h₁.tailLabel (t, c) rfl⟩,
    ⟨l', by rw [← hl']; exact hlinNew, hos, fun q hq => h'.tailLabel q hq⟩⟩
  -- the concatenation of the two action sequences is the original one
  have hmapOld : Mold.map (decomposeWith tn₁ t tn').α = Mold.map tn₁.α := by
    refine List.map_congr_left ?_
    intro x hx
    obtain ⟨hx₁, -⟩ := (hMold x).1 hx
    have hxu : x ∉ tn'.T := Finset.disjoint_left.1 hdisj hx₁
    simp [decomposeWith_α, hxu]
  have hmapNew : l'.map (decomposeWith tn₁ t tn').α = l'.map tn'.α := by
    refine List.map_congr_left ?_
    intro x hx
    have hxN : x ∈ Mnew := by rw [hl']; cases tail' <;> simp [hx]
    have hx' : x ∈ tn'.T := (hMnew x).1 hxN
    simp [decomposeWith_α, hx']
  have hfull : as₂.map (Sum.inl (β := C)) = (as ++ os).map Sum.inl := by
    rw [← hseq₂, hl₂, List.map_append, hmapOld, hmapNew, has, hos, List.map_append]
  exact List.map_injective_iff.2 (fun _ _ hxy => Sum.inl_injective hxy) hfull

/-- **Action sequences of a weak chain and of the inserted network compose.** -/
theorem Yields.compose (h₁ : tn₁.IsWeakChain (some (t, c))) (h' : tn'.IsWeakChain tail')
    (hdisj : Disjoint tn₁.T tn'.T) {as os : List A}
    (ha : tn₁.Yields (some (t, c)) as) (ho : tn'.Yields tail' os) :
    (decomposeWith tn₁ t tn').Yields tail' (as ++ os) := by
  classical
  obtain ⟨l, hlin, hseq, -⟩ := ha
  obtain ⟨l', hlin', hseq', hlab'⟩ := ho
  rw [chainIds_some] at hlin
  set N : List I := chainIds l' tail' with hNdef
  have hlN : ∀ x ∈ N, x ∈ tn'.T := fun x hx => (hlin'.2.1 x).1 hx
  have hlT : ∀ x ∈ l, x ∈ tn₁.T := fun x hx => (hlin.2.1 x).1 (List.mem_append_left _ hx)
  have hlt : t ∉ l := by
    intro hcon
    have := hlin.1
    rw [List.nodup_append] at this
    exact this.2.2 t hcon t (by simp) rfl
  have hlne : ∀ x ∈ l, x ≠ t := fun x hx hcon => hlt (hcon ▸ hx)
  have hdisj' : ∀ x ∈ l, x ∉ N := by
    intro x hx hxN
    exact (Finset.disjoint_left.1 hdisj (hlT x hx)) (hlN x hxN)
  refine ⟨l ++ l', ?_, ?_, ?_⟩
  · rw [chainIds_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Nodup.append ((List.nodup_append.1 hlin.1).1) hlin'.1 hdisj'
    · intro x
      rw [List.mem_append]
      constructor
      · rintro (hx | hx)
        · exact mem_decomposeWith_T.2 (Or.inl ⟨hlT x hx, hlne x hx⟩)
        · exact mem_decomposeWith_T.2 (Or.inr (hlN x hx))
      · intro hx
        rcases mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx'
        · refine Or.inl ?_
          have := (hlin.2.1 x).2 hx₁
          rcases List.mem_append.1 this with h | h
          · exact h
          · simp only [List.mem_singleton] at h
            exact absurd h hxt
        · exact Or.inr ((hlin'.2.1 x).2 hx')
    · refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
      · refine List.Pairwise.imp_of_mem ?_
          (List.Pairwise.and_mem.1 ((List.pairwise_append.1 hlin.2.2).1))
        rintro a b ha' hb' ⟨-, -, hnord⟩ hcon
        refine hnord ?_
        exact (decomposeWith_ord_old_old h'.wf hdisj (hlT b hb') (hlne b hb')
          (hlT a ha') (hlne a ha')).1 hcon
      · refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.and_mem.1 hlin'.2.2)
        rintro a b ha' hb' ⟨-, -, hnord⟩ hcon
        exact hnord ((decomposeWith_ord_new_new h₁.wf hdisj (hlN b hb') (hlN a ha')).1 hcon)
      · intro a ha' b hb'
        exact not_ord_new_old h₁ h'.wf hdisj (hlN b hb') (hlT a ha') (hlne a ha')
  · have hmapl : l.map (decomposeWith tn₁ t tn').α = l.map tn₁.α := by
      refine List.map_congr_left ?_
      intro x hx
      have hxu : x ∉ tn'.T := Finset.disjoint_left.1 hdisj (hlT x hx)
      simp [decomposeWith_α, hxu]
    have hmapl' : l'.map (decomposeWith tn₁ t tn').α = l'.map tn'.α := by
      refine List.map_congr_left ?_
      intro x hx
      have hx' : x ∈ tn'.T := hlN x (by rw [hNdef]; cases tail' <;> simp [hx])
      simp [decomposeWith_α, hx']
    show (l ++ l').map (decomposeWith tn₁ t tn').α = (as ++ os).map Sum.inl
    rw [List.map_append, hmapl, hmapl', hseq, hseq', List.map_append]
  · intro q hq
    have hqT : q.1 ∈ tn'.T := hlN q.1 (by rw [hNdef, hq]; simp)
    simpa [decomposeWith_α, hqT] using hlab' q hq

end Decompose

end Weak

end TaskNetwork

end HTN
