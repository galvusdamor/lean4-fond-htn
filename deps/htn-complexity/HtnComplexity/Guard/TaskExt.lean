import HtnComplexity.Guard.Insert
import HtnComplexity.Guard.Order
import HtnPlanning.Interleave.NetYield
/-!
# Guard tasks: the decomposition-level simulation

A *method guard* — "this method may only be applied when the instance says so" — is simulated in
the HTN formalism by putting an extra, unordered primitive subtask into the method's body whose
action is a no-op with the guard fact as its precondition.  This file relates the derivations of
the guarded domain to those of the original one.

* `HTN.GuardTask.addTask` — a network with one extra isolated primitive task;
* `HTN.GuardTask.guardMethod` — the method with its guard task;
* `HTN.GuardTask.Ext` — the invariant: the guarded network is the original one together with a
  set `K` of extra tasks, all of them carrying guard actions, the ordering of the old tasks being
  unchanged;
* `HTN.GuardTask.exists_ext_of_decomposesTo` — every derivation of the original domain is
  mirrored by one of the guarded domain, with guard ids avoiding any prescribed finite set;
* `HTN.GuardTask.exists_proj_of_decomposesTo` — every derivation of the guarded domain projects
  to one of the original domain.

Both simulations are inductions along the derivation from its *last* step: the freshness of the
guard ids is then chosen after the step that has to avoid them, which is what makes the
bookkeeping go through.
-/

namespace HTN

namespace GuardTask

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### The guarded method -/

/-- The network `tn` with one extra isolated task `k`, labelled by the action `a`. -/
def addTask [DecidableEq I] (tn : TaskNetwork I A C) (k : I) (a : A) : TaskNetwork I A C where
  T := insert k tn.T
  ord := tn.ord
  α := Function.update tn.α k (Sum.inl a)

@[simp] lemma addTask_T [DecidableEq I] (tn : TaskNetwork I A C) (k : I) (a : A) :
    (addTask tn k a).T = insert k tn.T := rfl

@[simp] lemma addTask_ord [DecidableEq I] (tn : TaskNetwork I A C) (k : I) (a : A) :
    (addTask tn k a).ord = tn.ord := rfl

lemma addTask_α_self [DecidableEq I] (tn : TaskNetwork I A C) (k : I) (a : A) :
    (addTask tn k a).α k = Sum.inl a := by simp [addTask]

lemma addTask_α_of_ne [DecidableEq I] (tn : TaskNetwork I A C) {k x : I} (a : A) (h : x ≠ k) :
    (addTask tn k a).α x = tn.α x := by simp [addTask, Function.update_of_ne h]

/-- Adding an isolated task preserves well-formedness. -/
lemma addTask_wf [DecidableEq I] {tn : TaskNetwork I A C} (hwf : tn.WF) (k : I) (a : A) :
    (addTask tn k a).WF where
  mem_left := fun h => by simp [Finset.mem_insert, hwf.mem_left h]
  mem_right := fun h => by simp [Finset.mem_insert, hwf.mem_right h]
  irrefl := hwf.irrefl
  trans := hwf.trans

/-- A task outside a well-formed network is unordered in it. -/
lemma not_ord_of_not_mem {tn : TaskNetwork I A C} (hwf : tn.WF) {k : I} (hk : k ∉ tn.T) (x : I) :
    ¬ tn.ord k x ∧ ¬ tn.ord x k :=
  ⟨fun h => hk (hwf.mem_left h), fun h => hk (hwf.mem_right h)⟩

/-- **Adding an isolated task to two isomorphic networks keeps them isomorphic.** -/
lemma addTask_iso [DecidableEq I] {u v : TaskNetwork I A C} {k j : I} {a : A} (hiso : u.Iso v)
    (huwf : u.WF) (hvwf : v.WF) (hk : k ∉ u.T) (hj : j ∉ v.T) :
    (addTask u k a).Iso (addTask v j a) := by
  classical
  obtain ⟨σ, hbij, hord, hα⟩ := hiso
  set τ : I → I := Function.update σ k j with hτ
  have hτk : τ k = j := by simp [hτ]
  have hτne : ∀ x, x ≠ k → τ x = σ x := by
    intro x hx; simp [hτ, Function.update_of_ne hx]
  refine ⟨τ, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · -- maps to
      intro x hx
      simp only [addTask_T, Finset.coe_insert, Set.mem_insert_iff] at hx ⊢
      by_cases hxk : x = k
      · subst hxk; left; exact hτk
      · right
        have hxu : x ∈ (u.T : Set I) := by
          rcases hx with h | h
          · exact absurd h hxk
          · exact h
        rw [hτne x hxk]
        exact hbij.mapsTo hxu
    · -- injective on
      intro x hx y hy hxy
      simp only [addTask_T, Finset.coe_insert, Set.mem_insert_iff] at hx hy
      by_cases hxk : x = k <;> by_cases hyk : y = k
      · rw [hxk, hyk]
      · have hyu : y ∈ (u.T : Set I) := by
          rcases hy with h | h
          · exact absurd h hyk
          · exact h
        rw [hxk, hτk, hτne y hyk] at hxy
        exact absurd (hxy ▸ hbij.mapsTo hyu) hj
      · have hxu : x ∈ (u.T : Set I) := by
          rcases hx with h | h
          · exact absurd h hxk
          · exact h
        rw [hyk, hτk, hτne x hxk] at hxy
        exact absurd (hxy.symm ▸ hbij.mapsTo hxu) hj
      · have hxu : x ∈ (u.T : Set I) := by
          rcases hx with h | h
          · exact absurd h hxk
          · exact h
        have hyu : y ∈ (u.T : Set I) := by
          rcases hy with h | h
          · exact absurd h hyk
          · exact h
        rw [hτne x hxk, hτne y hyk] at hxy
        exact hbij.injOn hxu hyu hxy
    · -- surjective on
      intro w hw
      simp only [addTask_T, Finset.coe_insert, Set.mem_insert_iff] at hw
      rcases hw with rfl | hw
      · exact ⟨k, by simp, hτk⟩
      · obtain ⟨x, hx, hxw⟩ := hbij.surjOn hw
        have hxk : x ≠ k := by
          intro hcon
          exact hk (by simpa [hcon] using hx)
        refine ⟨x, ?_, ?_⟩
        · simp only [addTask_T, Finset.coe_insert, Set.mem_insert_iff]
          exact Or.inr hx
        · rw [hτne x hxk]; exact hxw
  · -- the ordering
    intro x hx y hy
    simp only [addTask_T, Finset.mem_insert] at hx hy
    simp only [addTask_ord]
    by_cases hxk : x = k
    · have hL : ¬ u.ord x y := by
        subst hxk; exact (not_ord_of_not_mem huwf hk y).1
      have hR : ¬ v.ord (τ x) (τ y) := by
        rw [hxk, hτk]
        exact (not_ord_of_not_mem hvwf hj _).1
      simp [hL, hR]
    · by_cases hyk : y = k
      · have hL : ¬ u.ord x y := by
          subst hyk; exact (not_ord_of_not_mem huwf hk x).2
        have hR : ¬ v.ord (τ x) (τ y) := by
          rw [hyk, hτk]
          exact (not_ord_of_not_mem hvwf hj _).2
        simp [hL, hR]
      · have hxu : x ∈ u.T := by
          rcases hx with h | h
          · exact absurd h hxk
          · exact h
        have hyu : y ∈ u.T := by
          rcases hy with h | h
          · exact absurd h hyk
          · exact h
        rw [hτne x hxk, hτne y hyk]
        exact hord x hxu y hyu
  · -- the labels
    intro x hx
    simp only [addTask_T, Finset.mem_insert] at hx
    by_cases hxk : x = k
    · subst hxk
      rw [hτk, addTask_α_self, addTask_α_self]
    · have hxu : x ∈ u.T := by
        rcases hx with h | h
        · exact absurd h hxk
        · exact h
      have hsx : σ x ≠ j := by
        intro hcon
        exact hj (hcon ▸ hbij.mapsTo hxu)
      rw [hτne x hxk, addTask_α_of_ne _ _ hxk, addTask_α_of_ne _ _ hsx]
      exact hα x hxu

/-- **The guarded method**: the body of `m` with one extra isolated primitive subtask, whose
action is the guard action of `m`. -/
def guardMethod [DecidableEq I] (gid : Method I A C → I) (gact : Method I A C → A)
    (m : Method I A C) : Method I A C where
  abstractTask := m.abstractTask
  subtasks := addTask m.subtasks (gid m) (gact m)

@[simp] lemma guardMethod_abstractTask [DecidableEq I] (gid : Method I A C → I)
    (gact : Method I A C → A) (m : Method I A C) :
    (guardMethod gid gact m).abstractTask = m.abstractTask := rfl

@[simp] lemma guardMethod_subtasks [DecidableEq I] (gid : Method I A C → I)
    (gact : Method I A C → A) (m : Method I A C) :
    (guardMethod gid gact m).subtasks = addTask m.subtasks (gid m) (gact m) := rfl

/-! ### The invariant -/

/-- **The guarded network is the original one plus guard tasks.**  `K` collects the extra
tasks; they are primitive and carry guard actions, and the ordering of the old tasks is the
ordering they had. -/
structure Ext (Chk : A → Prop) (tn tng : TaskNetwork I A C) (K : Finset I) : Prop where
  /-- The tasks are the old ones together with the guard tasks. -/
  memT : ∀ z, z ∈ tng.T ↔ (z ∈ tn.T ∨ z ∈ K)
  /-- The guard tasks are new. -/
  disj : ∀ z ∈ tn.T, z ∉ K
  /-- The old tasks keep their labels. -/
  lab : ∀ z ∈ tn.T, tng.α z = tn.α z
  /-- The guard tasks are primitive and carry guard actions. -/
  chk : ∀ z ∈ K, ∃ a, tng.α z = Sum.inl a ∧ Chk a
  /-- The ordering of the old tasks is unchanged. -/
  ord_iff : ∀ a ∈ tn.T, ∀ b ∈ tn.T, (tng.ord a b ↔ tn.ord a b)

variable {Chk : A → Prop}

/-- The empty extension. -/
lemma Ext.refl (tn : TaskNetwork I A C) : Ext Chk tn tn ∅ where
  memT := fun z => by simp
  disj := fun z _ => by simp
  lab := fun _ _ => rfl
  chk := fun z hz => absurd hz (by simp)
  ord_iff := fun _ _ _ _ => Iff.rfl

/-- A guard task is not an old task. -/
lemma Ext.not_mem_of_mem_K {tn tng : TaskNetwork I A C} {K : Finset I} (h : Ext Chk tn tng K)
    {z : I} (hz : z ∈ K) : z ∉ tn.T := fun hzT => h.disj z hzT hz

/-- The old tasks are tasks of the guarded network. -/
lemma Ext.mem_of_mem {tn tng : TaskNetwork I A C} {K : Finset I} (h : Ext Chk tn tng K) {z : I}
    (hz : z ∈ tn.T) : z ∈ tng.T := (h.memT z).2 (Or.inl hz)

/-- A compound task of the guarded network is an old task. -/
lemma Ext.mem_of_isAbstract {tn tng : TaskNetwork I A C} {K : Finset I} (h : Ext Chk tn tng K)
    {z : I} {c : C} (hz : z ∈ tng.T) (hα : tng.α z = Sum.inr c) : z ∈ tn.T := by
  rcases (h.memT z).1 hz with hzT | hzK
  · exact hzT
  · obtain ⟨a, ha, -⟩ := h.chk z hzK
    rw [ha] at hα
    exact absurd hα (by simp)

/-! ### One step of the simulation -/

variable [DecidableEq I]

/-- **The invariant is preserved by a matched pair of decomposition steps**: the original domain
inserts `u`, the guarded one the same network with the guard task `k` added. -/
theorem Ext.decompose {tn tng u ug : TaskNetwork I A C} {K : Finset I} {t k : I} {a : A}
    (hext : Ext Chk tn tng K) (hwf : tn.WF) (hwfg : tng.WF) (htT : t ∈ tn.T)
    (hdisj : Disjoint tn.T u.T) (hdisjg : Disjoint tng.T ug.T)
    (hug : ug = addTask u k a) (hk : k ∉ u.T) (hka : Chk a)
    (hKu : ∀ z ∈ K, z ∉ u.T) :
    Ext Chk (decomposeWith tn t u) (decomposeWith tng t ug) (insert k K) := by
  classical
  have hugT : ∀ z, z ∈ ug.T ↔ (z = k ∨ z ∈ u.T) := by
    intro z; simp [hug, Finset.mem_insert]
  have hugord : ug.ord = u.ord := by simp [hug]
  have hkg : k ∉ tng.T := fun hkT =>
    (Finset.disjoint_left.1 hdisjg) hkT ((hugT k).2 (Or.inl rfl))
  have htK : t ∉ K := hext.disj t htT
  -- the ordering of the two networks agrees on the old tasks and the inserted ones
  have key : ∀ z w : I, (z ∈ tn.T ∨ z ∈ u.T) → (w ∈ tn.T ∨ w ∈ u.T) →
      (tng.ord z w ↔ tn.ord z w) := by
    have hnot : ∀ z, z ∈ u.T → z ∉ tn.T ∧ z ∉ tng.T := by
      intro z hz
      have h1 : z ∉ tn.T := fun h => (Finset.disjoint_left.1 hdisj) h hz
      refine ⟨h1, ?_⟩
      intro h
      rcases (hext.memT z).1 h with h' | h'
      · exact h1 h'
      · exact hKu z h' hz
    intro z w hz hw
    rcases hz with hz | hz
    · rcases hw with hw | hw
      · exact hext.ord_iff z hz w hw
      · obtain ⟨hw1, hw2⟩ := hnot w hw
        exact ⟨fun h => absurd (hwfg.mem_right h) hw2, fun h => absurd (hwf.mem_right h) hw1⟩
    · obtain ⟨hz1, hz2⟩ := hnot z hz
      exact ⟨fun h => absurd (hwfg.mem_left h) hz2, fun h => absurd (hwf.mem_left h) hz1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the tasks
    intro z
    constructor
    · intro hz
      rcases mem_decomposeWith_T.1 hz with ⟨hzg, hzt⟩ | hzu
      · rcases (hext.memT z).1 hzg with h | h
        · exact Or.inl (mem_decomposeWith_T.2 (Or.inl ⟨h, hzt⟩))
        · exact Or.inr (Finset.mem_insert.2 (Or.inr h))
      · rcases (hugT z).1 hzu with rfl | h
        · exact Or.inr (Finset.mem_insert.2 (Or.inl rfl))
        · exact Or.inl (mem_decomposeWith_T.2 (Or.inr h))
    · intro hz
      rcases hz with hz | hz
      · rcases mem_decomposeWith_T.1 hz with ⟨hzT, hzt⟩ | hzu
        · exact mem_decomposeWith_T.2 (Or.inl ⟨hext.mem_of_mem hzT, hzt⟩)
        · exact mem_decomposeWith_T.2 (Or.inr ((hugT z).2 (Or.inr hzu)))
      · rcases Finset.mem_insert.1 hz with rfl | hzK
        · exact mem_decomposeWith_T.2 (Or.inr ((hugT z).2 (Or.inl rfl)))
        · refine mem_decomposeWith_T.2 (Or.inl ⟨(hext.memT z).2 (Or.inr hzK), ?_⟩)
          rintro rfl
          exact htK hzK
  · -- the guard tasks are new
    intro z hz
    rcases mem_decomposeWith_T.1 hz with ⟨hzT, -⟩ | hzu
    · simp only [Finset.mem_insert]
      rintro (rfl | hzK)
      · exact hkg (hext.mem_of_mem hzT)
      · exact hext.disj z hzT hzK
    · simp only [Finset.mem_insert]
      rintro (rfl | hzK)
      · exact hk hzu
      · exact hKu z hzK hzu
  · -- the labels of the old tasks
    intro z hz
    rcases mem_decomposeWith_T.1 hz with ⟨hzT, -⟩ | hzu
    · have hzu' : z ∉ u.T := Finset.disjoint_left.1 hdisj hzT
      have hzug : z ∉ ug.T := by
        rw [hugT]
        rintro (rfl | h)
        · exact hkg (hext.mem_of_mem hzT)
        · exact hzu' h
      rw [decomposeWith_α, if_neg hzug, decomposeWith_α, if_neg hzu', hext.lab z hzT]
    · have hzug : z ∈ ug.T := (hugT z).2 (Or.inr hzu)
      have hzk : z ≠ k := by rintro rfl; exact hk hzu
      rw [decomposeWith_α, if_pos hzug, decomposeWith_α, if_pos hzu, hug,
        addTask_α_of_ne _ _ hzk]
  · -- the guard tasks carry guard actions
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzK
    · refine ⟨a, ?_, hka⟩
      have hzug : z ∈ ug.T := (hugT z).2 (Or.inl rfl)
      rw [decomposeWith_α, if_pos hzug, hug, addTask_α_self]
    · obtain ⟨b, hb, hbchk⟩ := hext.chk z hzK
      have hzg : z ∈ tng.T := (hext.memT z).2 (Or.inr hzK)
      have hzug : z ∉ ug.T := Finset.disjoint_left.1 hdisjg hzg
      exact ⟨b, by rw [decomposeWith_α, if_neg hzug, hb], hbchk⟩
  · -- the ordering of the old tasks
    intro x hx y hy
    have hx' : x ∈ tn.T ∨ x ∈ u.T := by
      rcases mem_decomposeWith_T.1 hx with ⟨h, -⟩ | h
      · exact Or.inl h
      · exact Or.inr h
    have hy' : y ∈ tn.T ∨ y ∈ u.T := by
      rcases mem_decomposeWith_T.1 hy with ⟨h, -⟩ | h
      · exact Or.inl h
      · exact Or.inr h
    have hxk : x ≠ k := by
      rintro rfl
      rcases hx' with h | h
      · exact hkg (hext.mem_of_mem h)
      · exact hk h
    have hyk : y ≠ k := by
      rintro rfl
      rcases hy' with h | h
      · exact hkg (hext.mem_of_mem h)
      · exact hk h
    have hxug : (x ∈ ug.T) ↔ (x ∈ u.T) := by
      rw [hugT]
      exact ⟨fun h => h.resolve_left hxk, Or.inr⟩
    have hyug : (y ∈ ug.T) ↔ (y ∈ u.T) := by
      rw [hugT]
      exact ⟨fun h => h.resolve_left hyk, Or.inr⟩
    rw [decomposeWith_ord_iff, decomposeWith_ord_iff, hugord, key x y hx' hy',
      key x t hx' (Or.inl htT), key t y (Or.inl htT) hy']
    simp only [hxug, hyug]

/-! ### The two simulations -/

/-- **Every derivation of the original domain is mirrored by the guarded domain.**  The guard
ids may be chosen outside any prescribed finite set, which is what makes the induction along the
derivation go through. -/
theorem exists_ext_of_decomposesTo [Infinite I] {M Mg : Set (Method I A C)}
    {gid : Method I A C → I} {gact : Method I A C → A}
    (hmeth : ∀ m ∈ M, guardMethod gid gact m ∈ Mg)
    (hwfm : ∀ m ∈ M, m.subtasks.WF) (hfresh : ∀ m ∈ M, gid m ∉ m.subtasks.T)
    (hChk : ∀ m ∈ M, Chk (gact m))
    {tn tn' : TaskNetwork I A C} (hwf : tn.WF) (hdec : DecomposesTo M tn tn') :
    ∀ S : Finset I, ∃ (tng : TaskNetwork I A C) (K : Finset I),
      DecomposesTo Mg tn tng ∧ Ext Chk tn' tng K ∧ (∀ z ∈ K, z ∉ S) := by
  classical
  induction hdec with
  | refl => exact fun S => ⟨tn, ∅, Relation.ReflTransGen.refl, Ext.refl tn, by simp⟩
  | @tail tnb tnc hdec hstep ih =>
      intro S
      obtain ⟨t, m, hm, htT, htα, u, huwf, hiso, hdisj, rfl⟩ := hstep
      obtain ⟨tngb, K, hdecg, hext, hKS⟩ := ih (S ∪ u.T)
      have hwfb : tnb.WF := HTN.DecomposesTo.wf hdec hwf
      have hwfgb : tngb.WF := HTN.DecomposesTo.wf hdecg hwf
      obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset ((tngb.T ∪ u.T) ∪ S)
      have hk1 : k ∉ tngb.T := fun h => hk (by simp [h])
      have hk2 : k ∉ u.T := fun h => hk (by simp [h])
      have hk3 : k ∉ S := fun h => hk (by simp [h])
      have hKu : ∀ z ∈ K, z ∉ u.T := fun z hz hzu => hKS z hz (by simp [hzu])
      refine ⟨decomposeWith tngb t (addTask u k (gact m)), insert k K, ?_, ?_, ?_⟩
      · refine hdecg.tail ⟨t, guardMethod gid gact m, hmeth m hm, hext.mem_of_mem htT, ?_,
          addTask u k (gact m), addTask_wf huwf k _,
          addTask_iso hiso huwf (hwfm m hm) hk2 (hfresh m hm), ?_, rfl⟩
        · rw [hext.lab t htT, htα]
          rfl
        · refine Finset.disjoint_left.2 ?_
          intro z hz hzu
          rcases Finset.mem_insert.1 hzu with rfl | hzu'
          · exact hk1 hz
          · rcases (hext.memT z).1 hz with h | h
            · exact (Finset.disjoint_left.1 hdisj) h hzu'
            · exact hKu z h hzu'
      · refine hext.decompose hwfb hwfgb htT hdisj ?_ rfl hk2 (hChk m hm) hKu
        refine Finset.disjoint_left.2 ?_
        intro z hz hzu
        rcases Finset.mem_insert.1 hzu with rfl | hzu'
        · exact hk1 hz
        · rcases (hext.memT z).1 hz with h | h
          · exact (Finset.disjoint_left.1 hdisj) h hzu'
          · exact hKu z h hzu'
      · intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hzK
        · exact hk3
        · exact fun hzS => hKS z hzK (by simp [hzS])

/-- **A guarded method's inserted copy splits into the copy of the original body and its guard
task.** -/
theorem exists_split_of_iso {u : TaskNetwork I A C} {m : Method I A C}
    {gid : Method I A C → I} {gact : Method I A C → A}
    (hiso : u.Iso (guardMethod gid gact m).subtasks) (huwf : u.WF) (hwfm : m.subtasks.WF)
    (hfresh : gid m ∉ m.subtasks.T) :
    ∃ (k : I) (v : TaskNetwork I A C), k ∈ u.T ∧ k ∉ v.T ∧ u = addTask v k (gact m) ∧
      v.WF ∧ v.Iso m.subtasks := by
  classical
  obtain ⟨σ, hbij, hord, hα⟩ := hiso
  -- the guard task of the inserted copy
  have hgid : gid m ∈ ((guardMethod gid gact m).subtasks.T : Set I) := by
    simp [guardMethod, addTask_T, Finset.coe_insert]
  obtain ⟨k, hk, hkσ⟩ := hbij.surjOn hgid
  have hkT : k ∈ u.T := by simpa using hk
  -- the tasks other than the guard task map into the body
  have hne : ∀ x ∈ u.T, x ≠ k → σ x ≠ gid m := by
    intro x hx hxk hcon
    exact hxk (hbij.injOn (by simpa using hx) hk (by rw [hcon, hkσ]))
  have hmaps : ∀ x ∈ u.T, x ≠ k → σ x ∈ m.subtasks.T := by
    intro x hx hxk
    have := hbij.mapsTo (by simpa using hx : x ∈ (u.T : Set I))
    simp only [guardMethod_subtasks, addTask_T, Finset.coe_insert, Set.mem_insert_iff] at this
    rcases this with h | h
    · exact absurd h (hne x hx hxk)
    · simpa using h
  -- the guard task is unordered
  have hkord : ∀ x, ¬ u.ord k x ∧ ¬ u.ord x k := by
    intro x
    constructor
    · intro hcon
      have hxT : x ∈ u.T := huwf.mem_right hcon
      have := (hord k hkT x hxT).1 hcon
      simp only [guardMethod_subtasks, addTask_ord] at this
      rw [hkσ] at this
      exact hfresh (hwfm.mem_left this)
    · intro hcon
      have hxT : x ∈ u.T := huwf.mem_left hcon
      have := (hord x hxT k hkT).1 hcon
      simp only [guardMethod_subtasks, addTask_ord] at this
      rw [hkσ] at this
      exact hfresh (hwfm.mem_right this)
  refine ⟨k, ⟨u.T.erase k, u.ord, u.α⟩, hkT, by simp, ?_, ?_, ?_⟩
  · -- the inserted copy is the body with the guard task added
    have hαk : u.α k = Sum.inl (gact m) := by
      rw [hα k hkT, hkσ]
      simp [guardMethod, addTask_α_self]
    refine TaskNetwork.ext' ?_ rfl ?_
    · simp [addTask_T, Finset.insert_erase hkT]
    · show u.α = Function.update u.α k (Sum.inl (gact m))
      rw [← hαk, Function.update_eq_self]
  · -- well-formedness
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      refine Finset.mem_erase.2 ⟨?_, huwf.mem_left hab⟩
      rintro rfl
      exact (hkord b).1 hab
    · intro a b hab
      refine Finset.mem_erase.2 ⟨?_, huwf.mem_right hab⟩
      rintro rfl
      exact (hkord a).2 hab
    · exact huwf.irrefl
    · exact huwf.trans
  · -- the body is a copy of the method's body
    refine ⟨σ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro x hx
      simp only [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff] at hx
      exact hmaps x (by simpa using hx.1) hx.2
    · intro x hx y hy hxy
      simp only [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff] at hx hy
      exact hbij.injOn hx.1 hy.1 hxy
    · intro w hw
      have hw' : w ∈ ((guardMethod gid gact m).subtasks.T : Set I) := by
        simp only [guardMethod_subtasks, addTask_T, Finset.coe_insert, Set.mem_insert_iff]
        exact Or.inr hw
      obtain ⟨x, hx, hxw⟩ := hbij.surjOn hw'
      have hxk : x ≠ k := by
        rintro rfl
        rw [hkσ] at hxw
        exact hfresh (by simpa [hxw] using hw)
      refine ⟨x, ?_, hxw⟩
      simp only [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff]
      exact ⟨hx, hxk⟩
    · intro x hx y hy
      have hxT : x ∈ u.T := (Finset.mem_erase.1 hx).2
      have hyT : y ∈ u.T := (Finset.mem_erase.1 hy).2
      have := hord x hxT y hyT
      simpa [guardMethod] using this
    · intro x hx
      have hxT : x ∈ u.T := (Finset.mem_erase.1 hx).2
      have hxk : x ≠ k := (Finset.mem_erase.1 hx).1
      have hsx : σ x ≠ gid m := hne x hxT hxk
      have := hα x hxT
      simpa [guardMethod, addTask_α_of_ne _ _ hsx] using this

/-- **Every derivation of the guarded domain projects to one of the original domain.** -/
theorem exists_proj_of_decomposesTo {M Mg : Set (Method I A C)}
    {gid : Method I A C → I} {gact : Method I A C → A}
    (hmeth' : ∀ mg ∈ Mg, ∃ m ∈ M, mg = guardMethod gid gact m)
    (hwfm : ∀ m ∈ M, m.subtasks.WF) (hfresh : ∀ m ∈ M, gid m ∉ m.subtasks.T)
    (hChk : ∀ m ∈ M, Chk (gact m))
    {tn tng tngf : TaskNetwork I A C} {K : Finset I}
    (hwf : tn.WF) (hwfg : tng.WF) (hext : Ext Chk tn tng K)
    (hdec : DecomposesTo Mg tng tngf) :
    ∃ (tnf : TaskNetwork I A C) (K' : Finset I),
      DecomposesTo M tn tnf ∧ Ext Chk tnf tngf K' := by
  classical
  induction hdec with
  | refl => exact ⟨tn, K, Relation.ReflTransGen.refl, hext⟩
  | @tail tngb tngc hdec hstep ih =>
      obtain ⟨tnb, K', hdecb, hextb⟩ := ih
      obtain ⟨t, mg, hmg, htT, htα, ug, hugwf, hisog, hdisjg, rfl⟩ := hstep
      obtain ⟨m, hm, rfl⟩ := hmeth' mg hmg
      have hwfb : tnb.WF := HTN.DecomposesTo.wf hdecb hwf
      have hwfgb : tngb.WF := HTN.DecomposesTo.wf hdec hwfg
      obtain ⟨k, u, hkug, hku, hug, huwf, hiso⟩ :=
        exists_split_of_iso hisog hugwf (hwfm m hm) (hfresh m hm)
      have htb : t ∈ tnb.T := hextb.mem_of_isAbstract htT (by simpa using htα)
      have htαb : tnb.α t = Sum.inr m.abstractTask := by
        rw [← hextb.lab t htb]
        simpa using htα
      have hsub : ∀ z ∈ u.T, z ∈ ug.T := by
        intro z hz
        rw [hug]
        exact Finset.mem_insert.2 (Or.inr hz)
      have hdisj : Disjoint tnb.T u.T := by
        refine Finset.disjoint_left.2 ?_
        intro z hz hzu
        exact (Finset.disjoint_left.1 hdisjg) (hextb.mem_of_mem hz) (hsub z hzu)
      have hKu : ∀ z ∈ K', z ∉ u.T := by
        intro z hz hzu
        exact (Finset.disjoint_left.1 hdisjg) ((hextb.memT z).2 (Or.inr hz)) (hsub z hzu)
      refine ⟨decomposeWith tnb t u, insert k K', ?_, ?_⟩
      · exact hdecb.tail ⟨t, m, hm, htb, htαb, u, huwf, hiso, hdisj, rfl⟩
      · exact hextb.decompose hwfb hwfgb htb hdisj hdisjg hug hku (hChk m hm) hKu

end GuardTask

end HTN
