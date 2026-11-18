import HtnComplexity.Space.ThrSem
/-!
# The steps of the thread system on the canonical network

For each step of the thread system (`HTN.Space.Thr.TStep`) this file computes what happens to
the canonical network `HTN.Space.Thr.toTN`:

* executing a primitive task is **progression** of its canonical identifier
  (`HTN.Space.Thr.toTN_exec`, `HTN.Space.Thr.toTN_execP`);
* starting a body is **decomposition** of the single task of the thread with the canonical copy
  `HTN.Space.Thr.copy` of the body (`HTN.Space.Thr.toTN_expand`), a copy isomorphic to the body
  (`HTN.Space.Thr.copy_iso`);
* closing a body changes the network only up to isomorphism (`HTN.Space.Thr.toTN_close_none`,
  `HTN.Space.Thr.close_iso_some`).

All statements are up to isomorphism (`HTN.Space.Thr.iso_of_same` and friends), which is all the
simulation of `HtnComplexity/Space/ThrSim.lean` needs.
-/

namespace HTN

namespace Space

namespace Thr

open Syn

variable {P : Par}

@[simp] theorem th_tid (th : ℕ → TSt) (j y : ℕ) : th (tid j y).unpair.1 = th j := by
  rw [unpair_tid]

theorem thLabel_run_congr (d : DomDesc) (lab : ℕ → ℕ ⊕ ℕ) (μ : ℕ) (D D' : Finset ℕ) (j y : ℕ) :
    thLabel d lab (.run μ D) j y = thLabel d lab (.run μ D') j y := by
  cases y <;> rfl

/-! ### Execution -/

/-- **Executing a primitive subtask of a running body is progression.** -/
theorem toTN_exec {th : ℕ → TSt} {j μ x : ℕ} {D : Finset ℕ} (hs : th j = .run μ D) :
    (toTN P (Function.update th j (.run μ (insert x D)))).Iso
      ((toTN P th).progress (tid j (x + 1))) := by
  have hT : tasks P (Function.update th j (.run μ (insert x D))) =
      (tasks P th).erase (tid j (x + 1)) := by
    ext a
    rw [tasks_update, Finset.mem_erase]
    by_cases ha : a.unpair.1 = j
    · rw [mem_tasks]
      simp only [ha, hs, true_and, ne_eq, not_true_eq_false, false_and, or_false,
        mem_thTasks_run, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨hk, y, hy, ⟨hyx, hyD⟩, rfl⟩
        exact ⟨fun h => hyx (Nat.succ_injective (tid_inj.1 h).2), hk, y, hy, hyD, rfl⟩
      · rintro ⟨hne, hk, y, hy, hyD, rfl⟩
        exact ⟨hk, y, hy, ⟨fun h => hne (by rw [h]), hyD⟩, rfl⟩
    · constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h ha
        · refine ⟨fun h' => ha ?_, h⟩
          rw [h']; simp
      · rintro ⟨-, h⟩
        exact Or.inr ⟨ha, h⟩
  refine iso_of_same hT ?_ ?_
  · intro a ha b hb
    simp only [toTN_T] at ha hb
    have ha' := ha
    have hb' := hb
    rw [hT, Finset.mem_erase] at ha' hb'
    show (a ∈ _ ∧ b ∈ _ ∧ rel P _ a b) ↔ ((a ∈ tasks P th ∧ b ∈ tasks P th ∧ rel P th a b) ∧ a ≠ _)
    have hrel : rel P (Function.update th j (.run μ (insert x D))) a b ↔ rel P th a b := by
      refine rel_congr fun μ' => ?_
      by_cases haj : a.unpair.1 = j
      · rw [haj, Function.update_self, hs]
        simp
      · rw [Function.update_of_ne haj]
    rw [hrel]
    exact ⟨fun h => ⟨⟨ha'.2, hb'.2, h.2.2⟩, ha'.1⟩, fun h => ⟨ha, hb, h.1.2.2⟩⟩
  · intro a _
    show thLabel _ _ _ _ _ = thLabel _ _ _ _ _
    by_cases haj : a.unpair.1 = j
    · rw [haj, Function.update_self, hs]
      exact thLabel_run_congr _ _ _ _ _ _ _
    · rw [Function.update_of_ne haj]

/-- **Executing a pending primitive initial task is progression.** -/
theorem toTN_execP {th : ℕ → TSt} {j : ℕ} (hs : th j = .pend) :
    (toTN P (Function.update th j .fin)).Iso ((toTN P th).progress (tid j 0)) := by
  have hT : tasks P (Function.update th j .fin) = (tasks P th).erase (tid j 0) := by
    ext a
    rw [tasks_update, Finset.mem_erase]
    by_cases ha : a.unpair.1 = j
    · rw [mem_tasks]
      simp only [ha, hs, thTasks, Finset.notMem_empty, and_false, ne_eq, not_true_eq_false,
        false_and, or_false, Finset.mem_singleton, false_iff, not_and, true_and]
      intro h _ h'
      exact h h'
    · constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h ha
        · refine ⟨fun h' => ha ?_, h⟩
          rw [h']; simp
      · rintro ⟨-, h⟩
        exact Or.inr ⟨ha, h⟩
  refine iso_of_same hT ?_ ?_
  · intro a ha b hb
    simp only [toTN_T] at ha hb
    have ha' := ha
    have hb' := hb
    rw [hT, Finset.mem_erase] at ha' hb'
    have haj : a.unpair.1 ≠ j := by
      intro h
      have := (tasks_update.1 ha)
      rcases this with ⟨-, -, h'⟩ | ⟨h', -⟩
      · simp [thTasks] at h'
      · exact h' h
    show (a ∈ _ ∧ b ∈ _ ∧ rel P _ a b) ↔ ((a ∈ tasks P th ∧ b ∈ tasks P th ∧ rel P th a b) ∧ a ≠ _)
    rw [rel_update_of_ne haj]
    exact ⟨fun h => ⟨⟨ha'.2, hb'.2, h.2.2⟩, ha'.1⟩, fun h => ⟨ha, hb, h.1.2.2⟩⟩
  · intro a ha
    simp only [toTN_T] at ha
    have haj : a.unpair.1 ≠ j := by
      intro h
      rcases tasks_update.1 ha with ⟨-, -, h'⟩ | ⟨h', -⟩
      · simp [thTasks] at h'
      · exact h' h
    exact label_update_of_ne haj

/-! ### The canonical copy of a body -/

variable (P) in
/-- **The canonical copy** of the body of the method number `μ`, inserted into the thread
`j`. -/
def copy (j μ : ℕ) : TaskNetwork ℕ ℕ ℕ where
  T := thTasks P.d (.run μ ∅) j
  ord a b := a ∈ thTasks P.d (.run μ ∅) j ∧ b ∈ thTasks P.d (.run μ ∅) j ∧
    (body P.d μ).ordOf (a.unpair.2 - 1) (b.unpair.2 - 1)
  α a := (body P.d μ).label (a.unpair.2 - 1)

theorem mem_copy {j μ a : ℕ} :
    a ∈ (copy P j μ).T ↔ ∃ x ∈ (body P.d μ).ids, a = tid j (x + 1) := by
  show a ∈ thTasks P.d (.run μ ∅) j ↔ _
  rw [mem_thTasks_run]
  simp

theorem copy_wf (j μ : ℕ) : (copy P j μ).WF where
  mem_left h := h.1
  mem_right h := h.2.1
  irrefl a h := (body P.d μ).toTaskNetwork_wf.irrefl _ h.2.2
  trans hab hbc := ⟨hab.1, hbc.2.1, (body P.d μ).toTaskNetwork_wf.trans hab.2.2 hbc.2.2⟩

/-- **The canonical copy is a copy.** -/
theorem copy_iso (j μ : ℕ) : (copy P j μ).Iso (body P.d μ).toTaskNetwork := by
  refine ⟨fun a => a.unpair.2 - 1, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := mem_copy.1 ha
    simpa using hx
  · intro a ha b hb h
    obtain ⟨x, hx, rfl⟩ := mem_copy.1 ha
    obtain ⟨y, hy, rfl⟩ := mem_copy.1 hb
    simp at h
    rw [h]
  · intro x hx
    refine ⟨tid j (x + 1), mem_copy.2 ⟨x, by simpa using hx, rfl⟩, by simp⟩
  · intro a ha b hb
    show (a ∈ _ ∧ b ∈ _ ∧ _) ↔ (body P.d μ).ordOf _ _
    exact ⟨fun h => h.2.2, fun h => ⟨ha, hb, h⟩⟩
  · intro a _
    rfl

/-! ### Starting a body -/

theorem mem_tasks_thread {th : ℕ → TSt} {j a : ℕ} (ha : a ∈ tasks P th) (haj : a.unpair.1 = j) :
    a ∈ thTasks P.d (th j) j := by
  have := (mem_tasks.1 ha).2
  rwa [haj] at this

/-- **Starting a body is decomposition** of the single task of the thread by the canonical copy
of the body. -/
theorem toTN_expand {th : ℕ → TSt} {j μ : ℕ} (hj : j < P.k)
    (hth : th j = .pend ∨ ∃ c, th j = .cur c) (hpre : ∀ i < P.k, P.O i j → Idle P th i) :
    (toTN P (Function.update th j (.run μ ∅))).Iso
      (decomposeWith (toTN P th) (tid j 0) (copy P j μ)) := by
  have hTj : thTasks P.d (th j) j = {tid j 0} := by
    rcases hth with h | ⟨c, h⟩ <;> rw [h] <;> rfl
  have hnr : ∀ μ' D, th j ≠ .run μ' D := by
    rcases hth with h | ⟨c, h⟩ <;> intro μ' D <;> rw [h] <;> simp
  have hTa : ∀ a ∈ tasks P th, a.unpair.1 = j → a = tid j 0 := by
    intro a ha haj
    have := mem_tasks_thread ha haj
    rw [hTj] at this
    simpa using this
  have hcopy1 : ∀ a ∈ (copy P j μ).T, a.unpair.1 = j := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := mem_copy.1 ha
    simp
  have hcopyT : ∀ a ∈ (copy P j μ).T, a ∉ tasks P th := by
    intro a ha hT
    obtain ⟨x, -, rfl⟩ := mem_copy.1 ha
    have := hTa _ hT (by simp)
    simp [tid_inj] at this
  have hT : tasks P (Function.update th j (.run μ ∅)) =
      (decomposeWith (toTN P th) (tid j 0) (copy P j μ)).T := by
    ext a
    rw [tasks_update, mem_decomposeWith_T]
    simp only [toTN_T]
    by_cases haj : a.unpair.1 = j
    · subst haj
      simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
      constructor
      · rintro ⟨-, h⟩
        exact Or.inr h
      · rintro (⟨h1, h2⟩ | h)
        · exact absurd (hTa a h1 rfl) h2
        · exact ⟨hj, h⟩
    · constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h haj
        · refine Or.inl ⟨h, fun h' => haj ?_⟩
          rw [h']; simp
      · rintro (⟨h, -⟩ | h)
        · exact Or.inr ⟨haj, h⟩
        · exact absurd (hcopy1 a h) haj
  refine iso_of_same hT ?_ ?_
  · intro a ha b hb
    simp only [toTN_T] at ha hb
    have hdec : ∀ z, z ∈ tasks P (Function.update th j (.run μ ∅)) →
        (z.unpair.1 = j ∧ z ∈ (copy P j μ).T) ∨ (z.unpair.1 ≠ j ∧ z ∈ tasks P th) := by
      intro z hz
      rcases tasks_update.1 hz with ⟨h1, -, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    have ht : tid j 0 ∈ tasks P th := mem_tasks_of hj (by rw [hTj]; simp)
    show (a ∈ _ ∧ b ∈ _ ∧ rel P _ a b) ↔ (decomposeWith (toTN P th) (tid j 0) (copy P j μ)).ord a b
    rw [decomposeWith_ord_iff]
    simp only [toTN_ord]
    have hidle : ∀ i, i ∈ tasks P th → ¬ P.O i.unpair.1 j := by
      intro i hiT hO
      have := hpre _ (mem_tasks.1 hiT).1 hO
      have hmem := (mem_tasks.1 hiT).2
      unfold Idle at this
      rw [this] at hmem
      simp at hmem
    rcases hdec a ha with ⟨haj, hac⟩ | ⟨haj, haT⟩ <;> rcases hdec b hb with ⟨hbj, hbc⟩ | ⟨hbj, hbT⟩
    · -- both in the copy
      constructor
      · rintro ⟨-, -, hr⟩
        rcases hr with ⟨-, μ', D, hs, -, -, hord⟩ | ⟨hne, -⟩
        · rw [haj, Function.update_self] at hs
          cases hs
          exact Or.inl ⟨hac, hbc, hord⟩
        · exact absurd (haj.trans hbj.symm) hne
      · rintro (hc | ⟨⟨haT', -, -⟩, -⟩ | ⟨⟨-, hbT', -⟩, -⟩ | ⟨⟨haT', -, -⟩, -⟩)
        · refine ⟨ha, hb, Or.inl ⟨haj.trans hbj.symm, μ, ∅, by rw [haj, Function.update_self],
            ?_, ?_, hc.2.2⟩⟩
          · obtain ⟨x, -, rfl⟩ := mem_copy.1 hac; simp
          · obtain ⟨x, -, rfl⟩ := mem_copy.1 hbc; simp
        · exact absurd haT' (hcopyT a hac)
        · exact absurd hbT' (hcopyT b hbc)
        · exact absurd haT' (hcopyT a hac)
    · -- `a` in the copy, `b` old
      constructor
      · rintro ⟨-, -, hr⟩
        rcases hr with ⟨h, -⟩ | ⟨-, hO⟩
        · exact absurd (haj ▸ h).symm hbj
        · refine Or.inr (Or.inr (Or.inl ⟨⟨ht, hbT, Or.inr ⟨?_, ?_⟩⟩, hac⟩))
          · simpa using fun h => hbj h.symm
          · simpa [haj] using hO
      · rintro (hc | ⟨⟨haT', -, -⟩, -⟩ | ⟨⟨-, -, hr⟩, -⟩ | ⟨⟨haT', -, -⟩, -⟩)
        · exact absurd (hcopy1 b hc.2.1) hbj
        · exact absurd haT' (hcopyT a hac)
        · rcases hr with ⟨h, -⟩ | ⟨-, hO⟩
          · simp only [unpair_tid] at h
            exact absurd h.symm hbj
          · refine ⟨ha, hb, Or.inr ⟨by rw [haj]; exact fun h => hbj h.symm, ?_⟩⟩
            rw [haj]
            simpa using hO
        · exact absurd haT' (hcopyT a hac)
    · -- `a` old, `b` in the copy
      constructor
      · rintro ⟨-, -, hr⟩
        rcases hr with ⟨h, -⟩ | ⟨-, hO⟩
        · exact absurd (h.trans hbj) haj
        · rw [hbj] at hO
          exact absurd hO (hidle a haT)
      · rintro (hc | ⟨⟨-, -, hr⟩, -⟩ | ⟨⟨-, hbT', -⟩, -⟩ | ⟨⟨-, hbT', -⟩, -⟩)
        · exact absurd (hcopy1 a hc.1) haj
        · rcases hr with ⟨h, -⟩ | ⟨-, hO⟩
          · simp only [unpair_tid] at h
            exact absurd h haj
          · simp only [unpair_tid] at hO
            exact absurd hO (hidle a haT)
        · exact absurd hbT' (hcopyT b hbc)
        · exact absurd hbT' (hcopyT b hbc)
    · -- both old
      have hat : a ≠ tid j 0 := fun h => haj (by rw [h]; simp)
      have hbt : b ≠ tid j 0 := fun h => hbj (by rw [h]; simp)
      constructor
      · rintro ⟨-, -, hr⟩
        exact Or.inr (Or.inr (Or.inr ⟨⟨haT, hbT, (rel_update_of_ne haj).1 hr⟩, hat, hbt⟩))
      · rintro (hc | ⟨-, hbc'⟩ | ⟨-, hac'⟩ | ⟨⟨-, -, hr⟩, -, -⟩)
        · exact absurd (hcopy1 a hc.1) haj
        · exact absurd (hcopy1 b hbc') hbj
        · exact absurd (hcopy1 a hac') haj
        · exact ⟨ha, hb, (rel_update_of_ne haj).2 hr⟩
  · intro a ha
    simp only [toTN_T] at ha
    rw [decomposeWith_α]
    rcases tasks_update.1 ha with ⟨haj, -, hac⟩ | ⟨haj, -⟩
    · have hac' : a ∈ (copy P j μ).T := hac
      rw [if_pos hac']
      obtain ⟨x, -, rfl⟩ := mem_copy.1 hac'
      rw [toTN_α, th_tid (Function.update th j _), Function.update_self]
      simp [copy, thLabel]
    · have hac : a ∉ (copy P j μ).T := fun h => haj (hcopy1 a h)
      rw [if_neg hac]
      exact label_update_of_ne haj

/-! ### Closing a body -/

/-- Closing a body without compound subtask does not change the network. -/
theorem toTN_close_none {th : ℕ → TSt} {j μ : ℕ} {D : Finset ℕ} (hs : th j = .run μ D)
    (hall : ∀ x ∈ (body P.d μ).ids, x ∈ D) :
    (toTN P (Function.update th j .fin)).Iso (toTN P th) := by
  have hT : tasks P (Function.update th j .fin) = tasks P th := by
    ext a
    rw [tasks_update, mem_tasks]
    by_cases ha : a.unpair.1 = j
    · subst ha
      rw [hs]
      simp only [thTasks, Finset.notMem_empty, and_false, true_and, ne_eq, not_true_eq_false,
        false_and, or_false, false_iff, not_and]
      intro _ h
      obtain ⟨x, hx, -⟩ := Finset.mem_image.1 h
      rw [Finset.mem_sdiff, List.mem_toFinset] at hx
      exact hx.2 (hall x hx.1)
    · simp [ha]
  refine iso_of_same hT ?_ ?_
  · intro a ha b hb
    simp only [toTN_T] at ha
    have haj : a.unpair.1 ≠ j := by
      intro h
      rcases tasks_update.1 ha with ⟨-, -, h'⟩ | ⟨h', -⟩
      · simp [thTasks] at h'
      · exact h' h
    show (a ∈ _ ∧ b ∈ _ ∧ rel P _ a b) ↔ (a ∈ _ ∧ b ∈ _ ∧ rel P th a b)
    rw [rel_update_of_ne haj, hT]
  · intro a ha
    simp only [toTN_T] at ha
    have haj : a.unpair.1 ≠ j := by
      intro h
      rcases tasks_update.1 ha with ⟨-, -, h'⟩ | ⟨h', -⟩
      · simp [thTasks] at h'
      · exact h' h
    exact label_update_of_ne haj

/-- The renaming used when a body with compound subtask `z` is closed: the single task of the
closed thread is the compound subtask. -/
def closeMap (j z : ℕ) (a : ℕ) : ℕ := if a = tid j 0 then tid j (z + 1) else a

@[simp] theorem closeMap_self (j z : ℕ) : closeMap j z (tid j 0) = tid j (z + 1) := by
  simp [closeMap]

/-- **Closing a body with compound subtask `z` changes the network only up to the renaming
`closeMap`.** -/
theorem close_iso_some {th : ℕ → TSt} {j μ z c : ℕ} {D : Finset ℕ} (hj : j < P.k)
    (hs : th j = .run μ D) (hz : z ∈ (body P.d μ).ids) (hzD : z ∉ D)
    (hall : ∀ x ∈ (body P.d μ).ids, x ≠ z → x ∈ D) (hl : (body P.d μ).label z = Sum.inr c) :
    Set.BijOn (closeMap j z) ((toTN P (Function.update th j (.cur c))).T : Set ℕ)
        ((toTN P th).T : Set ℕ) ∧
      (∀ a ∈ (toTN P (Function.update th j (.cur c))).T,
        ∀ b ∈ (toTN P (Function.update th j (.cur c))).T,
        ((toTN P (Function.update th j (.cur c))).ord a b ↔
          (toTN P th).ord (closeMap j z a) (closeMap j z b))) ∧
      (∀ a ∈ (toTN P (Function.update th j (.cur c))).T,
        (toTN P (Function.update th j (.cur c))).α a = (toTN P th).α (closeMap j z a)) := by
  -- the tasks of the thread `j` before and after
  have hold : ∀ a ∈ tasks P th, a.unpair.1 = j → a = tid j (z + 1) := by
    intro a ha haj
    have := mem_tasks_thread ha haj
    rw [hs] at this
    obtain ⟨x, hx, hxD, rfl⟩ := mem_thTasks_run.1 this
    by_cases hxz : x = z
    · rw [hxz]
    · exact absurd (hall x hx hxz) hxD
  have hzT : tid j (z + 1) ∈ tasks P th :=
    mem_tasks_of hj (by rw [hs]; exact mem_thTasks_run.2 ⟨z, hz, hzD, rfl⟩)
  have hnew : ∀ a ∈ tasks P (Function.update th j (.cur c)),
      (a = tid j 0) ∨ (a.unpair.1 ≠ j ∧ a ∈ tasks P th) := by
    intro a ha
    rcases tasks_update.1 ha with ⟨-, -, h⟩ | h
    · left; simpa [thTasks] using h
    · exact Or.inr h
  have ht0 : tid j 0 ∈ tasks P (Function.update th j (.cur c)) :=
    tasks_update.2 (Or.inl ⟨by simp, hj, by simp [thTasks]⟩)
  have hmap_ne : ∀ a, a.unpair.1 ≠ j → closeMap j z a = a := by
    intro a ha
    unfold closeMap
    rw [if_neg]
    rintro rfl
    simp at ha
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    rcases hnew a ha with rfl | ⟨haj, haT⟩
    · simpa using hzT
    · rw [hmap_ne a haj]; exact haT
  · intro a ha b hb h
    rcases hnew a ha with rfl | ⟨haj, haT⟩ <;> rcases hnew b hb with rfl | ⟨hbj, hbT⟩
    · rfl
    · rw [closeMap_self, hmap_ne b hbj] at h
      exact absurd (by rw [← h]; simp) hbj
    · rw [closeMap_self, hmap_ne a haj] at h
      exact absurd (by rw [h]; simp) haj
    · rwa [hmap_ne a haj, hmap_ne b hbj] at h
  · intro b hb
    by_cases hbj : b.unpair.1 = j
    · exact ⟨tid j 0, ht0, by rw [closeMap_self, hold b hb hbj]⟩
    · exact ⟨b, tasks_update.2 (Or.inr ⟨hbj, hb⟩), hmap_ne b hbj⟩
  · intro a ha b hb
    simp only [toTN_T] at ha hb
    have hmemA : closeMap j z a ∈ tasks P th := by
      rcases hnew a ha with rfl | ⟨haj, haT⟩
      · simpa using hzT
      · rw [hmap_ne a haj]; exact haT
    have hmemB : closeMap j z b ∈ tasks P th := by
      rcases hnew b hb with rfl | ⟨hbj, hbT⟩
      · simpa using hzT
      · rw [hmap_ne b hbj]; exact hbT
    suffices key : rel P (Function.update th j (.cur c)) a b ↔
        rel P th (closeMap j z a) (closeMap j z b) from
      ⟨fun h => ⟨hmemA, hmemB, key.1 h.2.2⟩, fun h => ⟨ha, hb, key.2 h.2.2⟩⟩
    rcases hnew a ha with rfl | ⟨haj, haT⟩ <;> rcases hnew b hb with rfl | ⟨hbj, hbT⟩
    · rw [closeMap_self]
      unfold rel
      rw [th_tid (Function.update th j _), Function.update_self]
      constructor
      · rintro (⟨-, μ', D', h, -⟩ | ⟨hne, -⟩)
        · simp at h
        · exact absurd rfl hne
      · rintro (⟨-, μ', D', -, -, -, hord⟩ | ⟨hne, -⟩)
        · exact absurd hord ((body P.d μ').toTaskNetwork_wf.irrefl _)
        · exact absurd rfl hne
    · rw [closeMap_self, hmap_ne b hbj]
      unfold rel
      simp only [unpair_tid]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h.symm hbj
        · exact Or.inr ⟨fun h' => hbj h'.symm, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h.symm hbj
        · exact Or.inr ⟨fun h' => hbj h'.symm, h⟩
    · rw [closeMap_self, hmap_ne a haj]
      unfold rel
      simp only [unpair_tid]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h haj
        · exact Or.inr ⟨haj, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h haj
        · exact Or.inr ⟨haj, h⟩
    · rw [hmap_ne a haj, hmap_ne b hbj, rel_update_of_ne haj]
  · intro a ha
    simp only [toTN_T] at ha
    rcases hnew a ha with rfl | ⟨haj, -⟩
    · rw [closeMap_self, toTN_α, toTN_α, th_tid (Function.update th j _), th_tid th,
        Function.update_self, hs]
      simp [thLabel, hl]
    · rw [hmap_ne a haj]
      exact label_update_of_ne haj

/-! ### Unconstrained tasks -/

/-- The single task of a pending or current thread whose predecessors are idle is
unconstrained. -/
theorem unc_single {th : ℕ → TSt} {j : ℕ} (hj : j < P.k)
    (hth : th j = .pend ∨ ∃ c, th j = .cur c) (hpre : ∀ i < P.k, P.O i j → Idle P th i) :
    (toTN P th).Unconstrained (tid j 0) := by
  refine ⟨mem_tasks_of hj (by rcases hth with h | ⟨c, h⟩ <;> rw [h] <;> simp [thTasks]), ?_⟩
  intro b hb hord
  rcases hord.2.2 with ⟨h, μ, D, hs, -, h0, -⟩ | ⟨hne, hO⟩
  · simp at h0
  · simp only [unpair_tid] at hO hne
    have := hpre _ (mem_tasks.1 hb).1 hO
    have hmem := (mem_tasks.1 hb).2
    unfold Idle at this
    rw [this] at hmem
    simp at hmem

/-- A primitive subtask of a running body whose predecessors in the body have been executed,
in a thread whose predecessors are idle, is unconstrained. -/
theorem unc_exec {th : ℕ → TSt} {j μ x : ℕ} {D : Finset ℕ} (hj : j < P.k)
    (hs : th j = .run μ D) (hx : x ∈ (body P.d μ).ids) (hxD : x ∉ D)
    (hbody : ∀ y, (body P.d μ).ordOf y x → y ∈ D) (hpre : ∀ i < P.k, P.O i j → Idle P th i) :
    (toTN P th).Unconstrained (tid j (x + 1)) := by
  refine ⟨mem_tasks_of hj (by rw [hs]; exact mem_thTasks_run.2 ⟨x, hx, hxD, rfl⟩), ?_⟩
  intro b hb hord
  rcases hord.2.2 with ⟨h, μ', D', hs', hb0, -, hordb⟩ | ⟨hne, hO⟩
  · simp only [unpair_tid] at h hordb
    rw [h, hs] at hs'
    cases hs'
    simp only [unpair_tid, add_tsub_cancel_right] at hordb
    have hbT := mem_tasks_thread hb h
    rw [hs] at hbT
    obtain ⟨y, -, hyD, rfl⟩ := mem_thTasks_run.1 hbT
    simp only [unpair_tid, add_tsub_cancel_right] at hordb
    exact hyD (hbody y hordb)
  · simp only [unpair_tid] at hO hne
    have := hpre _ (mem_tasks.1 hb).1 hO
    have hmem := (mem_tasks.1 hb).2
    unfold Idle at this
    rw [this] at hmem
    simp at hmem

end Thr

end Space

end HTN
