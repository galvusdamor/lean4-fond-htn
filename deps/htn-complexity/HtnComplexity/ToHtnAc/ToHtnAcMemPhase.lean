import HtnComplexity.ToHtnAc.ToHtnAcSim
/-!
# The two phases of a memory cell

In the compilation of totally ordered HTN problems into acyclic ones
(`HtnComplexity/ToHtnAc/ToHtnAc.lean`) a memory cell is the compound task `MEM`.  Its refinements
are described by `HTN.ToAc.yieldSeq_MEM_iff` and their effect, *when executed in one go*, by
`HTN.ToAc.yieldSeq_MEM_spec`.  In a plan of the compiled problem a memory cell is **not**
executed in one go: it is executed in two phases, separated by an arbitrarily long stretch of
other actions.

* the **write phase** `accept_W … done_W` runs inside the `WRITE` handshake of the proof step
  that produces the triple.  It *reads* the first and the third state copy and the stored task
  name, and changes no state copy at all;
* the **read phase** `accept_R … done_R` runs inside the `READ` handshake of a later proof step.
  It *writes* the triple the cell read during its write phase into the fourth and fifth copy and
  restores the task name.

The triple is therefore not stored in the state — it is stored in the *hierarchy*, in the
recursion of `STATE_n^1` and `STATE_n^3`: those tasks test one fact on the way down (before
`done_W`) and write it on the way up (after `accept_R`).  This file makes that precise.

## Contents

* `HTN.ToAc.testsOf`, `HTN.ToAc.writesOf` — the descending sequence of tests and the ascending
  sequence of writes belonging to a source state, and their semantics
  (`transitionSeq_testsOf`, `seqApplicable_testsOf_iff`, `representsOn_writesOf`, …);
* `HTN.ToAc.memWrite`, `HTN.ToAc.memRead` — the two phases;
* `HTN.ToAc.yieldSeq_MEM_phases` — **every refinement of `MEM` is `memWrite S S' t ++
  memRead S S' t`** for a unique triple `(S, S', t)`, and `HTN.ToAc.yieldSeq_MEM_memPhases` —
  conversely, every triple gives a refinement of `MEM`;
* `HTN.ToAc.seqApplicable_memWrite_iff`, `HTN.ToAc.transitionSeq_memWrite` — the write phase is
  executable exactly when the cell's `key₁^W` is up, the first copy represents `S`, the third
  represents `S'` and the stored task name is `t`; it only lowers `key₁^W` and raises `key₂^W`;
* `HTN.ToAc.seqApplicable_memRead`, `HTN.ToAc.memRead_spec` — the read phase is executable
  exactly when `key₁^R` is up, and it installs `S` in the fourth copy, `S'` in the fifth copy and
  `t` as the stored task name.

Together these are the "memory cell = latch" statement that the global simulation argument of
the compilation needs in both directions.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

/-! ### Tests and writes belonging to a state -/

open Classical in
/-- The test that the fact `v` has, in the `i`-th copy, the truth value it has in `S`. -/
noncomputable def testAct (i : Fin 5) (S : Set F) (v : F) : AcAct F A C :=
  if v ∈ S then AcAct.prePV v i i else AcAct.preNV v i i

open Classical in
/-- The write giving the fact `v`, in the `j`-th copy, the truth value it has in `S`. -/
noncomputable def writeAct (j : Fin 5) (S : Set F) (v : F) : AcAct F A C :=
  if v ∈ S then AcAct.setV v j else AcAct.delV v j

/-- The tests performed by `STATE_n^i` on the way down: the facts `vs` are tested in reverse
order. -/
noncomputable def testsOf (i : Fin 5) (S : Set F) (vs : List F) : List (AcAct F A C) :=
  (vs.map (testAct i S)).reverse

/-- The writes performed by `STATE_n^i` on the way up: the facts `vs` are written in order. -/
noncomputable def writesOf (j : Fin 5) (S : Set F) (vs : List F) : List (AcAct F A C) :=
  vs.map (writeAct j S)

@[simp] lemma testsOf_nil (i : Fin 5) (S : Set F) :
    testsOf (F := F) (A := A) (C := C) i S [] = [] := rfl

@[simp] lemma writesOf_nil (j : Fin 5) (S : Set F) :
    writesOf (F := F) (A := A) (C := C) j S [] = [] := rfl

lemma testsOf_append_singleton (i : Fin 5) (S : Set F) (vs : List F) (v : F) :
    testsOf (F := F) (A := A) (C := C) i S (vs ++ [v]) = testAct i S v :: testsOf i S vs := by
  simp [testsOf]

lemma writesOf_append_singleton (j : Fin 5) (S : Set F) (vs : List F) (v : F) :
    writesOf (F := F) (A := A) (C := C) j S (vs ++ [v]) =
      writesOf j S vs ++ [writeAct j S v] := by
  simp [writesOf]

/-- Two states that agree on `vs` give the same tests. -/
lemma testsOf_congr {i : Fin 5} {S S' : Set F} {vs : List F} (h : ∀ v ∈ vs, (v ∈ S ↔ v ∈ S')) :
    testsOf (F := F) (A := A) (C := C) i S vs = testsOf i S' vs := by
  classical
  simp only [testsOf]
  congr 1
  refine List.map_congr_left (fun v hv => ?_)
  simp only [testAct]
  by_cases hS : v ∈ S
  · rw [if_pos hS, if_pos ((h v hv).1 hS)]
  · rw [if_neg hS, if_neg (fun hc => hS ((h v hv).2 hc))]

/-- Two states that agree on `vs` give the same writes. -/
lemma writesOf_congr {j : Fin 5} {S S' : Set F} {vs : List F} (h : ∀ v ∈ vs, (v ∈ S ↔ v ∈ S')) :
    writesOf (F := F) (A := A) (C := C) j S vs = writesOf j S' vs := by
  classical
  simp only [writesOf]
  refine List.map_congr_left (fun v hv => ?_)
  simp only [writeAct]
  by_cases hS : v ∈ S
  · rw [if_pos hS, if_pos ((h v hv).1 hS)]
  · rw [if_neg hS, if_neg (fun hc => hS ((h v hv).2 hc))]

/-! ### The semantics of the tests -/

/-- The tests do not change the state. -/
@[simp] lemma transitionSeq_testsOf {i : Fin 5} {S : Set F} {vs : List F}
    {s : Set (AcFact F A C)} :
    (domain D vars bound).transitionSeq (testsOf i S vs) s = s := by
  classical
  induction vs using List.reverseRecOn generalizing s with
  | nil => simp
  | append_singleton vs v ih =>
      rw [testsOf_append_singleton, ActionModel.transitionSeq_cons]
      simp only [testAct]
      by_cases hv : v ∈ S
      · rw [if_pos hv, transition_prePV]; exact ih
      · rw [if_neg hv, transition_preNV]; exact ih

/-- The tests of the state `S` in copy `i` are executable exactly when the copy `i` really has
the truth values of `S`. -/
lemma seqApplicable_testsOf_iff {i : Fin 5} {S : Set F} {vs : List F}
    {s : Set (AcFact F A C)} :
    (domain D vars bound).SeqApplicable (testsOf i S vs) s ↔
      ∀ v ∈ vs, (v ∈ S → AcFact.pos v i ∈ s) ∧ (v ∉ S → AcFact.neg v i ∈ s) := by
  classical
  induction vs using List.reverseRecOn generalizing s with
  | nil => simp
  | append_singleton vs v ih =>
      rw [testsOf_append_singleton, ActionModel.seqApplicable_cons]
      simp only [testAct]
      by_cases hv : v ∈ S
      · rw [if_pos hv, transition_prePV, ih, applicable_prePV_iff]
        constructor
        · rintro ⟨⟨hp, -⟩, hrest⟩ u hu
          rcases List.mem_append.1 hu with hu | hu
          · exact hrest u hu
          · simp only [List.mem_singleton] at hu
            subst hu
            exact ⟨fun _ => hp, fun hc => absurd hv hc⟩
        · intro h
          refine ⟨⟨(h v (by simp)).1 hv, (h v (by simp)).1 hv⟩, fun u hu => h u ?_⟩
          exact List.mem_append_left _ hu
      · rw [if_neg hv, transition_preNV, ih, applicable_preNV_iff]
        constructor
        · rintro ⟨⟨hn, -⟩, hrest⟩ u hu
          rcases List.mem_append.1 hu with hu | hu
          · exact hrest u hu
          · simp only [List.mem_singleton] at hu
            subst hu
            exact ⟨fun hc => absurd hc hv, fun _ => hn⟩
        · intro h
          refine ⟨⟨(h v (by simp)).2 hv, (h v (by simp)).2 hv⟩, fun u hu => h u ?_⟩
          exact List.mem_append_left _ hu

/-! ### The semantics of the writes -/

/-- The writes are always executable. -/
lemma seqApplicable_writesOf {j : Fin 5} {S : Set F} {vs : List F}
    {s : Set (AcFact F A C)} :
    (domain D vars bound).SeqApplicable (writesOf j S vs) s := by
  classical
  induction vs generalizing s with
  | nil => simp
  | cons v vs ih =>
      simp only [writesOf, List.map_cons, ActionModel.seqApplicable_cons]
      simp only [writeAct]
      by_cases hv : v ∈ S
      · rw [if_pos hv]
        exact ⟨applicable_setV, ih⟩
      · rw [if_neg hv]
        exact ⟨applicable_delV, ih⟩

/-- The writes of copy `j` change nothing outside copy `j` of the facts they write. -/
lemma unchanged_writesOf {j : Fin 5} {S : Set F} {vs : List F} {s : Set (AcFact F A C)}
    {f : AcFact F A C} (hf : ∀ v ∈ vs, f ≠ AcFact.pos v j ∧ f ≠ AcFact.neg v j) :
    (f ∈ (domain D vars bound).transitionSeq (writesOf j S vs) s ↔ f ∈ s) := by
  classical
  induction vs generalizing s with
  | nil => simp
  | cons v vs ih =>
      have hv := hf v (by simp)
      have hrest : ∀ u ∈ vs, f ≠ AcFact.pos u j ∧ f ≠ AcFact.neg u j :=
        fun u hu => hf u (by simp [hu])
      simp only [writesOf, List.map_cons, ActionModel.transitionSeq_cons]
      rw [show (List.map (writeAct j S) vs) = writesOf j S vs from rfl, ih hrest]
      simp only [writeAct]
      by_cases hvS : v ∈ S
      · rw [if_pos hvS, mem_transition_setV]
        simp [hv.1, hv.2]
      · rw [if_neg hvS, mem_transition_delV]
        simp [hv.1, hv.2]

/-- After the writes, copy `j` represents `S` on `vs`. -/
lemma representsOn_writesOf {j : Fin 5} {S : Set F} {vs : List F} {s : Set (AcFact F A C)} :
    RepresentsOn ((domain D vars bound).transitionSeq (writesOf j S vs) s) j S vs := by
  classical
  induction vs generalizing s with
  | nil => intro v hv; simp at hv
  | cons v vs ih =>
      intro u hu
      simp only [writesOf, List.map_cons, ActionModel.transitionSeq_cons]
      rw [show (List.map (writeAct j S) vs) = writesOf j S vs from rfl]
      rcases List.mem_cons.1 hu with rfl | hu
      · by_cases huS : u ∈ S
        · by_cases hmem : u ∈ vs
          · exact ih u hmem
          · have h1 := unchanged_writesOf (D := D) (vars := vars) (bound := bound)
              (S := S) (j := j) (vs := vs)
              (s := (domain D vars bound).transition (writeAct j S u) s)
              (f := AcFact.pos u j)
              (fun w hw => ⟨by intro h; rw [AcFact.pos.injEq] at h; exact hmem (by rw [h.1]; exact hw), by simp⟩)
            have h2 := unchanged_writesOf (D := D) (vars := vars) (bound := bound)
              (S := S) (j := j) (vs := vs)
              (s := (domain D vars bound).transition (writeAct j S u) s)
              (f := AcFact.neg u j)
              (fun w hw => ⟨by simp, by intro h; rw [AcFact.neg.injEq] at h; exact hmem (by rw [h.1]; exact hw)⟩)
            rw [h1, h2]
            simp only [writeAct, if_pos huS]
            simp [huS]
        · by_cases hmem : u ∈ vs
          · exact ih u hmem
          · have h1 := unchanged_writesOf (D := D) (vars := vars) (bound := bound)
              (S := S) (j := j) (vs := vs)
              (s := (domain D vars bound).transition (writeAct j S u) s)
              (f := AcFact.pos u j)
              (fun w hw => ⟨by intro h; rw [AcFact.pos.injEq] at h; exact hmem (by rw [h.1]; exact hw), by simp⟩)
            have h2 := unchanged_writesOf (D := D) (vars := vars) (bound := bound)
              (S := S) (j := j) (vs := vs)
              (s := (domain D vars bound).transition (writeAct j S u) s)
              (f := AcFact.neg u j)
              (fun w hw => ⟨by simp, by intro h; rw [AcFact.neg.injEq] at h; exact hmem (by rw [h.1]; exact hw)⟩)
            rw [h1, h2]
            simp only [writeAct, if_neg huS]
            simp [huS]
      · exact ih u hu

/-! ### The phases of the copying tasks -/

omit D bound in
/-- In a duplicate-free list the `n`-th element does not occur among the first `n`. -/
lemma not_mem_take_of_getElem? {l : List F} (hnd : l.Nodup) {n : ℕ} {v : F}
    (hv : l[n]? = some v) : v ∉ l.take n := by
  have hn : n < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hv
    simp at hv
  have hget : l[n] = v := by
    rw [List.getElem?_eq_getElem hn] at hv
    exact Option.some.inj hv
  have hsplit : l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
  have hdrop : l.drop n = v :: l.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons hn, hget]
  rw [hsplit, hdrop] at hnd
  have hdisj := (List.nodup_append.1 hnd).2.2
  exact fun hmem => hdisj v hmem v (by simp) rfl

/-- **The two phases of `STATE_n^3`.**  Every refinement of `STATE_n^3` first tests the first
`n` facts in the third copy, then performs the synchronisation `preC t ; done_W ; accept_R ;
setC t`, and finally writes the tested values into the fifth copy. -/
theorem yieldSeq_STATE3_phases (hnd : vars.Nodup) :
    ∀ {n : ℕ}, n ≤ vars.length → ∀ {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE3 n)] as →
    ∃ (S' : Set F) (t : A ⊕ C),
      as = testsOf 2 S' (vars.take n) ++
        [AcAct.preC t, AcAct.doneA RW.write, AcAct.accept RW.read, AcAct.setC t] ++
        writesOf 4 S' (vars.take n) := by
  intro n
  induction n with
  | zero =>
      intro _ as h
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_STATE3_zero_iff] at hbs
      obtain ⟨t, rfl⟩ := hbs
      refine ⟨∅, t, ?_⟩
      simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff,
        yieldSeq_nil_iff] at hy
      obtain ⟨as₁, rfl, as₂, rfl, as₃, rfl, as₄, rfl, rfl⟩ := hy
      simp
  | succ n ih =>
      intro hn as h
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_STATE3_succ_iff] at hbs
      obtain ⟨v, hv, hbs⟩ := hbs
      have htake : vars.take (n + 1) = vars.take n ++ [v] := by
        rw [List.take_add_one, hv]; rfl
      have hvnot : v ∉ vars.take n := not_mem_take_of_getElem? hnd hv
      obtain ⟨a, b, hbs', hab⟩ :
          ∃ a b : AcAct F A C,
            bs = [Sum.inl a, Sum.inr (AcTask.STATE3 n), Sum.inl b] ∧
            ((a = AcAct.prePV v 2 2 ∧ b = AcAct.setV v 4) ∨
             (a = AcAct.preNV v 2 2 ∧ b = AcAct.delV v 4)) := by
        rcases hbs with rfl | rfl
        · exact ⟨_, _, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩⟩
      subst hbs'
      simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
      obtain ⟨as₁, rfl, hy⟩ := hy
      have hy' : (domain D vars bound).YieldSeq
          ([Sum.inr (AcTask.STATE3 n)] ++ [Sum.inl b]) as₁ := by simpa using hy
      obtain ⟨as₂, as₃, rfl, hy₂, hy₃⟩ := hy'.split
      simp only [yieldSeq_inl_cons_iff, yieldSeq_nil_iff] at hy₃
      obtain ⟨as₄, rfl, rfl⟩ := hy₃
      obtain ⟨S₀, t, hS₀⟩ := ih (by omega) hy₂
      classical
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨insert v S₀, t, ?_⟩
        have hagree : ∀ u ∈ vars.take n, (u ∈ insert v S₀ ↔ u ∈ S₀) := by
          intro u hu
          constructor
          · rintro (rfl | h)
            · exact absurd hu hvnot
            · exact h
          · exact fun h => Or.inr h
        rw [htake, testsOf_append_singleton, writesOf_append_singleton,
          testsOf_congr hagree, writesOf_congr hagree, hS₀]
        simp only [testAct, writeAct, if_pos (Set.mem_insert v S₀)]
        simp [List.append_assoc]
      · refine ⟨S₀ \ {v}, t, ?_⟩
        have hagree : ∀ u ∈ vars.take n, (u ∈ S₀ \ {v} ↔ u ∈ S₀) := by
          intro u hu
          constructor
          · exact fun h => h.1
          · intro h
            exact ⟨h, by rintro rfl; exact hvnot hu⟩
        have hvS : v ∉ S₀ \ {v} := by simp
        rw [htake, testsOf_append_singleton, writesOf_append_singleton,
          testsOf_congr hagree, writesOf_congr hagree, hS₀]
        simp only [testAct, writeAct, if_neg hvS]
        simp [List.append_assoc]

/-- **The two phases of `STATE_n^1`.**  Every refinement of `STATE_n^1` first tests the first
`n` facts in the first copy, then runs a refinement of `STATE_{|V|}^3`, and finally writes the
tested values into the fourth copy. -/
theorem yieldSeq_STATE1_phases (hnd : vars.Nodup) :
    ∀ {n : ℕ}, n ≤ vars.length → ∀ {as : List (AcAct F A C)},
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE1 n)] as →
    ∃ (S : Set F) (inner : List (AcAct F A C)),
      (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE3 vars.length)] inner ∧
      as = testsOf 0 S (vars.take n) ++ inner ++ writesOf 3 S (vars.take n) := by
  intro n
  induction n with
  | zero =>
      intro _ as h
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_STATE1_zero_iff] at hbs
      subst hbs
      refine ⟨∅, as, ?_, by simp⟩
      simpa using hy
  | succ n ih =>
      intro hn as h
      rw [yieldSeq_inr_cons_iff] at h
      obtain ⟨bs, hbs, hy⟩ := h
      rw [seqBody_STATE1_succ_iff] at hbs
      obtain ⟨v, hv, hbs⟩ := hbs
      have htake : vars.take (n + 1) = vars.take n ++ [v] := by
        rw [List.take_add_one, hv]; rfl
      have hvnot : v ∉ vars.take n := not_mem_take_of_getElem? hnd hv
      obtain ⟨a, b, hbs', hab⟩ :
          ∃ a b : AcAct F A C,
            bs = [Sum.inl a, Sum.inr (AcTask.STATE1 n), Sum.inl b] ∧
            ((a = AcAct.prePV v 0 0 ∧ b = AcAct.setV v 3) ∨
             (a = AcAct.preNV v 0 0 ∧ b = AcAct.delV v 3)) := by
        rcases hbs with rfl | rfl
        · exact ⟨_, _, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩⟩
      subst hbs'
      simp only [List.cons_append, List.nil_append, yieldSeq_inl_cons_iff] at hy
      obtain ⟨as₁, rfl, hy⟩ := hy
      have hy' : (domain D vars bound).YieldSeq
          ([Sum.inr (AcTask.STATE1 n)] ++ [Sum.inl b]) as₁ := by simpa using hy
      obtain ⟨as₂, as₃, rfl, hy₂, hy₃⟩ := hy'.split
      simp only [yieldSeq_inl_cons_iff, yieldSeq_nil_iff] at hy₃
      obtain ⟨as₄, rfl, rfl⟩ := hy₃
      obtain ⟨S₀, inner, hinner, hS₀⟩ := ih (by omega) hy₂
      classical
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨insert v S₀, inner, hinner, ?_⟩
        have hagree : ∀ u ∈ vars.take n, (u ∈ insert v S₀ ↔ u ∈ S₀) := by
          intro u hu
          constructor
          · rintro (rfl | h)
            · exact absurd hu hvnot
            · exact h
          · exact fun h => Or.inr h
        rw [htake, testsOf_append_singleton, writesOf_append_singleton,
          testsOf_congr hagree, writesOf_congr hagree, hS₀]
        simp only [testAct, writeAct, if_pos (Set.mem_insert v S₀)]
        simp [List.append_assoc]
      · refine ⟨S₀ \ {v}, inner, hinner, ?_⟩
        have hagree : ∀ u ∈ vars.take n, (u ∈ S₀ \ {v} ↔ u ∈ S₀) := by
          intro u hu
          constructor
          · exact fun h => h.1
          · intro h
            exact ⟨h, by rintro rfl; exact hvnot hu⟩
        have hvS : v ∉ S₀ \ {v} := by simp
        rw [htake, testsOf_append_singleton, writesOf_append_singleton,
          testsOf_congr hagree, writesOf_congr hagree, hS₀]
        simp only [testAct, writeAct, if_neg hvS]
        simp [List.append_assoc]

/-! ### The actions of the synchronisation part -/

@[simp] lemma applicable_accept_iff {x : RW} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.accept x) s ↔ AcFact.key1 x ∈ s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

@[simp] lemma applicable_doneA {x : RW} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.doneA x) s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

@[simp] lemma applicable_preC_iff {t : A ⊕ C} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.preC t) s ↔ AcFact.task t ∈ s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

@[simp] lemma applicable_setC {t : A ⊕ C} {s : Set (AcFact F A C)} :
    (domain D vars bound).Applicable (AcAct.setC t) s := by
  simp [ActionModel.Applicable, domain, actionModel, prec]

@[simp] lemma transition_preC {t : A ⊕ C} {s : Set (AcFact F A C)} :
    (domain D vars bound).transition (AcAct.preC t) s = s := by
  simp [ActionModel.transition, domain, actionModel, add, del]

@[simp] lemma mem_transition_setC {t : A ⊕ C} {s : Set (AcFact F A C)} {f : AcFact F A C} :
    f ∈ (domain D vars bound).transition (AcAct.setC t) s ↔
      ((f ∈ s ∧ ∀ t' : A ⊕ C, f ≠ AcFact.task t') ∨ f = AcFact.task t) := by
  simp only [ActionModel.transition, domain, actionModel, add, del, Set.mem_union,
    Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨hf, hnot⟩ | rfl)
    · by_cases hft : ∃ t' : A ⊕ C, f = AcFact.task t'
      · obtain ⟨t', rfl⟩ := hft
        by_cases htt : t' = t
        · exact Or.inr (by rw [htt])
        · exact absurd ⟨t', rfl, htt⟩ hnot
      · exact Or.inl ⟨hf, fun t' hc => hft ⟨t', hc⟩⟩
    · exact Or.inr rfl
  · rintro (⟨hf, hnot⟩ | rfl)
    · exact Or.inl ⟨hf, by rintro ⟨t', rfl, -⟩; exact (hnot t') rfl⟩
    · exact Or.inr rfl

/-! ### The two phases of a memory cell -/

/-- The **write phase** of a memory cell holding the triple `(S, t, S')`: it takes the write
handshake, tests that the first copy holds `S`, the third copy holds `S'` and the stored task
name is `t`, and signals `done_W`.  It changes no state copy. -/
noncomputable def memWrite (S S' : Set F) (t : A ⊕ C) (vars : List F) : List (AcAct F A C) :=
  AcAct.accept RW.write :: (testsOf 0 S vars ++ testsOf 2 S' vars ++
    [AcAct.preC t, AcAct.doneA RW.write])

/-- The **read phase** of a memory cell holding the triple `(S, t, S')`: it takes the read
handshake, restores the task name `t`, writes `S'` into the fifth copy and `S` into the fourth
copy, and signals `done_R`. -/
noncomputable def memRead (S S' : Set F) (t : A ⊕ C) (vars : List F) : List (AcAct F A C) :=
  AcAct.accept RW.read :: AcAct.setC t :: (writesOf 4 S' vars ++ writesOf 3 S vars ++
    [AcAct.doneA RW.read])

/-- **Every refinement of a memory cell is a write phase followed by a read phase.** -/
theorem yieldSeq_MEM_phases (hnd : vars.Nodup) {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] as) :
    ∃ (S S' : Set F) (t : A ⊕ C), as = memWrite S S' t vars ++ memRead S S' t vars := by
  rw [yieldSeq_MEM_iff] at h
  obtain ⟨as', hy, rfl⟩ := h
  obtain ⟨S, inner, hinner, hS⟩ :=
    yieldSeq_STATE1_phases (D := D) (bound := bound) hnd (le_refl vars.length) hy
  obtain ⟨S', t, hS'⟩ :=
    yieldSeq_STATE3_phases (D := D) (bound := bound) hnd (le_refl vars.length) hinner
  refine ⟨S, S', t, ?_⟩
  rw [List.take_length] at hS hS'
  rw [hS, hS', memWrite, memRead]
  simp [List.append_assoc]

/-- Conversely, **every triple gives a refinement of a memory cell**: the write phase followed
by the read phase for `(S, t, S')` is a refinement of `MEM`. -/
theorem yieldSeq_MEM_memPhases (S S' : Set F) (t : A ⊕ C) :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)]
      (memWrite S S' t vars ++ memRead S S' t vars) := by
  classical
  have hprim : ∀ a : AcAct F A C, (domain D vars bound).YieldSeq [Sum.inl a] [a] :=
    fun a => Domain.YieldSeq.prim Domain.YieldSeq.nil
  have hstate3 : ∀ n ≤ vars.length, (domain D vars bound).YieldSeq
      [Sum.inr (AcTask.STATE3 n)]
      (testsOf 2 S' (vars.take n) ++
        [AcAct.preC t, AcAct.doneA RW.write, AcAct.accept RW.read, AcAct.setC t] ++
        writesOf 4 S' (vars.take n)) := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [yieldSeq_inr_cons_iff]
        refine ⟨_, seqBody_STATE3_zero_iff.2 ⟨t, rfl⟩, ?_⟩
        simp only [List.take_zero, testsOf_nil, writesOf_nil, List.nil_append,
          List.append_nil]
        exact Domain.YieldSeq.prim (Domain.YieldSeq.prim (Domain.YieldSeq.prim
          (Domain.YieldSeq.prim Domain.YieldSeq.nil)))
    | succ n ih =>
        intro hn
        have hn' : n < vars.length := by omega
        have hv : vars[n]? = some vars[n] := List.getElem?_eq_getElem hn'
        have htake : vars.take (n + 1) = vars.take n ++ [vars[n]] := by
          rw [List.take_add_one, hv]; rfl
        have hmid := ih (by omega)
        have hstep : ∀ a b : AcAct F A C,
            (domain D vars bound).SeqBody (AcTask.STATE3 (n + 1))
              [Sum.inl a, Sum.inr (AcTask.STATE3 n), Sum.inl b] →
            (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE3 (n + 1))]
              (a :: ((testsOf 2 S' (vars.take n) ++
                [AcAct.preC t, AcAct.doneA RW.write, AcAct.accept RW.read, AcAct.setC t] ++
                writesOf 4 S' (vars.take n)) ++ [b])) := by
          intro a b hb
          rw [yieldSeq_inr_cons_iff]
          refine ⟨_, hb, ?_⟩
          simpa using (hprim a).append (hmid.append (hprim b))
        rw [htake, testsOf_append_singleton, writesOf_append_singleton]
        by_cases hmem : vars[n] ∈ S'
        · have hb := hstep (AcAct.prePV vars[n] 2 2) (AcAct.setV vars[n] 4)
            (seqBody_STATE3_succ_iff.2 ⟨vars[n], hv, Or.inl rfl⟩)
          simp only [testAct, writeAct, if_pos hmem]
          simpa [List.append_assoc] using hb
        · have hb := hstep (AcAct.preNV vars[n] 2 2) (AcAct.delV vars[n] 4)
            (seqBody_STATE3_succ_iff.2 ⟨vars[n], hv, Or.inr rfl⟩)
          simp only [testAct, writeAct, if_neg hmem]
          simpa [List.append_assoc] using hb
  have hstate1 : ∀ n ≤ vars.length, (domain D vars bound).YieldSeq
      [Sum.inr (AcTask.STATE1 n)]
      (testsOf 0 S (vars.take n) ++
        (testsOf 2 S' vars ++
          [AcAct.preC t, AcAct.doneA RW.write, AcAct.accept RW.read, AcAct.setC t] ++
          writesOf 4 S' vars) ++
        writesOf 3 S (vars.take n)) := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [yieldSeq_inr_cons_iff]
        refine ⟨_, seqBody_STATE1_zero_iff.2 rfl, ?_⟩
        simp only [List.take_zero, testsOf_nil, writesOf_nil, List.nil_append,
          List.append_nil]
        have h := hstate3 vars.length (le_refl _)
        rw [List.take_length] at h
        simpa using h
    | succ n ih =>
        intro hn
        have hn' : n < vars.length := by omega
        have hv : vars[n]? = some vars[n] := List.getElem?_eq_getElem hn'
        have htake : vars.take (n + 1) = vars.take n ++ [vars[n]] := by
          rw [List.take_add_one, hv]; rfl
        have hmid := ih (by omega)
        have hstep : ∀ a b : AcAct F A C,
            (domain D vars bound).SeqBody (AcTask.STATE1 (n + 1))
              [Sum.inl a, Sum.inr (AcTask.STATE1 n), Sum.inl b] →
            (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE1 (n + 1))]
              (a :: ((testsOf 0 S (vars.take n) ++
                (testsOf 2 S' vars ++
                  [AcAct.preC t, AcAct.doneA RW.write, AcAct.accept RW.read, AcAct.setC t] ++
                  writesOf 4 S' vars) ++
                writesOf 3 S (vars.take n)) ++ [b])) := by
          intro a b hb
          rw [yieldSeq_inr_cons_iff]
          refine ⟨_, hb, ?_⟩
          simpa using (hprim a).append (hmid.append (hprim b))
        rw [htake, testsOf_append_singleton, writesOf_append_singleton]
        by_cases hmem : vars[n] ∈ S
        · have hb := hstep (AcAct.prePV vars[n] 0 0) (AcAct.setV vars[n] 3)
            (seqBody_STATE1_succ_iff.2 ⟨vars[n], hv, Or.inl rfl⟩)
          simp only [testAct, writeAct, if_pos hmem]
          simpa [List.append_assoc] using hb
        · have hb := hstep (AcAct.preNV vars[n] 0 0) (AcAct.delV vars[n] 3)
            (seqBody_STATE1_succ_iff.2 ⟨vars[n], hv, Or.inr rfl⟩)
          simp only [testAct, writeAct, if_neg hmem]
          simpa [List.append_assoc] using hb
  rw [yieldSeq_MEM_iff]
  refine ⟨_, hstate1 vars.length (le_refl _), ?_⟩
  rw [List.take_length, memWrite, memRead]
  simp [List.append_assoc]

/-! ### The semantics of the two phases -/

/-- The write phase is executable exactly when the cell's write handshake is up, the first copy
holds `S`, the third copy holds `S'` and the stored task name is `t`. -/
theorem seqApplicable_memWrite_iff {S S' : Set F} {t : A ⊕ C} {s : Set (AcFact F A C)} :
    (domain D vars bound).SeqApplicable (memWrite S S' t vars) s ↔
      (AcFact.key1 RW.write ∈ s ∧
        (∀ v ∈ vars, (v ∈ S → AcFact.pos v 0 ∈ s) ∧ (v ∉ S → AcFact.neg v 0 ∈ s)) ∧
        (∀ v ∈ vars, (v ∈ S' → AcFact.pos v 2 ∈ s) ∧ (v ∉ S' → AcFact.neg v 2 ∈ s)) ∧
        AcFact.task t ∈ s) := by
  classical
  have key : ∀ f : AcFact F A C, f ≠ AcFact.key1 RW.write →
      (f ∈ (domain D vars bound).transition (AcAct.accept RW.write) s ↔ f ∈ s) := by
    intro f hf
    rw [mem_transition_accept]
    simp [hf]
  rw [memWrite, ActionModel.seqApplicable_cons, applicable_accept_iff,
    ActionModel.seqApplicable_append, ActionModel.seqApplicable_append,
    ActionModel.transitionSeq_append]
  simp only [transitionSeq_testsOf, seqApplicable_testsOf_iff, ActionModel.seqApplicable_cons,
    applicable_preC_iff, transition_preC, applicable_doneA, ActionModel.seqApplicable_nil,
    and_true]
  constructor
  · rintro ⟨hk, ⟨h0, h2⟩, ht⟩
    refine ⟨hk, ?_, ?_, (key _ (by simp)).1 ht⟩
    · exact fun v hv => ⟨fun hx => (key _ (by simp)).1 ((h0 v hv).1 hx),
        fun hx => (key _ (by simp)).1 ((h0 v hv).2 hx)⟩
    · exact fun v hv => ⟨fun hx => (key _ (by simp)).1 ((h2 v hv).1 hx),
        fun hx => (key _ (by simp)).1 ((h2 v hv).2 hx)⟩
  · rintro ⟨hk, h0, h2, ht⟩
    refine ⟨hk, ⟨?_, ?_⟩, (key _ (by simp)).2 ht⟩
    · exact fun v hv => ⟨fun hx => (key _ (by simp)).2 ((h0 v hv).1 hx),
        fun hx => (key _ (by simp)).2 ((h0 v hv).2 hx)⟩
    · exact fun v hv => ⟨fun hx => (key _ (by simp)).2 ((h2 v hv).1 hx),
        fun hx => (key _ (by simp)).2 ((h2 v hv).2 hx)⟩

/-- The write phase changes nothing but the two write semaphores: it lowers `key₁^W` and raises
`key₂^W`.  In particular it changes no state copy — the triple it read is stored in the
hierarchy, not in the state. -/
theorem mem_transitionSeq_memWrite {S S' : Set F} {t : A ⊕ C} {s : Set (AcFact F A C)}
    {f : AcFact F A C} :
    f ∈ (domain D vars bound).transitionSeq (memWrite S S' t vars) s ↔
      ((f ∈ s ∧ f ≠ AcFact.key1 RW.write) ∨ f = AcFact.key2 RW.write) := by
  classical
  rw [memWrite]
  simp only [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append,
    transitionSeq_testsOf, transition_preC, ActionModel.transitionSeq_nil,
    mem_transition_doneA, mem_transition_accept]

/-- The read phase is executable as soon as the cell's read handshake is up. -/
theorem seqApplicable_memRead {S S' : Set F} {t : A ⊕ C} {s : Set (AcFact F A C)}
    (h : AcFact.key1 RW.read ∈ s) :
    (domain D vars bound).SeqApplicable (memRead S S' t vars) s := by
  classical
  rw [memRead, ActionModel.seqApplicable_cons, ActionModel.seqApplicable_cons,
    ActionModel.seqApplicable_append, ActionModel.seqApplicable_append]
  refine ⟨by simpa using h, applicable_setC,
    ⟨seqApplicable_writesOf, seqApplicable_writesOf⟩, ?_⟩
  simp

/-- A representation in one copy survives writes to another copy. -/
lemma representsOn_writesOf_other {j j' : Fin 5} (hjj : j ≠ j') {S T : Set F}
    {vs ws : List F} {s : Set (AcFact F A C)} (h : RepresentsOn s j S vs) :
    RepresentsOn ((domain D vars bound).transitionSeq (writesOf j' T ws) s) j S vs := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [unchanged_writesOf (D := D) (vars := vars) (bound := bound)
      (fun w _ => ⟨by simp [hjj], by simp⟩),
    unchanged_writesOf (D := D) (vars := vars) (bound := bound)
      (fun w _ => ⟨by simp, by simp [hjj]⟩)]
  exact ⟨h1, h2⟩

/-- A representation survives the signalling actions. -/
lemma representsOn_transition_doneA {j : Fin 5} {S : Set F} {vs : List F}
    {s : Set (AcFact F A C)} {x : RW} (h : RepresentsOn s j S vs) :
    RepresentsOn ((domain D vars bound).transition (AcAct.doneA x) s) j S vs := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  rw [mem_transition_doneA, mem_transition_doneA]
  simpa using ⟨h1, h2⟩

/-- **What the read phase does.**  It installs the triple the cell latched during its write
phase: the fourth copy gets `S`, the fifth copy gets `S'`, the stored task name is `t` again,
and the read handshake is answered. -/
theorem memRead_spec {S S' : Set F} {t : A ⊕ C} {s : Set (AcFact F A C)} :
    RepresentsOn ((domain D vars bound).transitionSeq (memRead S S' t vars) s) 3 S vars ∧
    RepresentsOn ((domain D vars bound).transitionSeq (memRead S S' t vars) s) 4 S' vars ∧
    AcFact.task t ∈ (domain D vars bound).transitionSeq (memRead S S' t vars) s ∧
    AcFact.key2 RW.read ∈ (domain D vars bound).transitionSeq (memRead S S' t vars) s := by
  classical
  have hexp : (domain D vars bound).transitionSeq (memRead S S' t vars) s =
      (domain D vars bound).transition (AcAct.doneA RW.read)
        ((domain D vars bound).transitionSeq (writesOf 3 S vars)
          ((domain D vars bound).transitionSeq (writesOf 4 S' vars)
            ((domain D vars bound).transition (AcAct.setC t)
              ((domain D vars bound).transition (AcAct.accept RW.read) s)))) := by
    rw [memRead]
    simp [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_append]
  set s₂ := (domain D vars bound).transition (AcAct.setC t)
    ((domain D vars bound).transition (AcAct.accept RW.read) s) with hs₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hexp]
    exact representsOn_transition_doneA representsOn_writesOf
  · rw [hexp]
    refine representsOn_transition_doneA ?_
    exact representsOn_writesOf_other (by decide) representsOn_writesOf
  · rw [hexp]
    have h₂ : AcFact.task t ∈ s₂ := by rw [hs₂]; exact mem_transition_setC.2 (Or.inr rfl)
    have h₃ : AcFact.task t ∈ (domain D vars bound).transitionSeq (writesOf 4 S' vars) s₂ := by
      rw [unchanged_writesOf (D := D) (vars := vars) (bound := bound)
        (fun w _ => ⟨by simp, by simp⟩)]
      exact h₂
    have h₄ : AcFact.task t ∈ (domain D vars bound).transitionSeq (writesOf 3 S vars)
        ((domain D vars bound).transitionSeq (writesOf 4 S' vars) s₂) := by
      rw [unchanged_writesOf (D := D) (vars := vars) (bound := bound)
        (fun w _ => ⟨by simp, by simp⟩)]
      exact h₃
    exact mem_transition_doneA.2 (Or.inl h₄)
  · rw [hexp]
    exact mem_transition_doneA.2 (Or.inr rfl)

/-! ### The memory cell is a latch -/

/-- **A memory cell is a latch.**  Every refinement of `MEM` splits into two consecutive phases
`ws ++ rs` belonging to one triple `(S, t, S')`:

* the write phase `ws` is executable exactly in the states in which the write handshake is up,
  the first copy holds `S`, the third copy holds `S'` and the stored task name is `t`, and it
  changes nothing but the two write semaphores;
* the read phase `rs` is executable as soon as the read handshake is up, and it installs `S` in
  the fourth copy, `S'` in the fifth copy and `t` as the stored task name, and answers the read
  handshake.

The two phases may be separated by arbitrarily many other actions of the plan: the triple is
carried by the hierarchy, not by the state.  This is the specification of a memory cell that the
global simulation argument of the compilation uses, in both directions
(`HTN.ToAc.yieldSeq_MEM_memPhases` provides the converse: every triple arises this way). -/
theorem mem_isLatch (hnd : vars.Nodup) {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] as) :
    ∃ (S S' : Set F) (t : A ⊕ C) (ws rs : List (AcAct F A C)),
      as = ws ++ rs ∧
      (∀ s : Set (AcFact F A C), (domain D vars bound).SeqApplicable ws s ↔
        (AcFact.key1 RW.write ∈ s ∧
          (∀ v ∈ vars, (v ∈ S → AcFact.pos v 0 ∈ s) ∧ (v ∉ S → AcFact.neg v 0 ∈ s)) ∧
          (∀ v ∈ vars, (v ∈ S' → AcFact.pos v 2 ∈ s) ∧ (v ∉ S' → AcFact.neg v 2 ∈ s)) ∧
          AcFact.task t ∈ s)) ∧
      (∀ (s : Set (AcFact F A C)) (f : AcFact F A C),
        f ∈ (domain D vars bound).transitionSeq ws s ↔
          ((f ∈ s ∧ f ≠ AcFact.key1 RW.write) ∨ f = AcFact.key2 RW.write)) ∧
      (∀ s : Set (AcFact F A C), AcFact.key1 RW.read ∈ s →
        (domain D vars bound).SeqApplicable rs s) ∧
      (∀ s : Set (AcFact F A C),
        RepresentsOn ((domain D vars bound).transitionSeq rs s) 3 S vars ∧
        RepresentsOn ((domain D vars bound).transitionSeq rs s) 4 S' vars ∧
        AcFact.task t ∈ (domain D vars bound).transitionSeq rs s ∧
        AcFact.key2 RW.read ∈ (domain D vars bound).transitionSeq rs s) := by
  obtain ⟨S, S', t, rfl⟩ := yieldSeq_MEM_phases hnd h
  exact ⟨S, S', t, memWrite S S' t vars, memRead S S' t vars, rfl,
    fun s => seqApplicable_memWrite_iff, fun s f => mem_transitionSeq_memWrite,
    fun s hs => seqApplicable_memRead hs, fun s => memRead_spec⟩

end ToAc

end HTN
