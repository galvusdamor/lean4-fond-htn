import HtnComplexity.Regular.RegularToCE
/-!
# One step of the compiled problem

This file analyses a single action of the conditional-effect compilation
`HTN.RegularCE.ceProblem` of `HtnComplexity/Regular/RegularToCE.lean`.  The states that matter are
the three *configurations*

* `encP s c` — the source state `s`, the compound task `c` still to be decomposed;
* `encMid s m k` — the source state `s`, the body of the method `m` executed up to its position
  `k` (for `k = |body m|` this is the configuration the tail marker of `m` describes, i.e. again
  an `encP` or an `encD`);
* `encD s` — the source state `s`, the hierarchy completely decomposed.

The results are: which actions are applicable in a configuration (`applicable_start_encP_iff`,
`applicable_op_encMid_iff`, and the negative counterparts), and what they do
(`succ_start_encP`, `succ_op_encMid`).
-/

namespace HTN

namespace RegularCE

open CE

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### The configurations -/

/-- The configuration "the source state is `s` and the compound task `c` is still open". -/
def encP (s : Set F) (c : C) : Set (CEFact F A C I) := encS s ∪ {CEFact.pending c}

/-- The configuration "the source state is `s` and the hierarchy is fully decomposed". -/
def encD (s : Set F) : Set (CEFact F A C I) := encS s ∪ {CEFact.done}

@[simp] lemma state_mem_encP {s : Set F} {c : C} {v : F} :
    (CEFact.state v : CEFact F A C I) ∈ encP s c ↔ v ∈ s := by simp [encP]

@[simp] lemma state_mem_encD {s : Set F} {v : F} :
    (CEFact.state v : CEFact F A C I) ∈ encD s ↔ v ∈ s := by simp [encD]

@[simp] lemma pending_mem_encP {s : Set F} {c c' : C} :
    (CEFact.pending c' : CEFact F A C I) ∈ encP s c ↔ c' = c := by simp [encP]

@[simp] lemma done_notMem_encP {s : Set F} {c : C} :
    (CEFact.done : CEFact F A C I) ∉ encP s c := by simp [encP]

@[simp] lemma bot_notMem_encP {s : Set F} {c : C} :
    (CEFact.bot : CEFact F A C I) ∉ encP s c := by simp [encP]

@[simp] lemma run_notMem_encP {s : Set F} {c : C} {a : A} :
    (CEFact.run a : CEFact F A C I) ∉ encP s c := by simp [encP]

@[simp] lemma mark_notMem_encP {s : Set F} {c : C} {m : Method I A C} {k : ℕ} :
    (CEFact.mark m k : CEFact F A C I) ∉ encP s c := by simp [encP]

@[simp] lemma pending_notMem_encD {s : Set F} {c : C} :
    (CEFact.pending c : CEFact F A C I) ∉ encD s := by simp [encD]

@[simp] lemma run_notMem_encD {s : Set F} {a : A} :
    (CEFact.run a : CEFact F A C I) ∉ encD s := by simp [encD]

@[simp] lemma bot_notMem_encD {s : Set F} :
    (CEFact.bot : CEFact F A C I) ∉ encD s := by simp [encD]

@[simp] lemma done_mem_encD {s : Set F} :
    (CEFact.done : CEFact F A C I) ∈ encD s := by simp [encD]

/-! ### The state part of a transition -/

/-- The `state` facts of a configuration and its marker part do not interfere: this is the
computation of a successor state, once and for all. -/
lemma succ_calc (s dl ad : Set F) (P P' : Set (CEFact F A C I))
    (hP : ∀ v : F, CEFact.state v ∉ P) (hP' : ∀ v : F, CEFact.state v ∉ P') :
    ((encS s ∪ P) \ ((encS dl \ encS ad) ∪ (P \ P'))) ∪ (encS ad ∪ P') =
      encS ((s \ dl) ∪ ad) ∪ P' := by
  ext f
  cases f with
  | state v =>
      have h1 : (CEFact.state v : CEFact F A C I) ∉ P := hP v
      have h2 : (CEFact.state v : CEFact F A C I) ∉ P' := hP' v
      simp only [Set.mem_union, Set.mem_diff, state_mem_encS, h1, h2, or_false, and_true,
        not_false_eq_true]
      tauto
  | pending c => simp only [Set.mem_union, Set.mem_diff, pending_notMem_encS]; tauto
  | mark m k => simp only [Set.mem_union, Set.mem_diff, mark_notMem_encS]; tauto
  | run a => simp only [Set.mem_union, Set.mem_diff, run_notMem_encS]; tauto
  | done => simp only [Set.mem_union, Set.mem_diff, done_notMem_encS]; tauto
  | bot => simp only [Set.mem_union, Set.mem_diff, bot_notMem_encS]; tauto

/-- The special case of `succ_calc` in which no source fact changes. -/
lemma succ_calc_marker (s : Set F) (P P' : Set (CEFact F A C I))
    (hP : ∀ v : F, CEFact.state v ∉ P) (hP' : ∀ v : F, CEFact.state v ∉ P') :
    ((encS s ∪ P) \ (P \ P')) ∪ P' = encS s ∪ P' := by
  ext f
  cases f with
  | state v =>
      have h1 : (CEFact.state v : CEFact F A C I) ∉ P := hP v
      have h2 : (CEFact.state v : CEFact F A C I) ∉ P' := hP' v
      simp only [Set.mem_union, Set.mem_diff, state_mem_encS, h1, h2, or_false, and_true,
        not_false_eq_true]
  | pending c => simp only [Set.mem_union, Set.mem_diff, pending_notMem_encS]; tauto
  | mark m k => simp only [Set.mem_union, Set.mem_diff, mark_notMem_encS]; tauto
  | run a => simp only [Set.mem_union, Set.mem_diff, run_notMem_encS]; tauto
  | done => simp only [Set.mem_union, Set.mem_diff, done_notMem_encS]; tauto
  | bot => simp only [Set.mem_union, Set.mem_diff, bot_notMem_encS]; tauto

variable [DecidableEq I] {D : Domain F A C I} {ms : Finset (Method I A C)}

/-- The configuration "the source state is `s` and the body of `m` has been executed up to its
position `k`". -/
noncomputable def encMid (s : Set F) (m : Method I A C) (k : ℕ) : Set (CEFact F A C I) :=
  encS s ∪ posMark m k

@[simp] lemma state_mem_encMid {s : Set F} {m : Method I A C} {k : ℕ} {v : F} :
    (CEFact.state v : CEFact F A C I) ∈ encMid s m k ↔ v ∈ s := by
  simp only [encMid, Set.mem_union, state_mem_encS, state_notMem_posMark, or_false]

/-- At the end of the body of a method the configuration is the one its tail marker
describes. -/
lemma encMid_length (s : Set F) (m : Method I A C) :
    encMid s m (bodyOps m).length =
      match bodyNext m with
      | none => encD s
      | some c' => encP s c' := by
  rw [encMid, posMark_length, tailMark]
  cases hb : bodyNext m with
  | none => simp only [encD]
  | some c' => simp only [encP]

/-! ### The action of a method -/

lemma adds_startAction (m : Method I A C) (T : Set (CEFact F A C I)) :
    (startAction D m).adds T = posMark m 0 := by
  ext f
  constructor
  · rintro ⟨e, he, -, hf⟩
    rw [startAction, List.mem_singleton] at he
    subst he
    exact hf
  · intro hf
    exact ⟨_, by rw [startAction]; exact List.mem_singleton.2 rfl, Lits.holds_empty _, hf⟩

lemma dels_startAction (m : Method I A C) (T : Set (CEFact F A C I)) :
    (startAction D m).dels T = {CEFact.pending m.abstractTask} \ posMark (F := F) m 0 := by
  ext f
  constructor
  · rintro ⟨e, he, -, hf⟩
    rw [startAction, List.mem_singleton] at he
    subst he
    exact hf
  · intro hf
    exact ⟨_, by rw [startAction]; exact List.mem_singleton.2 rfl, Lits.holds_empty _, hf⟩

/-- **A method action is applicable exactly when the task it decomposes is the open one and the
method is usable.** -/
lemma applicable_start_encP_iff {m : Method I A C} {s : Set F} {c : C} :
    (startAction D m).Applicable (encP s c) ↔ (m.abstractTask = c ∧ Usable D m) := by
  constructor
  · rintro ⟨hpre, -⟩
    have hsub : ({CEFact.pending m.abstractTask} ∪
        {f : CEFact F A C I | f = CEFact.bot ∧ ¬ Usable D m}) ⊆ encP s c := hpre.1
    have hpend : (CEFact.pending m.abstractTask : CEFact F A C I) ∈ encP s c :=
      hsub (Or.inl rfl)
    refine ⟨pending_mem_encP.1 hpend, ?_⟩
    by_contra hcon
    exact bot_notMem_encP (hsub (Or.inr ⟨rfl, hcon⟩))
  · rintro ⟨hc, hu⟩
    refine ⟨⟨?_, fun f hf => absurd hf (Set.notMem_empty f)⟩, ?_⟩
    · rintro f (hf | ⟨rfl, hf⟩)
      · simp only [Set.mem_singleton_iff] at hf
        subst hf
        exact pending_mem_encP.2 hc
      · exact absurd hu hf
    · intro f hf hf'
      rw [adds_startAction] at hf
      rw [dels_startAction] at hf'
      exact hf'.2 hf

/-- **What a method action does.** -/
lemma succ_start_encP {m : Method I A C} {s : Set F} :
    (startAction D m).succ (encP s m.abstractTask) = encMid s m 0 := by
  rw [Action.succ, adds_startAction, dels_startAction, encP, encMid]
  exact succ_calc_marker s _ _ (by simp) (by simp)

/-- No method action is applicable inside the body of a method. -/
lemma not_applicable_start_encMid {m m' : Method I A C} {s : Set F} {k : ℕ}
    (hk : k < (bodyOps m).length) : ¬ (startAction D m').Applicable (encMid s m k) := by
  rintro ⟨hpre, -⟩
  have hsub : ({CEFact.pending m'.abstractTask} ∪
      {f : CEFact F A C I | f = CEFact.bot ∧ ¬ Usable D m'}) ⊆ encMid s m k := hpre.1
  have hpend : (CEFact.pending m'.abstractTask : CEFact F A C I) ∈ encMid s m k :=
    hsub (Or.inl rfl)
  obtain ⟨a, ha⟩ : ∃ a, (bodyOps m)[k]? = some a := by
    rw [List.getElem?_eq_getElem hk]
    exact ⟨_, rfl⟩
  rw [encMid, posMark_of_getElem ha] at hpend
  rcases hpend with h | h
  · exact pending_notMem_encS h
  · rcases h with h | h <;> exact absurd h (by simp)

/-- No method action is applicable once the hierarchy is decomposed. -/
lemma not_applicable_start_encD {m : Method I A C} {s : Set F} :
    ¬ (startAction D m).Applicable (encD s) := by
  rintro ⟨hpre, -⟩
  have hsub : ({CEFact.pending m.abstractTask} ∪
      {f : CEFact F A C I | f = CEFact.bot ∧ ¬ Usable D m}) ⊆ encD s := hpre.1
  exact pending_notMem_encD (hsub (Or.inl rfl))

/-! ### The action of an operator -/

/-- Inside the body of a method exactly one conditional effect of an operator action is
active. -/
lemma cond_holds_iff {a : A} {m : Method I A C} {k : ℕ} {s : Set F}
    (ha : (bodyOps m)[k]? = some a) {e : CEff (CEFact F A C I)} (he : e ∈ occEffs ms a) :
    e.cond.Holds (encMid s m k) ↔ e = occEff m k := by
  obtain ⟨m', -, k', hk', rfl⟩ := mem_occEffs.1 he
  constructor
  · rintro ⟨hpos, -⟩
    have hmem : (CEFact.mark m' k' : CEFact F A C I) ∈ encMid s m k := hpos (by simp [occEff])
    rw [encMid, posMark_of_getElem ha] at hmem
    rcases hmem with h | h
    · exact absurd h (by simp)
    · rcases h with h | h
      · obtain ⟨rfl, rfl⟩ : m' = m ∧ k' = k := by
          simpa using h
        rfl
      · exact absurd h (by simp)
  · intro he'
    obtain ⟨rfl, rfl⟩ : m' = m ∧ k' = k := by
      have h2 : (CEFact.mark m' k' : CEFact F A C I) ∈
          (occEff (F := F) m k).cond.pos := by
        rw [← he']
        exact rfl
      simpa [occEff] using h2
    refine ⟨?_, by simp [occEff]⟩
    intro f hf
    simp only [occEff, Set.mem_singleton_iff] at hf
    subst hf
    rw [encMid, posMark_of_getElem ha]
    exact Or.inr (Or.inl rfl)

lemma adds_opAction {a : A} {m : Method I A C} {k : ℕ} {s : Set F} (hm : m ∈ ms)
    (ha : (bodyOps m)[k]? = some a) :
    (opAction D ms a).adds (encMid s m k) = encS (D.add a) ∪ posMark m (k + 1) := by
  have hocc : occEff (F := F) m k ∈ occEffs ms a := mem_occEffs.2 ⟨m, hm, k, ha, rfl⟩
  ext f
  constructor
  · rintro ⟨e, he, hcond, hf⟩
    rw [opAction, List.mem_cons] at he
    rcases he with rfl | he
    · exact Or.inl hf
    · rw [cond_holds_iff ha he] at hcond
      subst hcond
      exact Or.inr hf
  · rintro (hf | hf)
    · refine ⟨⟨∅, ⟨encS (D.add a), encS (D.del a) \ encS (D.add a)⟩⟩, ?_, Lits.holds_empty _, hf⟩
      rw [opAction]
      exact List.mem_cons_self ..
    · refine ⟨occEff m k, ?_, (cond_holds_iff (s := s) ha hocc).2 rfl, hf⟩
      rw [opAction, List.mem_cons]
      exact Or.inr hocc

lemma dels_opAction {a : A} {m : Method I A C} {k : ℕ} {s : Set F} (hm : m ∈ ms)
    (ha : (bodyOps m)[k]? = some a) :
    (opAction D ms a).dels (encMid s m k) =
      (encS (D.del a) \ encS (D.add a)) ∪ (posMark m k \ posMark m (k + 1)) := by
  have hocc : occEff (F := F) m k ∈ occEffs ms a := mem_occEffs.2 ⟨m, hm, k, ha, rfl⟩
  ext f
  constructor
  · rintro ⟨e, he, hcond, hf⟩
    rw [opAction, List.mem_cons] at he
    rcases he with rfl | he
    · exact Or.inl hf
    · rw [cond_holds_iff ha he] at hcond
      subst hcond
      exact Or.inr hf
  · rintro (hf | hf)
    · refine ⟨⟨∅, ⟨encS (D.add a), encS (D.del a) \ encS (D.add a)⟩⟩, ?_, Lits.holds_empty _, hf⟩
      rw [opAction]
      exact List.mem_cons_self ..
    · refine ⟨occEff m k, ?_, (cond_holds_iff (s := s) ha hocc).2 rfl, hf⟩
      rw [opAction, List.mem_cons]
      exact Or.inr hocc

/-- **An operator action is applicable inside a body exactly when its precondition holds.** -/
lemma applicable_op_encMid_iff {a : A} {m : Method I A C} {k : ℕ} {s : Set F} (hm : m ∈ ms)
    (ha : (bodyOps m)[k]? = some a) :
    (opAction D ms a).Applicable (encMid s m k) ↔ D.prec a ⊆ s := by
  constructor
  · rintro ⟨hpre, -⟩
    intro v hv
    have : (CEFact.state v : CEFact F A C I) ∈ encMid s m k :=
      hpre.1 (Or.inl ⟨v, hv, rfl⟩)
    simpa using this
  · intro hprec
    refine ⟨⟨?_, by simp [opAction]⟩, ?_⟩
    · rintro f (hf | hf)
      · obtain ⟨v, hv, rfl⟩ := hf
        exact Or.inl ⟨v, hprec hv, rfl⟩
      · simp only [Set.mem_singleton_iff] at hf
        subst hf
        rw [encMid, posMark_of_getElem ha]
        exact Or.inr (Or.inr rfl)
    · intro f hf hf'
      rw [adds_opAction hm ha] at hf
      rw [dels_opAction hm ha] at hf'
      rcases hf with hf | hf
      · rcases hf' with hf' | hf'
        · exact hf'.2 hf
        · obtain ⟨v, -, rfl⟩ := hf
          exact (state_notMem_posMark (m := m) (k := k)) hf'.1
      · rcases hf' with hf' | hf'
        · obtain ⟨⟨v, -, rfl⟩, -⟩ := hf'
          exact (state_notMem_posMark (m := m) (k := k + 1)) hf
        · exact hf'.2 hf

/-- **What an operator action does inside a body.** -/
lemma succ_op_encMid {a : A} {m : Method I A C} {k : ℕ} {s : Set F} (hm : m ∈ ms)
    (ha : (bodyOps m)[k]? = some a) :
    (opAction D ms a).succ (encMid s m k) = encMid (D.transition a s) m (k + 1) := by
  rw [Action.succ, adds_opAction hm ha, dels_opAction hm ha, encMid, encMid,
    ActionModel.transition]
  exact succ_calc s (D.del a) (D.add a) _ _ (by simp) (by simp)

/-- No operator action is applicable while a compound task is open. -/
lemma not_applicable_op_encP {a : A} {s : Set F} {c : C} :
    ¬ (opAction D ms a).Applicable (encP s c) := by
  rintro ⟨hpre, -⟩
  exact run_notMem_encP (hpre.1 (Or.inr rfl))

/-- No operator action is applicable once the hierarchy is decomposed. -/
lemma not_applicable_op_encD {a : A} {s : Set F} :
    ¬ (opAction D ms a).Applicable (encD s) := by
  rintro ⟨hpre, -⟩
  exact run_notMem_encD (hpre.1 (Or.inr rfl))

/-- Inside the body of a method, the only operator action that is applicable is the one the
position marker calls for. -/
lemma eq_of_applicable_op_encMid {a a' : A} {m : Method I A C} {k : ℕ} {s : Set F}
    (ha : (bodyOps m)[k]? = some a) (happ : (opAction D ms a').Applicable (encMid s m k)) :
    a' = a := by
  obtain ⟨hpre, -⟩ := happ
  have hmem : (CEFact.run a' : CEFact F A C I) ∈ encMid s m k := hpre.1 (Or.inr rfl)
  rw [encMid, posMark_of_getElem ha] at hmem
  rcases hmem with h | h
  · exact absurd h (by simp)
  · rcases h with h | h
    · exact absurd h (by simp)
    · simpa using h

end RegularCE

end HTN
