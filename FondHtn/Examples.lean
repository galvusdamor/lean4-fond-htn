import FondHtn.FixedMethodsRelations
import FondHtn.MethodPoliciesStrong
/-!
# Examples from [CB21] and [CB22]

* `FOND.Examples.prop_2_13_converse_fails` — **[CB21, Prop. 2.13], second half**: the problem of
  the proof of Prop. 2.13 (`a` adds `1` or `2`; `b` needs `1`, `c` needs `2`; `a ≺ b`, `a ≺ c`)
  has a strong OD solution but no strong LD solution.
-/

namespace FOND

namespace Examples

open HTN

/-- The three primitive task names `a`, `b`, `c`. -/
inductive Act
  | a
  | b
  | c
  deriving DecidableEq

/-- `a ↦ (∅, {({1}, ∅), ({2}, ∅)})`. -/
def actA : Action ℕ := ⟨∅, ∅, {({1}, ∅), ({2}, ∅)}⟩

/-- `b ↦ ({1}, {2}, ∅)`. -/
def actB : Action ℕ := ⟨{1}, ∅, {({2}, ∅)}⟩

/-- `c ↦ ({2}, {1}, ∅)`. -/
def actC : Action ℕ := ⟨{2}, ∅, {({1}, ∅)}⟩

/-- The action mapping. -/
def δabc : Act → Action ℕ
  | .a => actA
  | .b => actB
  | .c => actC

/-! ## [CB21, Prop. 2.13] -/

/-- `tn_I = ⟨{1, 2, 3}, {(1, 2), (1, 3)}, 1 ↦ a, 2 ↦ b, 3 ↦ c⟩`. -/
def tn213 : TaskNetwork ℕ Act Empty where
  T := {1, 2, 3}
  ord := fun x y => x = 1 ∧ (y = 2 ∨ y = 3)
  α := fun x => if x = 1 then .inl .a else if x = 2 then .inl .b else .inl .c

/-- The problem of the proof of [CB21, Prop. 2.13] (no methods, `s_I = ∅`). -/
def P213 : Problem ℕ Act Empty ℕ where
  δ := δabc
  methods := ∅
  init := ∅
  tnI := tn213

lemma P213_decomposesTo {tn : TaskNetwork ℕ Act Empty} (h : P213.DecomposesTo tn213 tn) :
    tn = tn213 := by
  induction h with
  | refl => rfl
  | tail _ hstep _ =>
    obtain ⟨_, _, hm, -⟩ := hstep
    exact absurd hm (Set.notMem_empty _)

lemma outcomes_A {s s' : Set ℕ} (h : s' ∈ actA.outcomes s) : s' = s ∪ {1} ∨ s' = s ∪ {2} := by
  obtain ⟨e, he, rfl⟩ := h
  rcases he with rfl | rfl <;> simp [Action.applyEff]

lemma outcomes_B {s s' : Set ℕ} (h : s' ∈ actB.outcomes s) : s' = s ∪ {2} := by
  obtain ⟨e, rfl, rfl⟩ := h
  simp [Action.applyEff]

lemma outcomes_C {s s' : Set ℕ} (h : s' ∈ actC.outcomes s) : s' = s ∪ {1} := by
  obtain ⟨e, rfl, rfl⟩ := h
  simp [Action.applyEff]

lemma solvable_after_a (s : Set ℕ) (hs : 1 ∈ s ∨ 2 ∈ s) :
    P213.BeliefSolvable (tn213.progress 1) s := by
  rcases hs with hs | hs
  · refine .step (t := 2) (a := .b) ⟨by decide, ?_⟩ rfl ⟨by simpa [actB, δabc, P213] using hs,
      by simp [actB, δabc, P213]⟩ fun s' hs' => ?_
    · intro t' ht' h; simp [tn213] at ht' h
    · obtain rfl := outcomes_B hs'
      refine .step (t := 3) (a := .c) ⟨by decide, ?_⟩ rfl
        ⟨by simp [actC, δabc, P213], by simp [actC, δabc, P213]⟩ fun s'' _ => .empty (by decide)
      intro t' ht' h; simp [tn213] at ht' h
  · refine .step (t := 3) (a := .c) ⟨by decide, ?_⟩ rfl ⟨by simpa [actC, δabc, P213] using hs,
      by simp [actC, δabc, P213]⟩ fun s' hs' => ?_
    · intro t' ht' h; simp [tn213] at ht' h
    · obtain rfl := outcomes_C hs'
      refine .step (t := 2) (a := .b) ⟨by decide, ?_⟩ rfl
        ⟨by simp [actB, δabc, P213], by simp [actB, δabc, P213]⟩ fun s'' _ => .empty (by decide)
      intro t' ht' h; simp [tn213] at ht' h

theorem P213_strongODSolvable : P213.StrongODSolvable := by
  refine (Problem.strongODSolvable_iff_fmSolvableDB).2 ⟨tn213, ⟨Relation.ReflTransGen.refl, ?_⟩, ?_⟩
  · intro t ht
    simp only [tn213, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> simp [TaskNetwork.IsPrimitiveId, tn213]
  · refine .step (t := 1) (a := .a) ⟨by decide, ?_⟩ rfl
      ⟨by simp [actA, δabc, P213], by simp [actA, δabc, P213]⟩ fun s' hs' => ?_
    · intro t' _ h; simp [tn213] at h
    · rcases outcomes_A hs' with rfl | rfl <;> exact solvable_after_a _ (by simp)

theorem P213_not_strongLDSolvable : ¬ P213.StrongLDSolvable := by
  rintro ⟨tn, l, ⟨hd, -⟩, hl, as, has, hex⟩
  obtain rfl := P213_decomposesTo hd
  have hirr : ∀ x, ¬ tn213.ord x x := by intro x h; simp [tn213] at h; omega
  match l, hl, has with
  | [], hl, _ => exact absurd (TaskNetwork.isLinearization_nil.1 hl) (by decide)
  | x :: l', hl, has =>
    obtain ⟨hux, hl'⟩ := TaskNetwork.of_isLinearization_cons hirr hl
    have hx1 : x = 1 := by
      have hxT := hux.1
      simp only [tn213, Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with h | h | h
      · exact h
      · exact absurd (by simp [tn213, h]) (hux.2 1 (by decide))
      · exact absurd (by simp [tn213, h]) (hux.2 1 (by decide))
    subst hx1
    obtain ⟨a₁, as', rfl, hα₁, has'⟩ := TaskNetwork.isActionSeq_cons.1 has
    match l', hl', has' with
    | [], hl', _ => exact absurd (TaskNetwork.isLinearization_nil.1 hl') (by decide)
    | y :: l'', hl', has' =>
      obtain ⟨huy, -⟩ := TaskNetwork.of_isLinearization_cons
        (TaskNetwork.irrefl_progress hirr 1) hl'
      obtain ⟨a₂, as'', rfl, hα₂, -⟩ := TaskNetwork.isActionSeq_cons.1 has'
      have ha₁ : a₁ = .a := by simpa [tn213] using hα₁.symm
      subst ha₁
      obtain ⟨-, happ, -⟩ := hex
      have hyT := huy.1
      simp only [HTN.TaskNetwork.progress_T, tn213, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton] at hyT
      rcases hyT with ⟨hne, h | h | h⟩
      · exact absurd h hne
      · subst h
        have ha₂ : a₂ = .b := by simpa [tn213] using hα₂.symm
        subst ha₂
        have := (happ {2} ⟨∅, rfl, ({2}, ∅), by simp [P213, δabc, actA], by
          simp [Action.applyEff]⟩).1
        simp [P213, δabc, actB] at this
      · subst h
        have ha₂ : a₂ = .c := by simpa [tn213] using hα₂.symm
        subst ha₂
        have := (happ {1} ⟨∅, rfl, ({1}, ∅), by simp [P213, δabc, actA], by
          simp [Action.applyEff]⟩).1
        simp [P213, δabc, actC] at this

/-- **[CB21, Prop. 2.13], second half.** Strong OD solvability does not imply strong LD
solvability. -/
theorem prop_2_13_converse_fails : P213.StrongODSolvable ∧ ¬ P213.StrongLDSolvable :=
  ⟨P213_strongODSolvable, P213_not_strongLDSolvable⟩


/-! ## [CB22, Fig. 1] -/

namespace Fig1

open FOND.Examples

/-- The one-task network `⟨{0}, ∅, 0 ↦ d⟩`. -/
def single (d : Act) : TaskNetwork ℕ Act Unit := ⟨{0}, fun _ _ => False, fun _ => .inl d⟩

/-- `m₁ : C → b`. -/
def m1 : Method ℕ Act Unit := ⟨(), single .b⟩

/-- `m₂ : C → c`. -/
def m2 : Method ℕ Act Unit := ⟨(), single .c⟩

/-- `tn_I = ⟨a, C⟩`, totally ordered. -/
def tnI : TaskNetwork ℕ Act Unit where
  T := {1, 2}
  ord := fun x y => x = 1 ∧ y = 2
  α := fun x => if x = 1 then .inl .a else .inr ()

/-- The problem of [CB22, Fig. 1]: `a` leads to `{1}` or `{2}`, only `b` is executable in `{1}`
and only `c` in `{2}`; the compound task `C` can be refined into `b` or `c`. -/
def P : Problem ℕ Act Unit ℕ where
  δ := δabc
  methods := {m1, m2}
  init := ∅
  tnI := tnI

lemma single_wf (d : Act) : (single d).WF :=
  ⟨fun h => h.elim, fun h => h.elim, fun _ h => h, fun h _ => h.elim⟩

lemma tnI_wf : tnI.WF where
  mem_left := by intro a b h; simp [tnI] at h ⊢; omega
  mem_right := by intro a b h; simp [tnI] at h ⊢; omega
  irrefl := by intro a h; simp [tnI] at h; omega
  trans := by intro a b c h₁ h₂; simp [tnI] at h₁ h₂; omega

lemma δabc_wf : ∀ d, (δabc d).WF
  | .a => ⟨⟨({1}, ∅), Or.inl rfl⟩, (Set.finite_singleton _).insert _⟩
  | .b => ⟨⟨({2}, ∅), rfl⟩, Set.finite_singleton _⟩
  | .c => ⟨⟨({1}, ∅), rfl⟩, Set.finite_singleton _⟩

lemma P_wf : P.WF where
  tnI := tnI_wf
  methods := by
    rintro m (rfl | rfl) <;> exact single_wf _
  actions := δabc_wf

/-! ### A strong method-based solution exists -/

/-- The fresh copy `⟨{3}, ∅, 3 ↦ d⟩` of `single d`. -/
def copy (d : Act) : TaskNetwork ℕ Act Unit := ⟨{3}, fun _ _ => False, fun _ => .inl d⟩

lemma decomp_after_a (d : Act) (m : Method ℕ Act Unit) (hm : m ∈ P.methods)
    (hmd : m.subtasks = single d) :
    DecompStep P.methods (tnI.progress 1) 2 m (decomposeWith (tnI.progress 1) 2 (copy d)) := by
  refine ⟨hm, by decide, by simp [tnI], copy d,
    ⟨fun h => h.elim, fun h => h.elim, fun _ h => h, fun h _ => h.elim⟩, ?_,
    Finset.disjoint_singleton_right.2 (by simp [tnI]), rfl⟩
  rw [hmd]
  refine ⟨fun _ => 0, ⟨fun x hx => by simp [single], fun x hx y hy _ => ?_, fun y hy => ?_⟩,
    by simp [copy, single], by simp [copy, single]⟩
  · simp [copy] at hx hy; rw [hx, hy]
  · simp [single] at hy; exact ⟨3, by simp [copy], hy.symm⟩

lemma andOr_after_decomp (d : Act) (s : Set ℕ) (happ : (δabc d).Applicable s) :
    P.MPAndOr (decomposeWith (tnI.progress 1) 2 (copy d)) s := by
  refine .prim (t := 3) (a := d) ⟨by simp [decomposeWith, copy], ?_⟩ (by simp [copy]) happ
    fun s' _ => .empty ?_
  · intro t' _ h
    simp [decomposeWith, copy, tnI] at h
  · ext y; simp [decomposeWith, copy, tnI]

theorem P_mpStrongSolvable : P.MPStrongSolvable := by
  refine (Problem.mpStrongSolvable_iff_mpAndOr P_wf).2 ?_
  refine .prim (t := 1) (a := .a) ⟨by decide, ?_⟩ rfl
    ⟨by simp [P, δabc, actA], by simp [P, δabc, actA]⟩ fun s' hs' => ?_
  · intro t' _ h; simp [P, tnI] at h
  · rcases outcomes_A hs' with rfl | rfl
    · exact .decomp (decomp_after_a .b m1 (by simp [P]) rfl)
        (andOr_after_decomp .b _ ⟨by simp [δabc, actB], by simp [δabc, actB]⟩)
    · exact .decomp (decomp_after_a .c m2 (by simp [P]) rfl)
        (andOr_after_decomp .c _ ⟨by simp [δabc, actC], by simp [δabc, actC]⟩)

/-! ### No strong fixed-method solution exists -/

/-- The task networks reachable from `tn_I`: `tn_I` itself, or `a ≺ d` for `d ∈ {b, c}`. -/
def Inv (tn : TaskNetwork ℕ Act Unit) : Prop :=
  tn = tnI ∨ ∃ x d, x ≠ 1 ∧ tn.T = {1, x} ∧ tn.ord 1 x ∧ tn.α 1 = .inl .a ∧
    tn.α x = .inl d ∧ (d = .b ∨ d = .c)

lemma inv_of_decomposesTo {tn : TaskNetwork ℕ Act Unit} (h : P.DecomposesTo tnI tn) : Inv tn := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
    obtain ⟨t, m, hm, htT, hαt, tn', hw', hiso, hdisj, rfl⟩ := hstep
    rcases ih with rfl | ⟨x, d, -, hT, -, hα1, hαx, -⟩
    · have ht2 : t = 2 := by
        simp [tnI] at htT hαt; omega
      subst ht2
      have hd : ∃ d, m.subtasks = single d ∧ (d = .b ∨ d = .c) := by
        rcases hm with rfl | rfl
        · exact ⟨.b, rfl, Or.inl rfl⟩
        · exact ⟨.c, rfl, Or.inr rfl⟩
      obtain ⟨d, hmd, hdbc⟩ := hd
      rw [hmd] at hiso
      obtain ⟨y, hy⟩ := Finset.card_eq_one.1 (hiso.card_eq.trans (by simp [single]))
      obtain ⟨σ, -, -, hα⟩ := hiso
      have hy1 : y ≠ 1 := by
        rintro rfl
        exact Finset.disjoint_left.1 hdisj (show (1 : ℕ) ∈ tnI.T by simp [tnI]) (by simp [hy])
      have hy2 : y ≠ 2 := by
        rintro rfl
        exact Finset.disjoint_left.1 hdisj (show (2 : ℕ) ∈ tnI.T by simp [tnI]) (by simp [hy])
      have hyu : y ∈ tn'.T := by simp [hy]
      have h1u : (1 : ℕ) ∉ tn'.T := by simp [hy]; omega
      refine Or.inr ⟨y, d, hy1, ?_, ?_, ?_, ?_, hdbc⟩
      · ext z; simp only [decomposeWith, hy, tnI]; simp; omega
      · exact Or.inr (Or.inl ⟨⟨rfl, rfl⟩, hyu⟩)
      · simp [decomposeWith, h1u, tnI]
      · simp only [HTN.decomposeWith_α, if_pos hyu, hα y hyu]; rfl
    · exfalso
      rw [hT] at htT
      simp only [Finset.mem_insert, Finset.mem_singleton] at htT
      rcases htT with rfl | rfl
      · rw [hα1] at hαt; cases hαt
      · rw [hαx] at hαt; cases hαt

theorem P_not_fmSolvable : ¬ P.StrongODSolvable := by
  rw [Problem.strongODSolvable_iff_fmSolvableDB]
  rintro ⟨tn, ⟨hd, hprim⟩, hbs⟩
  rcases inv_of_decomposesTo hd with rfl | ⟨x, d, hx1, hT, hord, hα1, hαx, hdbc⟩
  · obtain ⟨_, ha⟩ := hprim 2 (by decide)
    simp [tnI] at ha
  · cases hbs with
    | empty h => rw [hT] at h; simp at h
    | @step _ _ t a₀ hu hα happ hall =>
      have ht1 : t = 1 := by
        have := hu.1
        rw [hT] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | rfl
        · exact h
        · exact absurd hord (hu.2 1 (by rw [hT]; simp))
      subst ht1
      obtain rfl : a₀ = .a := Sum.inl_injective (hα.symm.trans hα1)
      -- the outcome in which `d` is not executable
      obtain ⟨s', hs', hbad⟩ : ∃ s' ∈ (P.δ .a).outcomes ∅, ¬ (P.δ d).Applicable s' := by
        rcases hdbc with rfl | rfl
        · exact ⟨{2}, ⟨({2}, ∅), by simp [P, δabc, actA], by simp [Action.applyEff]⟩,
            by simp [P, δabc, actB, Action.Applicable]⟩
        · exact ⟨{1}, ⟨({1}, ∅), by simp [P, δabc, actA], by simp [Action.applyEff]⟩,
            by simp [P, δabc, actC, Action.Applicable]⟩
      have hrest := hall s' hs'
      have hT' : (tn.progress 1).T = {x} := by
        rw [HTN.TaskNetwork.progress_T, hT]; ext z; simp; omega
      cases hrest with
      | empty h => rw [hT'] at h; simp at h
      | @step _ _ t' a' hu' hα' happ' _ =>
        have : t' = x := by have h := hu'.1; rw [hT'] at h; simpa using h
        subst this
        obtain rfl : a' = d := Sum.inl_injective (hα'.symm.trans hαx)
        exact hbad happ'

/-- **[CB22, Fig. 1].** Method-based policies solve problems that fixed methods cannot. -/
theorem fig1 : P.MPStrongSolvable ∧ ¬ P.StrongODSolvable :=
  ⟨P_mpStrongSolvable, P_not_fmSolvable⟩

end Fig1

end Examples

end FOND
