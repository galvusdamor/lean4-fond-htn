import HtnPlanning.Core.Classical
import HtnPlanning.Core.TaskNetwork
/-!
# Inserting guard actions into a plan

The re-split tool of `HtnComplexity/Guard/Resplit.lean` guards *actions*.  Guarding a
**method** — "this method may only be applied when the instance says so" — is not directly
expressible in the HTN formalism, and the standard way of simulating it is to put an extra
primitive subtask at the head of the method's body whose action is a *guard action*: it has no
effects and its precondition is the fact the instance is asked to carry.

This file is the plan-level half of that construction.  A plan of the guarded domain is a plan
of the original one with guard actions inserted (`HTN.GuardTask.Ins`), and the two behave
identically as long as the guard facts hold in the initial state and no action ever deletes one:

* `HTN.GuardTask.transitionSeq_eq` — the inserted actions do not change the state;
* `HTN.GuardTask.seqApplicable_iff` — the inserted actions are always applicable, so the two
  plans are executable together.

The last result of the file, `HTN.GuardTask.ins_of_actionSeq`, produces the relation `Ins` from
the id level: if the guarded network's linearization restricts to the original one, its action
sequence is the original one with guard actions inserted.
-/

namespace HTN

namespace GuardTask

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-! ### Plans with inserted guard actions -/

/-- `Ins P as bs`: the list `bs` is the list `as` with extra actions satisfying `P` — the guard
actions — inserted at arbitrary places. -/
inductive Ins (P : A → Prop) : List A → List A → Prop
  /-- The empty plan. -/
  | nil : Ins P [] []
  /-- A common action of the two plans. -/
  | keep {as bs : List A} (a : A) : Ins P as bs → Ins P (a :: as) (a :: bs)
  /-- An inserted guard action. -/
  | extra {as bs : List A} (b : A) : P b → Ins P as bs → Ins P as (b :: bs)

variable {P : A → Prop}

/-- The original plan is a sublist of the one with the guard actions. -/
theorem Ins.sublist {as bs : List A} (h : Ins P as bs) : as.Sublist bs := by
  induction h with
  | nil => exact List.Sublist.refl _
  | keep a _ ih => exact ih.cons₂ a
  | extra b _ _ ih => exact ih.cons b

/-- Every action of the longer plan is an action of the shorter one or a guard action. -/
theorem Ins.mem_or {as bs : List A} (h : Ins P as bs) {a : A} (ha : a ∈ bs) : a ∈ as ∨ P a := by
  induction h with
  | nil => simp at ha
  | keep b _ ih =>
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact Or.inl (by simp)
      · rcases ih ha' with h' | h'
        · exact Or.inl (by simp [h'])
        · exact Or.inr h'
  | extra b hb _ ih =>
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact Or.inr hb
      · exact ih ha'

/-! ### The inserted actions do not change the state -/

variable (δ : ActionModel F A)

/-- A guard action — no additions, no deletions — leaves the state untouched. -/
theorem transition_eq_self {a : A} (hadd : δ.add a = ∅) (hdel : δ.del a = ∅) (s : Set F) :
    δ.transition a s = s := by
  simp [ActionModel.transition, hadd, hdel]

/-- **Inserting guard actions does not change the state a plan reaches.** -/
theorem transitionSeq_eq (hP : ∀ a, P a → δ.add a = ∅ ∧ δ.del a = ∅) {as bs : List A}
    (h : Ins P as bs) (s : Set F) : δ.transitionSeq bs s = δ.transitionSeq as s := by
  induction h generalizing s with
  | nil => rfl
  | keep a _ ih => simpa using ih (δ.transition a s)
  | extra b hb _ ih =>
      obtain ⟨hadd, hdel⟩ := hP b hb
      rw [ActionModel.transitionSeq_cons, transition_eq_self δ hadd hdel s]
      exact ih s

/-- A set of facts that no action deletes is contained in every state a plan reaches. -/
theorem subset_transitionSeq {G : Set F} (hdel : ∀ a, ∀ f ∈ G, f ∉ δ.del a) :
    ∀ (as : List A) {s : Set F}, G ⊆ s → G ⊆ δ.transitionSeq as s := by
  intro as
  induction as with
  | nil => exact fun hs => hs
  | cons a as ih =>
      intro s hs
      refine ih (s := δ.transition a s) ?_
      intro f hf
      exact Or.inl ⟨hs hf, hdel a f hf⟩

/-- **Inserting guard actions does not change executability**, provided the guard facts are
present in the state and no action deletes one. -/
theorem seqApplicable_iff {G : Set F}
    (hP : ∀ a, P a → δ.prec a ⊆ G ∧ δ.add a = ∅ ∧ δ.del a = ∅)
    (hdel : ∀ a, ∀ f ∈ G, f ∉ δ.del a) {as bs : List A} (h : Ins P as bs) {s : Set F}
    (hG : G ⊆ s) : δ.SeqApplicable bs s ↔ δ.SeqApplicable as s := by
  induction h generalizing s with
  | nil => exact Iff.rfl
  | keep a _ ih =>
      have hG' : G ⊆ δ.transition a s := by
        intro f hf
        exact Or.inl ⟨hG hf, hdel a f hf⟩
      simp only [ActionModel.SeqApplicable]
      exact and_congr_right fun _ => ih hG'
  | extra b hb _ ih =>
      obtain ⟨hprec, hadd, hdelb⟩ := hP b hb
      have happ : δ.Applicable b s := hprec.trans hG
      simp only [ActionModel.SeqApplicable, transition_eq_self δ hadd hdelb s]
      exact ⟨fun h' => (ih hG).1 h'.2, fun h' => ⟨happ, (ih hG).2 h'⟩⟩

/-! ### From the id level to the plan level -/

variable {δ}

/-- **The action sequence of a linearization that restricts to a given one is the original
action sequence with guard actions inserted.**  `lg` is a linearization of the guarded network,
`lg.filter p` the ids of the original one, and every id outside the filter carries a guard
action. -/
theorem ins_of_actionSeq {tn : TaskNetwork I A C} {p : I → Bool} :
    ∀ {lg : List I} {as asg : List A}, tn.IsActionSeq lg asg →
      tn.IsActionSeq (lg.filter p) as →
      (∀ x ∈ lg, p x = false → ∀ a, tn.α x = Sum.inl a → P a) → Ins P as asg := by
  intro lg
  induction lg with
  | nil =>
      intro as asg hg hl _
      have hasg : asg = [] := by
        have h0 : ([] : List (A ⊕ C)) = asg.map Sum.inl := hg
        exact List.map_eq_nil_iff.1 h0.symm
      have has : as = [] := by
        have h0 : ([] : List (A ⊕ C)) = as.map Sum.inl := hl
        exact List.map_eq_nil_iff.1 h0.symm
      subst hasg; subst has; exact Ins.nil
  | cons x lg ih =>
      intro as asg hg hl hchk
      -- the head of `asg`
      have hgmap : tn.α x :: lg.map tn.α = asg.map Sum.inl := by
        simpa [TaskNetwork.IsActionSeq] using hg
      cases asg with
      | nil => simp at hgmap
      | cons a asg' =>
          simp only [List.map_cons, List.cons.injEq] at hgmap
          obtain ⟨hax, hrest⟩ := hgmap
          have hαx : tn.α x = Sum.inl a := hax
          by_cases hpx : p x
          · -- the id is kept
            have hfil : (x :: lg).filter p = x :: lg.filter p := by
              simp [hpx]
            rw [hfil] at hl
            have hlmap : tn.α x :: (lg.filter p).map tn.α = as.map Sum.inl := by
              simpa [TaskNetwork.IsActionSeq] using hl
            cases as with
            | nil => simp at hlmap
            | cons b as' =>
                simp only [List.map_cons, List.cons.injEq] at hlmap
                obtain ⟨hbx, hrest'⟩ := hlmap
                have hab : a = b := by
                  have : (Sum.inl a : A ⊕ C) = Sum.inl b := by rw [← hαx, hbx]
                  exact Sum.inl_injective this
                subst hab
                exact Ins.keep a (ih (as := as') (asg := asg') hrest hrest'
                  (fun y hy hpy c hc => hchk y (by simp [hy]) hpy c hc))
          · -- the id carries a guard action
            have hpx' : p x = false := by simpa using hpx
            have hfil : (x :: lg).filter p = lg.filter p := by
              simp [hpx']
            rw [hfil] at hl
            exact Ins.extra a (hchk x (by simp) hpx' a hαx)
              (ih (as := as) (asg := asg') hrest hl
                (fun y hy hpy c hc => hchk y (by simp [hy]) hpy c hc))

end GuardTask

end HTN
