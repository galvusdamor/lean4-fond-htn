import FondHtn.Transfer.AppendLast
import FondHtn.MethodPoliciesStrong
import FondHtn.FixedMethodsRelations
/-!
# Deterministic FOND problems

For a FOND problem in which every action has exactly one effect, the criteria collapse:

* `FOND.Problem.det_fm_iff` — all four fixed-method criteria of [CB21] are equivalent to weak LD
  solvability;
* `FOND.Problem.det_mpStrong_iff`, `det_mpWeak_iff` — so are weak and strong solvability with
  method-based policies [CB22].  (Strong *cyclic* solvability does not collapse: under the
  literal Def. 7 a policy may decompose a recursive task forever; see the report.)

The method-based direction needs that decompositions done *after* executing a primitive task can
be done before it (`HTN.decomposesTo_progress_lift`).
-/

namespace HTN

universe v w x

variable {I : Type x} {A : Type v} {C : Type w} [DecidableEq I]

open TaskNetwork

namespace TaskNetwork

lemma progress_decomposeWith {X u : TaskNetwork I A C} {t t' : I} (hu : u.WF) (htt' : t ≠ t')
    (htu : t ∉ u.T) :
    (decomposeWith X t' u).progress t = decomposeWith (X.progress t) t' u := by
  refine ext' ?_ ?_ ?_
  · ext y
    simp only [progress_T, decomposeWith, Finset.mem_erase, Finset.mem_union]
    constructor
    · rintro ⟨hyt, ⟨hyt', hy⟩ | hy⟩
      · exact Or.inl ⟨hyt', hyt, hy⟩
      · exact Or.inr hy
    · rintro (⟨hyt', hyt, hy⟩ | hy)
      · exact ⟨hyt, Or.inl ⟨hyt', hy⟩⟩
      · exact ⟨fun e => htu (e ▸ hy), Or.inr hy⟩
  · funext a b
    apply propext
    simp only [progress, decomposeWith]
    have hau : ∀ {a}, a ∈ u.T → a ≠ t := fun h e => htu (e ▸ h)
    constructor
    · rintro ⟨h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, ha, hb⟩, hat⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨⟨h, hat⟩, hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨h, Ne.symm htt'⟩, ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨⟨h, hat⟩, ha, hb⟩))
    · rintro (h | ⟨⟨h, hat⟩, hb⟩ | ⟨⟨h, -⟩, ha⟩ | ⟨⟨h, hat⟩, ha, hb⟩)
      · exact ⟨Or.inl h, hau (hu.mem_left h)⟩
      · exact ⟨Or.inr (Or.inl ⟨h, hb⟩), hat⟩
      · exact ⟨Or.inr (Or.inr (Or.inl ⟨h, ha⟩)), hau ha⟩
      · exact ⟨Or.inr (Or.inr (Or.inr ⟨h, ha, hb⟩)), hat⟩
  · rfl

end TaskNetwork

/-- Decompositions after executing an unconstrained task `t` (avoiding `t`) can be done before
executing it. -/
theorem decomposesTo_progress_lift {M : Set (Method I A C)} {X Y₂ : TaskNetwork I A C} {t : I}
    (hX : X.WF) (hu : X.Unconstrained t)
    (h : Relation.ReflTransGen (StepAvoid M {t}) (X.progress t) Y₂) :
    ∃ X₂, DecomposesTo M X X₂ ∧ X₂.progress t = Y₂ ∧ X₂.Unconstrained t ∧ X₂.α t = X.α t ∧
      X₂.WF := by
  induction h with
  | refl => exact ⟨X, Relation.ReflTransGen.refl, rfl, hu, rfl, hX⟩
  | @tail b c _ hbc ih =>
    obtain ⟨Xb, hXb, rfl, hub, hαb, hwb⟩ := ih
    obtain ⟨⟨t', m, hm, ht'T, hαt', u, hu', huiso, hdisj, rfl⟩, hic⟩ := hbc
    have htc : t ∉ (decomposeWith (Xb.progress t) t' u).T :=
      Finset.disjoint_singleton_left.1 hic
    have htu : t ∉ u.T := fun h => htc (mem_decomposeWith_T.2 (Or.inr h))
    have ht'b : t' ∈ Xb.T := (mem_progress_T.1 ht'T).2
    have htt' : t ≠ t' := fun e => (mem_progress_T.1 ht'T).1 e.symm
    have hdisj' : Disjoint Xb.T u.T := by
      rw [Finset.disjoint_left]
      intro y hy hyu
      by_cases hyt : y = t
      · exact htu (hyt ▸ hyu)
      · exact Finset.disjoint_left.1 hdisj (mem_progress_T.2 ⟨hyt, hy⟩) hyu
    refine ⟨decomposeWith Xb t' u, hXb.tail ⟨t', m, hm, ht'b, hαt', u, hu', huiso, hdisj', rfl⟩,
      progress_decomposeWith hu' htt' htu, ⟨?_, ?_⟩, ?_, decomposeWith_wf hwb hu' hdisj'⟩
    · exact mem_decomposeWith_T.2 (Or.inl ⟨hub.1, htt'⟩)
    · intro y hy hord
      rcases hord with h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, hy', -⟩
      · exact htu (hu'.mem_right h)
      · exact htu h
      · exact hub.2 t' ht'b h
      · rcases mem_decomposeWith_T.1 hy with ⟨hyb, -⟩ | hyu
        · exact hub.2 y hyb h
        · exact Finset.disjoint_left.1 hdisj' (hwb.mem_left h) hyu
    · simp only [decomposeWith, if_neg htu]; exact hαb

end HTN

namespace FOND

open HTN HTN.TaskNetwork

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable {P : Problem F A C I}

lemma IsDeterministic.outcomes {hdet : P.IsDeterministic} (a : A) (s : Set F) :
    ∃ s', (P.δ a).outcomes s = {s'} := by
  obtain ⟨e, he⟩ := hdet a
  exact ⟨Action.applyEff e s, by ext; simp [Action.outcomes, he]⟩

lemma strongExec_iff_weakExec (hdet : P.IsDeterministic) :
    ∀ (as : List A) (s : Set F), P.StrongExec as {s} ↔ P.WeakExec as s := by
  intro as
  induction as with
  | nil => simp [StrongExec, WeakExec]
  | cons a as ih =>
    intro s
    obtain ⟨s', hs'⟩ := IsDeterministic.outcomes (hdet := hdet) a s
    have hset : {x | ∃ y ∈ ({s} : Set (Set F)), x ∈ (P.δ a).outcomes y} = {s'} := by
      ext x; simp [hs']
    have hc : P.StrongExec (a :: as) {s} ↔ (P.δ a).Applicable s ∧ P.StrongExec as {s'} := by
      show ((∀ x ∈ ({s} : Set (Set F)), (P.δ a).Applicable x) ∧
        P.StrongExec as {x | ∃ y ∈ ({s} : Set (Set F)), x ∈ (P.δ a).outcomes y}) ↔ _
      rw [hset]; simp only [Set.mem_singleton_iff, forall_eq]
    rw [hc, ih]; simp [WeakExec, hs']

variable [DecidableEq I]

lemma beliefSolvable_iff_weakBelief (hdet : P.IsDeterministic) {tn : TaskNetwork I A C}
    {s : Set F} : P.BeliefSolvable tn s ↔ P.WeakBelief tn s := by
  constructor
  · intro h
    induction h with
    | empty h => exact .empty h
    | @step tn s t a hu hα happ _ ih =>
      obtain ⟨s', hs'⟩ := IsDeterministic.outcomes (hdet := hdet) a s
      exact .step hu hα happ (by rw [hs']; exact Set.mem_singleton _) (ih s' (by rw [hs']; exact Set.mem_singleton _))
  · intro h
    induction h with
    | empty h => exact .empty h
    | @step tn s s' t a hu hα happ hs' _ ih =>
      obtain ⟨s'', hs''⟩ := IsDeterministic.outcomes (hdet := hdet) a s
      refine .step hu hα happ fun x hx => ?_
      rw [hs''] at hx hs'
      rw [hx, ← hs']; exact ih

/-- **All fixed-method criteria coincide on deterministic problems.** -/
theorem det_fm_iff (hdet : P.IsDeterministic) (hwf : P.tnI.WF) :
    (P.StrongLDSolvable ↔ P.WeakLDSolvable) ∧ (P.WeakODSolvable ↔ P.WeakLDSolvable) ∧
      (P.StrongODSolvable ↔ P.WeakLDSolvable) := by
  have hLD : P.StrongLDSolvable ↔ P.WeakLDSolvable := by
    constructor
    · rintro ⟨tn, l, hach, hl, as, has, hex⟩
      exact ⟨tn, l, hach, hl, as, has, (strongExec_iff_weakExec hdet as _).1 hex⟩
    · rintro ⟨tn, l, hach, hl, as, has, hex⟩
      exact ⟨tn, l, hach, hl, as, has, (strongExec_iff_weakExec hdet as _).2 hex⟩
  refine ⟨hLD, (weakLDSolvable_iff_weakODSolvable hwf).symm, ?_⟩
  rw [strongODSolvable_iff_fmSolvableDB]
  constructor
  · rintro ⟨tn, hach, hb⟩
    obtain ⟨l, as, hl, has, hex⟩ :=
      weakExec_of_weakBelief ((beliefSolvable_iff_weakBelief hdet).1 hb)
    exact ⟨tn, l, hach, hl, as, has, hex⟩
  · rintro ⟨tn, l, hach, hl, as, has, hex⟩
    exact ⟨tn, hach, (beliefSolvable_iff_weakBelief hdet).2
      (weakBelief_of_weakExec (hach.wf hwf).irrefl hl has hex)⟩

/-! ## Method-based policies on deterministic problems -/

lemma WeakBelief.isoVia {tn : TaskNetwork I A C} {s : Set F} (h : P.WeakBelief tn s) :
    ∀ {tn' : TaskNetwork I A C} {σ : I → I}, IsoVia σ tn tn' → P.WeakBelief tn' s := by
  induction h with
  | empty he => exact fun hσ => .empty (hσ.empty he)
  | step hu hα happ hs' _ ih =>
    intro tn' σ hσ
    exact .step (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ hs' (ih (hσ.progress hu.1))

lemma mpAndOr_of_beliefSolvable {tn : TaskNetwork I A C} {s : Set F}
    (h : P.BeliefSolvable tn s) : P.MPAndOr tn s := by
  induction h with
  | empty h => exact .empty h
  | step hu hα happ _ ih => exact .prim hu hα happ ih

lemma mpAndOr_of_decomposesTo {tn tn' : TaskNetwork I A C} {s : Set F}
    (hd : HTN.DecomposesTo P.methods tn tn') (h : P.MPAndOr tn' s) : P.MPAndOr tn s := by
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hstep _ ih =>
    obtain ⟨t, m, hs⟩ := hstep
    exact .decomp hs ih

/-- On deterministic problems the AND/OR game is decomposition followed by execution. -/
theorem det_of_mpAndOr [Infinite I] (hdet : P.IsDeterministic) {tn : TaskNetwork I A C}
    {s : Set F} (h : P.MPAndOr tn s) (hwf : tn.WF) :
    ∃ tn', HTN.DecomposesTo P.methods tn tn' ∧ tn'.IsPrimitive ∧ P.WeakBelief tn' s := by
  induction h with
  | empty he => exact ⟨_, Relation.ReflTransGen.refl, fun t ht => by simp [he] at ht, .empty he⟩
  | @prim tn s t a hu hα happ _ ih =>
    obtain ⟨s', hs'⟩ := IsDeterministic.outcomes (hdet := hdet) a s
    obtain ⟨Y₂, hY₂, hprim, hwb⟩ := ih s' (by rw [hs']; exact Set.mem_singleton _) (progress_wf hwf hu)
    obtain ⟨Y₂', σ, hav, hσ, -, -⟩ := decomposesTo_avoid hY₂ (progress_wf hwf hu) {t}
      (Finset.disjoint_singleton_left.2 (fun h => (mem_progress_T.1 h).1 rfl))
    obtain ⟨X₂, hX₂, hp, hu₂, hα₂, -⟩ := decomposesTo_progress_lift hwf hu hav
    refine ⟨X₂, hX₂, fun y hy => ?_, .step hu₂ (hα₂.trans hα) happ (by rw [hs']; exact Set.mem_singleton _) ?_⟩
    · by_cases hyt : y = t
      · subst hyt; exact ⟨a, hα₂.trans hα⟩
      · have hy' : y ∈ (X₂.progress t).T := mem_progress_T.2 ⟨hyt, hy⟩
        rw [hp] at hy'
        obtain ⟨y₀, hy₀, rfl⟩ := hσ.surj hy'
        obtain ⟨b, hb⟩ := hprim y₀ hy₀
        exact ⟨b, by rw [← progress_α X₂ t, hp, hσ.α_eq hy₀, hb]⟩
    · rw [hp]; exact hwb.isoVia hσ
  | decomp hd _ ih =>
    obtain ⟨tn', h1, h2, h3⟩ := ih (hd.wf hwf)
    exact ⟨tn', .head ⟨_, _, hd⟩ h1, h2, h3⟩

theorem det_mpAndOr_iff [Infinite I] (hdet : P.IsDeterministic) (hwf : P.tnI.WF) :
    P.MPAndOr P.tnI P.init ↔ P.WeakLDSolvable := by
  constructor
  · intro h
    obtain ⟨tn, hd, hprim, hwb⟩ := det_of_mpAndOr hdet h hwf
    obtain ⟨l, as, hl, has, hex⟩ := weakExec_of_weakBelief hwb
    exact ⟨tn, l, ⟨hd, hprim⟩, hl, as, has, hex⟩
  · rintro ⟨tn, l, hach, hl, as, has, hex⟩
    exact mpAndOr_of_decomposesTo hach.1 (mpAndOr_of_beliefSolvable
      ((beliefSolvable_iff_weakBelief hdet).2 (weakBelief_of_weakExec (hach.wf hwf).irrefl hl has
        hex)))

/-- **Strong method-based solvability of a deterministic problem.** -/
theorem det_mpStrong_iff [Infinite I] (hdet : P.IsDeterministic) (hP : P.WF) :
    P.MPStrongSolvable ↔ P.WeakLDSolvable :=
  (mpStrongSolvable_iff_mpAndOr hP).trans (det_mpAndOr_iff hdet hP.tnI)

/-- A strong solution has a reachable terminal node, hence is a weak solution. -/
theorem IsMPStrongSolution.isMPWeakSolution [Nonempty I] {π : MPPolicy F A C I}
    (h : P.IsMPStrongSolution π) : P.IsMPWeakSolution π := by
  classical
  obtain ⟨hwd, hfin, hacyc, hgoal⟩ := h
  have hex : ∃ n, ¬ P.MPPathFrom π P.mpInit n := exists_not_mpPathFrom hfin hacyc
  set k := Nat.find hex
  have hk0 : k ≠ 0 := by
    intro h0; apply Nat.find_spec hex; rw [show Nat.find hex = 0 from h0]; exact mpPathFrom_zero
  obtain ⟨f, hf0, hf⟩ : P.MPPathFrom π P.mpInit (k - 1) :=
    not_not.1 (Nat.find_min hex (by omega))
  have hreach : ∀ i ≤ k - 1, P.MPReach π (f i) := by
    intro i hi
    induction i with
    | zero => rw [hf0]; exact .refl
    | succ i ih => exact (ih (by omega)).tail (hf i (by omega))
  have hterm : P.MPTerminal π (f (k - 1)) := by
    intro y hy
    apply Nat.find_spec hex
    refine ⟨fun i => if i = k then y else f i, by beta_reduce; rw [if_neg (Ne.symm hk0)]; exact hf0,
      fun i hi => ?_⟩
    by_cases hik : i + 1 = k
    · have : i = k - 1 := by omega
      subst this
      simpa [hik, show k - 1 ≠ k by omega] using hy
    · simpa [hik, show i ≠ k by omega] using hf i (by omega)
  exact ⟨hwd, hfin, _, hreach _ le_rfl, hterm, hgoal _ (hreach _ le_rfl) hterm⟩

/-- On deterministic problems a weak solution yields a won AND/OR game. -/
theorem det_mpAndOr_of_weak (hdet : P.IsDeterministic) {π : MPPolicy F A C I}
    (h : P.IsMPWeakSolution π) : P.MPAndOr P.tnI P.init := by
  obtain ⟨-, -, x, hx, -, hgoal⟩ := h
  suffices key : ∀ y, Relation.ReflTransGen (P.MPStep π) y x → P.MPAndOr y.net y.state from
    key _ hx
  intro y hy
  induction hy using Relation.ReflTransGen.head_induction_on with
  | refl => exact .empty hgoal
  | head hstep _ ih =>
    cases hstep with
    | @prim t a s' _ hu hα happ hs' =>
      refine .prim hu hα happ fun s'' hs'' => ?_
      obtain ⟨z, hz⟩ := IsDeterministic.outcomes (hdet := hdet) a _
      rw [hz] at hs' hs''
      rw [hs'', ← hs']; exact ih
    | decomp _ hd => exact .decomp hd ih

/-- **Weak method-based solvability of a deterministic problem.** -/
theorem det_mpWeak_iff [Infinite I] (hdet : P.IsDeterministic) (hP : P.WF) :
    P.MPWeakSolvable ↔ P.WeakLDSolvable := by
  constructor
  · rintro ⟨π, hπ⟩
    exact (det_mpAndOr_iff hdet hP.tnI).1 (det_mpAndOr_of_weak hdet hπ)
  · intro h
    obtain ⟨π, hπ⟩ := (det_mpStrong_iff hdet hP).2 h
    exact ⟨π, hπ.isMPWeakSolution⟩

end Problem

end FOND
