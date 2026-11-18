import HtnComplexity.Regular.RegularWeak
/-!
# A normal form for regular HTN problems

This file lifts the weak-chain analysis of `HtnComplexity/Regular/RegularWeak.lean` to whole
problems, dropping the assumption — made in `HtnPlanning/Regular/RegularNormalForm.lean` — that
the methods are totally ordered.

* `Method.HasBlock m os next` — the method `m` decomposes its compound task into a *block* of
  primitive tasks, one of whose linearizations is the action sequence `os`, followed by the
  optional compound task `next`.  Unlike `Method.HasBody`, a method has in general **many**
  blocks: one per linearization of its primitive part.
* `Problem.DerivesW c as` — `as` is obtained from the compound task `c` by a chain of methods,
  each continuing the compound task left open by the previous one, choosing one block of each.
* `Problem.solvable_iff_derivesW` — **the normal form theorem**: a well-formed regular problem
  whose initial task network is a single compound task `c₀` is solvable exactly when some
  derivation of `c₀` is executable in the initial state and reaches the goal.

This is the source-side ingredient of the compilation of `HTN-REG` into a totally ordered
class.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Method

variable [DecidableEq I]

/-- **The blocks of a method.**  `m.HasBlock os next` states that the subtask network of `m`
is a weak chain whose primitive part has the linearization `os` and whose trailing compound
task is `next`. -/
def HasBlock (m : Method I A C) (os : List A) (next : Option C) : Prop :=
  ∃ tail : Option (I × C), m.subtasks.IsWeakChain tail ∧ m.subtasks.Yields tail os ∧
    tail.map Prod.snd = next

omit [DecidableEq I] in
/-- Every well-formed regular method has a block. -/
lemma exists_hasBlock {m : Method I A C} (hwf : m.subtasks.WF) (hreg : m.subtasks.IsRegular) :
    ∃ (os : List A) (next : Option C), m.HasBlock os next := by
  obtain ⟨tail, hchain⟩ := TaskNetwork.IsWeakChain.of_regular hwf hreg
  obtain ⟨os, hos⟩ := hchain.exists_yields
  exact ⟨os, tail.map Prod.snd, tail, hchain, hos, rfl⟩

omit [DecidableEq I] in
/-- The compound task left open by a method is determined by the method. -/
lemma HasBlock.next_unique {m : Method I A C} {os os' : List A} {next next' : Option C}
    (h : m.HasBlock os next) (h' : m.HasBlock os' next') : next = next' := by
  obtain ⟨tail, hchain, -, rfl⟩ := h
  obtain ⟨tail', -, hy', rfl⟩ := h'
  rw [hchain.tail_eq_of_yields hy']

end Method

namespace Problem

variable [DecidableEq I]

/-- **Derivations of a regular problem.**  `P.DerivesW c as` states that the compound task `c`
can be decomposed — by a chain of methods, each continuing the compound task left over by the
previous one — into the primitive action sequence `as`, choosing one linearization of the
primitive part of each method. -/
inductive DerivesW (P : Problem F A C I) : C → List A → Prop
  /-- The last method of the derivation leaves no compound task. -/
  | last {c : C} {os : List A} {m : Method I A C} (hm : m ∈ P.methods)
      (hc : m.abstractTask = c) (hb : m.HasBlock os none) : P.DerivesW c os
  /-- A method leaving the compound task `c'`, which is derived in turn. -/
  | cons {c c' : C} {os rest : List A} {m : Method I A C} (hm : m ∈ P.methods)
      (hc : m.abstractTask = c) (hb : m.HasBlock os (some c')) (h : P.DerivesW c' rest) :
      P.DerivesW c (os ++ rest)

/-- The continuation invariant of the normal form proof: the actions `os` produced so far,
together with a derivation of the compound task still open (if any), yield a derivation of the
initial compound task. -/
def ContDerivesW (P : Problem F A C I) (c₀ : C) (os : List A) (tail : Option (I × C)) : Prop :=
  match tail with
  | none => P.DerivesW c₀ os
  | some p => ∀ rest, P.DerivesW p.2 rest → P.DerivesW c₀ (os ++ rest)

end Problem

namespace Problem

section NormalForm

variable [DecidableEq I] {P : Problem F A C I}

open TaskNetwork

omit [DecidableEq I] in
/-- A problem whose initial task network is the single compound task `c₀` starts from the
one-element weak chain. -/
lemma isWeakChain_tnI (hwf : P.tnI.WF) {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀})
    (hα : P.tnI.α t₀ = Sum.inr c₀) : P.tnI.IsWeakChain (some (t₀, c₀)) := by
  have hmem : ∀ x, x ∈ P.tnI.T ↔ x = t₀ := by
    intro x; rw [hT]; simp
  refine ⟨hwf, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨rfl⟩; exact (hmem t₀).2 rfl
  · rintro p ⟨rfl⟩; exact hα
  · rintro p ⟨rfl⟩ x hx hxt
    exact absurd ((hmem x).1 hx) hxt
  · intro x hx hxp
    exact absurd ((hmem x).1 hx) (hxp (t₀, c₀) rfl)

omit [DecidableEq I] in
/-- The initial task network of a rooted problem yields the empty action sequence, and nothing
else. -/
lemma yields_tnI {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀})
    (hα : P.tnI.α t₀ = Sum.inr c₀) : P.tnI.Yields (some (t₀, c₀)) [] := by
  refine ⟨[], ⟨by simp, ?_, by simp⟩, rfl, ?_⟩
  · intro x
    rw [hT]
    simp
  · rintro p ⟨rfl⟩
    exact hα

omit [DecidableEq I] in
lemma eq_nil_of_yields_tnI {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀}) {as : List A}
    (h : P.tnI.Yields (some (t₀, c₀)) as) : as = [] := by
  obtain ⟨l, hlin, hseq, -⟩ := h
  have hl : l = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have hxT : x ∈ P.tnI.T := (hlin.2.1 x).1 (by simp [hx])
    rw [hT] at hxT
    simp only [Finset.mem_singleton] at hxT
    subst hxT
    have hnd := hlin.1
    rw [chainIds_some, List.nodup_append] at hnd
    exact hnd.2.2 x hx x (by simp) rfl
  subst hl
  have : as.map (Sum.inl (β := C)) = [] := hseq.symm
  simpa using this

/-- In a weak chain, the only task that can be decomposed is the trailing compound task. -/
lemma decompStep_tail_eq_weak {tn₁ tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    {tail : Option (I × C)} (hchain : tn₁.IsWeakChain tail)
    (hstep : DecompStep P.methods tn₁ t m tn₂) : tail = some (t, m.abstractTask) := by
  obtain ⟨-, htT, hαt, -⟩ := hstep
  have hnp : ¬ tn₁.IsPrimitiveId t := by
    rintro ⟨a, ha⟩
    rw [ha] at hαt
    exact absurd hαt (by simp)
  by_contra hcon
  refine hnp (hchain.prim t htT ?_)
  rintro p hp hct
  subst hct
  have := hchain.tailLabel p hp
  rw [hαt] at this
  simp only [Sum.inr.injEq] at this
  exact hcon (by rw [hp, this])

/-- **Every reachable task network of a regular problem is a weak chain**, and every action
sequence it yields, together with the open compound task, derives the initial task. -/
theorem exists_weakChain_contDerivesW (hwf : P.WF) (hreg : P.IsRegularM)
    {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀)
    {tn : TaskNetwork I A C} (hreach : P.Reachable tn) :
    ∃ tail : Option (I × C), tn.IsWeakChain tail ∧
      ∀ as : List A, tn.Yields tail as → P.ContDerivesW c₀ as tail := by
  induction hreach with
  | refl =>
      refine ⟨some (t₀, c₀), isWeakChain_tnI hwf.tnI hT hα, ?_⟩
      intro as has
      have : as = [] := eq_nil_of_yields_tnI hT has
      subst this
      intro rest hrest
      simpa using hrest
  | @tail tn₁ tn₂ hprefix hstep ih =>
      obtain ⟨tail₁, hchain₁, hcont⟩ := ih
      obtain ⟨t, m, hs⟩ := hstep
      have hmr : P.ReachableMethod m := Problem.reachableMethod_of_decomposesTo hprefix hs
      have htail₁ : tail₁ = some (t, m.abstractTask) := decompStep_tail_eq_weak hchain₁ hs
      subst htail₁
      obtain ⟨hm, htT, hαt, tn', hwf', hiso', hdisj, rfl⟩ := hs
      haveI : Nonempty I := ⟨t⟩
      obtain ⟨tailm, hchainm⟩ :=
        TaskNetwork.IsWeakChain.of_regular (hwf.methods m hmr.1) (hreg m hmr)
      -- transport the weak chain structure to the fresh copy
      obtain ⟨σ, hbij, hordσ, hασ⟩ := hiso'.symm
      have hchain' : tn'.IsWeakChain (tailm.map (fun p => (σ p.1, p.2))) :=
        TaskNetwork.IsWeakChain.map hbij hordσ hασ hwf' hchainm
      refine ⟨tailm.map (fun p => (σ p.1, p.2)),
        TaskNetwork.IsWeakChain.decompose hchain₁ hchain' hdisj, ?_⟩
      intro as₂ has₂
      obtain ⟨as, os, rfl, hasy, hosy⟩ :=
        TaskNetwork.Yields.split hchain₁ hchain' hdisj has₂
      -- the block of `m` used by the step
      obtain ⟨τ, hbijτ, hordτ, hατ⟩ := hiso'
      have hblock : m.HasBlock os
          ((tailm.map (fun p => (σ p.1, p.2))).map Prod.snd) := by
        refine ⟨(tailm.map (fun p => (σ p.1, p.2))).map (fun p => (τ p.1, p.2)),
          TaskNetwork.IsWeakChain.map hbijτ hordτ hατ (hwf.methods m hmr.1) hchain',
          TaskNetwork.Yields.map hbijτ hordτ hατ hosy, ?_⟩
        cases tailm <;> simp
      cases htail' : tailm.map (fun p => (σ p.1, p.2)) with
      | none =>
          show P.DerivesW c₀ (as ++ os)
          refine hcont as hasy os ?_
          exact DerivesW.last hm rfl (by rw [htail'] at hblock; simpa using hblock)
      | some q =>
          show ∀ rest, P.DerivesW q.2 rest → P.DerivesW c₀ ((as ++ os) ++ rest)
          intro rest hrest
          rw [List.append_assoc]
          refine hcont as hasy (os ++ rest) ?_
          exact DerivesW.cons hm rfl (by rw [htail'] at hblock; simpa using hblock) hrest

/-- **Every solution plan of a regular problem is a derivation.** -/
theorem derivesW_of_isSolutionPlan (hwf : P.WF) (hreg : P.IsRegularM)
    {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀)
    {as : List A} (hsol : P.IsSolutionPlan as) : P.DerivesW c₀ as := by
  obtain ⟨tn, l, hreach, hprim, hlin, hseq, -, -⟩ := hsol
  obtain ⟨tail, hchain, hcont⟩ := exists_weakChain_contDerivesW hwf hreg hT hα hreach
  have htail : tail = none := by
    cases htail : tail with
    | none => rfl
    | some p =>
        exfalso
        obtain ⟨a, ha⟩ := hprim p.1 (hchain.tailMem p htail)
        have := hchain.tailLabel p htail
        rw [ha] at this
        exact absurd this (by simp)
  subst htail
  exact hcont as ⟨l, by simpa using hlin, hseq, by rintro p ⟨⟩⟩

/-- **Every derivation of the open compound task of a reachable weak chain yields a
solution.** -/
theorem exists_yields_none_of_derivesW [Infinite I] (hwf : P.WF)
    {rest : List A} {c : C} (hd : P.DerivesW c rest) :
    ∀ {tn : TaskNetwork I A C} {pre : List A} {t : I},
      tn.IsWeakChain (some (t, c)) → tn.Yields (some (t, c)) pre → P.Reachable tn →
      ∃ tn₂ : TaskNetwork I A C, P.Reachable tn₂ ∧ tn₂.Yields none (pre ++ rest) := by
  induction hd with
  | @last c os m hm hc hb =>
      intro tn pre t hchain hyield hreach
      obtain ⟨tailm, hchainm, hym, htailm⟩ := hb
      have htailm' : tailm = none := by
        cases tailm with
        | none => rfl
        | some q => simp at htailm
      subst htailm'
      obtain ⟨tn', hwf', hiso', hdisj⟩ :=
        TaskNetwork.exists_fresh_iso_copy m.subtasks (hwf.methods m hm) tn.T
      haveI : Nonempty I := ⟨t⟩
      obtain ⟨σ, hbij, hordσ, hασ⟩ := hiso'.symm
      have hchain' : tn'.IsWeakChain none :=
        TaskNetwork.IsWeakChain.map hbij hordσ hασ hwf' hchainm
      have hy' : tn'.Yields none os := TaskNetwork.Yields.map hbij hordσ hασ hym
      have hstep : DecompStep P.methods tn t m (decomposeWith tn t tn') := by
        refine ⟨hm, hchain.tailMem (t, c) rfl, ?_, tn', hwf', hiso', hdisj, rfl⟩
        have := hchain.tailLabel (t, c) rfl
        simpa [hc] using this
      exact ⟨decomposeWith tn t tn', Relation.ReflTransGen.tail hreach ⟨t, m, hstep⟩,
        TaskNetwork.Yields.compose hchain hchain' hdisj hyield hy'⟩
  | @cons c c' os rest m hm hc hb h ih =>
      intro tn pre t hchain hyield hreach
      obtain ⟨tailm, hchainm, hym, htailm⟩ := hb
      obtain ⟨q, htailmq⟩ : ∃ q : I × C, tailm = some q := by
        cases tailm with
        | none => simp at htailm
        | some q => exact ⟨q, rfl⟩
      subst htailmq
      have hq : q.2 = c' := by simpa using htailm
      obtain ⟨tn', hwf', hiso', hdisj⟩ :=
        TaskNetwork.exists_fresh_iso_copy m.subtasks (hwf.methods m hm) tn.T
      haveI : Nonempty I := ⟨t⟩
      obtain ⟨σ, hbij, hordσ, hασ⟩ := hiso'.symm
      have hchain' : tn'.IsWeakChain (some (σ q.1, c')) := by
        have := TaskNetwork.IsWeakChain.map hbij hordσ hασ hwf' hchainm
        simpa [hq] using this
      have hy' : tn'.Yields (some (σ q.1, c')) os := by
        have := TaskNetwork.Yields.map hbij hordσ hασ hym
        simpa [hq] using this
      have hstep : DecompStep P.methods tn t m (decomposeWith tn t tn') := by
        refine ⟨hm, hchain.tailMem (t, c) rfl, ?_, tn', hwf', hiso', hdisj, rfl⟩
        have := hchain.tailLabel (t, c) rfl
        simpa [hc] using this
      obtain ⟨tn₃, hreach₃, hy₃⟩ :=
        ih (TaskNetwork.IsWeakChain.decompose hchain hchain' hdisj)
          (TaskNetwork.Yields.compose hchain hchain' hdisj hyield hy')
          (Relation.ReflTransGen.tail hreach ⟨t, m, hstep⟩)
      exact ⟨tn₃, hreach₃, by rwa [List.append_assoc] at hy₃⟩

/-- **Normal form theorem for regular problems.**  A well-formed regular HTN planning problem
whose initial task network is a single compound task `c₀` is solvable exactly when there is a
derivation of `c₀` whose action sequence is executable in the initial state and reaches the
goal.  Unlike `Problem.solvable_iff_derives`, the methods need *not* be totally ordered: each
step of the derivation picks one linearization of the primitive part of the method it uses. -/
theorem solvable_iff_derivesW [Infinite I] (hwf : P.WF) (hreg : P.IsRegularM)
    {t₀ : I} {c₀ : C} (hT : P.tnI.T = {t₀}) (hα : P.tnI.α t₀ = Sum.inr c₀) :
    P.Solvable ↔ ∃ as : List A, P.DerivesW c₀ as ∧ P.SeqApplicable as P.init ∧
      P.GoalState (P.transitionSeq as P.init) := by
  constructor
  · intro h
    obtain ⟨as, hplan⟩ := solvable_iff_exists_solutionPlan.1 h
    have hplan' := hplan
    obtain ⟨-, -, -, -, -, -, happ, hgoal⟩ := hplan'
    exact ⟨as, derivesW_of_isSolutionPlan hwf hreg hT hα hplan, happ, hgoal⟩
  · rintro ⟨as, hd, happ, hgoal⟩
    obtain ⟨tn₂, hreach₂, hy₂⟩ :=
      exists_yields_none_of_derivesW hwf hd (isWeakChain_tnI hwf.tnI hT hα)
        (yields_tnI hT hα) Relation.ReflTransGen.refl
    rw [List.nil_append] at hy₂
    obtain ⟨l, hlin, hseq, -⟩ := hy₂
    refine ⟨tn₂, hreach₂, TaskNetwork.Yields.isPrimitive ⟨l, hlin, hseq, by rintro p ⟨⟩⟩,
      l, as, by simpa using hlin, hseq, happ, hgoal⟩

end NormalForm

end Problem

end HTN
