import HtnPlanning.Article.TIHTN
import HtnPlanning.Article.Classes
import HtnPlanning.Core.DecompositionIso
import HtnPlanning.Core.Construction
/-!
# Mostly-acyclic problems are acyclic (Lemma 4.2.2, Corollary 4.2.3)

Lemma 4.2.2: every mostly-acyclic problem `P` becomes acyclic when every strongly connected
component of compound task names is collapsed to one representative, and the resulting problem
`P'` has the same primitive task networks reachable from `tn_I` (Cor. 4.2.3: the same solutions).

**The construction.** `ρ : C → C` maps every compound task name to the representative of its
strongly connected component of the decomposition graph (`HTN.SCCRep`).  `P'` relabels every
compound task name `c` by `ρ c` in `tn_I` and in the methods (`HTN.TaskNetwork.mapC`,
`HTN.Method.mapC`) and drops the methods that become self-loops, i.e. methods `(c, tn)` whose
network consists of a single compound task `c'` of the same component (`HTN.Method.IsLoop`).

**A correction.** The article only collapses components *of size at least two*.  A singleton
component `{c}` may still carry a method `(c, [c])` (Def. 3.7 allows it, since `c ≤₁ c`), which
is a self-loop, so the result is not acyclic.  Here those methods are dropped as well (they are
loops in the sense above); this does not change the reachable primitive networks.

**Statements.** Task ids change under decomposition, so "the same primitive task networks" is
read up to isomorphism, as everywhere in this development:

* `HTN.Article.Problem.lem_4_2_2` — `P'` is acyclic (if only finitely many compound task names
  are reachable, which holds for every finite description), it has the same primitive networks
  reachable from its initial task network up to isomorphism, and it has a solution (an HTN
  solution, a TIHTN solution) iff `P` has one (Cor. 4.2.3 at the level of plan existence);
* `HTN.Article.Problem.cor_4_2_3` — `Sol(P)` and `Sol(P')` agree up to isomorphism, and so do
  the TIHTN solutions.

The proof: a decomposition of `P` is mapped to one of `P'` by relabelling, a loop method being
simply skipped (`HTN.decomposesTo_mergeMethods`).  Conversely a method of `P'` applied to a task
`ρ c₀` stems from a method of some `c` with `ρ c = ρ c₀`; in `P` the task `c₀` is first turned
into `c` along a chain of single-task methods (`HTN.decomposesTo_of_chain`), which exists because
in a `≤₁`-stratification every cycle of the decomposition graph consists of single-task methods
(`HTN.chain_of_cycle`).  Acyclicity: a method of `P'` leads from one component to a component
strictly below it, so the number of reachable names strictly below a component is a rank
(`HTN.Problem.isAcyclic_of_rank`).
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

/-! ### Relabelling compound task names -/

namespace TaskNetwork

/-- The task network with every compound task name `c` replaced by `ρ c`. -/
def mapC (ρ : C → C) (tn : TaskNetwork I A C) : TaskNetwork I A C where
  T := tn.T
  ord := tn.ord
  α x := Sum.map id ρ (tn.α x)

/-- The task network with the label of the task `t` replaced by `x`. -/
def setLabel [DecidableEq I] (tn : TaskNetwork I A C) (t : I) (x : A ⊕ C) : TaskNetwork I A C where
  T := tn.T
  ord := tn.ord
  α := Function.update tn.α t x

variable {ρ : C → C}

theorem mapC_wf {tn : TaskNetwork I A C} (h : tn.WF) : (tn.mapC ρ).WF :=
  ⟨fun h' => h.mem_left h', fun h' => h.mem_right h', h.irrefl, fun h₁ h₂ => h.trans h₁ h₂⟩

theorem setLabel_wf [DecidableEq I] {tn : TaskNetwork I A C} (h : tn.WF) (t : I) (x : A ⊕ C) :
    (tn.setLabel t x).WF :=
  ⟨fun h' => h.mem_left h', fun h' => h.mem_right h', h.irrefl, fun h₁ h₂ => h.trans h₁ h₂⟩

theorem Iso.mapC {tn tn' : TaskNetwork I A C} (h : tn.Iso tn') : (tn.mapC ρ).Iso (tn'.mapC ρ) := by
  obtain ⟨σ, hb, ho, hα⟩ := h
  exact ⟨σ, hb, ho, fun t ht => by simp only [TaskNetwork.mapC, hα t ht]⟩

/-- A primitive network is not changed by relabelling compound names. -/
theorem iso_mapC_of_isPrimitive {tn : TaskNetwork I A C} (h : tn.IsPrimitive) :
    tn.Iso (tn.mapC ρ) := by
  refine ⟨id, Set.bijOn_id _, fun _ _ _ _ => Iff.rfl, fun t ht => ?_⟩
  obtain ⟨a, ha⟩ := h t ht
  simp [TaskNetwork.mapC, ha]

theorem isPrimitive_of_mapC {tn : TaskNetwork I A C} (h : (tn.mapC ρ).IsPrimitive) :
    tn.IsPrimitive := by
  intro t ht
  obtain ⟨a, ha⟩ := h t ht
  simp only [TaskNetwork.mapC] at ha
  rcases hα : tn.α t with a' | c
  · exact ⟨a', hα⟩
  · rw [hα] at ha; simp at ha

theorem mapC_decomposeWith [DecidableEq I] (tn u : TaskNetwork I A C) (t : I) :
    (decomposeWith tn t u).mapC ρ = decomposeWith (tn.mapC ρ) t (u.mapC ρ) := by
  simp only [TaskNetwork.mapC, decomposeWith, mk.injEq, true_and]
  funext x
  split_ifs <;> rfl

theorem setLabel_self [DecidableEq I] {tn : TaskNetwork I A C} {t : I} {x : A ⊕ C}
    (h : tn.α t = x) : tn.setLabel t x = tn := by
  simp only [setLabel]
  rw [← h, Function.update_eq_self]

theorem setLabel_setLabel [DecidableEq I] (tn : TaskNetwork I A C) (t : I) (x y : A ⊕ C) :
    (tn.setLabel t x).setLabel t y = tn.setLabel t y := by
  simp [setLabel]

theorem mapC_setLabel [DecidableEq I] {tn : TaskNetwork I A C} {t : I} {c c₀ : C}
    (h : tn.α t = Sum.inr c₀) (hc : ρ c = ρ c₀) : (tn.setLabel t (Sum.inr c)).mapC ρ = tn.mapC ρ := by
  simp only [mapC, setLabel, mk.injEq, true_and]
  funext x
  by_cases hx : x = t
  · subst hx; simp [h, hc]
  · simp [Function.update_of_ne hx]

/-- **Decomposing a task by a single task** relabels it: the result is isomorphic to the network
with the label of `t` replaced by the label of the new task. -/
theorem decomposeWith_single_iso [DecidableEq I] {tn u : TaskNetwork I A C} {t t' : I}
    (h₁ : tn.WF) (hu : u.WF) (hdisj : Disjoint tn.T u.T) (ht : t ∈ tn.T) (hT : u.T = {t'}) :
    (decomposeWith tn t u).Iso (tn.setLabel t (u.α t')) := by
  classical
  have ht'u : t' ∈ u.T := by rw [hT]; exact Finset.mem_singleton_self _
  have ht'n : t' ∉ tn.T := fun h => Finset.disjoint_left.1 hdisj h ht'u
  have hmem : ∀ x, x ∈ (decomposeWith tn t u).T ↔ (x ∈ tn.T ∧ x ≠ t) ∨ x = t' := by
    intro x; rw [mem_decomposeWith_T, hT, Finset.mem_singleton]
  let σ : I → I := fun x => if x = t' then t else x
  have hσold : ∀ x, x ≠ t' → σ x = x := fun x hx => if_neg hx
  have hσnew : σ t' = t := if_pos rfl
  refine ⟨σ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    rcases (hmem x).1 hx with ⟨hx, -⟩ | rfl
    · rw [hσold x (fun h => ht'n (h ▸ hx))]; exact hx
    · rw [hσnew]; exact ht
  · intro x hx y hy hxy
    rcases (hmem x).1 hx with ⟨hx, hxt⟩ | rfl <;> rcases (hmem y).1 hy with ⟨hy, hyt⟩ | rfl
    · rwa [hσold x (fun h => ht'n (h ▸ hx)), hσold y (fun h => ht'n (h ▸ hy))] at hxy
    · rw [hσold x (fun h => ht'n (h ▸ hx)), hσnew] at hxy; exact absurd hxy hxt
    · rw [hσold y (fun h => ht'n (h ▸ hy)), hσnew] at hxy; exact absurd hxy.symm hyt
    · rfl
  · intro y hy
    by_cases hyt : y = t
    · exact ⟨t', (hmem t').2 (Or.inr rfl), by rw [hσnew, hyt]⟩
    · exact ⟨y, (hmem y).2 (Or.inl ⟨hy, hyt⟩), hσold y (fun h => ht'n (h ▸ hy))⟩
  · intro x hx y hy
    show _ ↔ tn.ord (σ x) (σ y)
    rcases (hmem x).1 hx with ⟨hx, hxt⟩ | rfl <;> rcases (hmem y).1 hy with ⟨hy, hyt⟩ | rfl
    · rw [hσold x (fun h => ht'n (h ▸ hx)), hσold y (fun h => ht'n (h ▸ hy))]
      exact decomposeWith_ord_old_old hu hdisj hx hxt hy hyt
    · rw [hσold x (fun h => ht'n (h ▸ hx)), hσnew]
      exact decomposeWith_ord_old_new h₁ hu hdisj hx ht'u
    · rw [hσold y (fun h => ht'n (h ▸ hy)), hσnew]
      exact decomposeWith_ord_new_old h₁ hu hdisj ht'u hy
    · rw [hσnew, decomposeWith_ord_new_new h₁ hdisj ht'u ht'u]
      exact ⟨fun h => absurd h (hu.irrefl _), fun h => absurd h (h₁.irrefl _)⟩
  · intro x hx
    show (if x ∈ u.T then u.α x else tn.α x) = Function.update tn.α t (u.α t') (σ x)
    rcases (hmem x).1 hx with ⟨hx, hxt⟩ | rfl
    · have hxu : x ∉ u.T := Finset.disjoint_left.1 hdisj hx
      rw [if_neg hxu, hσold x (fun h => ht'n (h ▸ hx)), Function.update_of_ne hxt]
    · rw [if_pos ht'u, hσnew, Function.update_self]

end TaskNetwork

namespace Method

/-- The method with every compound task name `c` replaced by `ρ c`. -/
def mapC (ρ : C → C) (m : Method I A C) : Method I A C := ⟨ρ m.abstractTask, m.subtasks.mapC ρ⟩

/-- A method that becomes a **self-loop** under `ρ`: its network is a single compound task in the
same class as the decomposed task. -/
def IsLoop (ρ : C → C) (m : Method I A C) : Prop :=
  ∃ t c, m.subtasks.T = {t} ∧ m.subtasks.α t = Sum.inr c ∧ ρ c = ρ m.abstractTask

end Method

/-- The methods of the collapsed domain: the relabelled methods that are no self-loops. -/
def mergeMethods (ρ : C → C) (M : Set (Method I A C)) : Set (Method I A C) :=
  Method.mapC ρ '' {m | m ∈ M ∧ ¬ m.IsLoop ρ}

/-! ### From `P` to `P'` -/

section Forward

variable [DecidableEq I] {ρ : C → C} {M : Set (Method I A C)}

theorem DecompStep.mapC {tn tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    (h : DecompStep M tn t m tn₂) (hl : ¬ m.IsLoop ρ) :
    DecompStep (mergeMethods ρ M) (tn.mapC ρ) t (m.mapC ρ) (tn₂.mapC ρ) := by
  obtain ⟨hm, ht, hα, u, hu, hiso, hdisj, rfl⟩ := h
  refine ⟨⟨m, ⟨hm, hl⟩, rfl⟩, ht, ?_, u.mapC ρ, TaskNetwork.mapC_wf hu, hiso.mapC, hdisj,
    TaskNetwork.mapC_decomposeWith _ _ _⟩
  show Sum.map id ρ (tn.α t) = _
  rw [hα]; rfl

/-- A loop step does not change the relabelled network (up to isomorphism). -/
theorem DecompStep.mapC_loop {tn tn₂ : TaskNetwork I A C} {t : I} {m : Method I A C}
    (h : DecompStep M tn t m tn₂) (hl : m.IsLoop ρ) (hwf : tn.WF) :
    (tn₂.mapC ρ).Iso (tn.mapC ρ) := by
  obtain ⟨hm, ht, hα, u, hu, hiso, hdisj, rfl⟩ := h
  obtain ⟨t₀, c, hT, hc, hρ⟩ := hl
  have hcard : u.T.card = 1 := by rw [hiso.card_eq, hT]; rfl
  obtain ⟨t', hT'⟩ := Finset.card_eq_one.1 hcard
  obtain ⟨σ, hb, -, hσα⟩ := hiso
  have ht'u : t' ∈ u.T := by rw [hT']; exact Finset.mem_singleton_self _
  have hσt : σ t' = t₀ := by
    have := hb.mapsTo (show t' ∈ (u.T : Set I) from ht'u)
    simpa [hT] using this
  have hlab : u.α t' = Sum.inr c := by rw [hσα t' ht'u, hσt, hc]
  have h1 := (TaskNetwork.decomposeWith_single_iso hwf hu hdisj ht hT').mapC (ρ := ρ)
  rwa [hlab, TaskNetwork.mapC_setLabel hα hρ] at h1

/-- **Decompositions of `P` are decompositions of `P'`**, up to isomorphism. -/
theorem decomposesTo_mergeMethods [Infinite I] {tn tn₂ : TaskNetwork I A C} (h : DecomposesTo M tn tn₂)
    (hwf : tn.WF) : ∃ u, DecomposesTo (mergeMethods ρ M) (tn.mapC ρ) u ∧ (tn₂.mapC ρ).Iso u := by
  induction h with
  | refl => exact ⟨_, Relation.ReflTransGen.refl, TaskNetwork.Iso.refl _⟩
  | @tail b c hab hbc ih =>
    obtain ⟨ub, hub, hiso⟩ := ih
    obtain ⟨t, m, hstep⟩ := hbc
    have hbwf : b.WF := HTN.DecomposesTo.wf hab hwf
    by_cases hl : m.IsLoop ρ
    · exact ⟨ub, hub, (hstep.mapC_loop hl hbwf).trans hiso⟩
    · have hubwf : ub.WF := HTN.DecomposesTo.wf hub (TaskNetwork.mapC_wf hwf)
      obtain ⟨t', uc, hstep', hiso'⟩ :=
        (hstep.mapC hl).iso (TaskNetwork.mapC_wf hbwf) hubwf hiso
      exact ⟨uc, Relation.ReflTransGen.tail hub ⟨t', _, hstep'⟩, hiso'⟩

end Forward

/-! ### Chains of single-task methods -/

/-- `a` has a method whose network is the single compound task `b`. -/
def SEdge (M : Set (Method I A C)) (a b : C) : Prop :=
  ∃ m ∈ M, m.abstractTask = a ∧ ∃ t, m.subtasks.T = {t} ∧ m.subtasks.α t = Sum.inr b

/-- A chain of single-task methods. -/
def Chain (M : Set (Method I A C)) : C → C → Prop := Relation.ReflTransGen (SEdge M)

section Chain

variable [DecidableEq I] [Infinite I] {M : Set (Method I A C)}

/-- **A chain of single-task methods relabels a task.** -/
theorem decomposesTo_of_chain (hM : ∀ m ∈ M, m.subtasks.WF) {a b : C} (h : Chain M a b) :
    ∀ {tn : TaskNetwork I A C} {t : I}, tn.WF → t ∈ tn.T → tn.α t = Sum.inr a →
      ∃ tn₁, DecomposesTo M tn tn₁ ∧ (tn.setLabel t (Sum.inr b)).Iso tn₁ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro tn t _ _ hα
    exact ⟨tn, Relation.ReflTransGen.refl, by rw [TaskNetwork.setLabel_self hα]⟩
  | @head a a' hedge _ ih =>
    intro tn t hwf ht hα
    obtain ⟨m, hm, hma, t₀, hT, hc⟩ := hedge
    obtain ⟨u, hu, hiso, hdisj⟩ := TaskNetwork.exists_fresh_iso_copy m.subtasks (hM m hm) tn.T
    have hcard : u.T.card = 1 := by rw [hiso.card_eq, hT]; rfl
    obtain ⟨t', hT'⟩ := Finset.card_eq_one.1 hcard
    have ht'u : t' ∈ u.T := by rw [hT']; exact Finset.mem_singleton_self _
    have hlab : u.α t' = Sum.inr a' := by
      obtain ⟨σ, hb, -, hσα⟩ := hiso
      have := hb.mapsTo (show t' ∈ (u.T : Set I) from ht'u)
      have hσt : σ t' = t₀ := by simpa [hT] using this
      rw [hσα t' ht'u, hσt, hc]
    have hstep : DecompStep M tn t m (decomposeWith tn t u) :=
      ⟨hm, ht, by rw [hα, hma], u, hu, hiso, hdisj, rfl⟩
    have hs := TaskNetwork.decomposeWith_single_iso hwf hu hdisj ht hT'
    rw [hlab] at hs
    have hwf' := TaskNetwork.setLabel_wf hwf t (Sum.inr a')
    obtain ⟨tn₂, hd₂, hiso₂⟩ := ih hwf' ht (by simp [TaskNetwork.setLabel])
    have hdwf : (decomposeWith tn t u).WF := HTN.DecomposesTo.wf
      (Relation.ReflTransGen.single ⟨t, m, hstep⟩) hwf
    obtain ⟨tn₃, hd₃, hiso₃⟩ := hd₂.iso hwf' hdwf hs.symm
    refine ⟨tn₃, Relation.ReflTransGen.head ⟨t, m, hstep⟩ hd₃, ?_⟩
    rw [TaskNetwork.setLabel_setLabel] at hiso₂
    exact hiso₂.trans hiso₃

end Chain

/-! ### From `P'` back to `P` -/

section Backward

variable [DecidableEq I] [Infinite I] {ρ : C → C} {M : Set (Method I A C)}

/-- The compound labels of a network lie in `R`. -/
def LabelsIn (R : C → Prop) (tn : TaskNetwork I A C) : Prop :=
  ∀ t ∈ tn.T, ∀ c, tn.α t = Sum.inr c → R c

/-- `R` is closed under the methods of `M`. -/
def ClosedUnder (R : C → Prop) (M : Set (Method I A C)) : Prop :=
  ∀ m ∈ M, R m.abstractTask → ∀ t ∈ m.subtasks.T, ∀ c, m.subtasks.α t = Sum.inr c → R c

omit [Infinite I] in
theorem DecomposesTo.labelsIn {R : C → Prop} (hR : ClosedUnder R M) {tn tn₂ : TaskNetwork I A C}
    (h : DecomposesTo M tn tn₂) (h₀ : LabelsIn R tn) : LabelsIn R tn₂ := by
  induction h with
  | refl => exact h₀
  | @tail b c _ hbc ih =>
    obtain ⟨t, m, hm, ht, hα, u, -, hiso, -, rfl⟩ := hbc
    intro x hx d hd
    simp only [decomposeWith_α] at hd
    split_ifs at hd with hxu
    · obtain ⟨σ, hb, -, hσα⟩ := hiso
      have hσx : σ x ∈ m.subtasks.T := by
        simpa using hb.mapsTo (show x ∈ (u.T : Set I) from hxu)
      exact hR m hm (ih t ht _ hα) (σ x) hσx d (by rw [← hσα x hxu]; exact hd)
    · rw [mem_decomposeWith_T] at hx
      rcases hx with ⟨hx, -⟩ | hx
      · exact ih x hx d hd
      · exact absurd hx hxu

/-- **Decompositions of `P'` are decompositions of `P`**, up to isomorphism, provided every
compound task `c₀` that can occur reaches the decomposed task of every method of the same class
by a chain of single-task methods. -/
theorem exists_decomposesTo_of_merge (hM : ∀ m ∈ M, m.subtasks.WF) {R : C → Prop}
    (hR : ClosedUnder R M)
    (hchain : ∀ c₀, R c₀ → ∀ m ∈ M, ¬ m.IsLoop ρ → ρ c₀ = ρ m.abstractTask →
      Chain M c₀ m.abstractTask)
    {u u₂ : TaskNetwork I A C} (h : DecomposesTo (mergeMethods ρ M) u u₂) (hu : u.WF)
    {tn : TaskNetwork I A C} (hwf : tn.WF) (hl : LabelsIn R tn) (hiso : u.Iso (tn.mapC ρ)) :
    ∃ tn₂, DecomposesTo M tn tn₂ ∧ u₂.Iso (tn₂.mapC ρ) := by
  induction h with
  | refl => exact ⟨tn, Relation.ReflTransGen.refl, hiso⟩
  | @tail b c hab hbc ih =>
    obtain ⟨tnb, hdb, hisob⟩ := ih
    have hbwf : b.WF := HTN.DecomposesTo.wf hab hu
    have htnbwf : tnb.WF := HTN.DecomposesTo.wf hdb hwf
    have hlb : LabelsIn R tnb := hdb.labelsIn hR hl
    obtain ⟨x, m', ⟨m, ⟨hm, hnl⟩, rfl⟩, hx, hαx, w', hw', hw'iso, hdisj', rfl⟩ := hbc
    obtain ⟨σ, hσb, hσo, hσα⟩ := hisob
    have hσx : σ x ∈ tnb.T := by simpa using hσb.mapsTo (show x ∈ (b.T : Set I) from hx)
    -- the label `c₀` of the corresponding task of `tnb`
    obtain ⟨c₀, hc₀, hρc₀⟩ : ∃ c₀, tnb.α (σ x) = Sum.inr c₀ ∧ ρ c₀ = ρ m.abstractTask := by
      have h1 := hσα x hx
      rw [hαx] at h1
      change _ = Sum.map id ρ (tnb.α (σ x)) at h1
      rcases hα : tnb.α (σ x) with a | c₀
      · rw [hα] at h1; simp at h1
      · rw [hα] at h1
        exact ⟨c₀, rfl, (Sum.inr.inj h1).symm⟩
    -- turn `c₀` into the decomposed task of `m` in `P`
    obtain ⟨tn₁, hd₁, hiso₁⟩ := decomposesTo_of_chain hM
      (hchain c₀ (hlb _ hσx _ hc₀) m hm hnl hρc₀) htnbwf hσx hc₀
    set v := tnb.setLabel (σ x) (Sum.inr m.abstractTask) with hv
    have hvwf : v.WF := TaskNetwork.setLabel_wf htnbwf _ _
    have hvmap : v.mapC ρ = tnb.mapC ρ := TaskNetwork.mapC_setLabel hc₀ hρc₀.symm
    -- apply `m` in `P`
    obtain ⟨w, hw, hwiso, hdisj⟩ := TaskNetwork.exists_fresh_iso_copy m.subtasks (hM m hm) v.T
    have hstep : DecompStep M v (σ x) m (decomposeWith v (σ x) w) :=
      ⟨hm, hσx, by simp [hv, TaskNetwork.setLabel], w, hw, hwiso, hdisj, rfl⟩
    obtain ⟨t'', tn₂, hstep₂, hiso₂⟩ := hstep.iso hvwf (HTN.DecomposesTo.wf hd₁ htnbwf) hiso₁
    refine ⟨tn₂, (hdb.trans hd₁).trans (Relation.ReflTransGen.single ⟨t'', m, hstep₂⟩), ?_⟩
    refine TaskNetwork.Iso.trans ?_ hiso₂.mapC
    rw [TaskNetwork.mapC_decomposeWith]
    -- the two steps are isomorphic
    have hwmap : w'.Iso (w.mapC ρ) := hw'iso.trans (hwiso.mapC (ρ := ρ)).symm
    obtain ⟨τ, hτb, hτo, hτα⟩ := hwmap
    rw [hvmap]
    exact decomposeWith_iso_congr hbwf (TaskNetwork.mapC_wf htnbwf) hw' (TaskNetwork.mapC_wf hw)
      hdisj' (by rw [← hvmap]; exact hdisj) hx hσb hσo hσα hτb hτo hτα

end Backward

/-! ### Cycles of a `≤₁`-stratification -/

/-- The decomposition graph: `b` occurs in a method of `a`. -/
def DEdge (M : Set (Method I A C)) (a b : C) : Prop :=
  ∃ m ∈ M, m.abstractTask = a ∧ ∃ t ∈ m.subtasks.T, m.subtasks.α t = Sum.inr b

/-- `a` and `b` lie in the same strongly connected component of the decomposition graph. -/
def SameSCC (M : Set (Method I A C)) (a b : C) : Prop :=
  Relation.ReflTransGen (DEdge M) a b ∧ Relation.ReflTransGen (DEdge M) b a

theorem SameSCC.symm {M : Set (Method I A C)} {a b : C} (h : SameSCC M a b) : SameSCC M b a :=
  ⟨h.2, h.1⟩

theorem SameSCC.trans {M : Set (Method I A C)} {a b c : C} (h₁ : SameSCC M a b)
    (h₂ : SameSCC M b c) : SameSCC M a c := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- `ρ` picks a representative of every strongly connected component. -/
structure SCCRep (M : Set (Method I A C)) (ρ : C → C) : Prop where
  /-- Every name lies in the component of its representative. -/
  same : ∀ c, SameSCC M c (ρ c)
  /-- Names of the same component have the same representative. -/
  eq : ∀ c c', SameSCC M c c' → ρ c = ρ c'

theorem SCCRep.iff {M : Set (Method I A C)} {ρ : C → C} (h : SCCRep M ρ) {c c' : C} :
    ρ c = ρ c' ↔ SameSCC M c c' :=
  ⟨fun e => (h.same c).trans (e ▸ (h.same c').symm), h.eq c c'⟩

/-- Representatives exist. -/
theorem exists_sccRep (M : Set (Method I A C)) : ∃ ρ : C → C, SCCRep M ρ := by
  let s : Setoid C := ⟨SameSCC M, ⟨fun _ => ⟨.refl, .refl⟩, SameSCC.symm, SameSCC.trans⟩⟩
  refine ⟨fun c => (Quotient.mk s c).out, fun c => ?_, fun c c' h => ?_⟩
  · exact Setoid.symm (Quotient.mk_out (s := s) c)
  · show (Quotient.mk s c).out = (Quotient.mk s c').out
    rw [Quotient.sound (s := s) h]

namespace Problem

variable {F : Type*} (P : Problem F A C I)

theorem dEdge_reachable {a b : C} (h : DEdge P.methods a b) (ha : P.ReachableName a) :
    P.ReachableName b := by
  obtain ⟨m, hm, rfl, t, ht, hb⟩ := h
  exact .method hm ha ht hb

theorem reachable_of_path {a b : C} (h : Relation.ReflTransGen (DEdge P.methods) a b)
    (ha : P.ReachableName a) : P.ReachableName b := by
  induction h with
  | refl => exact ha
  | tail _ h ih => exact P.dEdge_reachable h ih

variable {P}

/-- In a `≤₁`-stratification, the names reachable from `a` are below `a`. -/
theorem IsStrat1.le_of_path {le : C → C → Prop} (hs : P.IsStrat1 le) {a b : C}
    (h : Relation.ReflTransGen (DEdge P.methods) a b) (ha : P.ReachableName a) :
    P.ReachableName b ∧ le b a := by
  induction h with
  | refl => exact ⟨ha, hs.strat.refl a ha⟩
  | @tail x b _ hxb ih =>
    obtain ⟨hx, hle⟩ := ih
    have hb := P.dEdge_reachable hxb hx
    obtain ⟨m, hm, rfl, t, ht, hc⟩ := hxb
    have hmr : P.ReachableMethod m := ⟨hm, hx⟩
    have hbx : le b m.abstractTask := by
      rcases Nat.lt_or_ge 1 m.subtasks.T.card with h1 | h1
      · exact (hs.big m hmr h1 t ht b hc).1
      · have : m.subtasks.T.card = 1 :=
          le_antisymm h1 (Finset.card_pos.2 ⟨t, ht⟩)
        exact hs.small m hmr this t ht b hc
    exact ⟨hb, hs.strat.trans _ _ _ hb hx ha hbx hle⟩

/-- **Cycles consist of single-task methods.** In a `≤₁`-stratification, if `a` (reachable) and
`b` reach each other, then `a` reaches `b` along single-task methods. -/
theorem IsStrat1.chain_of_cycle {le : C → C → Prop} (hs : P.IsStrat1 le) {a b : C}
    (hab : Relation.ReflTransGen (DEdge P.methods) a b)
    (hba : Relation.ReflTransGen (DEdge P.methods) b a) (ha : P.ReachableName a) :
    Chain P.methods a b := by
  induction hab with
  | refl => exact .refl
  | @tail x b hax hxb ih =>
    have hxa : Relation.ReflTransGen (DEdge P.methods) x a := (Relation.ReflTransGen.single hxb).trans hba
    have hc := ih hxa
    have hx := P.reachable_of_path hax ha
    have hb := P.dEdge_reachable hxb hx
    -- `x ≤ b`, since `b` reaches `x`
    have hle : le x b := (hs.le_of_path (hba.trans hax) hb).2
    obtain ⟨m, hm, rfl, t, ht, hc'⟩ := hxb
    have hmr : P.ReachableMethod m := ⟨hm, hx⟩
    have h1 : m.subtasks.T.card = 1 := by
      rcases Nat.lt_or_ge 1 m.subtasks.T.card with h1 | h1
      · exact absurd hle (hs.big m hmr h1 t ht b hc').2
      · exact le_antisymm h1 (Finset.card_pos.2 ⟨t, ht⟩)
    obtain ⟨t', hT⟩ := Finset.card_eq_one.1 h1
    have : t = t' := by rw [hT] at ht; simpa using ht
    subst this
    exact hc.tail ⟨m, hm, rfl, t, hT, hc'⟩

end Problem

end HTN

/-! ### Insertion is compatible with isomorphism -/

namespace HTN

namespace Article

universe u' v' w'

variable {A : Type v'} {C : Type w'} {I : Type u'} [DecidableEq I]

/-- `σ` is an isomorphism from `tn` to `u`. -/
def IsoVia (σ : I → I) (tn u : TaskNetwork I A C) : Prop :=
  Set.BijOn σ (tn.T : Set I) (u.T : Set I) ∧
    (∀ x ∈ tn.T, ∀ y ∈ tn.T, (tn.ord x y ↔ u.ord (σ x) (σ y))) ∧ ∀ x ∈ tn.T, tn.α x = u.α (σ x)

theorem IsoVia.iso {σ : I → I} {tn u : TaskNetwork I A C} (h : IsoVia σ tn u) : tn.Iso u :=
  ⟨σ, h⟩

/-- Transitive closures of two relations living on sets matched by a bijection agree. -/
theorem transGen_iff_of_bijOn {S S' : Set I} {σ : I → I} (hb : Set.BijOn σ S S')
    {R R' : I → I → Prop} (hR : ∀ a b, R a b → a ∈ S ∧ b ∈ S)
    (hR' : ∀ a b, R' a b → a ∈ S' ∧ b ∈ S') (h : ∀ a ∈ S, ∀ b ∈ S, (R a b ↔ R' (σ a) (σ b)))
    {x y : I} (hx : x ∈ S) (hy : y ∈ S) :
    Relation.TransGen R x y ↔ Relation.TransGen R' (σ x) (σ y) := by
  constructor
  · intro hxy
    induction hxy with
    | single hab => exact .single ((h _ hx _ (hR _ _ hab).2).1 hab)
    | @tail b c hxb hbc ih =>
      have hb' := (hR _ _ hbc).1
      exact .tail (ih hb') ((h _ hb' _ (hR _ _ hbc).2).1 hbc)
  · intro hxy
    suffices ∀ z, Relation.TransGen R' (σ x) z → ∀ y ∈ S, σ y = z → Relation.TransGen R x y from
      this _ hxy y hy rfl
    intro z hz
    induction hz with
    | single hab =>
      rintro y hy rfl
      exact .single ((h _ hx _ hy).2 hab)
    | @tail b c _ hbc ih =>
      rintro y hy rfl
      obtain ⟨b₀, hb₀, rfl⟩ := hb.surjOn (hR' _ _ hbc).1
      exact .tail (ih b₀ hb₀ rfl) ((h _ hb₀ _ hy).2 hbc)

theorem OIStep.isoVia {σ : I → I} {tn₁ tn₂ u₁ : TaskNetwork I A C} (h : OIStep tn₁ tn₂)
    (h₁ : tn₁.WF) (hu₁ : u₁.WF) (hσ : IsoVia σ tn₁ u₁) :
    ∃ u₂, OIStep u₁ u₂ ∧ IsoVia σ tn₂ u₂ := by
  obtain ⟨t, t', ht, ht', hpt, hpt', rfl, hwf₂⟩ := h
  obtain ⟨hb, ho, hα⟩ := hσ
  have hmaps : ∀ x ∈ tn₁.T, σ x ∈ u₁.T := fun x hx => hb.mapsTo (show x ∈ (tn₁.T : Set I) from hx)
  let R : I → I → Prop := fun a b => tn₁.ord a b ∨ (a = t ∧ b = t')
  let R' : I → I → Prop := fun a b => u₁.ord a b ∨ (a = σ t ∧ b = σ t')
  have hR : ∀ a b, R a b → a ∈ (tn₁.T : Set I) ∧ b ∈ (tn₁.T : Set I) := by
    rintro a b (hab | ⟨rfl, rfl⟩)
    · exact ⟨h₁.mem_left hab, h₁.mem_right hab⟩
    · exact ⟨ht, ht'⟩
  have hR' : ∀ a b, R' a b → a ∈ (u₁.T : Set I) ∧ b ∈ (u₁.T : Set I) := by
    rintro a b (hab | ⟨rfl, rfl⟩)
    · exact ⟨hu₁.mem_left hab, hu₁.mem_right hab⟩
    · exact ⟨hmaps t ht, hmaps t' ht'⟩
  have hRR : ∀ a ∈ (tn₁.T : Set I), ∀ b ∈ (tn₁.T : Set I), (R a b ↔ R' (σ a) (σ b)) := by
    intro a ha b hb'
    refine or_congr (ho a ha b hb') ⟨fun ⟨e₁, e₂⟩ => ⟨e₁ ▸ rfl, e₂ ▸ rfl⟩, fun ⟨e₁, e₂⟩ => ?_⟩
    exact ⟨hb.injOn ha ht e₁, hb.injOn hb' ht' e₂⟩
  have hiff := fun x (hx : x ∈ (tn₁.T : Set I)) y (hy : y ∈ (tn₁.T : Set I)) =>
    transGen_iff_of_bijOn hb hR hR' hRR hx hy
  have hwf : (ordInsert u₁ (σ t) (σ t')).WF := by
    refine ⟨fun hab => ?_, fun hab => ?_, fun y hy => ?_, fun h₁ h₂ => h₁.trans h₂⟩
    · obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 hab; exact (hR' _ _ hc).1
    · obtain ⟨c, -, hc⟩ := Relation.TransGen.tail'_iff.1 hab; exact (hR' _ _ hc).2
    · have hyT : y ∈ (u₁.T : Set I) := by
        obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 hy; exact (hR' _ _ hc).1
      obtain ⟨x, hx, rfl⟩ := hb.surjOn hyT
      exact hwf₂.irrefl x ((hiff x hx x hx).2 hy)
  refine ⟨ordInsert u₁ (σ t) (σ t'), ⟨σ t, σ t', hmaps t ht, hmaps t' ht', ?_, ?_, rfl, hwf⟩,
    hb, fun x hx y hy => hiff x hx y hy, hα⟩
  · obtain ⟨a, ha⟩ := hpt; exact ⟨a, by rw [← hα t ht, ha]⟩
  · obtain ⟨a, ha⟩ := hpt'; exact ⟨a, by rw [← hα t' ht', ha]⟩

theorem OIReach.isoVia {σ : I → I} {tn₁ tn₂ u₁ : TaskNetwork I A C} (h : OIReach tn₁ tn₂)
    (h₁ : tn₁.WF) (hu₁ : u₁.WF) (hσ : IsoVia σ tn₁ u₁) :
    ∃ u₂, OIReach u₁ u₂ ∧ IsoVia σ tn₂ u₂ := by
  induction h with
  | refl => exact ⟨u₁, .refl, hσ⟩
  | @tail b c hab hbc ih =>
    obtain ⟨ub, hub, hσb⟩ := ih
    obtain ⟨uc, huc, hσc⟩ := hbc.isoVia (OIReach.wf hab h₁) (OIReach.wf hub hu₁) hσb
    exact ⟨uc, hub.tail huc, hσc⟩

theorem TIStep.isoVia [Infinite I] {σ : I → I} {tn₁ tn₂ u₁ : TaskNetwork I A C}
    (h : TIStep tn₁ tn₂) (h₁ : tn₁.WF) (hu₁ : u₁.WF) (hσ : IsoVia σ tn₁ u₁) :
    ∃ σ' u₂, TIStep u₁ u₂ ∧ IsoVia σ' tn₂ u₂ := by
  obtain ⟨t, a, ht, rfl⟩ := h
  obtain ⟨t₂, ht₂⟩ := Infinite.exists_notMem_finset u₁.T
  obtain ⟨hb, ho, hα⟩ := hσ
  have hmaps : ∀ x ∈ tn₁.T, σ x ∈ u₁.T := fun x hx => hb.mapsTo (show x ∈ (tn₁.T : Set I) from hx)
  let σ' := Function.update σ t t₂
  have hσ'old : ∀ x ∈ tn₁.T, σ' x = σ x := fun x hx =>
    Function.update_of_ne (by rintro rfl; exact ht hx) _ _
  have hσ't : σ' t = t₂ := Function.update_self _ _ _
  have hmem : ∀ x, x ∈ (taskInsert tn₁ t a).T ↔ x = t ∨ x ∈ tn₁.T := fun x => Finset.mem_insert
  refine ⟨σ', taskInsert u₁ t₂ a, ⟨t₂, a, ht₂, rfl⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    rcases (hmem x).1 hx with rfl | hx
    · rw [hσ't]; exact Finset.mem_insert_self _ _
    · rw [hσ'old x hx]; exact Finset.mem_insert_of_mem (hmaps x hx)
  · intro x hx y hy hxy
    rcases (hmem x).1 hx with hxt | hx <;> rcases (hmem y).1 hy with hyt | hy
    · rw [hxt, hyt]
    · rw [hxt, hσ't, hσ'old y hy] at hxy; exact absurd (hxy ▸ hmaps y hy) ht₂
    · rw [hyt, hσ't, hσ'old x hx] at hxy; exact absurd (hxy ▸ hmaps x hx) ht₂
    · rw [hσ'old x hx, hσ'old y hy] at hxy; exact hb.injOn hx hy hxy
  · intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ⟨t, Finset.mem_insert_self _ _, hσ't⟩
    · obtain ⟨x, hx, rfl⟩ := hb.surjOn (show y ∈ (u₁.T : Set I) from hy)
      exact ⟨x, Finset.mem_insert_of_mem hx, hσ'old x hx⟩
  · intro x hx y hy
    show tn₁.ord x y ↔ u₁.ord (σ' x) (σ' y)
    rcases (hmem x).1 hx with rfl | hx
    · rw [hσ't]
      exact ⟨fun h => absurd (h₁.mem_left h) ht, fun h => absurd (hu₁.mem_left h) ht₂⟩
    rcases (hmem y).1 hy with rfl | hy
    · rw [hσ't]
      exact ⟨fun h => absurd (h₁.mem_right h) ht, fun h => absurd (hu₁.mem_right h) ht₂⟩
    rw [hσ'old x hx, hσ'old y hy]; exact ho x hx y hy
  · intro x hx
    show Function.update tn₁.α t (Sum.inl a) x = Function.update u₁.α t₂ (Sum.inl a) (σ' x)
    rcases (hmem x).1 hx with hxt | hx'
    · rw [hxt, hσ't, Function.update_self, Function.update_self]
    · have hne : x ≠ t := fun e => ht (e ▸ hx')
      have hne' : σ x ≠ t₂ := fun e => ht₂ (e ▸ hmaps x hx')
      rw [hσ'old x hx', Function.update_of_ne hne, Function.update_of_ne hne']
      exact hα x hx'

theorem TIReach.isoVia [Infinite I] {σ : I → I} {tn₁ tn₂ u₁ : TaskNetwork I A C}
    (h : TIReach tn₁ tn₂) (h₁ : tn₁.WF) (hu₁ : u₁.WF) (hσ : IsoVia σ tn₁ u₁) :
    ∃ σ' u₂, TIReach u₁ u₂ ∧ IsoVia σ' tn₂ u₂ := by
  induction h with
  | refl => exact ⟨σ, u₁, .refl, hσ⟩
  | @tail b c hab hbc ih =>
    obtain ⟨σb, ub, hub, hσb⟩ := ih
    obtain ⟨σc, uc, huc, hσc⟩ := hbc.isoVia (TIReach.wf hab h₁) (TIReach.wf hub hu₁) hσb
    exact ⟨σc, uc, hub.tail huc, hσc⟩

namespace Problem

variable {F : Type*} (P : Problem F A C I)

theorem executableIn_of_iso [Nonempty I] {tn u : TaskNetwork I A C} (h : tn.Iso u) {s : Set F}
    (hex : P.ExecutableIn tn s) : P.ExecutableIn u s := by
  refine ⟨h.isPrimitive hex.1, fun l as hl has => ?_⟩
  obtain ⟨l', hl', has'⟩ := (h.exists_linearization_actionSeq_iff as).2 ⟨l, hl, has⟩
  exact hex.2 l' as hl' has'

theorem generates_of_iso [Nonempty I] {tn u : TaskNetwork I A C} (h : tn.Iso u) {s s' : Set F}
    (hg : P.Generates u s s') : P.Generates tn s s' := by
  obtain ⟨l, as, hl, has, hrun⟩ := hg
  obtain ⟨l', hl', has'⟩ := (h.exists_linearization_actionSeq_iff as).2 ⟨l, hl, has⟩
  exact ⟨l', as, hl', has', hrun⟩

end Problem

end Article

end HTN

/-! ### The collapsed problem -/

namespace HTN

namespace Article

namespace Problem

universe u' v' w' x'

variable {F : Type u'} {A : Type v'} {C : Type w'} {I : Type x'} [DecidableEq I]

/-- **The collapsed problem** `P'` of Lemma 4.2.2: every compound task name replaced by the
representative `ρ` of its strongly connected component, self-loops dropped. -/
def mergeSCC (P : Problem F A C I) (ρ : C → C) : Problem F A C I :=
  { P with methods := mergeMethods ρ P.methods, tnI := P.tnI.mapC ρ }

variable (P : Problem F A C I) {ρ : C → C}

@[simp] theorem mergeSCC_methods : (P.mergeSCC ρ).methods = mergeMethods ρ P.methods := rfl
@[simp] theorem mergeSCC_tnI : (P.mergeSCC ρ).tnI = P.tnI.mapC ρ := rfl
@[simp] theorem mergeSCC_δ : (P.mergeSCC ρ).δ = P.δ := rfl
@[simp] theorem mergeSCC_init : (P.mergeSCC ρ).init = P.init := rfl

theorem mergeSCC_run (as : List A) (s s' : Set F) : (P.mergeSCC ρ).Run as s s' ↔ P.Run as s s' := by
  induction as generalizing s with
  | nil => exact Iff.rfl
  | cons a as ih => exact and_congr Iff.rfl (ih _)
theorem mergeSCC_goalState : (P.mergeSCC ρ).GoalState = P.GoalState := rfl

variable {P}

theorem mergeSCC_wf (hP : P.WF) : (P.mergeSCC ρ).WF := by
  refine ⟨TaskNetwork.mapC_wf hP.tnI, ?_⟩
  rintro _ ⟨m, ⟨hm, -⟩, rfl⟩
  exact TaskNetwork.mapC_wf (hP.methods m hm)

/-- The reachable names of `P'` are representatives of reachable names of `P`. -/
theorem reachableName_mergeSCC (hρ : SCCRep P.methods ρ) {r : C}
    (h : (P.mergeSCC ρ).toPos.ReachableName r) : ∃ c, P.toPos.ReachableName c ∧ ρ c = r := by
  induction h with
  | @tnI t c ht hc =>
    change Sum.map id ρ (P.tnI.α t) = _ at hc
    rcases hα : P.tnI.α t with a | c₀
    · rw [hα] at hc; simp at hc
    · rw [hα] at hc
      exact ⟨c₀, .tnI ht hα, Sum.inr.inj hc⟩
  | @method m' t c hm' _ ht hc ih =>
    obtain ⟨m, ⟨hm, -⟩, rfl⟩ := hm'
    obtain ⟨c₀, hc₀, hρ₀⟩ := ih
    have hh : P.toPos.ReachableName m.abstractTask :=
      P.toPos.reachable_of_path ((hρ.iff.1 hρ₀).1) hc₀
    change Sum.map id ρ (m.subtasks.α t) = _ at hc
    rcases hα : m.subtasks.α t with a | c₁
    · rw [hα] at hc; simp at hc
    · rw [hα] at hc
      exact ⟨c₁, .method hm hh ht hα, Sum.inr.inj hc⟩

/-- The reachable names strictly below `c` in the decomposition graph. -/
def below (P : Problem F A C I) (c : C) : Set C :=
  {d | P.toPos.ReachableName d ∧ Relation.ReflTransGen (DEdge P.methods) c d ∧
    ¬ Relation.ReflTransGen (DEdge P.methods) d c}

theorem below_congr {a b : C} (h : SameSCC P.methods a b) : P.below a = P.below b := by
  ext d
  exact ⟨fun ⟨hd, h1, h2⟩ => ⟨hd, h.2.trans h1, fun h' => h2 (h'.trans h.2)⟩,
    fun ⟨hd, h1, h2⟩ => ⟨hd, h.1.trans h1, fun h' => h2 (h'.trans h.1)⟩⟩

/-- **`P'` is acyclic** (if only finitely many compound task names are reachable). -/
theorem isACYC_mergeSCC (hs : P.IsMostlyACYC) (hρ : SCCRep P.methods ρ)
    (hfin : {c | P.toPos.ReachableName c}.Finite) : (P.mergeSCC ρ).IsACYC := by
  obtain ⟨le, hle⟩ := hs
  refine HTN.Problem.isAcyclic_of_rank _ (fun c => (P.below c).ncard) ?_
  rintro m' ⟨hm', hr⟩ t ht c hc
  obtain ⟨m, ⟨hm, hnl⟩, rfl⟩ := hm'
  obtain ⟨c₀, hc₀, hρ₀⟩ := reachableName_mergeSCC hρ hr
  have hh : P.toPos.ReachableName m.abstractTask :=
    P.toPos.reachable_of_path ((hρ.iff.1 hρ₀).1) hc₀
  change Sum.map id ρ (m.subtasks.α t) = _ at hc
  rcases hα : m.subtasks.α t with a | c₁
  · rw [hα] at hc; simp at hc
  · rw [hα] at hc
    obtain rfl := Sum.inr.inj hc
    have ht' : t ∈ m.subtasks.T := ht
    have hc₁ : P.toPos.ReachableName c₁ := .method hm hh ht' hα
    have hedge : DEdge P.methods m.abstractTask c₁ := ⟨m, hm, rfl, t, ht', hα⟩
    -- `c₁` does not reach back
    have hnot : ¬ Relation.ReflTransGen (DEdge P.methods) c₁ m.abstractTask := by
      intro hback
      have hmr : P.toPos.ReachableMethod m := ⟨hm, hh⟩
      rcases Nat.lt_or_ge 1 m.subtasks.T.card with h1 | h1
      · exact (hle.big m hmr h1 t ht' c₁ hα).2 (hle.le_of_path hback hc₁).2
      · have h1' : m.subtasks.T.card = 1 := le_antisymm h1 (Finset.card_pos.2 ⟨t, ht'⟩)
        obtain ⟨t', hT⟩ := Finset.card_eq_one.1 h1'
        have : t = t' := by rw [hT] at ht'; simpa using ht'
        subst this
        exact hnl ⟨t, c₁, hT, hα, hρ.eq _ _ ⟨hback, .single hedge⟩⟩
    show (P.below (ρ c₁)).ncard < (P.below (ρ m.abstractTask)).ncard
    rw [← below_congr (hρ.same c₁), ← below_congr (hρ.same m.abstractTask)]
    refine Set.ncard_lt_ncard ?_ (hfin.subset fun d hd => hd.1)
    refine ⟨fun d ⟨hd, h1, h2⟩ => ⟨hd, (Relation.ReflTransGen.single hedge).trans h1,
      fun h' => h2 (h'.trans (.single hedge))⟩, fun hsub => ?_⟩
    exact (hsub ⟨hc₁, .single hedge, hnot⟩).2.2 .refl

section Sim

variable [Infinite I]

/-- Primitive networks reachable in `P` are reachable in `P'` (up to isomorphism). -/
theorem exists_decomp_mergeSCC (hP : P.WF) {tn : TaskNetwork I A C}
    (hd : DecomposesTo P.methods P.tnI tn) (hp : tn.IsPrimitive) :
    ∃ u, DecomposesTo (P.mergeSCC ρ).methods (P.mergeSCC ρ).tnI u ∧ tn.Iso u := by
  obtain ⟨u, hu, hiso⟩ := decomposesTo_mergeMethods (ρ := ρ) hd hP.tnI
  exact ⟨u, hu, (TaskNetwork.iso_mapC_of_isPrimitive hp).trans hiso⟩

/-- Primitive networks reachable in `P'` are reachable in `P` (up to isomorphism). -/
theorem exists_decomp_of_mergeSCC (hP : P.WF) (hs : P.IsMostlyACYC) (hρ : SCCRep P.methods ρ)
    {u : TaskNetwork I A C} (hd : DecomposesTo (P.mergeSCC ρ).methods (P.mergeSCC ρ).tnI u)
    (hp : u.IsPrimitive) : ∃ tn, DecomposesTo P.methods P.tnI tn ∧ u.Iso tn := by
  obtain ⟨le, hle⟩ := hs
  have hR : ClosedUnder P.toPos.ReachableName P.methods :=
    fun m hm hr t ht c hc => .method hm hr ht hc
  have hchain : ∀ c₀, P.toPos.ReachableName c₀ → ∀ m ∈ P.methods, ¬ m.IsLoop ρ →
      ρ c₀ = ρ m.abstractTask → Chain P.methods c₀ m.abstractTask := by
    intro c₀ hc₀ m _ _ he
    have h := hρ.iff.1 he
    exact hle.chain_of_cycle h.1 h.2 hc₀
  obtain ⟨tn, hd', hiso⟩ := exists_decomposesTo_of_merge hP.methods hR hchain hd
    (TaskNetwork.mapC_wf hP.tnI) hP.tnI (fun t ht c hc => .tnI ht hc) (TaskNetwork.Iso.refl _)
  have hp' : tn.IsPrimitive := TaskNetwork.isPrimitive_of_mapC (hiso.isPrimitive hp)
  exact ⟨tn, hd', hiso.trans (TaskNetwork.iso_mapC_of_isPrimitive hp').symm⟩

theorem solvable_mergeSCC_iff (hP : P.WF) (hs : P.IsMostlyACYC) (hρ : SCCRep P.methods ρ) :
    (P.mergeSCC ρ).Solvable ↔ P.Solvable := by
  rw [solvable_iff_decomp _ (mergeSCC_wf hP), solvable_iff_decomp _ hP]
  constructor
  · rintro ⟨u, hd, hp, l, as, s, hl, has, hrun, hg⟩
    obtain ⟨tn, hd', hiso⟩ := exists_decomp_of_mergeSCC hP hs hρ hd hp
    obtain ⟨l', hl', has'⟩ := (hiso.exists_linearization_actionSeq_iff as).1 ⟨l, hl, has⟩
    exact ⟨tn, hd', hiso.isPrimitive hp, l', as, s, hl', has', (mergeSCC_run P as _ _).1 hrun, hg⟩
  · rintro ⟨tn, hd, hp, l, as, s, hl, has, hrun, hg⟩
    obtain ⟨u, hd', hiso⟩ := exists_decomp_mergeSCC (ρ := ρ) hP hd hp
    obtain ⟨l', hl', has'⟩ := (hiso.exists_linearization_actionSeq_iff as).1 ⟨l, hl, has⟩
    exact ⟨u, hd', hiso.isPrimitive hp, l', as, s, hl', has', (mergeSCC_run P as _ _).2 hrun, hg⟩

theorem solvableTI_mergeSCC_iff (hP : P.WF) (hs : P.IsMostlyACYC) (hρ : SCCRep P.methods ρ) :
    (P.mergeSCC ρ).SolvableTI ↔ P.SolvableTI := by
  rw [solvableTI_iff_decomp _ (mergeSCC_wf hP), solvableTI_iff_decomp _ hP]
  constructor
  · rintro ⟨u, hd, hp, l, as, π, s, hl, has, hsub, hrun, hg⟩
    obtain ⟨tn, hd', hiso⟩ := exists_decomp_of_mergeSCC hP hs hρ hd hp
    obtain ⟨l', hl', has'⟩ := (hiso.exists_linearization_actionSeq_iff as).1 ⟨l, hl, has⟩
    exact ⟨tn, hd', hiso.isPrimitive hp, l', as, π, s, hl', has', hsub,
      (mergeSCC_run P π _ _).1 hrun, hg⟩
  · rintro ⟨tn, hd, hp, l, as, π, s, hl, has, hsub, hrun, hg⟩
    obtain ⟨u, hd', hiso⟩ := exists_decomp_mergeSCC (ρ := ρ) hP hd hp
    obtain ⟨l', hl', has'⟩ := (hiso.exists_linearization_actionSeq_iff as).1 ⟨l, hl, has⟩
    exact ⟨u, hd', hiso.isPrimitive hp, l', as, π, s, hl', has', hsub,
      (mergeSCC_run P π _ _).2 hrun, hg⟩

/-- **Lemma 4.2.2.** For a mostly-acyclic problem `P` and representatives `ρ` of the strongly
connected components, the collapsed problem `P'` (same state variables, task names, actions,
initial state and goal) is acyclic, it has the same primitive task networks reachable from its
initial task network as `P` (up to isomorphism), and hence it has a solution iff `P` has one, in
the HTN as in the TIHTN setting. -/
theorem lem_4_2_2 (hP : P.WF) (hs : P.IsMostlyACYC) (hρ : SCCRep P.methods ρ)
    (hfin : {c | P.toPos.ReachableName c}.Finite) :
    (P.mergeSCC ρ).IsACYC ∧ (P.mergeSCC ρ).WF ∧
      (∀ tn, tn.IsPrimitive → DecomposesTo P.methods P.tnI tn →
        ∃ u, DecomposesTo (P.mergeSCC ρ).methods (P.mergeSCC ρ).tnI u ∧ tn.Iso u) ∧
      (∀ u, u.IsPrimitive → DecomposesTo (P.mergeSCC ρ).methods (P.mergeSCC ρ).tnI u →
        ∃ tn, DecomposesTo P.methods P.tnI tn ∧ u.Iso tn) ∧
      ((P.mergeSCC ρ).Solvable ↔ P.Solvable) ∧ ((P.mergeSCC ρ).SolvableTI ↔ P.SolvableTI) :=
  ⟨isACYC_mergeSCC hs hρ hfin, mergeSCC_wf hP, fun _ hp hd => exists_decomp_mergeSCC hP hd hp,
    fun _ hp hd => exists_decomp_of_mergeSCC hP hs hρ hd hp, solvable_mergeSCC_iff hP hs hρ,
    solvableTI_mergeSCC_iff hP hs hρ⟩

theorem executableIn_mergeSCC (tn : TaskNetwork I A C) (s : Set F) :
    (P.mergeSCC ρ).ExecutableIn tn s ↔ P.ExecutableIn tn s := by
  unfold ExecutableIn
  refine and_congr Iff.rfl (forall_congr' fun l => forall_congr' fun as => ?_)
  exact imp_congr_right fun _ => imp_congr_right fun _ =>
    exists_congr fun s' => mergeSCC_run P as s s'

theorem generates_mergeSCC (tn : TaskNetwork I A C) (s s' : Set F) :
    (P.mergeSCC ρ).Generates tn s s' ↔ P.Generates tn s s' := by
  unfold Generates
  exact exists_congr fun l => exists_congr fun as => and_congr Iff.rfl (and_congr Iff.rfl
    (mergeSCC_run P as s s'))

theorem isPrimitive_of_oiReach {tn tnS : TaskNetwork I A C} (hoi : OIReach tn tnS)
    (hp : tnS.IsPrimitive) : tn.IsPrimitive := by
  intro t ht
  obtain ⟨a, ha⟩ := hp t (by rw [hoi.T]; exact ht)
  exact ⟨a, by rw [← hoi.α]; exact ha⟩

theorem isPrimitive_of_tiReach {tn tn' : TaskNetwork I A C} (hti : TIReach tn tn')
    (hp : tn'.IsPrimitive) : tn.IsPrimitive := by
  intro t ht
  obtain ⟨a, ha⟩ := hp t (hti.T_sub ht)
  exact ⟨a, by rw [← hti.α_old t ht]; exact ha⟩

/-- **Corollary 4.2.3** (up to isomorphism): `Sol(P)` and `Sol(P')` agree up to the identifiers
of the tasks, and so do the TIHTN solutions. -/
theorem cor_4_2_3 (hP : P.WF) (hs : P.IsMostlyACYC) (hρ : SCCRep P.methods ρ) :
    (∀ tnS ∈ P.Sol, ∃ u ∈ (P.mergeSCC ρ).Sol, tnS.Iso u) ∧
      (∀ u ∈ (P.mergeSCC ρ).Sol, ∃ tnS ∈ P.Sol, u.Iso tnS) ∧
      (∀ tnS ∈ P.SolTI, ∃ u ∈ (P.mergeSCC ρ).SolTI, tnS.Iso u) ∧
      (∀ u ∈ (P.mergeSCC ρ).SolTI, ∃ tnS ∈ P.SolTI, u.Iso tnS) := by
  have hP' := mergeSCC_wf (ρ := ρ) hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro tnS ⟨hex, hgoal, tn, hdec, hoi⟩
    obtain ⟨u, hu, σ, hσ⟩ := exists_decomp_mergeSCC (ρ := ρ) hP hdec
      (isPrimitive_of_oiReach hoi hex.1)
    obtain ⟨u', hoi', hσ'⟩ := OIReach.isoVia hoi (HTN.DecomposesTo.wf hdec hP.tnI)
      (HTN.DecomposesTo.wf hu hP'.tnI) hσ
    refine ⟨u', ⟨(executableIn_mergeSCC _ _).2 (P.executableIn_of_iso hσ'.iso hex),
      fun s hg => hgoal s (P.generates_of_iso hσ'.iso ((generates_mergeSCC _ _ _).1 hg)),
      u, hu, hoi'⟩, hσ'.iso⟩
  · rintro u' ⟨hex, hgoal, u, hdec, hoi⟩
    obtain ⟨tn, htn, σ, hσ⟩ := exists_decomp_of_mergeSCC hP hs hρ hdec
      (isPrimitive_of_oiReach hoi hex.1)
    obtain ⟨tn', hoi', hσ'⟩ := OIReach.isoVia hoi (HTN.DecomposesTo.wf hdec hP'.tnI)
      (HTN.DecomposesTo.wf htn hP.tnI) hσ
    refine ⟨tn', ⟨P.executableIn_of_iso hσ'.iso ((executableIn_mergeSCC _ _).1 hex),
      fun s hg => hgoal s ((generates_mergeSCC _ _ _).2 (P.generates_of_iso hσ'.iso hg)),
      tn, htn, hoi'⟩, hσ'.iso⟩
  · rintro tnS ⟨hex, hgoal, tn, tn', hdec, hti, hoi⟩
    obtain ⟨u, hu, σ, hσ⟩ := exists_decomp_mergeSCC (ρ := ρ) hP hdec
      (isPrimitive_of_tiReach hti (isPrimitive_of_oiReach hoi hex.1))
    have hwf := HTN.DecomposesTo.wf hdec hP.tnI
    have hwfu := HTN.DecomposesTo.wf hu hP'.tnI
    obtain ⟨σ₁, u₁, hti', hσ₁⟩ := TIReach.isoVia hti hwf hwfu hσ
    obtain ⟨u₂, hoi', hσ₂⟩ := OIReach.isoVia hoi (TIReach.wf hti hwf) (TIReach.wf hti' hwfu) hσ₁
    refine ⟨u₂, ⟨(executableIn_mergeSCC _ _).2 (P.executableIn_of_iso hσ₂.iso hex),
      fun s hg => hgoal s (P.generates_of_iso hσ₂.iso ((generates_mergeSCC _ _ _).1 hg)),
      u, u₁, hu, hti', hoi'⟩, hσ₂.iso⟩
  · rintro u' ⟨hex, hgoal, u, u₁, hdec, hti, hoi⟩
    obtain ⟨tn, htn, σ, hσ⟩ := exists_decomp_of_mergeSCC hP hs hρ hdec
      (isPrimitive_of_tiReach hti (isPrimitive_of_oiReach hoi hex.1))
    have hwfu := HTN.DecomposesTo.wf hdec hP'.tnI
    have hwf := HTN.DecomposesTo.wf htn hP.tnI
    obtain ⟨σ₁, tn₁, hti', hσ₁⟩ := TIReach.isoVia hti hwfu hwf hσ
    obtain ⟨tn₂, hoi', hσ₂⟩ := OIReach.isoVia hoi (TIReach.wf hti hwfu) (TIReach.wf hti' hwf) hσ₁
    refine ⟨tn₂, ⟨P.executableIn_of_iso hσ₂.iso ((executableIn_mergeSCC _ _).1 hex),
      fun s hg => hgoal s ((generates_mergeSCC _ _ _).2 (P.generates_of_iso hσ₂.iso hg)),
      tn, tn₁, htn, hti', hoi'⟩, hσ₂.iso⟩

end Sim

end Problem

end Article

end HTN
