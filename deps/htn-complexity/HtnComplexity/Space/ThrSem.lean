import HtnComplexity.Computable.PoNet
import HtnPlanning.Computable.Classes
import HtnPlanning.Core.DecompositionIso
import HtnPlanning.Progression.ProgressionSound
/-!
# Regular HTN with an initial task network, as a system of threads

This is layer (A) of the planner P-REG (`TABLE4-PLAN.md` §4, `NOTES.md` §63).  A regular domain
description `d` together with an instance whose initial task network is an *arbitrary*
(partially ordered) network of `k` tasks behaves like `k` **threads**, one per initial task:

* a thread whose initial task has not been touched yet is `pend`;
* a thread whose current compound task is `c` (and nothing else is left of it) is `cur c`;
* a thread which is running the body of the method number `μ` of `d`, of whose primitive
  subtasks those in `D` have been executed, is `run μ D`;
* a finished thread is `fin`.

A regular body has at most one compound subtask, ordered after all the others, so this is all a
thread can be.  The threads interleave freely, except that a thread may only start when every
thread whose initial task precedes its own (the relation `O` on the slots) is idle.

`HTN.Space.Thr.TStep` is the step relation of this system, and the main theorem of the file,
`HTN.Space.Thr.solvable_iff_tsolv`, says that the described problem is solvable exactly when the
thread system reaches a configuration in which every thread is idle and the goal holds —
provided the initial task network is isomorphic to the canonical network of the initial
configuration (`HTN.Space.Thr.toTN`), which is what a slot numbering of the identifiers gives.

The proof relates a thread configuration to the search nodes of the progression search
(`HtnPlanning/Progression/Progression.lean`) whose task network is isomorphic to its canonical
network, and simulates each step in both directions.
-/

namespace HTN

namespace Space

namespace Thr

open Syn

/-! ### Methods of a description, by number -/

/-- The method number `μ` of a domain description. -/
def mth (d : DomDesc) (μ : ℕ) : MethodDesc := d.methods.getD μ (0, TnDesc.nil)

/-- The body of the method number `μ`. -/
def body (d : DomDesc) (μ : ℕ) : TnDesc := (mth d μ).2

/-- The compound task decomposed by the method number `μ`. -/
def head (d : DomDesc) (μ : ℕ) : ℕ := (mth d μ).1

/-- The primitive subtasks of the method number `μ`. -/
def prims (d : DomDesc) (μ : ℕ) : Finset ℕ :=
  (body d μ).ids.toFinset.filter (fun x => ((body d μ).label x).isLeft)

/-- The compound subtask of the method number `μ`, if any. -/
def tail (d : DomDesc) (μ : ℕ) : Option ℕ := (body d μ).compoundNames.head?

/-! ### Thread configurations -/

/-- **The state of a thread.** -/
inductive TSt where
  | pend
  | cur (c : ℕ)
  | run (μ : ℕ) (D : Finset ℕ)
  | fin
  deriving DecidableEq

/-- **A thread configuration**: the current state and the state of every thread. -/
structure Cfg where
  st : Set ℕ
  th : ℕ → TSt

/-- The parameters of a thread system: the domain description, the number of threads, the
labels of the initial tasks and the order between them. -/
structure Par where
  d : DomDesc
  k : ℕ
  lab : ℕ → ℕ ⊕ ℕ
  O : ℕ → ℕ → Prop

/-- The canonical identifier of the task number `y` of the thread `j` (`0` for the single task
of a `pend` or `cur` thread, `x + 1` for the subtask `x` of a running body). -/
def tid (j y : ℕ) : ℕ := Nat.pair j y

@[simp] theorem unpair_tid (j y : ℕ) : (tid j y).unpair = (j, y) := Nat.unpair_pair j y

theorem tid_inj {j y j' y' : ℕ} : tid j y = tid j' y' ↔ j = j' ∧ y = y' := by
  constructor
  · intro h
    have := congrArg Nat.unpair h
    simpa using this
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The tasks of a thread in the canonical network. -/
def thTasks (d : DomDesc) : TSt → ℕ → Finset ℕ
  | .pend, j => {tid j 0}
  | .cur _, j => {tid j 0}
  | .run μ D, j => ((body d μ).ids.toFinset \ D).image (fun x => tid j (x + 1))
  | .fin, _ => ∅

/-- The label of the task number `y` of a thread. -/
def thLabel (d : DomDesc) (lab : ℕ → ℕ ⊕ ℕ) : TSt → ℕ → ℕ → ℕ ⊕ ℕ
  | .pend, j, 0 => lab j
  | .cur c, _, 0 => Sum.inr c
  | .run μ _, _, y + 1 => (body d μ).label y
  | _, _, _ => Sum.inl 0

variable (P : Par)

/-- The tasks of the canonical network. -/
def tasks (th : ℕ → TSt) : Finset ℕ :=
  (Finset.range P.k).biUnion (fun j => thTasks P.d (th j) j)

/-- The ordering of the canonical network, before restriction to its tasks. -/
def rel (th : ℕ → TSt) (a b : ℕ) : Prop :=
  (a.unpair.1 = b.unpair.1 ∧ ∃ μ D, th a.unpair.1 = .run μ D ∧ 0 < a.unpair.2 ∧
      0 < b.unpair.2 ∧ (body P.d μ).ordOf (a.unpair.2 - 1) (b.unpair.2 - 1)) ∨
    (a.unpair.1 ≠ b.unpair.1 ∧ P.O a.unpair.1 b.unpair.1)

/-- **The canonical network of a thread configuration.** -/
def toTN (th : ℕ → TSt) : TaskNetwork ℕ ℕ ℕ where
  T := tasks P th
  ord a b := a ∈ tasks P th ∧ b ∈ tasks P th ∧ rel P th a b
  α a := thLabel P.d P.lab (th a.unpair.1) a.unpair.1 a.unpair.2

/-- A thread is *idle* iff it has no task left. -/
def Idle (th : ℕ → TSt) (i : ℕ) : Prop := thTasks P.d (th i) i = ∅

/-- The state a thread is left in by `close`. -/
def closed (d : DomDesc) (μ : ℕ) : TSt :=
  match tail d μ with
  | some c => .cur c
  | none => .fin

/-- **The step relation of the thread system.** -/
inductive TStep : Cfg → Cfg → Prop
  /-- A pending compound initial task is decomposed. -/
  | expandP {c : Cfg} {j μ : ℕ} (hj : j < P.k) (hs : c.th j = .pend)
      (hl : P.lab j = Sum.inr (head P.d μ)) (hμ : μ < P.d.methods.length)
      (hpre : ∀ i < P.k, P.O i j → Idle P c.th i) :
      TStep c ⟨c.st, Function.update c.th j (.run μ ∅)⟩
  /-- The current compound task of a thread is decomposed. -/
  | expandC {c : Cfg} {j μ : ℕ} (hj : j < P.k) (hs : c.th j = .cur (head P.d μ))
      (hμ : μ < P.d.methods.length) :
      TStep c ⟨c.st, Function.update c.th j (.run μ ∅)⟩
  /-- A primitive subtask of a running body is executed. -/
  | exec {c : Cfg} {j μ x a : ℕ} {D : Finset ℕ} (hj : j < P.k) (hs : c.th j = .run μ D)
      (hx : x ∈ prims P.d μ) (hxD : x ∉ D) (hpre : ∀ y, (body P.d μ).ordOf y x → y ∈ D)
      (hl : (body P.d μ).label x = Sum.inl a) (happ : P.d.prec a ⊆ c.st) :
      TStep c ⟨(c.st \ P.d.del a) ∪ P.d.add a, Function.update c.th j (.run μ (insert x D))⟩
  /-- A body whose primitive subtasks have all been executed is closed. -/
  | close {c : Cfg} {j μ : ℕ} {D : Finset ℕ} (hj : j < P.k) (hs : c.th j = .run μ D)
      (hD : prims P.d μ ⊆ D) :
      TStep c ⟨c.st, Function.update c.th j (closed P.d μ)⟩
  /-- A pending primitive initial task is executed. -/
  | execP {c : Cfg} {j a : ℕ} (hj : j < P.k) (hs : c.th j = .pend) (hl : P.lab j = Sum.inl a)
      (hpre : ∀ i < P.k, P.O i j → Idle P c.th i) (happ : P.d.prec a ⊆ c.st) :
      TStep c ⟨(c.st \ P.d.del a) ∪ P.d.add a, Function.update c.th j .fin⟩

/-- The initial thread configuration. -/
def initCfg (s₀ : Set ℕ) : Cfg := ⟨s₀, fun _ => .pend⟩

/-- **Solvability of the thread system**: a configuration in which every thread is idle and
the goal holds is reachable. -/
def TSolv (s₀ g : Set ℕ) : Prop :=
  ∃ c, Relation.ReflTransGen (TStep P) (initCfg s₀) c ∧ (∀ j < P.k, Idle P c.th j) ∧ g ⊆ c.st

/-- The hypotheses on the parameters: a regular domain and a strict order on the slots. -/
structure Good : Prop where
  reg : P.d.MethodsReg
  irrefl : ∀ i, ¬ P.O i i
  trans : ∀ {a b c}, P.O a b → P.O b c → P.O a c

/-! ### Basic facts about the canonical network -/

section Basic

variable {P}

theorem mem_thTasks_fst {s : TSt} {j a : ℕ} (h : a ∈ thTasks P.d s j) : a.unpair.1 = j := by
  cases s with
  | pend => simp [thTasks] at h; subst h; simp
  | cur c => simp [thTasks] at h; subst h; simp
  | run μ D =>
    simp only [thTasks, Finset.mem_image] at h
    obtain ⟨x, -, rfl⟩ := h
    simp
  | fin => simp [thTasks] at h

theorem mem_thTasks_run {μ j a : ℕ} {D : Finset ℕ} :
    a ∈ thTasks P.d (.run μ D) j ↔ ∃ x ∈ (body P.d μ).ids, x ∉ D ∧ a = tid j (x + 1) := by
  simp only [thTasks, Finset.mem_image, Finset.mem_sdiff, List.mem_toFinset]
  constructor
  · rintro ⟨x, ⟨hx, hxD⟩, rfl⟩
    exact ⟨x, hx, hxD, rfl⟩
  · rintro ⟨x, hx, hxD, rfl⟩
    exact ⟨x, ⟨hx, hxD⟩, rfl⟩

theorem mem_tasks {th : ℕ → TSt} {a : ℕ} :
    a ∈ tasks P th ↔ a.unpair.1 < P.k ∧ a ∈ thTasks P.d (th a.unpair.1) a.unpair.1 := by
  simp only [tasks, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, ha⟩
    have := mem_thTasks_fst ha
    subst this
    exact ⟨hj, ha⟩
  · rintro ⟨hj, ha⟩
    exact ⟨_, hj, ha⟩

theorem mem_tasks_of {th : ℕ → TSt} {j a : ℕ} (hj : j < P.k) (ha : a ∈ thTasks P.d (th j) j) :
    a ∈ tasks P th := by
  simp only [tasks, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨j, hj, ha⟩

theorem toTN_ord {th : ℕ → TSt} {a b : ℕ} :
    (toTN P th).ord a b ↔ a ∈ tasks P th ∧ b ∈ tasks P th ∧ rel P th a b := Iff.rfl

@[simp] theorem toTN_T (th : ℕ → TSt) : (toTN P th).T = tasks P th := rfl

theorem toTN_α (th : ℕ → TSt) (a : ℕ) :
    (toTN P th).α a = thLabel P.d P.lab (th a.unpair.1) a.unpair.1 a.unpair.2 := rfl

/-- **The canonical network is well formed.** -/
theorem toTN_wf (hP : Good P) (th : ℕ → TSt) : (toTN P th).WF where
  mem_left h := h.1
  mem_right h := h.2.1
  irrefl a h := by
    rcases h.2.2 with ⟨-, μ, D, -, -, -, hord⟩ | ⟨hne, -⟩
    · exact (body P.d μ).toTaskNetwork_wf.irrefl _ hord
    · exact hne rfl
  trans := by
    intro a b c hab hbc
    refine ⟨hab.1, hbc.2.1, ?_⟩
    rcases hab.2.2 with ⟨h1, μ, D, hs, ha0, hb0, hord1⟩ | ⟨h1, hO1⟩ <;>
      rcases hbc.2.2 with ⟨h2, μ', D', hs', hb0', hc0, hord2⟩ | ⟨h2, hO2⟩
    · rw [h1] at hs
      rw [hs] at hs'
      cases hs'
      exact Or.inl ⟨h1.trans h2, μ, D, by rw [h1]; exact hs, ha0, hc0,
        (body P.d μ).toTaskNetwork_wf.trans hord1 hord2⟩
    · exact Or.inr ⟨by rw [h1]; exact h2, by rw [h1]; exact hO2⟩
    · exact Or.inr ⟨by rw [← h2]; exact h1, by rw [← h2]; exact hO1⟩
    · refine Or.inr ⟨fun h => ?_, hP.trans hO1 hO2⟩
      rw [h] at hO1
      exact hP.irrefl _ (hP.trans hO1 hO2)

/-- Two task networks with the same tasks, and the same ordering and labels on them, are
isomorphic. -/
theorem iso_of_same {tn tn' : TaskNetwork ℕ ℕ ℕ} (hT : tn.T = tn'.T)
    (hord : ∀ a ∈ tn.T, ∀ b ∈ tn.T, (tn.ord a b ↔ tn'.ord a b))
    (hα : ∀ a ∈ tn.T, tn.α a = tn'.α a) : tn.Iso tn' := by
  refine ⟨id, ?_, fun a ha b hb => hord a ha b hb, fun a ha => hα a ha⟩
  rw [← hT]
  exact Set.bijOn_id _

theorem tasks_update {th : ℕ → TSt} {j : ℕ} {s : TSt} {a : ℕ} :
    a ∈ tasks P (Function.update th j s) ↔
      (a.unpair.1 = j ∧ j < P.k ∧ a ∈ thTasks P.d s j) ∨ (a.unpair.1 ≠ j ∧ a ∈ tasks P th) := by
  rw [mem_tasks, mem_tasks]
  by_cases h : a.unpair.1 = j
  · subst h
    simp
  · simp [h]

theorem thTasks_run_eq_empty {μ j : ℕ} {D : Finset ℕ} :
    thTasks P.d (.run μ D) j = ∅ ↔ ∀ x ∈ (body P.d μ).ids, x ∈ D := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h x hx
    by_contra hxD
    exact h _ (mem_thTasks_run.2 ⟨x, hx, hxD, rfl⟩)
  · intro h a ha
    obtain ⟨x, hx, hxD, -⟩ := mem_thTasks_run.1 ha
    exact hxD (h x hx)

/-- `rel` only looks at which method a thread runs, not at how far it has got. -/
theorem rel_congr {th th' : ℕ → TSt} {a b : ℕ}
    (h : ∀ μ, (∃ D, th a.unpair.1 = .run μ D) ↔ (∃ D, th' a.unpair.1 = .run μ D)) :
    rel P th a b ↔ rel P th' a b := by
  unfold rel
  refine or_congr (and_congr_right fun _ => ?_) Iff.rfl
  constructor
  · rintro ⟨μ, D, hs, rest⟩
    obtain ⟨D', hD'⟩ := (h μ).1 ⟨D, hs⟩
    exact ⟨μ, D', hD', rest⟩
  · rintro ⟨μ, D, hs, rest⟩
    obtain ⟨D', hD'⟩ := (h μ).2 ⟨D, hs⟩
    exact ⟨μ, D', hD', rest⟩

theorem rel_update_of_ne {th : ℕ → TSt} {j : ℕ} {s : TSt} {a b : ℕ} (ha : a.unpair.1 ≠ j) :
    rel P (Function.update th j s) a b ↔ rel P th a b :=
  rel_congr fun μ => by rw [Function.update_of_ne ha]

theorem label_update_of_ne {th : ℕ → TSt} {j : ℕ} {s : TSt} {a : ℕ} (ha : a.unpair.1 ≠ j) :
    (toTN P (Function.update th j s)).α a = (toTN P th).α a := by
  simp only [toTN_α, Function.update_of_ne ha]

end Basic

/-! ### Regular bodies -/

section Regular

variable {P}

theorem mth_mem {d : DomDesc} {μ : ℕ} (hμ : μ < d.methods.length) : mth d μ ∈ d.methods := by
  unfold mth
  rw [List.getD_eq_getElem _ _ hμ]
  exact List.getElem_mem hμ

theorem exists_mth_eq {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) :
    ∃ μ < d.methods.length, mth d μ = e := by
  obtain ⟨μ, hμ, rfl⟩ := List.mem_iff_getElem.1 he
  exact ⟨μ, hμ, by unfold mth; rw [List.getD_eq_getElem _ _ hμ]⟩

theorem body_isRegular {d : DomDesc} (hreg : d.MethodsReg) {μ : ℕ} (hμ : μ < d.methods.length) :
    (body d μ).toTaskNetwork.IsRegular :=
  hreg _ (mth_mem hμ)

/-- In a regular body every other subtask precedes a compound one. -/
theorem ordOf_of_compound {d : DomDesc} (hreg : d.MethodsReg) {μ : ℕ}
    (hμ : μ < d.methods.length) {z x c : ℕ} (hz : z ∈ (body d μ).ids)
    (hl : (body d μ).label z = Sum.inr c) (hx : x ∈ (body d μ).ids) (hxz : x ≠ z) :
    (body d μ).ordOf x z :=
  (body_isRegular hreg hμ).2 z (List.mem_toFinset.2 hz) ⟨c, hl⟩ x (List.mem_toFinset.2 hx) hxz

/-- A regular body has at most one compound subtask. -/
theorem compound_unique {d : DomDesc} (hreg : d.MethodsReg) {μ : ℕ} (hμ : μ < d.methods.length)
    {z z' c c' : ℕ} (hz : z ∈ (body d μ).ids) (hl : (body d μ).label z = Sum.inr c)
    (hz' : z' ∈ (body d μ).ids) (hl' : (body d μ).label z' = Sum.inr c') : z = z' :=
  (body_isRegular hreg hμ).1 z (List.mem_toFinset.2 hz) z' (List.mem_toFinset.2 hz') ⟨c, hl⟩
    ⟨c', hl'⟩

theorem tail_eq_some {d : DomDesc} (hreg : d.MethodsReg) {μ : ℕ} (hμ : μ < d.methods.length)
    {z c : ℕ} (hz : z ∈ (body d μ).ids) (hl : (body d μ).label z = Sum.inr c) :
    tail d μ = some c := by
  unfold tail
  have hmem : c ∈ (body d μ).compoundNames := TnDesc.mem_compoundNames.2 ⟨z, hz, hl⟩
  rcases hh : (body d μ).compoundNames with _ | ⟨c', l⟩
  · rw [hh] at hmem
    simp at hmem
  · have hc' : c' ∈ (body d μ).compoundNames := by rw [hh]; simp
    obtain ⟨z', hz', hl'⟩ := TnDesc.mem_compoundNames.1 hc'
    have := compound_unique hreg hμ hz hl hz' hl'
    subst this
    rw [hl] at hl'
    simp only [Sum.inr.injEq] at hl'
    simp [hl']

theorem tail_eq_none {d : DomDesc} {μ : ℕ}
    (h : ∀ z ∈ (body d μ).ids, ((body d μ).label z).isLeft) : tail d μ = none := by
  unfold tail
  rcases hh : (body d μ).compoundNames with _ | ⟨c', l⟩
  · rfl
  · have hc' : c' ∈ (body d μ).compoundNames := by rw [hh]; simp
    obtain ⟨z', hz', hl'⟩ := TnDesc.mem_compoundNames.1 hc'
    have := h z' hz'
    rw [hl'] at this
    simp at this

theorem mem_prims {d : DomDesc} {μ x : ℕ} :
    x ∈ prims d μ ↔ x ∈ (body d μ).ids ∧ ((body d μ).label x).isLeft := by
  simp [prims]

end Regular

end Thr

end Space

end HTN
