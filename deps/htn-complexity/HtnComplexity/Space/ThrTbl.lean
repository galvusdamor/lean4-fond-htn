import HtnComplexity.Space.ThrSim
import HtnComplexity.Space.SeqGadget
/-!
# The thread system as an action table

Layer (B) of the planner P-REG (`NOTES.md` §64.3).  The thread system of
`HtnComplexity/Space/ThrSem.lean` is simulated by an action table `HTN.Space.Thr.thrTbl d N`
over an inductive type of facts `HTN.Space.Thr.TF`; the table depends only on the domain
description `d` and on a bound `N` on the number of threads (and of nodes of the ordering graph).

The instance enters only through the initial fact set `HTN.Space.Thr.initF`: the facts of the
initial state, the labels of the initial tasks (`lab j x`, and `nop j` for the primitive tasks the
domain does not mention), the number of threads (`len k`), the listed ordering pairs as edges of a
graph `E` on node numbers, a closed superset `Cl` of `E` (`cl`) and a set `NC` of pairs outside
`Cl` (`nc`), the certificate for "`i` does not reach `j`".

This file holds the definitions and the transfer of reachability along an injective encoding of
the facts into numbers; the simulation is in `ThrTblSound.lean` / `ThrTblComp.lean`.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG

/-- **The facts of the thread table.** -/
inductive TF where
  /-- A fact of the planning problem. -/
  | inst (v : ℕ)
  /-- The initial task of the thread `j` is `x`, and is still pending (or is an unknown
  primitive task). -/
  | lab (j : ℕ) (x : ℕ ⊕ ℕ)
  /-- The initial task of the thread `j` is a primitive task the domain does not mention, and is
  still pending. -/
  | nop (j : ℕ)
  /-- There are `p` threads. -/
  | len (p : ℕ)
  /-- An inert witness fact: the node `a` has number `p`. -/
  | wit (p a : ℕ)
  /-- A listed ordering pair between the nodes numbered `x` and `y`. -/
  | edge (x y : ℕ)
  /-- The guessed closed relation. -/
  | cl (x y : ℕ)
  /-- The guessed pairs outside the closed relation. -/
  | nc (x y : ℕ)
  /-- The final sweep has checked the threads below `p`. -/
  | swp (p : ℕ)
  /-- The thread `j` has only the compound task `c` left. -/
  | cur (j c : ℕ)
  /-- The thread `j` runs the body of the method number `μ`. -/
  | blk (j μ : ℕ)
  /-- The primitive subtask `x` of the running body of the thread `j` is still to be done. -/
  | tok (j μ x : ℕ)
  /-- The primitive subtask `x` of the running body of the thread `j` has been done. -/
  | don (j μ x : ℕ)
  /-- The thread `j` has finished. -/
  | fin (j : ℕ)
  /-- The thread `i` does not hold up the thread `j`. -/
  | ok (i j : ℕ)
  /-- The node `y` is reachable from the node `x`. -/
  | rch (x y : ℕ)
  /-- There is no thread `p`. -/
  | unused (p : ℕ)
  /-- Every thread is idle. -/
  | done
  deriving DecidableEq

/-- A row over the facts `TF`: precondition, add and delete list. -/
abbrev Rw : Type := List TF × List TF × List TF

/-- The state a row leaves behind. -/
def apply (r : Rw) (s : Set TF) : Set TF := {f | f ∈ r.2.1 ∨ (f ∈ s ∧ f ∉ r.2.2)}

@[simp] theorem mem_apply {r : Rw} {s : Set TF} {f : TF} :
    f ∈ apply r s ↔ f ∈ r.2.1 ∨ (f ∈ s ∧ f ∉ r.2.2) := Iff.rfl

/-- The transition relation of a table over `TF`. -/
def StepF (tbl : List Rw) (s s' : Set TF) : Prop :=
  ∃ r ∈ tbl, (∀ f ∈ r.1, f ∈ s) ∧ s' = apply r s

/-- Solvability of a table over `TF`. -/
def SolvF (tbl : List Rw) (s₀ : Set TF) (g : List TF) : Prop :=
  ∃ s, Relation.ReflTransGen (StepF tbl) s₀ s ∧ ∀ f ∈ g, f ∈ s

/-! ### The rows -/

section Rows

variable (d : DomDesc) (N : ℕ)

/-- The primitive subtasks of the method number `μ`, as a list. -/
def primsL (μ : ℕ) : List ℕ := (body d μ).ids.filter fun x => ((body d μ).label x).isLeft

theorem mem_primsL {μ x : ℕ} : x ∈ primsL d μ ↔ x ∈ prims d μ := by
  simp [primsL, mem_prims]

open Classical in
/-- The subtasks of the method number `μ` ordered before its subtask `x`. -/
noncomputable def predsL (μ x : ℕ) : List ℕ := (body d μ).ids.filter fun y => (body d μ).ordOf y x

theorem mem_predsL {μ x y : ℕ} : y ∈ predsL d μ x ↔ (body d μ).ordOf y x := by
  unfold predsL
  simp only [List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
  exact fun h => h.1

/-- The `ok` facts a thread `j` needs to start. -/
def oks (j : ℕ) : List TF := ((List.range N).filter (· ≠ j)).map (TF.ok · j)

/-- The facts of a running body all of whose primitive subtasks are done. -/
def doneL (j μ : ℕ) : List TF := TF.blk j μ :: (primsL d μ).map (TF.don j μ)

/-- The facts a freshly started body adds. -/
def startL (j μ : ℕ) : List TF := TF.blk j μ :: (primsL d μ).map (TF.tok j μ)

/-- The fact a closed body leaves behind. -/
def closedF (j μ : ℕ) : TF :=
  match tail d μ with
  | some c => .cur j c
  | none => .fin j

/-- Start the pending compound initial task of the thread `j` with the method `μ`. -/
def rExpP (j μ : ℕ) : Rw :=
  (TF.lab j (Sum.inr (head d μ)) :: oks N j, startL d j μ, [TF.lab j (Sum.inr (head d μ))])

/-- Decompose the current compound task of the thread `j` with the method `μ`. -/
def rExpC (j μ : ℕ) : Rw :=
  ([TF.cur j (head d μ)], startL d j μ, [TF.cur j (head d μ)])

/-- Execute the primitive subtask `x` (the action `a`) of the running body `μ` of thread `j`. -/
noncomputable def rExec (j μ x a : ℕ) : Rw :=
  (TF.tok j μ x :: (predsL d μ x).map (TF.don j μ) ++ (actOf d a).1.map TF.inst,
    TF.don j μ x :: (actOf d a).2.1.map TF.inst,
    TF.tok j μ x :: (actOf d a).2.2.map TF.inst)

/-- The execution rows of a subtask (none for a compound subtask). -/
noncomputable def rExecs (j μ x : ℕ) : List Rw :=
  match (body d μ).label x with
  | Sum.inl a => [rExec d j μ x a]
  | Sum.inr _ => []

/-- Close the running body `μ` of the thread `j`. -/
def rClose (j μ : ℕ) : Rw := (doneL d j μ, [closedF d j μ], doneL d j μ)

/-- Execute the pending primitive initial task `a` of the thread `j`. -/
def rExecP (j a : ℕ) : Rw :=
  (TF.lab j (Sum.inl a) :: oks N j ++ (actOf d a).1.map TF.inst,
    TF.fin j :: (actOf d a).2.1.map TF.inst,
    TF.lab j (Sum.inl a) :: (actOf d a).2.2.map TF.inst)

/-- Skip the pending unknown primitive initial task of the thread `j`. -/
def rNop (j : ℕ) : Rw := (TF.nop j :: oks N j, [TF.fin j], [TF.nop j])

/-- An idle running thread `i` (whose body has no compound subtask) does not hold up `j`. -/
def rZok (i j μ : ℕ) : List Rw :=
  match tail d μ with
  | some _ => []
  | none => [(doneL d i μ, [TF.ok i j], [])]

/-- The `ok` rows for the pair `i`, `j`. -/
def rOks (i j : ℕ) : List Rw :=
  [([TF.fin i], [TF.ok i j], []), ([TF.nc i j], [TF.ok i j], []),
    ([TF.rch j i], [TF.ok i j], []), ([TF.unused i], [TF.ok i j], [])]

/-- The reachability rows. -/
def rRch (x y z : ℕ) : List Rw :=
  [([TF.edge x y], [TF.rch x y], []), ([TF.rch x y, TF.edge y z], [TF.rch x z], [])]

/-- The rows of the counters (`unused` and the final sweep). -/
def rCnt (p : ℕ) : List Rw :=
  [([TF.len p], [TF.unused p], []), ([TF.unused p], [TF.unused (p + 1)], []),
    ([TF.swp p, TF.fin p], [TF.swp (p + 1)], []), ([TF.swp p, TF.len p], [TF.done], [])]

/-- **The thread table** for the domain description `d` and at most `N` threads and nodes. -/
noncomputable def thrTbl : List Rw :=
  ((List.range N).flatMap fun j => (List.range d.methods.length).flatMap fun μ =>
      [rExpP d N j μ, rExpC d j μ, rClose d j μ] ++ (primsL d μ).flatMap (rExecs d j μ)) ++
  ((List.range N).flatMap fun j => (vocA d).map (rExecP d N j) ++ [rNop N j]) ++
  ((List.range N).flatMap fun i => (List.range N).flatMap fun j =>
      rOks i j ++ (List.range d.methods.length).flatMap (rZok d i j)) ++
  ((List.range N).flatMap fun x => (List.range N).flatMap fun y =>
      (List.range N).flatMap (rRch x y)) ++
  (List.range N).flatMap rCnt

end Rows

/-! ### The initial facts and the goal -/

/-- Is the task a primitive task the domain does not mention? -/
def Unk (d : DomDesc) (x : ℕ ⊕ ℕ) : Prop := unknownPrimB d x = true

/-- **The initial fact set**, for the initial state `s₀`, the ordering graph `E`, the closed
relation `Cl`, the certificate `NC` and the inert witness pairs `W`. -/
def initF (P : Par) (E Cl NC : ℕ → ℕ → Prop) (W : ℕ → ℕ → Prop) (s₀ : Set ℕ) : Set TF :=
  {f | match f with
    | .inst v => v ∈ s₀
    | .lab j x => j < P.k ∧ x = P.lab j
    | .nop j => j < P.k ∧ Unk P.d (P.lab j)
    | .len p => p = P.k
    | .wit p a => W p a
    | .edge x y => E x y
    | .cl x y => Cl x y
    | .nc x y => NC x y
    | .swp p => p = 0
    | _ => False}

/-- The goal: the goal facts and `done`. -/
def goalF (g : List ℕ) : List TF := g.map TF.inst ++ [TF.done]

/-! ### Transfer to numbered facts -/

section Transfer

variable (enc : TF → ℕ)

/-- A row over `TF`, encoded. -/
def encRow (r : Rw) : Row := (r.1.map enc, r.2.1.map enc, r.2.2.map enc)

variable {enc}

theorem stepF_of_stepTbl (henc : Function.Injective enc) {tbl : List Rw} {u u' : List ℕ}
    (h : StepTbl (tbl.map (encRow enc)) u u') :
    StepF tbl (enc ⁻¹' {n | n ∈ u}) (enc ⁻¹' {n | n ∈ u'}) := by
  obtain ⟨row, hrow, hpre, hpost⟩ := h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrow
  refine ⟨r, hr, fun f hf => hpre _ (List.mem_map_of_mem hf), ?_⟩
  ext f
  simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_apply, hpost, encRow,
    List.mem_map, henc.eq_iff, exists_eq_right]

theorem stepTbl_of_stepF (henc : Function.Injective enc) {tbl : List Rw} {u : List ℕ} {s' : Set TF}
    (h : StepF tbl (enc ⁻¹' {n | n ∈ u}) s') :
    ∃ u' : List ℕ, StepTbl (tbl.map (encRow enc)) u u' ∧ enc ⁻¹' {n | n ∈ u'} = s' := by
  obtain ⟨r, hr, hpre, rfl⟩ := h
  refine ⟨r.2.1.map enc ++ u.filter (fun n => decide (n ∉ r.2.2.map enc)),
    ⟨encRow enc r, List.mem_map_of_mem hr, ?_, fun f => ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hf
    exact hpre a ha
  · simp [encRow]
  · ext f
    simp only [Set.mem_preimage, Set.mem_setOf_eq, List.mem_append, List.mem_map, henc.eq_iff,
      exists_eq_right, List.mem_filter, decide_eq_true_eq, mem_apply]

theorem reachF_of_reachTbl (henc : Function.Injective enc) {tbl : List Rw} {u u' : List ℕ}
    (h : ReachTbl (tbl.map (encRow enc)) u u') :
    Relation.ReflTransGen (StepF tbl) (enc ⁻¹' {n | n ∈ u}) (enc ⁻¹' {n | n ∈ u'}) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (stepF_of_stepTbl henc hs)

theorem reachTbl_of_reachF (henc : Function.Injective enc) {tbl : List Rw} {u : List ℕ}
    {s' : Set TF} (h : Relation.ReflTransGen (StepF tbl) (enc ⁻¹' {n | n ∈ u}) s') :
    ∃ u' : List ℕ, ReachTbl (tbl.map (encRow enc)) u u' ∧ enc ⁻¹' {n | n ∈ u'} = s' := by
  induction h with
  | refl => exact ⟨u, .refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨u₁, h₁, rfl⟩ := ih
    obtain ⟨u₂, h₂, rfl⟩ := stepTbl_of_stepF henc hs
    exact ⟨u₂, h₁.tail h₂, rfl⟩

/-- **Solvability transfers along an injective encoding** of the facts, from any list of
numbers whose facts are the initial fact set. -/
theorem solvableTbl_iff_solvF (henc : Function.Injective enc) {tbl : List Rw} {S : List ℕ}
    {s₀ : Set TF} (hS : enc ⁻¹' {n | n ∈ S} = s₀) (g : List TF) :
    SolvableTbl (tbl.map (encRow enc)) S (g.map enc) ↔ SolvF tbl s₀ g := by
  subst hS
  constructor
  · rintro ⟨u, hu, hg⟩
    exact ⟨_, reachF_of_reachTbl henc hu, fun f hf => hg _ (List.mem_map_of_mem hf)⟩
  · rintro ⟨s, hs, hg⟩
    obtain ⟨u, hu, rfl⟩ := reachTbl_of_reachF henc hs
    refine ⟨u, hu, fun n hn => ?_⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hn
    exact hg f hf

end Transfer

end Thr

end Space

end HTN
