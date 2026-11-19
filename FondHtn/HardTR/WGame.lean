import FondHtn.MPStrong.Prog
import HtnPlanning.Progression.ProgressionSound
import HtnPlanning.Interleave.NetYield
/-!
# CB22 Thm 5, soundness layer: from the progression game to a game on words

**Deviation from `doc/notes_cb22_thm5_progress.md`.**  The plan proposed to prove the round lemma
directly on (partially decomposed) task networks along `MPProg` derivations.  Instead, the
soundness direction forgets the networks altogether:

* `FOND.HardTR.LWin` — the **word game** on a set of action words `L` (a language) and an abstract
  state: the player wins if `[] ∈ L`, or by an applicable action `a` all of whose outcomes win
  on the residual language `a⁻¹ L`.  The player is *stronger* than in the progression game: it
  never commits to a decomposition, only to the executed actions.
* **`FOND.HardTR.lwin_of_mpProg`** — a winning progression game from `(tn, s)` gives a winning
  word game on the refinements (`HTN.Domain.NetYield`) of `tn`.  The proof uses soundness of
  progression search (`HTN.Problem.isSolutionPlan_of_goalNode`) for the skeleton problem with
  initial network `tn`.
* `FOND.HardTR.NWin` — the same game on a *set of configurations* of a labelled transition system
  (an NFA, possibly infinite), and `FOND.HardTR.nwin_of_lwin`: the word game on a language
  contained in the language of the configurations is won in the configuration game.

So soundness of an encoding reduces to (i) an over-approximation of the refinements of the
initial network by the language of an automaton, and (ii) the analysis of the configuration game
— where the *configurations* (multisets of thread states, `FondHtn/HardTR/Round.lean`) replace
task networks.
-/

namespace FOND

namespace HardTR

open HTN

universe u v w x

/-! ## The word game -/

section Games

variable {A : Type u} {S : Type v} (app : A → S → Prop) (outs : A → S → Set S)

/-- **The word game** on a language `L` from the state `s`. -/
inductive LWin : Set (List A) → S → Prop
  /-- The empty word is in the language. -/
  | nil {L : Set (List A)} {s : S} (h : [] ∈ L) : LWin L s
  /-- An applicable action, all of whose outcomes win on the residual language. -/
  | step {L : Set (List A)} {s : S} (a : A) (ha : app a s)
      (h : ∀ s' ∈ outs a s, LWin {w | a :: w ∈ L} s') : LWin L s

variable {app outs}

theorem LWin.mono {L : Set (List A)} {s : S} (h : LWin app outs L s) :
    ∀ {L' : Set (List A)}, L ⊆ L' → LWin app outs L' s := by
  induction h with
  | nil h => exact fun hL => .nil (hL h)
  | step a ha _ ih => exact fun hL => .step a ha fun s' hs' => ih s' hs' fun w hw => hL hw

/-- A labelled transition system: a step relation and accepting configurations. -/
structure LTS (Q : Type w) (A : Type u) where
  /-- The step relation. -/
  step : Q → A → Q → Prop
  /-- The accepting configurations. -/
  acc : Q → Prop

variable {Q : Type w}

/-- The words accepted from a configuration. -/
inductive LTS.Acc (T : LTS Q A) : Q → List A → Prop
  | nil {q : Q} (h : T.acc q) : T.Acc q []
  | cons {q q' : Q} {a : A} {w : List A} (h : T.step q a q') (hw : T.Acc q' w) : T.Acc q (a :: w)

/-- The successors of a set of configurations under the action `a`. -/
def LTS.post (T : LTS Q A) (X : Set Q) (a : A) : Set Q := {q' | ∃ q ∈ X, T.step q a q'}

variable (app outs)

/-- **The configuration game** on a set `X` of configurations of `T`. -/
inductive NWin (T : LTS Q A) : Set Q → S → Prop
  /-- An accepting configuration. -/
  | nil {X : Set Q} {s : S} (h : ∃ q ∈ X, T.acc q) : NWin T X s
  /-- An applicable action, all of whose outcomes win from the successor configurations. -/
  | step {X : Set Q} {s : S} (a : A) (ha : app a s)
      (h : ∀ s' ∈ outs a s, NWin T (T.post X a) s') : NWin T X s

variable {app outs}

theorem NWin.mono {T : LTS Q A} {X : Set Q} {s : S} (h : NWin app outs T X s) :
    ∀ {Y : Set Q}, X ⊆ Y → NWin app outs T Y s := by
  induction h with
  | nil h =>
    intro Y hXY
    obtain ⟨q, hq, hacc⟩ := h
    exact .nil ⟨q, hXY hq, hacc⟩
  | step a ha _ ih =>
    intro Y hXY
    exact .step a ha fun s' hs' => ih s' hs' fun q ⟨p, hp, hpq⟩ => ⟨p, hXY hp, hpq⟩

/-- **From the word game to the configuration game.** -/
theorem nwin_of_lwin {T : LTS Q A} {L : Set (List A)} {s : S} (h : LWin app outs L s) :
    ∀ {X : Set Q}, (∀ w ∈ L, ∃ q ∈ X, T.Acc q w) → NWin app outs T X s := by
  induction h with
  | nil h =>
    intro X hX
    obtain ⟨q, hq, hacc⟩ := hX _ h
    cases hacc with
    | nil hacc => exact .nil ⟨q, hq, hacc⟩
  | step a ha _ ih =>
    intro X hX
    refine .step a ha fun s' hs' => ih s' hs' fun w hw => ?_
    obtain ⟨q, hq, hacc⟩ := hX _ hw
    cases hacc with
    | cons hstep hw' => exact ⟨_, ⟨q, hq, hstep⟩, hw'⟩

/-- A configuration game on the empty set is only won thanks to an applicable action without
outcomes (in some state). -/
theorem NWin.exists_of_empty {T : LTS Q A} {X : Set Q} {s : S} (h : NWin app outs T X s)
    (hX : X = ∅) : ∃ s' a, app a s' ∧ outs a s' = ∅ := by
  induction h with
  | nil h =>
    obtain ⟨q, hq, -⟩ := h
    rw [hX] at hq
    exact absurd hq (Set.notMem_empty q)
  | @step X s a ha h ih =>
    by_cases he : outs a s = ∅
    · exact ⟨s, a, ha, he⟩
    · obtain ⟨s', hs'⟩ := Set.nonempty_iff_ne_empty.2 he
      have hpost : T.post X a = ∅ := by
        rw [hX]; ext q; simp [LTS.post]
      exact ih s' hs' hpost

/-- If all applicable actions have outcomes, the configuration game on `∅` is lost. -/
theorem NWin.false_of_empty {T : LTS Q A} {s : S}
    (hne : ∀ a s, app a s → (outs a s).Nonempty) (h : NWin app outs T ∅ s) : False := by
  obtain ⟨s₀, a, ha, he⟩ := h.exists_of_empty rfl
  obtain ⟨s', hs'⟩ := hne a s₀ ha
  rw [he] at hs'
  exact hs'

/-! ## Safety-closed games (for fair policies)

The *safe* versions of the games are post-fixpoints instead of least fixpoints: a set of
positions all of which are nonempty and either accept or have a move all of whose outcomes stay
in the set.  They do not force termination; the soundness argument gets termination elsewhere
(from the decreasing time of the tableau).  Every inductive win is a safe win. -/

variable (app outs)

/-- **The safe word game**: a self-supporting set of (language, state) pairs. -/
def LSafe (L : Set (List A)) (s : S) : Prop :=
  ∃ R : Set (Set (List A) × S), (L, s) ∈ R ∧ ∀ p ∈ R, (∃ w, w ∈ p.1) ∧
    ([] ∈ p.1 ∨ ∃ a, app a p.2 ∧ ∀ s' ∈ outs a p.2, ({w | a :: w ∈ p.1}, s') ∈ R)

/-- **The safe configuration game.** -/
def SWin (T : LTS Q A) (X : Set Q) (s : S) : Prop :=
  ∃ R : Set (Set Q × S), (X, s) ∈ R ∧ ∀ p ∈ R, p.1.Nonempty ∧
    ((∃ q ∈ p.1, T.acc q) ∨ ∃ a, app a p.2 ∧ ∀ s' ∈ outs a p.2, (T.post p.1 a, s') ∈ R)

variable {app outs}

/-- Unfolding a safe configuration game. -/
theorem SWin.unfold {T : LTS Q A} {X : Set Q} {s : S} (h : SWin app outs T X s) :
    X.Nonempty ∧ ((∃ q ∈ X, T.acc q) ∨ ∃ a, app a s ∧ ∀ s' ∈ outs a s, SWin app outs T (T.post X a) s') := by
  obtain ⟨R, hR, hcl⟩ := h
  obtain ⟨hne, h⟩ := hcl _ hR
  refine ⟨hne, h.imp id fun ⟨a, ha, hs⟩ => ⟨a, ha, fun s' hs' => ⟨R, hs s' hs', hcl⟩⟩⟩

theorem SWin.mono {T : LTS Q A} {X : Set Q} {s : S} (h : SWin app outs T X s) :
    ∀ {Y : Set Q}, X ⊆ Y → SWin app outs T Y s := by
  obtain ⟨R, hR, hcl⟩ := h
  intro Y hXY
  refine ⟨{p | ∃ X', (X', p.2) ∈ R ∧ X' ⊆ p.1}, ⟨X, hR, hXY⟩, ?_⟩
  rintro ⟨Y', s'⟩ ⟨X', hX', hsub⟩
  obtain ⟨⟨q, hq⟩, h⟩ := hcl _ hX'
  refine ⟨⟨q, hsub hq⟩, ?_⟩
  rcases h with ⟨q', hq', hacc⟩ | ⟨a, ha, hs⟩
  · exact Or.inl ⟨q', hsub hq', hacc⟩
  · exact Or.inr ⟨a, ha, fun s'' hs'' => ⟨_, hs s'' hs'', fun q ⟨p, hp, hpq⟩ => ⟨p, hsub hp, hpq⟩⟩⟩

theorem SWin.false_of_empty {T : LTS Q A} {s : S} (h : SWin app outs T ∅ s) : False := by
  obtain ⟨⟨q, hq⟩, -⟩ := h.unfold
  exact hq

/-- **An inductive win is a safe win** (when applicable actions have outcomes). -/
theorem NWin.toSWin {T : LTS Q A} (hne : ∀ a s, app a s → (outs a s).Nonempty) {X : Set Q} {s : S}
    (h : NWin app outs T X s) : SWin app outs T X s := by
  refine ⟨{p | NWin app outs T p.1 p.2}, h, ?_⟩
  rintro ⟨X', s'⟩ (hp : NWin app outs T X' s')
  refine ⟨?_, ?_⟩
  · by_contra hX
    rw [Set.not_nonempty_iff_eq_empty] at hX
    subst hX
    exact NWin.false_of_empty hne hp
  · cases hp with
    | nil h => exact Or.inl h
    | step a ha h => exact Or.inr ⟨a, ha, h⟩

/-- **From the safe word game to the safe configuration game.** -/
theorem swin_of_lsafe {T : LTS Q A} {L : Set (List A)} {s : S} (h : LSafe app outs L s)
    {X : Set Q} (hX : ∀ w ∈ L, ∃ q ∈ X, T.Acc q w) : SWin app outs T X s := by
  obtain ⟨R, hR, hcl⟩ := h
  refine ⟨{p | ∃ L', (L', p.2) ∈ R ∧ ∀ w ∈ L', ∃ q ∈ p.1, T.Acc q w}, ⟨L, hR, hX⟩, ?_⟩
  rintro ⟨X', s'⟩ ⟨L', hL', hacc⟩
  obtain ⟨⟨w, hw⟩, h⟩ := hcl _ hL'
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq, -⟩ := hacc w hw
    exact ⟨q, hq⟩
  · rcases h with hnil | ⟨a, ha, hs⟩
    · obtain ⟨q, hq, hq'⟩ := hacc _ hnil
      cases hq' with
      | nil hq' => exact Or.inl ⟨q, hq, hq'⟩
    · refine Or.inr ⟨a, ha, fun s'' hs'' => ⟨_, hs s'' hs'', fun w hw => ?_⟩⟩
      obtain ⟨q, hq, hq'⟩ := hacc _ hw
      cases hq' with
      | cons hstep hw' => exact ⟨_, ⟨q, hq, hstep⟩, hw'⟩

end Games

/-! ## From the progression game to the word game -/

section Prog

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- The skeleton of a FOND problem (trivial actions, empty goal) with the initial network
`tn`. -/
def skelAt (P : Problem F A C I) (tn : TaskNetwork I A C) : HTN.Problem F A C I :=
  { P.skeleton with tnI := tn }

/-- **A winning progression game gives a winning word game on the refinements.** -/
theorem lwin_of_mpProg [DecidableEq I] [Infinite I] {P : Problem F A C I} (hP : P.WF)
    {tn₀ : TaskNetwork I A C} (hwf : tn₀.WF) {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPProg tn s) :
    ∀ π : List A, (skelAt P tn₀).ReachableNode ⟨P.init, tn, π⟩ →
      LWin (fun a s => (P.δ a).Applicable s) (fun a s => (P.δ a).outcomes s)
        {as | (skelAt P tn₀).domain.NetYield tn₀ (π ++ as)} s := by
  have hP0 : (skelAt P tn₀).WF := ⟨hwf, hP.methods⟩
  induction h with
  | empty he =>
    intro π hr
    refine .nil ?_
    have hsol := HTN.Problem.isSolutionPlan_of_goalNode hP0 hr ⟨he, by
      intro f hf; simp [skelAt, Problem.skeleton] at hf⟩
    simpa using (HTN.Problem.isSolutionPlan_iff.1 hsol).1
  | @prim tn s t a hu hα happ _ ih =>
    intro π hr
    refine .step a happ fun s' hs' => ?_
    have hstep : (skelAt P tn₀).Step ⟨P.init, tn, π⟩ ⟨P.init, tn.progress t, π ++ [a]⟩ := by
      have h0 := HTN.Problem.Step.prog (P := skelAt P tn₀) (s := P.init) (π := π) hu hα
        (by intro f hf; simp [skelAt, Problem.skeleton] at hf)
      have htr : (skelAt P tn₀).transition a P.init = P.init := by
        simp [ActionModel.transition, skelAt, Problem.skeleton]
      rwa [htr] at h0
    refine (ih s' hs' (π ++ [a]) (hr.tail hstep)).mono ?_
    intro w hw
    simpa using hw
  | @decomp tn tn' s t m hu hd _ ih =>
    intro π hr
    exact ih π (hr.tail (HTN.Problem.Step.decomp hu hd))

/-- **The progression game from the initial network is won only if the word game on the
refinements of the initial network is won.** -/
theorem lwin_of_mpProg_init [DecidableEq I] [Infinite I] {P : Problem F A C I} (hP : P.WF)
    (h : P.MPProg P.tnI P.init) :
    LWin (fun a s => (P.δ a).Applicable s) (fun a s => (P.δ a).outcomes s)
      {as | (skelAt P P.tnI).domain.NetYield P.tnI as} P.init := by
  have := lwin_of_mpProg hP hP.tnI h [] Relation.ReflTransGen.refl
  simpa using this

end Prog

end HardTR

end FOND
