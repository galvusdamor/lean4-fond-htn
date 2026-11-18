import HtnPlanning.Article.ProgBound
import HtnPlanning.Article.Progression
import HtnPlanning.Article.AcycProgression
/-!
# Progression bounds in the article's model (Def. 4.3, Prop. 4.2.14, Lemmas 4.2.15/19/21)

* `HTN.Article.Problem.IsHTNProgBound`, `IsTIHTNProgBound`, `IsProgBound` — **Def. 4.3**.  The
  article quantifies over the networks `tn` with `(s_I, tn_I) →*_P (s_I, tn)`, i.e. reached *in
  the initial state*; this is a typo — the bounds are used (and proved) for all reachable states,
  which is what is formalised.
* `HTN.Article.Problem.abstraction` — the abstraction of Prop. 4.2.14 (no state variables: every
  action has empty preconditions and effects).
* **`HTN.Article.Problem.prop_4_2_14`** — an HTN progression bound of the abstraction is an HTN and
  a TIHTN progression bound of the problem.
* **`lem_4_2_15`**, **`lem_4_2_19`**, **`lem_4_2_21`** — the bounds of `HtnPlanning/Article/
  ProgBound.lean` as progression bounds (`lem_4_2_21` in its corrected form).
-/

namespace HTN

namespace Article

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

namespace Problem

variable (P : Problem F A C I)

/-- **Definition 4.3.** `n` bounds the size of every task network reachable by progression. -/
def IsHTNProgBound (n : ℕ) : Prop := ∀ nd, P.ProgReach nd → nd.net.T.card ≤ n

/-- **Definition 4.3.** `n` bounds the size of every task network reachable by acyclic
progression. -/
def IsTIHTNProgBound (n : ℕ) : Prop := ∀ nd, P.AProgReach nd → nd.net.T.card ≤ n

/-- **Definition 4.3.** A progression bound: both an HTN and a TIHTN progression bound. -/
def IsProgBound (n : ℕ) : Prop := P.IsHTNProgBound n ∧ P.IsTIHTNProgBound n

/-- Progression reaches its networks by abstract progression. -/
theorem absReach_of_progReach {nd : PNode F A C I} (h : P.ProgReach nd) :
    ∃ n, AbsReachN P.methods n P.tnI nd.net := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | tail _ hs ih =>
    obtain ⟨n, hn⟩ := ih
    cases hs with
    | prog hu hα _ => exact ⟨n + 1, hn.tail (.prog hu ⟨_, hα⟩)⟩
    | decomp hu hstep => exact ⟨n + 1, hn.tail (.decomp hu hstep)⟩

/-- Acyclic progression reaches its networks by abstract progression. -/
theorem absReach_of_aProgReach {nd : APNode F A C I} (h : P.AProgReach nd) :
    ∃ n, AbsReachN P.methods n P.tnI nd.net := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | tail _ hs ih =>
    obtain ⟨n, hn⟩ := ih
    cases hs with
    | prog hu hα _ => exact ⟨n + 1, hn.tail (.prog hu ⟨_, hα⟩)⟩
    | decomp hu hm hα hwf'' hiso hdisj _ =>
      exact ⟨n + 1, hn.tail (.decomp hu ⟨hm, hu.1, hα, _, hwf'', hiso, hdisj, rfl⟩)⟩
    | insert _ => exact ⟨n, hn⟩

/-- **The abstraction** of Prop. 4.2.14: all state variables removed. -/
def abstraction : Problem F A C I where
  δ _ := ⟨∅, ∅, ∅, ∅⟩
  methods := P.methods
  init := ∅
  tnI := P.tnI
  goalPos := ∅
  goalNeg := ∅

/-- In the abstraction, every network reachable by abstract progression is reached by
progression. -/
theorem progReach_abstraction {n : ℕ} {tn : TaskNetwork I A C}
    (h : AbsReachN P.methods n P.tnI tn) : ∃ nd, P.abstraction.ProgReach nd ∧ nd.net = tn := by
  induction n generalizing tn with
  | zero => cases h; exact ⟨_, Relation.ReflTransGen.refl, rfl⟩
  | succ n ih =>
    obtain ⟨tn₁, hr, hs⟩ := h.exists_last
    obtain ⟨⟨s, tn₀, π⟩, hnd, rfl⟩ := ih hr
    have happ : ∀ a, (P.abstraction.δ a).Applicable s := fun a =>
      ⟨by simp [abstraction], by simp [abstraction]⟩
    cases hs with
    | prog hu hp =>
      obtain ⟨a, ha⟩ := hp
      exact ⟨_, hnd.tail (ProgStep.prog hu ha (happ a)), rfl⟩
    | decomp hu hstep => exact ⟨_, hnd.tail (ProgStep.decomp hu hstep), rfl⟩

/-- **Proposition 4.2.14.** An HTN progression bound of the abstraction is both an HTN and a
TIHTN progression bound of the problem. -/
theorem prop_4_2_14 {n : ℕ} (h : P.abstraction.IsHTNProgBound n) : P.IsProgBound n := by
  constructor
  · intro nd hnd
    obtain ⟨k, hk⟩ := P.absReach_of_progReach hnd
    obtain ⟨nd', h1, h2⟩ := P.progReach_abstraction hk
    rw [← h2]; exact h nd' h1
  · intro nd hnd
    obtain ⟨k, hk⟩ := P.absReach_of_aProgReach hnd
    obtain ⟨nd', h1, h2⟩ := P.progReach_abstraction hk
    rw [← h2]; exact h nd' h1

/-- A bound on abstract progression is a progression bound. -/
theorem isProgBound_of_abs {B : ℕ}
    (h : ∀ n tn, AbsReachN P.methods n P.tnI tn → tn.T.card ≤ B) : P.IsProgBound B :=
  ⟨fun nd hnd => by obtain ⟨k, hk⟩ := P.absReach_of_progReach hnd; exact h k _ hk,
    fun nd hnd => by obtain ⟨k, hk⟩ := P.absReach_of_aProgReach hnd; exact h k _ hk⟩

/-- **Lemma 4.2.15.** A tail-recursive problem with a `≤_r`-stratification of height `h`, at most
`k` initial tasks and at most `m ≥ 1` tasks in every reachable method has the progression bound
`k · m^h`. -/
theorem lem_4_2_15 (hP : P.WF) {h k m : ℕ} (hrec : P.IsTailREC_h h) (hk : P.tnI.T.card ≤ k)
    (hm1 : 1 ≤ m) (hm : ∀ m', P.toPos.ReachableMethod m' → m'.subtasks.T.card ≤ m) :
    P.IsProgBound (k * m ^ h) := by
  obtain ⟨le, hs, hh⟩ := hrec
  refine P.isProgBound_of_abs fun n tn hr => ?_
  have := HTN.Problem.progBound_tailRec P.toPos hs hh hm1 hm hP.tnI hr
  exact this.trans (Nat.mul_le_mul_right _ hk)

/-- **Lemma 4.2.19.** For `P ∈ TAIL-REC ∩ TO` (height `h`, at most `k` initial tasks, at most `m`
tasks per reachable method): the progression bound `k + (m - 1) · h`. -/
theorem lem_4_2_19 (hP : P.WF) {h k m : ℕ} (hrec : P.IsTailREC_h h) (hto : P.IsTO)
    (hk : P.tnI.T.card ≤ k) (hm : ∀ m', P.toPos.ReachableMethod m' → m'.subtasks.T.card ≤ m) :
    P.IsProgBound (k + (m - 1) * h) := by
  obtain ⟨le, hs, f, hfh, hf⟩ := hrec
  refine P.isProgBound_of_abs fun n tn hr => ?_
  have : tn.T.card ≤ P.tnI.T.card + (m - 1) * h :=
    HTN.Problem.progBound_TO P.toPos hs hf hm hto.2 hfh hP.tnI hto.1 hr
  omega

/-- **Lemma 4.2.21 (corrected).** For `P ∈ TAIL-REC ∩ TO-M`: the progression bound
`k · (1 + (m - 1) · h)`; for `m, h ≥ 1` this is at most the article's `k · m · h`
(`lem_4_2_21_article`). -/
theorem lem_4_2_21 (hP : P.WF) {h k m : ℕ} (hrec : P.IsTailREC_h h) (hto : P.IsTO_M)
    (hk : P.tnI.T.card ≤ k) (hm : ∀ m', P.toPos.ReachableMethod m' → m'.subtasks.T.card ≤ m) :
    P.IsProgBound (k * (1 + (m - 1) * h)) := by
  obtain ⟨le, hs, f, hfh, hf⟩ := hrec
  refine P.isProgBound_of_abs fun n tn hr => ?_
  have := HTN.Problem.progBound_TOM P.toPos hs hf hm hto hfh hP.tnI hr
  exact this.trans (Nat.mul_le_mul_right _ hk)

/-- **Lemma 4.2.21** in the article's form, for `m, h ≥ 1`. -/
theorem lem_4_2_21_article (hP : P.WF) {h k m : ℕ} (hrec : P.IsTailREC_h h) (hto : P.IsTO_M)
    (hk : P.tnI.T.card ≤ k) (hm : ∀ m', P.toPos.ReachableMethod m' → m'.subtasks.T.card ≤ m)
    (hm1 : 1 ≤ m) (hh1 : 1 ≤ h) : P.IsProgBound (k * m * h) := by
  have := P.lem_4_2_21 hP hrec hto hk hm
  refine ⟨fun nd hnd => (this.1 nd hnd).trans ?_, fun nd hnd => (this.2 nd hnd).trans ?_⟩ <;>
  · rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have : (m - 1) * h + h = m * h := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hm1]
    omega

end Problem

end Article

end HTN
