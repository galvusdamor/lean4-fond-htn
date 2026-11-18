import HtnComplexity.Guard.Resplit
import HtnPlanning.Core.Construction
import HtnPlanning.Interleave.GridNet
/-!
# The re-split theorem is not vacuous

`HtnComplexity/Guard/Resplit.lean` proves that a construction whose domain writes a fixed
word can be re-split — the word moving into the instance — under a list of hypotheses.  This
file checks that the list can be met, on the smallest construction of that shape: a domain whose
single compound task writes one bit.

* the **word-carrying** domain `HTN.Guard.Ex.domSpec b₀` has a single method, which writes the
  bit `b₀`; its problem is solvable exactly when `b₀` is `true`, since the goal asks for the fact
  `out true`;
* the **family** domain `HTN.Guard.Ex.domFam` has one method per bit and does not mention `b₀`;
  the bit enters through the guard fact `inp b₀` of the instance, which is the precondition the
  guarded action model attaches to the action writing `b₀`.

`HTN.Guard.Ex.solvable_resplit_iff_ex` is the re-split theorem for this pair, and
`HTN.Guard.Ex.solvable_guarded_iff` evaluates both sides: the re-split problem for the bit `b₀`
is solvable exactly when `b₀` is `true`, which is what the original construction decides.
-/

namespace HTN

namespace Guard

namespace Ex

open TaskNetwork

/-- The facts: `inp b` says that the input bit is `b` — this is the guard fact the instance
carries — and `out b` is produced by writing `b`. -/
inductive GFact
  /-- The input bit is `b`: a static fact, supplied by the instance. -/
  | inp (b : Bool)
  /-- The bit `b` has been written. -/
  | out (b : Bool)
  deriving DecidableEq

/-- The actions: write the bit `b`. -/
abbrev GAct := Bool

/-- The only compound task: write the input bit. -/
abbrev GTask := Unit

/-- Writing a bit has no precondition and produces the fact `out b`. -/
def model : ActionModel GFact GAct where
  prec _ := ∅
  add b := {GFact.out b}
  del _ := ∅

/-- The guard of an action: writing `b` needs the static fact `inp b`. -/
def guard : GAct → Set GFact := fun b => {GFact.inp b}

/-- The guard facts. -/
def guardFacts : Set GFact := {f | ∃ b, f = GFact.inp b}

/-- The methods of the family domain: one per bit. -/
def methodsFam : Set (Method (ℕ × ℕ) GAct GTask) :=
  {m | ∃ b : Bool, m = ⟨(), seq [Sum.inl b]⟩}

/-- The methods of the word-carrying domain: the one that writes `b₀`. -/
def methodsSpec (b₀ : Bool) : Set (Method (ℕ × ℕ) GAct GTask) := {⟨(), seq [Sum.inl b₀]⟩}

/-- The family domain: one method per bit, no mention of the input. -/
def domFam : Domain GFact GAct GTask (ℕ × ℕ) where
  toActionModel := model
  methods := methodsFam

/-- The word-carrying domain. -/
def domSpec (b₀ : Bool) : Domain GFact GAct GTask (ℕ × ℕ) where
  toActionModel := model
  methods := methodsSpec b₀

/-- The instance: nothing given, the goal `out true`, and the single initial compound task. -/
def inst : Instance GFact GAct GTask (ℕ × ℕ) where
  init := ∅
  goal := {GFact.out true}
  tnI := seq [Sum.inr ()]

/-! ### The hypotheses of the re-split theorem -/

theorem methodsSpec_subset (b₀ : Bool) : methodsSpec b₀ ⊆ methodsFam := by
  rintro m rfl
  exact ⟨b₀, rfl⟩

theorem staticGuards_ex :
    StaticGuards model (domFam.mkProblem inst).UsedAction guardFacts guard := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro b f rfl
    exact ⟨b, rfl⟩
  · rintro b - f hf
    exact absurd hf (by simp [model])
  · rintro b - f hf hG
    obtain ⟨c, hc⟩ := hG
    rw [show f = GFact.out b from hf] at hc
    exact GFact.noConfusion hc
  · rintro b - f hf
    exact absurd hf (by simp [model])

/-- Only the methods of the bit `b₀` are admitted by the guard facts of the instance. -/
theorem bad_ex (b₀ : Bool) : ∀ m ∈ domFam.methods, m ∉ (domSpec b₀).methods →
    ∃ t ∈ m.subtasks.T,
      (∃ a, m.subtasks.α t = Sum.inl a ∧ ¬ guard a ⊆ {GFact.inp b₀}) ∨
        (∃ c, m.subtasks.α t = Sum.inr c ∧ False) := by
  rintro m ⟨b, rfl⟩ hnot
  have hb : b ≠ b₀ := by
    rintro rfl
    exact hnot rfl
  refine ⟨(0, 0), ?_, Or.inl ⟨b, ?_, ?_⟩⟩
  · exact (isSingle_seq_singleton (Sum.inl b)).mem
  · simp [seq, grid_α]
  · intro hsub
    have : GFact.inp b ∈ ({GFact.inp b₀} : Set GFact) := hsub rfl
    simp only [Set.mem_singleton_iff] at this
    exact hb (by injection this)

/-- Every plan of the word-carrying domain writes `b₀`, so the guards of the instance admit
it. -/
theorem granted_ex (b₀ : Bool) : ∀ as : List GAct, (domSpec b₀).NetYield inst.tnI as →
    ∀ a ∈ as, guard a ⊆ {GFact.inp b₀} := by
  intro as hy a ha
  have hused := usedAction_of_netYield (P := (domSpec b₀).mkProblem inst) hy a ha
  have hab : a = b₀ := by
    rcases hused with ⟨t, ht, hα⟩ | ⟨m, hm, t, ht, hα⟩
    · exfalso
      have hts : t = (0, 0) := (isSingle_seq_singleton (Sum.inr (() : GTask))).memT t |>.1 ht
      subst hts
      rw [show ((domSpec b₀).mkProblem inst).tnI = seq [Sum.inr ()] from rfl] at hα
      simp only [seq, grid_α] at hα
      exact Sum.inr_ne_inl hα
    · have hm' : m = ⟨(), seq [Sum.inl b₀]⟩ := hm
      subst hm'
      have hts : t = (0, 0) := (isSingle_seq_singleton (Sum.inl b₀)).memT t |>.1 ht
      subst hts
      simp only [seq, grid_α] at hα
      exact (Sum.inl_injective hα).symm
  subst hab
  exact fun f hf => hf

/-- **The re-split theorem applies to the example.** -/
theorem solvable_resplit_iff_ex (b₀ : Bool) :
    (guardedProblem (domFam.mkProblem inst) guard {GFact.inp b₀}).Solvable ↔
      ((domSpec b₀).mkProblem inst).Solvable := by
  refine solvable_resplit_iff (Taint := fun _ => False) rfl (methodsSpec_subset b₀)
    staticGuards_ex ?_ ?_ ?_ ⟨fun _ _ h => h.elim⟩ (bad_ex b₀) (granted_ex b₀)
  · rintro f rfl
    exact ⟨b₀, rfl⟩
  · intro f hf
    exact absurd hf (by simp [inst])
  · rintro f hf ⟨b, hb⟩
    rw [show f = GFact.out true from hf] at hb
    exact GFact.noConfusion hb

/-! ### Both sides, evaluated -/

theorem methods_wf_spec (b₀ : Bool) : ∀ m ∈ (domSpec b₀).methods, m.subtasks.WF := by
  rintro m rfl
  exact seq_wf

theorem transitionSeq_single (b : Bool) : model.transitionSeq [b] ∅ = {GFact.out b} := by
  simp [ActionModel.transitionSeq, ActionModel.transition, model]

/-- The plans of the word-carrying domain are exactly `[b₀]`. -/
theorem netYield_domSpec_iff (b₀ : Bool) (as : List GAct) :
    (domSpec b₀).NetYield inst.tnI as ↔ as = [b₀] := by
  have htn : inst.tnI = seq [Sum.inr (() : GTask)] := rfl
  constructor
  · rintro ⟨n, hn⟩
    rw [htn, Domain.netYieldN_single_comp (D := domSpec b₀) (c := ())
      (isSingle_seq_singleton (Sum.inr ())) (by simp [seq, grid_α]) (methods_wf_spec b₀)] at hn
    obtain ⟨k, m, -, hm, -, hy⟩ := hn
    have hm' : m = ⟨(), seq [Sum.inl b₀]⟩ := hm
    subst hm'
    rw [Domain.netYieldN_single_prim (D := domSpec b₀) (a := b₀)
      (isSingle_seq_singleton (Sum.inl b₀)) (by simp [seq, grid_α])] at hy
    exact hy.2
  · rintro rfl
    refine ⟨1, ?_⟩
    rw [htn, Domain.netYieldN_single_comp (D := domSpec b₀) (c := ())
      (isSingle_seq_singleton (Sum.inr ())) (by simp [seq, grid_α]) (methods_wf_spec b₀)]
    refine ⟨0, ⟨(), seq [Sum.inl b₀]⟩, rfl, rfl, rfl, ?_⟩
    exact (Domain.netYieldN_single_prim (D := domSpec b₀) (a := b₀)
      (isSingle_seq_singleton (Sum.inl b₀)) (by simp [seq, grid_α])).2 ⟨rfl, rfl⟩

/-- The word-carrying problem is solvable exactly when the bit is `true`. -/
theorem solvable_domSpec_iff (b₀ : Bool) :
    ((domSpec b₀).mkProblem inst).Solvable ↔ b₀ = true := by
  rw [Problem.solvable_iff_netYield]
  constructor
  · rintro ⟨as, hy, -, hg⟩
    have has : as = [b₀] := (netYield_domSpec_iff b₀ as).1 hy
    subst has
    have hstate : ((domSpec b₀).mkProblem inst).transitionSeq [b₀]
        ((domSpec b₀).mkProblem inst).init = {GFact.out b₀} := transitionSeq_single b₀
    rw [hstate] at hg
    have hmem : GFact.out true ∈ ({GFact.out b₀} : Set GFact) := hg rfl
    simp only [Set.mem_singleton_iff] at hmem
    exact (by injection hmem : true = b₀).symm
  · rintro rfl
    refine ⟨[true], (netYield_domSpec_iff true [true]).2 rfl, ?_, ?_⟩
    · exact ⟨fun f hf => (Set.notMem_empty f hf).elim, trivial⟩
    · have hstate : ((domSpec true).mkProblem inst).transitionSeq [true]
          ((domSpec true).mkProblem inst).init = {GFact.out true} := transitionSeq_single true
      rw [hstate]
      exact fun f hf => hf

/-- **The re-split problem decides the same thing as the original one.**  The family domain does
not mention the bit; the bit is the guard fact of the instance, and the problem is solvable
exactly when it is `true`. -/
theorem solvable_guarded_iff (b₀ : Bool) :
    (guardedProblem (domFam.mkProblem inst) guard {GFact.inp b₀}).Solvable ↔ b₀ = true :=
  (solvable_resplit_iff_ex b₀).trans (solvable_domSpec_iff b₀)

end Ex

end Guard

end HTN
