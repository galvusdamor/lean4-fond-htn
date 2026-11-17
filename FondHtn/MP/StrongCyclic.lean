import FondHtn.IsoLemmas
import FondHtn.FixedMethods
/-!
# Strong cyclic solutions: the literal definition of [CB22] and the fair one

[CB22, Def. 7] calls `π` a strong cyclic solution iff every *terminal* node of the execution
structure is a goal node (`FOND.Problem.IsMPStrongCyclicSolution`).  Nothing excludes infinite
executions, so a policy that decomposes a recursive task forever is a strong cyclic solution.
The usual notion (Cimatti et al. 2003) asks that a goal node remains *reachable* from every
reachable node (`FOND.Problem.IsMPStrongCyclicFairSolution`).

* `FOND.Problem.IsMPStrongSolution.isMPStrongCyclicSolution`,
  `FOND.Problem.IsMPStrongSolution.fair` — strong solutions are strong cyclic solutions in both
  senses;
* `FOND.LoopEx.literal_not_planExistence` — a **deterministic** problem without any solution
  (no primitive task network is reachable from `tn_I`) that has a literal strong cyclic
  solution.  Hence the literal notion does not coincide with plan existence on deterministic
  problems, and the lower bounds [CB22] states for strong cyclic solutions are not inherited
  from deterministic HTN planning under the literal definition (catalogue G6).
-/

namespace FOND

open HTN HTN.TaskNetwork

namespace Problem

variable {F A C I : Type} {P : Problem F A C I} [DecidableEq I] {π : MPPolicy F A C I}

theorem IsMPStrongSolution.isMPStrongCyclicSolution (h : P.IsMPStrongSolution π) :
    P.IsMPStrongCyclicSolution π := ⟨h.1, h.2.2.2⟩

/-- **Strong solutions are fair strong cyclic solutions**: in a finite acyclic execution
structure every path ends in a terminal node, which is a goal node. -/
theorem IsMPStrongSolution.fair [Nonempty I] (h : P.IsMPStrongSolution π) :
    P.IsMPStrongCyclicFairSolution π := by
  classical
  obtain ⟨hwd, ⟨S, hS, hrep⟩, hac, hterm⟩ := h
  refine ⟨hwd, fun x hx => ?_⟩
  by_contra hno
  push_neg at hno
  have hsucc : ∀ y, Relation.ReflTransGen (P.MPStep π) x y → ∃ z, P.MPStep π y z := by
    intro y hy
    by_contra hn
    push_neg at hn
    exact hno y hy (hterm y (hx.trans hy) hn)
  let R := {y // Relation.ReflTransGen (P.MPStep π) x y}
  let nxt : R → R := fun y =>
    ⟨Classical.choose (hsucc y.1 y.2), y.2.tail (Classical.choose_spec (hsucc y.1 y.2))⟩
  let path : ℕ → R := fun n => nxt^[n] ⟨x, .refl⟩
  have hstep : ∀ n, P.MPStep π (path n).1 (path (n + 1)).1 := fun n => by
    show P.MPStep π (path n).1 (nxt^[n + 1] ⟨x, .refl⟩).1
    rw [Function.iterate_succ_apply']
    exact Classical.choose_spec (hsucc (path n).1 (path n).2)
  have htg : ∀ i k, Relation.TransGen (P.MPStep π) (path i).1 (path (i + k + 1)).1 := by
    intro i k
    induction k with
    | zero => exact .single (hstep i)
    | succ k ih =>
      have := hstep (i + k + 1)
      rw [show i + (k + 1) + 1 = i + k + 1 + 1 by omega]
      exact ih.tail this
  have hreach : ∀ n, P.MPReach π (path n).1 := fun n => hx.trans (path n).2
  haveI : Finite S := hS.to_subtype
  let rep : ℕ → S := fun n =>
    ⟨Classical.choose (hrep _ (hreach n)), (Classical.choose_spec (hrep _ (hreach n))).1⟩
  have hrepIso : ∀ n, (path n).1.Iso (rep n).1 := fun n =>
    (Classical.choose_spec (hrep _ (hreach n))).2
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite rep
  have hiso : (path i).1.Iso (path j).1 :=
    (hrepIso i).trans (heq ▸ (hrepIso j).symm)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have := htg i (j - i - 1)
    rw [show i + (j - i - 1) + 1 = j by omega] at this
    exact hac _ _ (hreach i) this hiso
  · have := htg j (i - j - 1)
    rw [show j + (i - j - 1) + 1 = i by omega] at this
    exact hac _ _ (hreach j) this hiso.symm

end Problem

/-! ## A deterministic problem with a literal strong cyclic solution but no plan -/

namespace LoopEx

/-- A single compound task `()` with id `i`. -/
def single (i : ℕ) : TaskNetwork ℕ Unit Unit := ⟨{i}, fun _ _ => False, fun _ => .inr ()⟩

/-- The only method: `() → ()`. -/
def m : Method ℕ Unit Unit := ⟨(), single 0⟩

/-- The deterministic problem `tn_I = (), () → ()`; its single action is never used. -/
def P : Problem ℕ Unit Unit ℕ where
  δ := fun _ => ⟨∅, ∅, {(∅, ∅)}⟩
  methods := {m}
  init := ∅
  tnI := single 0

theorem P_deterministic : P.IsDeterministic := fun _ => ⟨_, rfl⟩

theorem single_wf (i : ℕ) : (single i).WF :=
  ⟨fun h => h.elim, fun h => h.elim, fun _ h => h, fun h => h.elim⟩

/-- The invariant: a single compound task. -/
def Inv (tn : TaskNetwork ℕ Unit Unit) : Prop :=
  ∃ t₀, tn.T = {t₀} ∧ tn.α t₀ = .inr () ∧ tn.WF

theorem inv_single (i : ℕ) : Inv (single i) := ⟨i, rfl, rfl, single_wf i⟩

theorem inv_isoVia {tn : TaskNetwork ℕ Unit Unit} {t₀ : ℕ} (hT : tn.T = {t₀}) (hwf : tn.WF)
    (hα : tn.α t₀ = .inr ()) (i : ℕ) :
    IsoVia (fun _ => t₀) (single i) tn := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x _; simp [hT]
  · intro x hx y hy _; simp [single] at hx hy; rw [hx, hy]
  · intro y hy; simp [hT] at hy; exact ⟨i, by simp [single], hy.symm⟩
  · intro x _ y _; simp only [single, false_iff]; exact hwf.irrefl _
  · intro x _; simp [single, hα]

theorem inv_step {tn tn' : TaskNetwork ℕ Unit Unit} {t : ℕ} {m' : Method ℕ Unit Unit}
    (h : Inv tn) (hs : DecompStep P.methods tn t m' tn') : Inv tn' := by
  obtain ⟨t₀, hT, -, hwf⟩ := h
  obtain ⟨hm, ht, -, u, hu, huiso, hdisj, rfl⟩ := hs
  rw [Set.mem_singleton_iff.1 hm] at huiso
  obtain ⟨σ, hb, -, hα⟩ := huiso
  have hcard : u.T.card = 1 := by
    have h' : u.T.image σ = (single 0).T := by
      ext x; simpa [Set.ext_iff] using congrArg (x ∈ ·) hb.image_eq
    rw [← Finset.card_image_of_injOn hb.injOn, h']; rfl
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hcard
  rw [hT, Finset.mem_singleton] at ht
  subst ht
  refine ⟨j, ?_, ?_, decomposeWith_wf hwf hu hdisj⟩
  · simp [decomposeWith, hT, hj]
  · have : u.α j = .inr () := by rw [hα j (by simp [hj])]; rfl
    simp [decomposeWith, hj, this]

theorem not_achievable {tn : TaskNetwork ℕ Unit Unit} (h : HTN.DecomposesTo P.methods P.tnI tn) :
    ¬ tn.IsPrimitive := by
  have hinv : Inv tn := by
    induction h with
    | refl => exact inv_single 0
    | tail _ hs ih => obtain ⟨t, m', hs⟩ := hs; exact inv_step ih hs
  obtain ⟨t₀, hT, hα, -⟩ := hinv
  intro hp
  obtain ⟨a, ha⟩ := hp t₀ (by simp [hT])
  rw [hα] at ha; cases ha

/-- No weak (hence no strong) LD solution: no primitive network is reachable. -/
theorem not_weakLDSolvable : ¬ P.WeakLDSolvable := fun ⟨_, _, ⟨hd, hp⟩, _⟩ => not_achievable hd hp

theorem not_strongLDSolvable : ¬ P.StrongLDSolvable := fun ⟨_, _, ⟨hd, hp⟩, _⟩ => not_achievable hd hp

open Classical in
/-- The policy: always decompose the task. -/
noncomputable def π : MPPolicy ℕ Unit Unit ℕ := fun tn _ => if tn = single 0 then some (0, some m) else none

theorem π_wellDefined : π.WellDefined := by
  intro tn tn' s h h' _
  simp only [π] at h h'
  split_ifs at h h' with h1 h2
  · rw [h1, h2]
  all_goals simp at h h'

theorem reach_inv {x : MPNode ℕ Unit Unit ℕ} (hx : P.MPReach π x) : Inv x.net := by
  induction hx with
  | refl => exact inv_single 0
  | tail _ hs ih =>
    cases hs with
    | prim hi hu hα =>
      exfalso
      obtain ⟨tn', σ, t', hσ, ht', -, rfl⟩ := hi
      obtain ⟨t₀, hT, ht₀, -⟩ := ih
      have := hσ.mem ht'
      rw [hT, Finset.mem_singleton] at this
      rw [this, ht₀] at hα; cases hα
    | decomp _ hd => exact inv_step ih hd

theorem not_terminal {x : MPNode ℕ Unit Unit ℕ} (h : Inv x.net) : ¬ P.MPTerminal π x := by
  obtain ⟨t₀, hT, hα, hwf⟩ := h
  intro hterm
  have hi : MPInstr π x t₀ (some m) :=
    ⟨single 0, fun _ => t₀, 0, inv_isoVia hT hwf hα 0, by simp [single], by simp [π], rfl⟩
  have hd : DecompStep P.methods x.net t₀ m (decomposeWith x.net t₀ (single (t₀ + 1))) := by
    refine ⟨Set.mem_singleton _, by simp [hT], by rw [hα], single (t₀ + 1), single_wf _,
      ⟨fun _ => 0, ?_, ?_, ?_⟩, ?_, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro _ _; simp [single, m]
      · intro a ha b hb _; simp [single] at ha hb; rw [ha, hb]
      · intro y hy; simp [single, m] at hy; exact ⟨t₀ + 1, by simp [single], hy.symm⟩
    · intro _ _ _ _; simp [single, m]
    · intro _ _; rfl
    · simp [hT, single]
  exact hterm _ (Problem.MPStep.decomp hi hd)

/-- **The literal strong cyclic criterion differs from plan existence on deterministic
problems.** -/
theorem literal_not_planExistence :
    P.IsDeterministic ∧ P.MPStrongCyclicSolvable ∧ ¬ P.WeakLDSolvable ∧ ¬ P.StrongLDSolvable :=
  ⟨P_deterministic, ⟨π, π_wellDefined, fun x hx ht => absurd ht (not_terminal (reach_inv hx))⟩,
    not_weakLDSolvable, not_strongLDSolvable⟩

end LoopEx

end FOND
