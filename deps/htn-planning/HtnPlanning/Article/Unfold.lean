import HtnPlanning.Article.ProgBoundArticle
import HtnPlanning.Article.ProgBound
/-!
# A TIHTN progression bound for totally ordered methods

Cor. 4.2.23 of the article claims `PlanEx^{UNRES ∩ TO-M}_tihtn ∈ PSPACE`, arguing that "any TIHTN
problem can be restricted to its acyclic variant".  The progression bounds of the article
(Lems. 4.2.15–4.2.21) need a stratification, which an unrestricted problem lacks; this file makes
the argument precise.

**Unfolding.**  Acyclic progression (Def. 4.2) labels every compound task with its ancestors.
`HTN.Article.Problem.unfoldPos` takes the pair `(c, S)` of a compound name and an ancestor set as
the task name; its methods decompose `(c, S)` like `c`, provided no compound name of the method is
in `S`, and label the new compound tasks `(c', S ∪ {c})`.  Acyclic progression of `P` is abstract
progression of the unfolding (`HTN.Article.Problem.absReach_unfold`), and the unfolding is
acyclic: the rank `2 (N - |S|) + [c ∈ S]` (`N` the number of reachable names of `P`) decreases
along every method.  The bound of Lem. 4.2.21 for the unfolding gives

* **`HTN.Article.Problem.tihtn_bound_TOM`** — with totally ordered reachable methods, acyclic
  progression reaches networks of at most `k · (1 + (m - 1) · (2N + 2))` tasks.
-/

namespace HTN

namespace Article

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

/-- A network with its compound tasks labelled by their ancestors. -/
def unfoldNet (tn : TaskNetwork I A C) (an : I → Set C) : TaskNetwork I A (C × Set C) where
  T := tn.T
  ord := tn.ord
  α := fun i => Sum.map id (fun c => (c, an i)) (tn.α i)

namespace Problem

variable (P : Problem F A C I)

/-- The unfolded methods. -/
def unfoldMethods : Set (Method I A (C × Set C)) :=
  {m' | ∃ m ∈ P.methods, ∃ S : Set C,
    (∀ u ∈ m.subtasks.T, ∀ c, m.subtasks.α u = Sum.inr c → c ∉ S) ∧
      m' = ⟨(m.abstractTask, S), unfoldNet m.subtasks (fun _ => Insert.insert m.abstractTask S)⟩}

/-- **The unfolding** of a problem by ancestor sets. -/
def unfoldPos : HTN.Problem (F ⊕ F) A (C × Set C) I where
  prec := P.toPos.prec
  add := P.toPos.add
  del := P.toPos.del
  methods := P.unfoldMethods
  init := P.toPos.init
  goal := P.toPos.goal
  tnI := unfoldNet P.tnI P.initANode.anc

theorem unfoldNet_wf {tn : TaskNetwork I A C} (h : tn.WF) (an : I → Set C) : (unfoldNet tn an).WF :=
  ⟨h.mem_left, h.mem_right, h.irrefl, h.trans⟩

theorem unfoldNet_iso {tn u : TaskNetwork I A C} (h : tn.Iso u) (S : Set C) :
    (unfoldNet tn fun _ => S).Iso (unfoldNet u fun _ => S) := by
  obtain ⟨σ, hb, ho, hα⟩ := h
  exact ⟨σ, hb, ho, fun t ht => by simp only [unfoldNet]; rw [hα t ht]⟩

/-- **Acyclic progression is abstract progression of the unfolding.** -/
theorem absReach_unfold (hP : P.WF) {nd : APNode F A C I} (h : P.AProgReach nd) :
    nd.net.WF ∧ ∃ n, AbsReachN P.unfoldMethods n (unfoldNet P.tnI P.initANode.anc)
      (unfoldNet nd.net nd.anc) := by
  induction h with
  | refl => exact ⟨hP.tnI, 0, .refl _⟩
  | @tail n₁ n₂ _ hs ih =>
    obtain ⟨hwf, n, hr⟩ := ih
    cases hs with
    | @prog s tn an π t a hu hα happ =>
      refine ⟨TaskNetwork.progress_wf hwf hu, n + 1, hr.tail ?_⟩
      exact .prog (t := t) ⟨hu.1, hu.2⟩ ⟨a, by simp [unfoldNet, hα]⟩
    | @decomp s tn tn'' an π t m hu hm hα hwf'' hiso hdisj hanc =>
      refine ⟨decomposeWith_wf hwf hwf'' hdisj, n + 1, hr.tail ?_⟩
      have hstep : DecompStep P.unfoldMethods (unfoldNet tn an) t
          ⟨(m.abstractTask, an t), unfoldNet m.subtasks fun _ => Insert.insert m.abstractTask (an t)⟩
          (decomposeWith (unfoldNet tn an) t
            (unfoldNet tn'' fun _ => Insert.insert m.abstractTask (an t))) :=
        ⟨⟨m, hm, an t, hanc, rfl⟩, hu.1, by simp [unfoldNet, hα],
          _, unfoldNet_wf hwf'' _, unfoldNet_iso hiso _, hdisj, rfl⟩
      have heq : decomposeWith (unfoldNet tn an) t
          (unfoldNet tn'' fun _ => Insert.insert m.abstractTask (an t)) =
          unfoldNet (decomposeWith tn t tn'')
            (fun x => if x ∈ tn''.T then Insert.insert m.abstractTask (an t) else an x) := by
        apply TaskNetwork.ext'
        · rfl
        · rfl
        funext x
        simp only [decomposeWith, unfoldNet]
        split_ifs <;> rfl
      rw [← heq]
      exact .decomp (t := t) ⟨hu.1, hu.2⟩ hstep
    | @insert s tn an π a happ => exact ⟨hwf, n, hr⟩

/-- The names reachable in the unfolding come from reachable names, with reachable ancestors. -/
theorem unfold_reach {c : C} {S : Set C} (h : P.unfoldPos.ReachableName (c, S)) :
    P.toPos.ReachableName c ∧ S ⊆ {c | P.toPos.ReachableName c} := by
  generalize hcs : (c, S) = cs at h
  induction h generalizing c S with
  | @tnI t cs' ht hc =>
    subst hcs
    simp only [unfoldPos, unfoldNet] at hc
    rcases hα : P.tnI.α t with a | c₀ <;> rw [hα] at hc
    · simp at hc
    · simp only [Sum.map_inr, Sum.inr.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hr : P.toPos.ReachableName c₀ := HTN.Problem.ReachableName.tnI ht hα
      refine ⟨hr, fun c' hc' => ?_⟩
      simp only [initANode, Set.mem_setOf_eq, hα, Sum.inr.injEq] at hc'
      exact hc' ▸ hr
  | @method m' u cs' hm' hr' hu hc ih =>
    subst hcs
    obtain ⟨m, hm, S₀, hanc, rfl⟩ := hm'
    obtain ⟨ihr, ihS⟩ := ih rfl
    simp only [unfoldNet] at hc
    rcases hα : m.subtasks.α u with a | c₀ <;> rw [hα] at hc
    · simp at hc
    · simp only [Sum.map_inr, Sum.inr.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨HTN.Problem.ReachableName.method hm ihr hu hα,
        Set.insert_subset ihr ihS⟩

open Classical in
/-- **A TIHTN progression bound for totally ordered methods.** -/
theorem tihtn_bound_TOM (hP : P.WF) (hto : P.IsTO_M)
    (hfin : {c | P.toPos.ReachableName c}.Finite) {k mm : ℕ} (hk : P.tnI.T.card ≤ k)
    (hm : ∀ m', P.toPos.ReachableMethod m' → m'.subtasks.T.card ≤ mm) :
    P.IsTIHTNProgBound (k * (1 + (mm - 1) * (2 * {c | P.toPos.ReachableName c}.ncard + 2))) := by
  set R := {c | P.toPos.ReachableName c} with hRdef
  set N := R.ncard with hN
  let rk : C × Set C → ℕ := fun x => 2 * (N - x.2.ncard) + if x.1 ∈ x.2 then 1 else 0
  -- the rank decreases along the methods of the unfolding
  have hdec : ∀ m', P.unfoldPos.ReachableMethod m' → ∀ u ∈ m'.subtasks.T, ∀ c',
      m'.subtasks.α u = Sum.inr c' → rk c' < rk m'.abstractTask := by
    rintro m' ⟨⟨m, hm, S₀, hanc, rfl⟩, hr⟩ u hu ⟨c₁, S₁⟩ hc
    obtain ⟨hr₀, hS₀⟩ := P.unfold_reach hr
    simp only [unfoldNet] at hc
    rcases hα : m.subtasks.α u with a | c₀ <;> rw [hα] at hc
    · simp at hc
    · simp only [Sum.map_inr, Sum.inr.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hc₁ : c₀ ∉ S₀ := hanc u hu c₀ hα
      have hfin₀ : S₀.Finite := hfin.subset hS₀
      have hsub : Insert.insert m.abstractTask S₀ ⊆ R := Set.insert_subset hr₀ hS₀
      have hle : (Insert.insert m.abstractTask S₀).ncard ≤ N := Set.ncard_le_ncard hsub hfin
      dsimp only [rk]
      by_cases hin : m.abstractTask ∈ S₀
      · rw [Set.insert_eq_of_mem hin]
        simp only [hc₁, hin, if_true, if_false]
        omega
      · rw [Set.ncard_insert_of_notMem hin hfin₀] at hle ⊢
        simp only [hin, if_false]
        split_ifs <;> omega
  have hrk : ∀ x, P.unfoldPos.ReachableName x → rk x < 2 * N + 2 := by
    rintro ⟨c, S⟩ hx
    dsimp only [rk]
    split_ifs <;> omega
  have hs : P.unfoldPos.IsStratR fun x y => rk x ≤ rk y :=
    ⟨⟨fun _ _ => le_rfl, fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂, fun _ _ _ _ => le_total _ _⟩,
      fun m' hm' u hu _ c' hc' => (hdec m' hm' u hu c' hc').le,
      fun m' hm' u hu _ c' hc' => ⟨(hdec m' hm' u hu c' hc').le, by
        have := hdec m' hm' u hu c' hc'; omega⟩⟩
  have hmm : ∀ m', P.unfoldPos.ReachableMethod m' → m'.subtasks.T.card ≤ mm := by
    rintro m' ⟨⟨m, hm', S₀, hanc, rfl⟩, hr⟩
    exact hm m ⟨hm', (P.unfold_reach hr).1⟩
  have hTO : ∀ m', P.unfoldPos.ReachableMethod m' → m'.subtasks.IsTotallyOrdered := by
    rintro m' ⟨⟨m, hm', S₀, hanc, rfl⟩, hr⟩
    exact hto m ⟨hm', (P.unfold_reach hr).1⟩
  intro nd hnd
  obtain ⟨-, n, hr⟩ := P.absReach_unfold hP hnd
  have := HTN.Problem.progBound_TOM P.unfoldPos hs (f := rk) (fun _ _ _ _ => Iff.rfl) hmm hTO hrk
    (unfoldNet_wf hP.tnI _) hr
  exact this.trans (Nat.mul_le_mul_right _ hk)

end Problem

end Article

end HTN
