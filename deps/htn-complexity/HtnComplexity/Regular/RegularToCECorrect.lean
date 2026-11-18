import HtnComplexity.Regular.RegularToCEStep
import HtnPlanning.Core.DerivationLength
/-!
# Correctness of the linear conditional-effect compilation of regular HTN problems

`HTN.RegularCE.ceProblem_solvable_iff`: the STRIPS-with-conditional-effects problem compiled
from a well-formed, totally ordered, regular HTN problem with a single initial compound task is
solvable exactly when the HTN problem is.

The two halves are

* `HTN.RegularCE.exists_plan_of_derivesN` — a derivation of the initial compound task using `n`
  methods and producing the action sequence `as` is turned into a plan of the compiled problem
  of length `|as| + n` (one action per action of the source plan, one per method application);
* `HTN.RegularCE.derives_of_plan` — every plan of the compiled problem that reaches a `done`
  state is such a derivation.  It is proved by peeling the plan one action at a time, along the
  three configurations of `HtnComplexity/Regular/RegularToCEStep.lean`.

Together with `HTN.Problem.exists_derivesN_le` (the cut-elimination bound on the number of
method applications) the first half gives the plan-length statement
`HTN.RegularCE.exists_solution_length_le`: the compilation is *linear* in the sense of the
compilability framework.
-/

namespace HTN

namespace RegularCE

open CE

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]
variable {D : Domain F A C I} {ms : Finset (Method I A C)} {Q : Instance F A C I}

@[simp] lemma act_start (m : Method I A C) :
    (ceProblem D ms Q).act (CEAct.start m) = startAction D m := rfl

@[simp] lemma act_op (a : A) :
    (ceProblem D ms Q).act (CEAct.op a) = opAction D ms a := rfl

/-! ### From derivations to plans -/

/-- **Executing the rest of the body of a method.** -/
lemma runs_body {m : Method I A C} (hm : m ∈ ms) :
    ∀ (n k : ℕ), (bodyOps m).length - k = n → ∀ s : Set F,
      D.SeqApplicable ((bodyOps m).drop k) s →
        (ceProblem D ms Q).SeqApplicable (((bodyOps m).drop k).map CEAct.op) (encMid s m k) ∧
        (ceProblem D ms Q).transitionSeq (((bodyOps m).drop k).map CEAct.op) (encMid s m k) =
          encMid (D.transitionSeq ((bodyOps m).drop k) s) m (bodyOps m).length := by
  intro n
  induction n with
  | zero =>
      intro k hk s _
      have hle : (bodyOps m).length ≤ k := by omega
      have hdrop : (bodyOps m).drop k = [] := List.drop_eq_nil_of_le hle
      have hmark : posMark (F := F) m k = posMark (F := F) m (bodyOps m).length := by
        rw [posMark_of_getElem_none (List.getElem?_eq_none hle), posMark_length]
      refine ⟨by rw [hdrop]; exact trivial, ?_⟩
      rw [hdrop]
      simp only [List.map_nil, Problem.transitionSeq_nil, ActionModel.transitionSeq_nil]
      rw [encMid, encMid, hmark]
  | succ n ih =>
      intro k hk s happ
      have hklt : k < (bodyOps m).length := by omega
      have hdrop : (bodyOps m).drop k = (bodyOps m)[k] :: (bodyOps m).drop (k + 1) :=
        List.drop_eq_getElem_cons hklt
      have hget : (bodyOps m)[k]? = some (bodyOps m)[k] := List.getElem?_eq_getElem hklt
      rw [hdrop] at happ ⊢
      obtain ⟨happ1, happ2⟩ := happ
      have hstep : (opAction D ms (bodyOps m)[k]).succ (encMid s m k) =
          encMid (D.transition (bodyOps m)[k] s) m (k + 1) := succ_op_encMid hm hget
      obtain ⟨hrest, htr⟩ := ih (k + 1) (by omega) (D.transition (bodyOps m)[k] s) happ2
      constructor
      · refine ⟨?_, ?_⟩
        · exact (applicable_op_encMid_iff hm hget).2 happ1
        · rw [act_op, hstep]
          exact hrest
      · rw [List.map_cons, Problem.transitionSeq_cons, act_op, hstep, htr]
        rfl

/-- **A derivation using `n` methods yields a plan of the compiled problem of length
`|as| + n`.** -/
lemma exists_plan_of_derivesN (hms : (ms : Set (Method I A C)) = D.methods) {n : ℕ} {c : C}
    {as : List A} (hd : (D.mkProblem Q).DerivesN n c as) :
    ∀ s : Set F, D.SeqApplicable as s →
      ∃ plan : List (CEAct A C I), plan.length = as.length + n ∧
        (ceProblem D ms Q).SeqApplicable plan (encP s c) ∧
        (ceProblem D ms Q).transitionSeq plan (encP s c) = encD (D.transitionSeq as s) := by
  induction hd with
  | @last c os m hm hc hb =>
      intro s happ
      have hmem : m ∈ ms := by rw [← Finset.mem_coe, hms]; exact hm
      have hu : Usable D m := ⟨hm, ⟨(os, none), hb⟩⟩
      have hops : bodyOps m = os := bodyOps_eq hb
      have hnext : bodyNext m = none := bodyNext_eq hb
      subst hc
      rw [← hops] at happ ⊢
      obtain ⟨hrun, htr⟩ := runs_body (Q := Q) hmem (bodyOps m).length 0 (by omega) s
        (by simpa using happ)
      simp only [List.drop_zero] at hrun htr
      have hfin : encMid (D.transitionSeq (bodyOps m) s) m (bodyOps m).length =
          encD (D.transitionSeq (bodyOps m) s) := by rw [encMid_length, hnext]
      refine ⟨CEAct.start m :: ((bodyOps m).map CEAct.op), by simp, ⟨?_, ?_⟩, ?_⟩
      · rw [act_start]
        exact applicable_start_encP_iff.2 ⟨rfl, hu⟩
      · rw [act_start, succ_start_encP]
        exact hrun
      · rw [Problem.transitionSeq_cons, act_start, succ_start_encP, htr, hfin]
  | @cons n c c' os rest m hm hc hb h ih =>
      intro s happ
      rw [D.seqApplicable_append] at happ
      obtain ⟨happ1, happ2⟩ := happ
      obtain ⟨plan, hlen, hpapp, hptr⟩ := ih (D.transitionSeq os s) happ2
      have hmem : m ∈ ms := by rw [← Finset.mem_coe, hms]; exact hm
      have hu : Usable D m := ⟨hm, ⟨(os, some c'), hb⟩⟩
      have hops : bodyOps m = os := bodyOps_eq hb
      have hnext : bodyNext m = some c' := bodyNext_eq hb
      subst hc
      rw [← hops] at happ1 hpapp hptr ⊢
      obtain ⟨hrun, htr⟩ := runs_body (Q := Q) hmem (bodyOps m).length 0 (by omega) s
        (by simpa using happ1)
      simp only [List.drop_zero] at hrun htr
      have hmid : encMid (D.transitionSeq (bodyOps m) s) m (bodyOps m).length =
          encP (D.transitionSeq (bodyOps m) s) c' := by rw [encMid_length, hnext]
      refine ⟨CEAct.start m :: ((bodyOps m).map CEAct.op ++ plan), ?_, ⟨?_, ?_⟩, ?_⟩
      · simp only [List.length_cons, List.length_append, List.length_map, hlen,
          List.length_append]
        omega
      · rw [act_start]
        exact applicable_start_encP_iff.2 ⟨rfl, hu⟩
      · rw [act_start, succ_start_encP, Problem.seqApplicable_append]
        exact ⟨hrun, by rw [htr, hmid]; exact hpapp⟩
      · rw [Problem.transitionSeq_cons, act_start, succ_start_encP,
          Problem.transitionSeq_append, htr, hmid, hptr, D.transitionSeq_append]

/-! ### From plans to derivations -/

/-- The configurations a plan of the compiled problem passes through. -/
inductive Cfg (A : Type v) (C : Type w) (I : Type x)
  /-- A compound task is still open. -/
  | pend (c : C)
  /-- The body of a method is being executed. -/
  | mid (m : Method I A C) (k : ℕ)
  /-- The hierarchy is fully decomposed. -/
  | fin

/-- The state of the compiled problem a configuration describes. -/
noncomputable def encC (s : Set F) : Cfg A C I → Set (CEFact F A C I)
  | Cfg.pend c => encP s c
  | Cfg.mid m k => encMid s m k
  | Cfg.fin => encD s

/-- A configuration inside the body of a method has to be a genuine position of a method of the
domain. -/
def CfgOk (ms : Finset (Method I A C)) : Cfg A C I → Prop
  | Cfg.pend _ => True
  | Cfg.mid m k => m ∈ ms ∧ k < (bodyOps m).length
  | Cfg.fin => True

/-- What the action sequence extracted from a plan has to be, per configuration: a derivation of
the open compound task, resp. the rest of the body of the method being executed followed by a
derivation of the task it leaves open. -/
def TailRes (D : Domain F A C I) (Q : Instance F A C I) : Option C → List A → Prop
  | none => fun as => as = []
  | some c' => fun as => (D.mkProblem Q).Derives c' as

/-- The specification of the action sequence extracted from a plan, per configuration. -/
noncomputable def Res (D : Domain F A C I) (Q : Instance F A C I) : Cfg A C I → List A → Prop
  | Cfg.pend c => fun as => (D.mkProblem Q).Derives c as
  | Cfg.mid m k => fun as => ∃ rest, as = (bodyOps m).drop k ++ rest ∧
      TailRes D Q (bodyNext m) rest
  | Cfg.fin => fun as => as = []

/-- The configuration reached at the end of the body of a method. -/
private noncomputable def tailCfg (m : Method I A C) : Cfg A C I :=
  match bodyNext m with
  | none => Cfg.fin
  | some c' => Cfg.pend c'

private lemma encC_tailCfg (s : Set F) (m : Method I A C) :
    encC s (tailCfg m : Cfg A C I) = encMid s m (bodyOps m).length := by
  rw [tailCfg, encMid_length]
  cases hb : bodyNext m with
  | none => rfl
  | some c' => rfl

private lemma cfgOk_tailCfg (m : Method I A C) : CfgOk ms (tailCfg m : Cfg A C I) := by
  rw [tailCfg]
  cases hb : bodyNext m with
  | none => exact trivial
  | some c' => exact trivial

private lemma tailRes_of_res_tailCfg {m : Method I A C} {as : List A}
    (h : Res D Q (tailCfg m : Cfg A C I) as) : TailRes D Q (bodyNext m) as := by
  rw [tailCfg] at h
  cases hb : bodyNext m with
  | none => rw [hb] at h; exact h
  | some c' => rw [hb] at h; exact h

/-- **Every plan of the compiled problem that reaches a `done` state is a derivation.** -/
lemma derives_of_plan (hms : (ms : Set (Method I A C)) = D.methods) (g : Set F) :
    ∀ (plan : List (CEAct A C I)) (s : Set F) (cfg : Cfg A C I), CfgOk ms cfg →
      (ceProblem D ms Q).SeqApplicable plan (encC s cfg) →
      (CEFact.done : CEFact F A C I) ∈ (ceProblem D ms Q).transitionSeq plan (encC s cfg) →
      encS g ⊆ (ceProblem D ms Q).transitionSeq plan (encC s cfg) →
      ∃ as : List A, D.SeqApplicable as s ∧ g ⊆ D.transitionSeq as s ∧ Res D Q cfg as := by
  intro plan
  induction plan with
  | nil =>
      intro s cfg hok _ hdone hgoal
      simp only [Problem.transitionSeq_nil] at hdone hgoal
      cases cfg with
      | pend c => exact absurd hdone (by rw [encC]; exact done_notMem_encP)
      | mid m k =>
          exfalso
          obtain ⟨-, hk⟩ := hok
          obtain ⟨a, ha⟩ : ∃ a, (bodyOps m)[k]? = some a :=
            ⟨_, List.getElem?_eq_getElem hk⟩
          rw [encC, encMid, posMark_of_getElem ha] at hdone
          rcases hdone with h | h
          · exact done_notMem_encS h
          · rcases h with h | h <;> exact absurd h (by simp)
      | fin =>
          refine ⟨[], trivial, ?_, rfl⟩
          intro v hv
          have : (CEFact.state v : CEFact F A C I) ∈ encC s (Cfg.fin : Cfg A C I) :=
            hgoal ⟨v, hv, rfl⟩
          rw [encC] at this
          simpa using this
  | cons act rest ih =>
      intro s cfg hok happ hdone hgoal
      obtain ⟨happ1, happ2⟩ := happ
      cases cfg with
      | pend c =>
          rw [encC] at happ1 happ2 hdone hgoal
          cases act with
          | op a => exact absurd happ1 not_applicable_op_encP
          | start m =>
              obtain ⟨hc, hu⟩ := applicable_start_encP_iff.1 happ1
              subst hc
              have hmem : m ∈ ms := by rw [← Finset.mem_coe, hms]; exact hu.1
              have hb : m.HasBody (bodyOps m) (bodyNext m) := hasBody_of_usable hu
              rw [act_start, succ_start_encP] at happ2
              rw [Problem.transitionSeq_cons, act_start, succ_start_encP] at hdone hgoal
              by_cases hlen : 0 < (bodyOps m).length
              · have hok' : CfgOk ms (Cfg.mid m 0 : Cfg A C I) := ⟨hmem, hlen⟩
                have heq : encC s (Cfg.mid m 0 : Cfg A C I) = encMid s m 0 := rfl
                rw [← heq] at happ2 hdone hgoal
                obtain ⟨as, hasapp, hasgoal, hres⟩ := ih s (Cfg.mid m 0) hok' happ2 hdone hgoal
                rw [Res] at hres
                obtain ⟨tl, rfl, htl⟩ := hres
                simp only [List.drop_zero] at hasapp hasgoal
                refine ⟨bodyOps m ++ tl, hasapp, hasgoal, ?_⟩
                rw [Res]
                cases hn : bodyNext m with
                | none =>
                    rw [hn] at htl
                    rw [TailRes] at htl
                    subst htl
                    have hb' : m.HasBody (bodyOps m) none := by rw [← hn]; exact hb
                    simpa using Problem.Derives.last hu.1 rfl hb'
                | some c' =>
                    rw [hn] at htl
                    rw [TailRes] at htl
                    have hb' : m.HasBody (bodyOps m) (some c') := by rw [← hn]; exact hb
                    exact Problem.Derives.cons hu.1 rfl hb' htl
              · have hzero : (bodyOps m).length = 0 := by omega
                have heq : encC s (tailCfg m : Cfg A C I) = encMid s m 0 := by
                  rw [encC_tailCfg, hzero]
                rw [← heq] at happ2 hdone hgoal
                obtain ⟨as, hasapp, hasgoal, hres⟩ :=
                  ih s (tailCfg m) (cfgOk_tailCfg m) happ2 hdone hgoal
                refine ⟨as, hasapp, hasgoal, ?_⟩
                rw [Res]
                have htl := tailRes_of_res_tailCfg hres
                have hnil : bodyOps m = [] := List.eq_nil_of_length_eq_zero hzero
                cases hn : bodyNext m with
                | none =>
                    rw [hn] at htl
                    rw [TailRes] at htl
                    subst htl
                    have hb' : m.HasBody (bodyOps m) none := by rw [← hn]; exact hb
                    have hlast := Problem.Derives.last (P := D.mkProblem Q) hu.1 rfl hb'
                    rwa [hnil] at hlast
                | some c' =>
                    rw [hn] at htl
                    rw [TailRes] at htl
                    have hb' : m.HasBody (bodyOps m) (some c') := by rw [← hn]; exact hb
                    have := Problem.Derives.cons hu.1 rfl hb' htl
                    rwa [hnil, List.nil_append] at this
      | fin =>
          exfalso
          rw [encC] at happ1
          cases act with
          | op a => exact not_applicable_op_encD happ1
          | start m => exact not_applicable_start_encD happ1
      | mid m k =>
          obtain ⟨hmem, hk⟩ := hok
          have hget : (bodyOps m)[k]? = some (bodyOps m)[k] := List.getElem?_eq_getElem hk
          rw [encC] at happ1 happ2 hdone hgoal
          cases act with
          | start m' => exact absurd happ1 (not_applicable_start_encMid hk)
          | op a =>
              have hae : a = (bodyOps m)[k] := eq_of_applicable_op_encMid hget happ1
              have hget2 : (bodyOps m)[k]? = some a := by rw [hget, hae]
              have hprec : D.prec a ⊆ s := (applicable_op_encMid_iff hmem hget2).1 happ1
              have hstep : (opAction D ms a).succ (encMid s m k) =
                  encMid (D.transition a s) m (k + 1) := succ_op_encMid hmem hget2
              rw [act_op, hstep] at happ2
              rw [Problem.transitionSeq_cons, act_op, hstep] at hdone hgoal
              have hdropk : (bodyOps m).drop k = a :: (bodyOps m).drop (k + 1) := by
                rw [List.drop_eq_getElem_cons hk, hae]
              by_cases hlen : k + 1 < (bodyOps m).length
              · have hok' : CfgOk ms (Cfg.mid m (k + 1) : Cfg A C I) := ⟨hmem, hlen⟩
                have heq : encC (D.transition a s) (Cfg.mid m (k + 1) : Cfg A C I) =
                    encMid (D.transition a s) m (k + 1) := rfl
                rw [← heq] at happ2 hdone hgoal
                obtain ⟨as, hasapp, hasgoal, hres⟩ :=
                  ih (D.transition a s) (Cfg.mid m (k + 1)) hok' happ2 hdone hgoal
                rw [Res] at hres
                obtain ⟨tl, rfl, htl⟩ := hres
                refine ⟨a :: ((bodyOps m).drop (k + 1) ++ tl), ⟨hprec, hasapp⟩, hasgoal, ?_⟩
                exact ⟨tl, by rw [hdropk, List.cons_append], htl⟩
              · have hlen' : k + 1 = (bodyOps m).length := by omega
                have heq : encC (D.transition a s) (tailCfg m : Cfg A C I) =
                    encMid (D.transition a s) m (k + 1) := by
                  rw [encC_tailCfg, hlen']
                rw [← heq] at happ2 hdone hgoal
                obtain ⟨as, hasapp, hasgoal, hres⟩ :=
                  ih (D.transition a s) (tailCfg m) (cfgOk_tailCfg m) happ2 hdone hgoal
                have htl := tailRes_of_res_tailCfg hres
                refine ⟨a :: as, ⟨hprec, hasapp⟩, hasgoal, ⟨as, ?_, htl⟩⟩
                rw [hdropk, List.drop_eq_nil_of_le (by omega), List.singleton_append]

/-! ### Correctness -/

/-- For a problem with a single initial compound task the initial state of the compiled problem
is the encoding of the initial state together with that task. -/
lemma ceProblem_init {t₀ : I} {c₀ : C} (hT : Q.tnI.T = {t₀})
    (hα : Q.tnI.α t₀ = Sum.inr c₀) : (ceProblem D ms Q).init = encP Q.init c₀ := by
  ext f
  simp only [ceProblem, encP, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro (hf | ⟨c, ⟨t, hTt, hαt⟩, rfl⟩)
    · exact Or.inl hf
    · refine Or.inr ?_
      have ht : t = t₀ := by
        have hmem : t ∈ Q.tnI.T := by rw [hTt]; simp
        rw [hT] at hmem
        simpa using hmem
      subst ht
      rw [hα] at hαt
      simp only [Sum.inr.injEq] at hαt
      rw [hαt]
  · rintro (hf | rfl)
    · exact Or.inl hf
    · exact Or.inr ⟨c₀, ⟨t₀, hT, hα⟩, rfl⟩

/-- **The compiled STRIPS-with-conditional-effects problem is solvable exactly when the regular
HTN problem is.** -/
theorem ceProblem_solvable_iff [Infinite I] (hms : (ms : Set (Method I A C)) = D.methods)
    (hwf : (D.mkProblem Q).WF) (hreg : (D.mkProblem Q).IsRegularM)
    (hto : (D.mkProblem Q).IsTO_M) {t₀ : I} {c₀ : C} (hT : Q.tnI.T = {t₀})
    (hα : Q.tnI.α t₀ = Sum.inr c₀) :
    (ceProblem D ms Q).Solvable ↔ (D.mkProblem Q).Solvable := by
  have hinit : (ceProblem D ms Q).init = encP Q.init c₀ := ceProblem_init hT hα
  have hderiv := Problem.solvable_iff_derives (P := D.mkProblem Q) hwf hreg hto hT hα
  constructor
  · rintro ⟨plan, happ, hgoal⟩
    rw [hinit] at happ hgoal
    obtain ⟨hpos, -⟩ := hgoal
    have hdone : (CEFact.done : CEFact F A C I) ∈
        (ceProblem D ms Q).transitionSeq plan (encP Q.init c₀) := hpos (Or.inr rfl)
    have hst : encS Q.goal ⊆ (ceProblem D ms Q).transitionSeq plan (encP Q.init c₀) :=
      fun f hf => hpos (Or.inl hf)
    have heq : encC Q.init (Cfg.pend c₀ : Cfg A C I) = encP Q.init c₀ := rfl
    rw [← heq] at happ hdone hst
    obtain ⟨as, hasapp, hasgoal, hres⟩ :=
      derives_of_plan (Q := Q) hms Q.goal plan Q.init (Cfg.pend c₀) trivial happ hdone hst
    exact hderiv.2 ⟨as, hres, hasapp, hasgoal⟩
  · intro hsol
    obtain ⟨as, hd, happ, hgoal⟩ := hderiv.1 hsol
    obtain ⟨n, hdn⟩ := hd.exists_derivesN
    obtain ⟨plan, -, hpapp, hptr⟩ := exists_plan_of_derivesN (Q := Q) hms hdn Q.init happ
    refine ⟨plan, ?_, ?_⟩
    · rw [hinit]; exact hpapp
    · rw [hinit, hptr]
      refine ⟨?_, fun f hf => absurd hf (Set.notMem_empty f)⟩
      rintro f (hf | hf)
      · obtain ⟨v, hv, rfl⟩ := hf
        exact state_mem_encD.2 (hgoal hv)
      · simp only [Set.mem_singleton_iff] at hf
        subst hf
        exact done_mem_encD

/-! ### The compilation is linear -/

/-- **The compiled problem has a short solution.**  If the regular, totally ordered HTN problem
has a solution plan `as`, then the compiled problem has a solution of length at most
`|as| + (|as| + 1) · (|C| + 1)`: one action per action of the source plan, plus one action per
method application, of which the cut-elimination bound of
`HtnPlanning/Core/DerivationLength.lean` allows at most `(|as| + 1) · (|C| + 1)`. -/
theorem exists_solution_length_le [Fintype C] [Infinite I]
    (hms : (ms : Set (Method I A C)) = D.methods)
    (hwf : (D.mkProblem Q).WF) (hreg : (D.mkProblem Q).IsRegularM)
    (hto : (D.mkProblem Q).IsTO_M) {t₀ : I} {c₀ : C} (hT : Q.tnI.T = {t₀})
    (hα : Q.tnI.α t₀ = Sum.inr c₀) {as : List A}
    (hsol : (D.mkProblem Q).IsSolutionPlan as) :
    ∃ plan : List (CEAct A C I), (ceProblem D ms Q).IsSolution plan ∧
      plan.length ≤ as.length + (as.length + 1) * (Fintype.card C + 1) := by
  classical
  have hd : (D.mkProblem Q).Derives c₀ as :=
    Problem.derives_of_isSolutionPlan hwf hreg hto hT hα hsol
  obtain ⟨-, -, -, -, -, -, happ, hgoal⟩ := hsol
  obtain ⟨n, hn, hdn⟩ := Problem.exists_derivesN_le hd
  obtain ⟨plan, hplen, hpapp, hptr⟩ := exists_plan_of_derivesN (Q := Q) hms hdn Q.init happ
  have hinit : (ceProblem D ms Q).init = encP Q.init c₀ := ceProblem_init hT hα
  refine ⟨plan, ⟨?_, ?_⟩, ?_⟩
  · rw [hinit]; exact hpapp
  · rw [hinit, hptr]
    refine ⟨?_, fun f hf => absurd hf (Set.notMem_empty f)⟩
    rintro f (hf | hf)
    · obtain ⟨v, hv, rfl⟩ := hf
      exact state_mem_encD.2 (hgoal hv)
    · simp only [Set.mem_singleton_iff] at hf
      subst hf
      exact done_mem_encD
  · rw [hplen]
    omega

end RegularCE

end HTN
