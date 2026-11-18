import HtnComplexity.Article.CFGEnc
import HtnComplexity.Article.GridFull
import HtnComplexity.Undec.Bridge
import HtnPlanning.Article.OfSyn
/-!
# The descriptions of the grammar encoding

`HtnComplexity/Article/CFGEnc.lean` builds the problem of the proof of Thm. 4.1.1 as a semantic
object.  This file writes it down:

* `HTN.Article.CFGEnc.cfgDom`, `HTN.Article.CFGEnc.cfgInst` — the domain and instance
  descriptions (in the format of `HTN.Syn.DomDesc`, `HTN.Syn.InstDesc`);
* `HTN.Article.CFGEnc.cfgProb` — the same as a description of the article's model
  (`HTN.Article.ofSyn`: no negative preconditions, no negative goal);
* `HTN.Article.CFGEnc.solvable_cfgProb_iff` — **it has a solution iff the grammars have a common
  word**;
* `HTN.Article.CFGEnc.valid_cfgProb` — it is well formed.
-/

namespace HTN

namespace Article

namespace CFGEnc

open CFG Syn TaskNetwork Domain

/-- The action of the task name `n`: `2σ` is `σ`, `2σ + 1` is `σ'`. -/
def actOf (n : ℕ) : List ℕ × List ℕ × List ℕ :=
  if n % 2 = 0 then ([0], [1, n / 2 + 2], [0]) else ([1, n / 2 + 2], [0], [1, n / 2 + 2])

/-- The actions for the terminals below `B`. -/
def actD (B : ℕ) : List ActionDesc := (List.range (2 * B)).map fun n => (n, actOf n)

/-- The method of a rule of the grammar `k`. -/
def methD (k : ℕ) (r : Rule) : MethodDesc := (2 * r.1 + k, gridDescFullOf id id [r.2.map (trS k)])

/-- **The described domain of the encoding.** -/
def cfgDom (g₁ g₂ : Grammar) : DomDesc :=
  (actD (bnd g₁ g₂), g₁.rules.map (methD 0) ++ g₂.rules.map (methD 1))

/-- **The described instance of the encoding.** -/
def cfgInst (g₁ g₂ : Grammar) : InstDesc :=
  ([0], [0], gridDescFullOf id id [[Sum.inr (2 * g₁.start)], [Sum.inr (2 * g₂.start + 1)]])

/-- **The encoding, as a description of the article's model.** -/
def cfgProb (g₁ g₂ : Grammar) : ProbDesc := ofSyn (cfgDom g₁ g₂) (cfgInst g₁ g₂)

variable {g₁ g₂ : Grammar}

/-! ### The action model -/

theorem lookup_cfgDom (n : ℕ) : (cfgDom g₁ g₂).actions.lookup n =
    if n / 2 < bnd g₁ g₂ then some (actOf n) else none := by
  unfold cfgDom DomDesc.actions actD
  split_ifs with h
  · exact Undec.lookup_map_self _ _ (List.mem_range.2 (by omega))
  · exact Undec.lookup_map_self_none _ _ (fun hm => h (by have := List.mem_range.1 hm; omega))

theorem prec_cfgDom (n : ℕ) : (cfgDom g₁ g₂).prec n = (semDom g₁ g₂).prec n := by
  unfold DomDesc.prec
  rw [lookup_cfgDom]
  simp only [semDom]
  split_ifs <;> ext x <;> simp_all [actOf]

theorem add_cfgDom (n : ℕ) : (cfgDom g₁ g₂).add n = (semDom g₁ g₂).add n := by
  unfold DomDesc.add
  rw [lookup_cfgDom]
  simp only [semDom]
  split_ifs <;> ext x <;> simp_all [actOf]

theorem del_cfgDom (n : ℕ) : (cfgDom g₁ g₂).del n = (semDom g₁ g₂).del n := by
  unfold DomDesc.del
  rw [lookup_cfgDom]
  simp only [semDom]
  split_ifs <;> ext x <;> simp_all [actOf]

/-! ### The methods -/

theorem methodsIsoEquiv_cfgDom :
    HTN.Problem.MethodsIsoEquiv
      {m : Method ℕ ℕ ℕ | ∃ e ∈ (cfgDom g₁ g₂).methods, e.toMethod = m}
      (Method.relabel id id Nat.pairEquiv '' (semDom g₁ g₂).methods) := by
  have hiso : ∀ k (r : Rule), (methD k r).toMethod.subtasks.Iso
      (TaskNetwork.relabel id id Nat.pairEquiv (TaskNetwork.grid [r.2.map (trS k)])) := by
    intro k r
    show (gridDescFullOf id id [r.2.map (trS k)]).toTaskNetwork.Iso _
    rw [toTaskNetwork_gridDescFullOf]
    exact gridDesc_iso id id _
  constructor
  · rintro m ⟨e, he, rfl⟩
    simp only [cfgDom, DomDesc.methods, List.mem_append, List.mem_map] at he
    rcases he with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · exact ⟨Method.relabel id id Nat.pairEquiv ⟨2 * r.1 + 0, grid [r.2.map (trS 0)]⟩,
        ⟨_, Or.inl ⟨r, hr, rfl⟩, rfl⟩, rfl, hiso 0 r⟩
    · exact ⟨Method.relabel id id Nat.pairEquiv ⟨2 * r.1 + 1, grid [r.2.map (trS 1)]⟩,
        ⟨_, Or.inr ⟨r, hr, rfl⟩, rfl⟩, rfl, hiso 1 r⟩
  · rintro m ⟨m', (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩), rfl⟩
    · refine ⟨(methD 0 r).toMethod, ⟨_, ?_, rfl⟩, rfl, (hiso 0 r).symm⟩
      simp only [cfgDom, DomDesc.methods, List.mem_append, List.mem_map]
      exact Or.inl ⟨r, hr, rfl⟩
    · refine ⟨(methD 1 r).toMethod, ⟨_, ?_, rfl⟩, rfl, (hiso 1 r).symm⟩
      simp only [cfgDom, DomDesc.methods, List.mem_append, List.mem_map]
      exact Or.inr ⟨r, hr, rfl⟩

/-- **The described problem is the semantic one.** -/
theorem solvable_cfg_iff_sem :
    Syn.Solvable (cfgDom g₁ g₂) (cfgInst g₁ g₂) ↔ (semProblem g₁ g₂).Solvable := by
  classical
  set PD := Syn.problem (cfgDom g₁ g₂) (cfgInst g₁ g₂)
  set PS := semProblem g₁ g₂
  set tn' := TaskNetwork.relabel id id Nat.pairEquiv PS.tnI
  set N := Method.relabel (I := ℕ × ℕ) (I' := ℕ) id id Nat.pairEquiv '' PS.methods
  have htnIiso : PD.tnI.Iso tn' := by
    show (gridDescFullOf id id _).toTaskNetwork.Iso _
    rw [toTaskNetwork_gridDescFullOf]
    exact gridDesc_iso id id _
  have hwfPD : PD.tnI.WF := TnDesc.toTaskNetwork_wf _
  have hwftn' : tn'.WF := TaskNetwork.relabel_wf TaskNetwork.grid_wf
  have step1 : PD.Solvable ↔ (PD.withTnI tn').Solvable := by
    refine Iff.trans (Iff.of_eq (congrArg HTN.Problem.Solvable (rfl : PD = PD.withTnI PD.tnI))) ?_
    exact HTN.Problem.solvable_congr_tnI_iff PD hwfPD hwftn' htnIiso
  have hmiso : HTN.Problem.MethodsIsoEquiv (PD.withTnI tn').methods N := methodsIsoEquiv_cfgDom
  have step2 : (PD.withTnI tn').Solvable ↔ ((PD.withTnI tn').withMethods N).Solvable :=
    (HTN.Problem.solvable_congr_methods hmiso).symm
  have step3 : ((PD.withTnI tn').withMethods N).Solvable ↔ PS.Solvable := by
    refine HTN.Problem.solvable_relabel_iff (eF := id) (eA := id) (eC := id) (eI := Nat.pairEquiv)
      Function.injective_id Function.injective_id Function.injective_id
      (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_) ?_ ?_ TaskNetwork.grid_wf rfl rfl
    · show (cfgDom g₁ g₂).prec o = _
      rw [prec_cfgDom, Set.image_id]; rfl
    · show (cfgDom g₁ g₂).add o = _
      rw [add_cfgDom, Set.image_id]; rfl
    · show (cfgDom g₁ g₂).del o = _
      rw [del_cfgDom, Set.image_id]; rfl
    · show {f | f ∈ [0]} = _
      rw [Set.image_id]
      show {f | f ∈ [0]} = ({0} : Set ℕ)
      ext x; simp
    · show {f | f ∈ [0]} = _
      rw [Set.image_id]
      show {f | f ∈ [0]} = ({0} : Set ℕ)
      ext x; simp
  exact step1.trans (step2.trans step3)

/-- **The described encoding has a solution iff the grammars have a common word.** -/
theorem solvable_cfgDom_iff : Syn.Solvable (cfgDom g₁ g₂) (cfgInst g₁ g₂) ↔ Inter g₁ g₂ :=
  solvable_cfg_iff_sem.trans solvable_semProblem_iff

/-- **Thm. 4.1.1, the encoding in the article's model.** -/
theorem solvable_cfgProb_iff : (cfgProb g₁ g₂).toProblem.Solvable ↔ Inter g₁ g₂ :=
  (solvable_ofSyn_iff _ _).trans solvable_cfgDom_iff

/-! ### Well-formedness -/

theorem lt_bnd_of_rule₁ {r : Rule} (hr : r ∈ g₁.rules) {a : ℕ} (ha : Sum.inl a ∈ r.2) :
    a < bnd g₁ g₂ := by
  have hmem : a ∈ terms g₁ := List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨_, ha, by simp⟩⟩
  have := le_foldr_max (l := terms g₁ ++ terms g₂) (List.mem_append_left _ hmem)
  unfold bnd; omega

theorem lt_bnd_of_rule₂ {r : Rule} (hr : r ∈ g₂.rules) {a : ℕ} (ha : Sum.inl a ∈ r.2) :
    a < bnd g₁ g₂ := by
  have hmem : a ∈ terms g₂ := List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨_, ha, by simp⟩⟩
  have := le_foldr_max (l := terms g₁ ++ terms g₂) (List.mem_append_right _ hmem)
  unfold bnd; omega

theorem names_cfgDom : (cfgDom g₁ g₂).actions.map Prod.fst = List.range (2 * bnd g₁ g₂) := by
  simp [cfgDom, DomDesc.actions, actD, Function.comp_def]

theorem prim_methD {k : ℕ} (hk : k < 2) {r : Rule}
    (hb : ∀ a, Sum.inl a ∈ r.2 → a < bnd g₁ g₂) :
    ∀ row ∈ [(r.2.map (trS k)).map (encLabel id id)], ∀ n, (false, n) ∈ row →
      n ∈ (cfgDom g₁ g₂).actions.map Prod.fst := by
  intro row hrow n hn
  simp only [List.mem_singleton] at hrow
  subst hrow
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hn
  obtain ⟨x, hx, hxn⟩ := hn
  rcases x with a | X
  · simp only [trS, encLabel, id, Prod.mk.injEq, true_and] at hxn
    rw [names_cfgDom, List.mem_range, ← hxn]
    have := hb a hx
    omega
  · simp [trS, encLabel] at hxn

/-- **The described encoding is well formed.** -/
theorem valid_cfgProb : (cfgProb g₁ g₂).Valid := by
  refine valid_ofSyn ?_ ?_ ?_
  · rw [names_cfgDom]; exact List.nodup_range
  · refine tnValid_gridDescFull ?_
    intro row hrow n hn
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl <;> simp [encLabel] at hn
  · intro m hm
    simp only [cfgDom, DomDesc.methods, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · exact tnValid_gridDescFull (prim_methD (k := 0) (by omega) fun a ha => lt_bnd_of_rule₁ hr ha)
    · exact tnValid_gridDescFull (prim_methD (k := 1) (by omega) fun a ha => lt_bnd_of_rule₂ hr ha)

end CFGEnc

end Article

end HTN
