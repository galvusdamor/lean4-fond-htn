import HtnComplexity.Article.SATReg
import HtnComplexity.Article.Undecidability
/-!
# The descriptions of the regular encoding of satisfiability (Thm. 4.3.12)

* `HTN.Article.SATReg.regProb φ` — the description of the encoding of
  `HtnComplexity/Article/SATReg.lean`, well formed (`valid_regProb`), regular, acyclic and totally
  ordered (`isREG_regProb`, `isACYC_regProb`, `isTO_regProb`), polynomial-time (`pt_regProb`);
* `HTN.Article.SATReg.solvable_regProb_iff` — solvable iff the formula is satisfiable;
* **`HTN.Article.thm_4_3_12`** — `PlanEx^REG∩ACYC∩TO_htn` and `PlanEx^REG∩ACYC∩TO-M_htn` are
  NP-hard.
-/

namespace HTN

namespace Article

namespace SATReg

open Syn Syn.PolyDom PTime NPHard SATNo TaskNetwork HTN.Domain

variable (φ : CNF)

/-- The actions. -/
def actD : List ActionDesc :=
  (List.range (2 * K φ)).map fun n => (n, ([], clauses φ (n / 2) (n % 2 == 0), []))

/-- The described body of a method. -/
def bodyTn (i c : ℕ) : TnDesc := gridDescFullOf id id [body φ i c]

/-- The two methods of the variable `i`. -/
def methsOf (i : ℕ) : List MethodDesc := [(i, bodyTn φ i 0), (i, bodyTn φ i 1)]

/-- **The described domain.** -/
def regDom : DomDesc := (actD φ, (List.range (K φ)).flatMap (methsOf φ))

/-- **The described instance.** -/
def regInst : InstDesc := ([], List.range φ.length, gridDescFullOf id id [[Sum.inr 0]])

/-- **The encoding, in the article's format.** -/
def regProb : ProbDesc := ofSyn (regDom φ) (regInst φ)

variable {φ}

theorem lookup_regDom (n : ℕ) : (regDom φ).actions.lookup n =
    if n < 2 * K φ then some ([], clauses φ (n / 2) (n % 2 == 0), []) else none := by
  unfold regDom DomDesc.actions actD
  split_ifs with h
  · exact Undec.lookup_map_self _ _ (List.mem_range.2 h)
  · exact Undec.lookup_map_self_none _ _ (fun hm => h (List.mem_range.1 hm))

theorem prec_regDom (n : ℕ) : (regDom φ).prec n = (semDom φ).prec n := by
  unfold DomDesc.prec; rw [lookup_regDom]; simp only [semDom]
  split_ifs <;> ext x <;> simp

theorem add_regDom (n : ℕ) : (regDom φ).add n = (semDom φ).add n := by
  unfold DomDesc.add; rw [lookup_regDom]; simp only [semDom]
  split_ifs <;> ext x <;> simp

theorem del_regDom (n : ℕ) : (regDom φ).del n = (semDom φ).del n := by
  unfold DomDesc.del; rw [lookup_regDom]; simp only [semDom]
  split_ifs <;> ext x <;> simp

theorem mem_regDom_methods {e : MethodDesc} :
    e ∈ (regDom φ).methods ↔ ∃ i < K φ, ∃ c < 2, e = (i, gridDescFullOf id id [body φ i c]) := by
  simp only [regDom, DomDesc.methods, methsOf, bodyTn, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact ⟨i, hi, 0, by omega, rfl⟩
    · exact ⟨i, hi, 1, by omega, rfl⟩
  · rintro ⟨i, hi, c, hc, rfl⟩
    interval_cases c
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩

theorem methodsIsoEquiv_regDom :
    HTN.Problem.MethodsIsoEquiv
      {m : Method ℕ ℕ ℕ | ∃ e ∈ (regDom φ).methods, e.toMethod = m}
      (Method.relabel id id Nat.pairEquiv '' (semDom φ).methods) := by
  have hiso : ∀ i c, (MethodDesc.toMethod (i, gridDescFullOf id id [body φ i c])).subtasks.Iso
      (TaskNetwork.relabel id id Nat.pairEquiv (TaskNetwork.grid [body φ i c])) := by
    intro i c
    show (gridDescFullOf id id [body φ i c]).toTaskNetwork.Iso _
    rw [toTaskNetwork_gridDescFullOf]
    exact gridDesc_iso id id _
  constructor
  · rintro m ⟨e, he, rfl⟩
    obtain ⟨i, hi, c, hc, rfl⟩ := mem_regDom_methods.1 he
    exact ⟨Method.relabel id id Nat.pairEquiv ⟨i, grid [body φ i c]⟩,
      ⟨_, ⟨i, hi, c, hc, rfl⟩, rfl⟩, rfl, hiso i c⟩
  · rintro m ⟨m', ⟨i, hi, c, hc, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, mem_regDom_methods.2 ⟨i, hi, c, hc, rfl⟩, rfl⟩, rfl, (hiso i c).symm⟩

theorem solvable_reg_iff_sem :
    Syn.Solvable (regDom φ) (regInst φ) ↔ (semProblem φ).Solvable := by
  classical
  set PD := Syn.problem (regDom φ) (regInst φ)
  set PS := semProblem φ
  set tn' := TaskNetwork.relabel id id Nat.pairEquiv PS.tnI
  set N := Method.relabel (I := ℕ × ℕ) (I' := ℕ) id id Nat.pairEquiv '' PS.methods
  have htnIiso : PD.tnI.Iso tn' := by
    show (gridDescFullOf id id _).toTaskNetwork.Iso _
    rw [toTaskNetwork_gridDescFullOf]
    exact gridDesc_iso id id _
  have step1 : PD.Solvable ↔ (PD.withTnI tn').Solvable := by
    refine Iff.trans (Iff.of_eq (congrArg HTN.Problem.Solvable (rfl : PD = PD.withTnI PD.tnI))) ?_
    exact HTN.Problem.solvable_congr_tnI_iff PD (TnDesc.toTaskNetwork_wf _)
      (TaskNetwork.relabel_wf TaskNetwork.grid_wf) htnIiso
  have step2 : (PD.withTnI tn').Solvable ↔ ((PD.withTnI tn').withMethods N).Solvable :=
    (HTN.Problem.solvable_congr_methods methodsIsoEquiv_regDom).symm
  have step3 : ((PD.withTnI tn').withMethods N).Solvable ↔ PS.Solvable := by
    refine HTN.Problem.solvable_relabel_iff (eF := id) (eA := id) (eC := id) (eI := Nat.pairEquiv)
      Function.injective_id Function.injective_id Function.injective_id
      (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_) ?_ ?_ TaskNetwork.grid_wf rfl rfl
    · show (regDom φ).prec o = _; rw [prec_regDom, Set.image_id]; rfl
    · show (regDom φ).add o = _; rw [add_regDom, Set.image_id]; rfl
    · show (regDom φ).del o = _; rw [del_regDom, Set.image_id]; rfl
    · show {f | f ∈ ([] : List ℕ)} = _; rw [Set.image_id]; ext x; simp [PS, semProblem, semInst,
        Domain.mkProblem]
    · show {f | f ∈ List.range φ.length} = _; rw [Set.image_id]; ext x; simp [PS, semProblem,
        semInst, Domain.mkProblem]
  exact step1.trans (step2.trans step3)

/-- **The described encoding is solvable iff the formula is satisfiable.** -/
theorem solvable_regProb_iff : (regProb φ).toProblem.Solvable ↔ Satisfiable φ :=
  (solvable_ofSyn_iff _ _).trans (solvable_reg_iff_sem.trans solvable_semProblem_iff)

/-! ### Well-formedness -/

theorem names_regDom : (regDom φ).actions.map Prod.fst = List.range (2 * K φ) := by
  simp [regDom, DomDesc.actions, actD, Function.comp_def]

theorem valid_regProb : (regProb φ).Valid := by
  refine valid_ofSyn ?_ ?_ ?_
  · rw [names_regDom]; exact List.nodup_range
  · refine tnValid_gridDescFull fun row hrow n hn => ?_
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hrow
    subst hrow; simp [encLabel] at hn
  · intro m hm
    obtain ⟨i, hi, c, hc, rfl⟩ := mem_regDom_methods.1 hm
    refine tnValid_gridDescFull fun row hrow n hn => ?_
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hrow
    subst hrow
    rw [names_regDom, List.mem_range]
    simp only [List.mem_map] at hn
    obtain ⟨x, hx, hxn⟩ := hn
    unfold body at hx
    split_ifs at hx <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl <;> simp [encLabel] at hxn <;> omega

/-! ### The classes -/

theorem methods_toProblem {m : Method ℕ ℕ ℕ} (hm : m ∈ (regProb φ).toProblem.toPos.methods) :
    ∃ i < K φ, ∃ c < 2, m = MethodDesc.toMethod (i, gridDescFullOf id id [body φ i c]) := by
  obtain ⟨e, he, rfl⟩ := hm
  obtain ⟨i, hi, c, hc, rfl⟩ := mem_regDom_methods.1 he
  exact ⟨i, hi, c, hc, rfl⟩

theorem label_body {i c j : ℕ} (hj : j < (body φ i c).length) :
    (gridDescFullOf id id [body φ i c]).toTaskNetwork.α (Nat.pair 0 j) = (body φ i c)[j] := by
  rw [toTaskNetwork_gridDescFullOf]
  show (gridDescOf id id [body φ i c]).label (Nat.pair 0 j) = _
  rw [label_gridDescOf (by simp) (by simpa using hj),
    show ([body φ i c].getD 0 []) = body φ i c from rfl, List.getD_eq_getElem _ _ hj]
  rcases (body φ i c)[j] with a | b <;> rfl

theorem mem_T_body {i c x : ℕ} :
    x ∈ (gridDescFullOf id id [body φ i c]).toTaskNetwork.T ↔
      ∃ j < (body φ i c).length, x = Nat.pair 0 j := by
  rw [gridDescFullOf_single_T]
  simp only [List.mem_toFinset, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

/-- The compound tasks of a body. -/
theorem compound_body {i c : ℕ} {x d : ℕ}
    (hx : x ∈ (gridDescFullOf id id [body φ i c]).toTaskNetwork.T)
    (hd : (gridDescFullOf id id [body φ i c]).toTaskNetwork.α x = Sum.inr d) :
    d = i + 1 ∧ x = Nat.pair 0 1 ∧ i + 1 < K φ := by
  obtain ⟨j, hj, rfl⟩ := mem_T_body.1 hx
  rw [label_body hj] at hd
  unfold body at hj hd
  split_ifs at hj hd with h
  · simp at hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simp at hd
    · simp at hd; exact ⟨hd.symm, rfl, h⟩
  · simp at hj
    obtain rfl : j = 0 := by omega
    simp at hd

theorem isREG_regProb : (regProb φ).toProblem.IsREG := by
  rintro m ⟨hm, -⟩
  obtain ⟨i, -, c, -, rfl⟩ := methods_toProblem hm
  refine ⟨fun x hx y hy ⟨d, hd⟩ ⟨d', hd'⟩ => ?_, fun x hx ⟨d, hd⟩ y hy hyx => ?_⟩
  · rw [(compound_body hx hd).2.1, (compound_body hy hd').2.1]
  · obtain ⟨-, rfl, hi1⟩ := compound_body hx hd
    obtain ⟨j, hj, rfl⟩ := mem_T_body.1 hy
    have hj' : j = 0 := by
      unfold body at hj; rw [if_pos hi1] at hj; simp at hj
      rcases Nat.lt_or_ge j 1 with h | h
      · omega
      · exfalso; exact hyx (by rw [show j = 1 by omega])
    subst hj'
    show (gridDescFullOf id id [body φ i c]).toTaskNetwork.ord _ _
    rw [toTaskNetwork_gridDescFullOf]
    unfold gridDescOf
    rw [gridDesc_ord]
    refine ⟨0, 0, 1, by simp, by omega, ?_, rfl, rfl⟩
    simp [gridRow, body, hi1]

theorem isTO_regProb : (regProb φ).toProblem.IsTO := by
  refine ⟨isTotallyOrdered_gridDescFullOf_single [Sum.inr 0], ?_⟩
  rintro m ⟨hm, -⟩
  obtain ⟨i, -, c, -, rfl⟩ := methods_toProblem hm
  exact isTotallyOrdered_gridDescFullOf_single _

theorem isACYC_regProb : (regProb φ).toProblem.IsACYC := by
  refine ⟨fun a b => b ≤ a, ⟨⟨fun _ _ => le_rfl, fun _ _ _ _ _ _ h1 h2 => h2.trans h1,
    fun a b _ _ => le_total b a⟩, fun _ _ _ _ h1 h2 => le_antisymm h2 h1, ?_⟩⟩
  rintro m ⟨hm, -⟩ t ht d hd
  obtain ⟨i, -, c, -, rfl⟩ := methods_toProblem hm
  obtain ⟨rfl, -, -⟩ := compound_body ht hd
  show i ≤ i + 1 ∧ ¬ i + 1 ≤ i
  omega

/-! ### Polynomial time -/

/-- The described chain `a · b`. -/
def twoTn (a b : ℕ) : TnDesc :=
  ([Nat.pair 0 0, Nat.pair 0 1], [(Nat.pair 0 0, Nat.pair 0 1)],
    [(Nat.pair 0 0, false, a), (Nat.pair 0 1, true, b)])

/-- The described single action `a`. -/
def oneTn (a : ℕ) : TnDesc := ([Nat.pair 0 0], [], [(Nat.pair 0 0, false, a)])

theorem gridDescFullOf_body (i c : ℕ) : gridDescFullOf id id [body φ i c] =
    if i + 1 < K φ then twoTn (2 * i + c) (i + 1) else oneTn (2 * i + c) := by
  unfold body
  split_ifs <;> simp [gridDescFullOf, gridDescFull, cellIds, cellOrdFull, cellLbl, gridRow,
    encLabel, twoTn, oneTn, List.range_succ]

theorem pt_clauses : PT fun x : CNF × ℕ × Bool => clauses x.1 x.2.1 x.2.2 := by
  unfold clauses
  exact PT.ite (PT.lt (PT.fst.comp PT.snd) (pt_nv.comp PT.fst)) pt_clauseIdx PT.nil

theorem pt_bodyTn : PT fun x : CNF × ℕ × ℕ => bodyTn x.1 x.2.1 x.2.2 := by
  refine PT.of_eq (f := fun x : CNF × ℕ × ℕ =>
    if x.2.1 + 1 < K x.1 then twoTn (2 * x.2.1 + x.2.2) (x.2.1 + 1) else oneTn (2 * x.2.1 + x.2.2))
    ?_ fun x => (gridDescFullOf_body (φ := x.1) _ _).symm
  have hi : PT fun x : CNF × ℕ × ℕ => x.2.1 := PT.fst.comp PT.snd
  have ha : PT fun x : CNF × ℕ × ℕ => 2 * x.2.1 + x.2.2 :=
    PT.add (PT.affine 2 0 hi |>.of_eq fun _ => by ring) (PT.snd.comp PT.snd)
  have hK : PT fun x : CNF × ℕ × ℕ => K x.1 := PT.succ (pt_nv.comp PT.fst)
  unfold twoTn oneTn
  refine PT.ite (PT.lt (PT.succ hi) hK) ?_ ?_
  · exact PT.pair (PT.const _) (PT.pair (PT.const _) (PT.cons (PT.pair (PT.const _)
      (PT.pair (PT.const _) ha)) (PT.cons (PT.pair (PT.const _) (PT.pair (PT.const _)
        (PT.succ hi))) PT.nil)))
  · exact PT.pair (PT.const _) (PT.pair PT.nil (PT.cons (PT.pair (PT.const _)
      (PT.pair (PT.const _) ha)) PT.nil))

set_option maxHeartbeats 1000000 in
theorem pt_regProb : PT regProb := by
  have hL : PT fun φ : CNF => (vars φ ++ [0]) ++ (vars φ ++ [0]) :=
    PT.append (PT.append pt_vars (PT.const [0])) (PT.append pt_vars (PT.const [0]))
  have hlen : ∀ φ : CNF, ((vars φ ++ [0]) ++ (vars φ ++ [0])).length = 2 * K φ := fun φ => by
    simp [K, nv]; ring
  have hK : PT fun φ : CNF => vars φ ++ [0] := PT.append pt_vars (PT.const [0])
  have hlenK : ∀ φ : CNF, (vars φ ++ [0]).length = K φ := fun φ => by simp [K, nv]
  have hact : PT actD := by
    unfold actD
    refine (PT.map (g := fun (φ : CNF) (n : ℕ) => (n, (([] : List ℕ),
      clauses φ (n / 2) (n % 2 == 0), ([] : List ℕ)))) (PT.rangeLength hL) ?_).of_eq
      fun φ => by rw [hlen]
    exact PT.pair PT.snd (PT.pair PT.nil (PT.pair (pt_clauses.comp (PT.pair PT.fst
      (PT.pair (PT.divC PT.snd (by norm_num)) (PT.beq (PT.modC PT.snd (by norm_num))
        (PT.const 0))))) PT.nil))
  have hmeth : PT fun φ : CNF => (List.range (K φ)).flatMap (methsOf φ) := by
    unfold methsOf
    refine (PT.flatMap (g := fun (φ : CNF) (i : ℕ) => [(i, bodyTn φ i 0),
      (i, bodyTn φ i 1)]) (PT.rangeLength hK) ?_).of_eq fun φ => by
        rw [hlenK]
    have hb0 : PT fun q : CNF × ℕ => bodyTn q.1 q.2 0 :=
      PT.comp (f := fun q : CNF × ℕ => (q.1, q.2, (0 : ℕ))) pt_bodyTn
        (PT.pair PT.fst (PT.pair PT.snd (PT.const (0 : ℕ))))
    have hb1 : PT fun q : CNF × ℕ => bodyTn q.1 q.2 1 :=
      PT.comp (f := fun q : CNF × ℕ => (q.1, q.2, (1 : ℕ))) pt_bodyTn
        (PT.pair PT.fst (PT.pair PT.snd (PT.const (1 : ℕ))))
    exact PT.cons (PT.pair PT.snd hb0) (PT.cons (PT.pair PT.snd hb1) PT.nil)
  have hdom : PT regDom := PT.pair hact hmeth
  have hinst : PT regInst :=
    (PT.pair (PT.nil (β := ℕ)) (PT.pair (PT.rangeLength (PT.id (α := CNF)))
      (PT.const (gridDescFullOf id id [[(Sum.inr 0 : ℕ ⊕ ℕ)]])))).of_eq fun φ => rfl
  have hofs : PT ofSynAct := by
    unfold ofSynAct
    exact PT.pair PT.fst (PT.pair (PT.fst.comp PT.snd) (PT.pair PT.nil
      (PT.pair (PT.fst.comp (PT.snd.comp PT.snd)) (PT.snd.comp (PT.snd.comp PT.snd)))))
  unfold regProb ofSyn
  exact PT.pair (PT.pair (PT.map (PT.fst.comp hdom) (hofs.comp PT.snd)) (PT.snd.comp hdom))
    (PT.pair (PT.fst.comp hinst) (PT.pair (PT.snd.comp (PT.snd.comp hinst))
      (PT.pair (PT.fst.comp (PT.snd.comp hinst)) PT.nil)))

end SATReg

open SATReg

/-- **Theorem 4.3.12** (first part). `PlanEx^REG∩ACYC∩TO_htn` is NP-hard. -/
theorem thm_4_3_12_TO : Cx.Hard Cx.NP (PlanEx fun P => P.IsREG ∧ P.IsACYC ∧ P.IsTO) :=
  npHard_of_sat pt_regProb (fun _ => ⟨valid_regProb, isREG_regProb, isACYC_regProb, isTO_regProb⟩)
    (fun _ => solvable_regProb_iff)

/-- **Theorem 4.3.12** (second part). `PlanEx^REG∩ACYC∩TO-M_htn` is NP-hard. -/
theorem thm_4_3_12_TOM : Cx.Hard Cx.NP (PlanEx fun P => P.IsREG ∧ P.IsACYC ∧ P.IsTO_M) :=
  npHard_of_sat pt_regProb
    (fun _ => ⟨valid_regProb, isREG_regProb, isACYC_regProb, isTO_regProb.2⟩)
    (fun _ => solvable_regProb_iff)


end Article

end HTN
