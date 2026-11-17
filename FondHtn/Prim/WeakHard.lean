import FondHtn.Prim.WeakMem
import FondHtn.Hardness.FromDet
import HtnComplexity.Article.SATNoHTN
import HtnComplexity.Article.AcycRegNP
/-!
# Weak plan existence of primitive totally ordered problems is NP-complete ([CB21, Thm. 4.1])

**Hardness** by the reduction of [CB21, Thm. 4.1] from satisfiability.  For a formula `φ` with
(distinct) variables `x₀, …, x_{N-1}` (numbered by position in `HTN.Article.SATNo.vars φ`) and
clauses `c₀, …, c_{m-1}`:

* facts: `j` for the clause `c_j` (`j < m`);
* actions: `i < N` is `e_i = (∅, ∅, {({c_j | x_i ∈ c_j}, ∅), ({c_j | ¬x_i ∈ c_j}, ∅)})`, two
  outcomes adding the clauses satisfied by `x_i = ⊤` resp. `x_i = ⊥`; `N` is
  `k = ({c₀, …, c_{m-1}}, ∅, {(∅, ∅)})`, whose precondition is all clauses;
* `s_I = ∅`, `tn_I` is the chain `e₀ ≺ e₁ ≺ … ≺ e_{N-1} ≺ k` (task id `i` labelled by action
  `i`, all pairs `i ≺ j` for `i < j ≤ N` listed, as descriptions list a transitive order), no
  methods.

This is exactly the paper's construction: only positive preconditions, at most two outcomes, no
deletes.  A weak (LD) solution chooses one outcome per variable action such that all clause facts
are present before `k`, i.e. a satisfying assignment (`FOND.PrimHard.weakLD_satDesc_iff`).

**Membership** for `PRIM ∩ TO` adds a total-order test of `tn_I` to the certificate check of
`FondHtn/Prim/WeakMem.lean` (for primitive problems the methods are unreachable, so `TO` is just
total order of `tn_I`).

Results (each for weak LD and weak OD, which coincide, [CB21, Prop. 2.12]):

* `FOND.weakLD_PRIM_TO_hard`, `FOND.weakOD_PRIM_TO_hard` — NP-hard ([CB21, Thm. 4.1]);
* `FOND.weakLD_PRIM_TO_mem`, `FOND.weakOD_PRIM_TO_mem` — in NP;
* `FOND.weakLD_PRIM_TO_complete`, `FOND.weakOD_PRIM_TO_complete` — NP-complete;
* `FOND.weakLD_PRIM_complete`, `FOND.weakOD_PRIM_complete` — NP-complete for primitive
  (partially ordered) problems ([CB21, Cor. 4.2]).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.Article.SATNo HTN.NPHard PTime

/-! ## Classes of primitive problems -/

theorem not_reachableName_of_primitive {F A C I : Type*} {P : HTN.Problem F A C I}
    (hn : P.tnI.IsPrimitive) (c : C) : ¬ P.ReachableName c := by
  intro h
  induction h with
  | tnI ht hc =>
    obtain ⟨a, ha⟩ := hn _ ht
    rw [ha] at hc; exact absurd hc (by simp)
  | method _ _ _ _ ih => exact ih

/-- For primitive problems `TO` is total order of `tn_I`. -/
theorem to_iff_of_prim {P : Problem ℕ ℕ ℕ ℕ} (hP : FClass.PRIM P) :
    FClass.TO P ↔ P.tnI.IsTotallyOrdered :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hm => absurd hm.2 (not_reachableName_of_primitive hP _)⟩⟩

namespace PrimHard

/-! ## The encoding -/

variable (φ : CNF)

/-- The action `i`: a variable action (`i < N`) or the check action (`i = N`). -/
def satAct (i : ℕ) : FActDesc :=
  if i < nv φ then (i, [], [], [(clauseIdx φ i true, []), (clauseIdx φ i false, [])])
  else (i, List.range φ.length, [], [([], [])])

/-- All pairs `i < j < n` (the chain on `0, …, n - 1`, transitively closed). -/
def chainOrd (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun j => ((List.range n).filter fun i => decide (i < j)).map fun i => (i, j)

theorem mem_chainOrd {n a b : ℕ} : (a, b) ∈ chainOrd n ↔ a < b ∧ b < n := by
  simp only [chainOrd, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, i, ⟨-, hij⟩, rfl, rfl⟩; exact ⟨hij, hj⟩
  · rintro ⟨hab, hb⟩; exact ⟨b, hb, a, ⟨by omega, hab⟩, rfl, rfl⟩

/-- The initial task network: the chain of the `N + 1` actions. -/
def satTn : TnDesc :=
  (List.range (nv φ + 1), chainOrd (nv φ + 1), (List.range (nv φ + 1)).map fun i => (i, false, i))

/-- **The encoding of [CB21, Thm. 4.1].** -/
def satDesc : FProbDesc :=
  (((List.range (nv φ + 1)).map (satAct φ), []), ([], satTn φ))

/-! ### Well-formedness and classes -/

variable {φ}

theorem satAct_name (i : ℕ) : (satAct φ i).name = i := by
  unfold satAct; split_ifs <;> rfl

theorem names_satDesc : (satDesc φ).actions.map FActDesc.name = List.range (nv φ + 1) := by
  simp only [satDesc, FProbDesc.actions, List.map_map]
  conv_rhs => rw [← List.map_id (List.range (nv φ + 1))]
  exact List.map_congr_left fun i _ => satAct_name i

theorem tnValid_satTn : TnValid (satDesc φ).Declared (satTn φ) where
  nodup := List.nodup_range
  ord_mem := by
    rintro ⟨a, b⟩ hq
    have := mem_chainOrd.1 hq
    show a ∈ List.range (nv φ + 1) ∧ b ∈ List.range (nv φ + 1)
    simp only [List.mem_range]; omega
  irrefl := fun a h => by have := mem_chainOrd.1 h; omega
  trans := fun a b c h1 h2 => by
    have := mem_chainOrd.1 h1; have := mem_chainOrd.1 h2
    exact mem_chainOrd.2 (by omega)
  lbl_perm := by simp [satTn, TnDesc.lbl, TnDesc.ids, List.map_map, Function.comp_def]
  prim_ok := by
    intro q hq _
    simp only [satTn, TnDesc.lbl, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    unfold FProbDesc.Declared
    rw [names_satDesc]; exact List.mem_range.2 hi

theorem valid_satDesc : (satDesc φ).Valid where
  names_nodup := by rw [names_satDesc]; exact List.nodup_range
  effs_ne := by
    intro a ha
    simp only [satDesc, FProbDesc.actions, List.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    unfold satAct FActDesc.effs; split_ifs <;> simp
  tnI := tnValid_satTn
  methods := by simp [satDesc, FProbDesc.methods]

theorem tnI_satDesc : (satDesc φ).toProblem.tnI = (satTn φ).toTaskNetwork := rfl

theorem label_satTn {i : ℕ} (hi : i < nv φ + 1) : (satTn φ).label i = Sum.inl i := by
  unfold TnDesc.label
  rw [show (satTn φ).lbl = (List.range (nv φ + 1)).map fun i => (i, (false, i)) from rfl,
    Undec.lookup_map_self _ _ (List.mem_range.2 hi)]

theorem mem_T_satTn {i : ℕ} : i ∈ (satTn φ).toTaskNetwork.T ↔ i < nv φ + 1 := by
  simp [TnDesc.toTaskNetwork, satTn, TnDesc.ids]

theorem ord_satTn {a b : ℕ} : (satTn φ).toTaskNetwork.ord a b ↔ a < b ∧ b < nv φ + 1 := by
  show (satTn φ).ordOf a b ↔ _
  rw [tnValid_satTn.ordOf_iff]; exact mem_chainOrd

theorem prim_satDesc : FClass.PRIM (satDesc φ).toProblem := by
  intro t ht
  exact ⟨t, label_satTn (mem_T_satTn.1 ht)⟩

theorem to_satDesc : FClass.TO (satDesc φ).toProblem := by
  refine (to_iff_of_prim prim_satDesc).2 ?_
  intro a ha b hb hab
  rw [tnI_satDesc] at ha hb ⊢
  rw [mem_T_satTn] at ha hb
  rw [ord_satTn, ord_satTn]
  omega

/-! ### The action model -/

theorem toProblem_δ (p : FProbDesc) : p.toProblem.δ = p.δ := rfl

theorem δ_satDesc {a : ℕ} (ha : a < nv φ + 1) : (satDesc φ).δ a = (satAct φ a).toAction := by
  have hm : satAct φ a ∈ (satDesc φ).actions := by
    simp only [satDesc, FProbDesc.actions, List.mem_map, List.mem_range]
    exact ⟨a, ha, rfl⟩
  rw [← FProbDesc.δ_of_mem valid_satDesc hm, satAct_name]

theorem applicable_var {i : ℕ} (hi : i < nv φ) (S : Set ℕ) :
    ((satDesc φ).δ i).Applicable S := by
  rw [δ_satDesc (by omega)]
  unfold satAct; rw [if_pos hi]
  simp [Action.Applicable, FActDesc.toAction]

theorem outcomes_var {i : ℕ} (hi : i < nv φ) (S s' : Set ℕ) :
    s' ∈ ((satDesc φ).δ i).outcomes S ↔ ∃ b : Bool, s' = S ∪ {j | j ∈ clauseIdx φ i b} := by
  rw [δ_satDesc (by omega)]
  unfold satAct; rw [if_pos hi]
  simp only [Action.outcomes, FActDesc.toAction, FActDesc.effs, Set.mem_setOf_eq, Action.applyEff,
    List.mem_cons, List.not_mem_nil, or_false, Bool.exists_bool]
  constructor
  · rintro ⟨e, ⟨x, hx, rfl⟩, rfl⟩
    rcases hx with rfl | rfl
    · right; simp
    · left; simp
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨_, Or.inr rfl, rfl⟩, by simp⟩
    · exact ⟨_, ⟨_, Or.inl rfl, rfl⟩, by simp⟩

theorem weakExec_check (S : Set ℕ) :
    (satDesc φ).toProblem.WeakExec [nv φ] S ↔ ∀ j < φ.length, j ∈ S := by
  simp only [Problem.WeakExec, toProblem_δ]
  rw [δ_satDesc (by omega)]
  unfold satAct; rw [if_neg (by omega)]
  simp only [Action.Applicable, FActDesc.toAction, FActDesc.effs, Action.outcomes,
    List.mem_cons, List.not_mem_nil, or_false, and_true]
  constructor
  · intro h j hj
    exact h.1.1 (by simpa using hj)
  · intro h
    refine ⟨⟨fun j hj => h j (by simpa using hj), by simp⟩, ?_⟩
    simp

/-- **The weak executions of the chain.** -/
theorem weakExec_chain (n : ℕ) : ∀ (k : ℕ) (S : Set ℕ), k + n ≤ nv φ →
    ((satDesc φ).toProblem.WeakExec (List.range' k n ++ [nv φ]) S ↔
      ∃ bs : ℕ → Bool, ∀ j < φ.length, j ∈ S ∨ ∃ i, k ≤ i ∧ i < k + n ∧ j ∈ clauseIdx φ i (bs i)) := by
  induction n with
  | zero =>
    intro k S _
    simp only [List.range'_zero, List.nil_append, weakExec_check]
    exact ⟨fun h => ⟨fun _ => true, fun j hj => Or.inl (h j hj)⟩,
      fun ⟨_, h⟩ j hj => (h j hj).resolve_right (by omega)⟩
  | succ n ih =>
    intro k S hk
    rw [List.range'_succ, List.cons_append]
    simp only [Problem.WeakExec, toProblem_δ]
    simp only [applicable_var (show k < nv φ by omega), true_and, outcomes_var (show k < nv φ by omega)]
    constructor
    · rintro ⟨s', ⟨b, rfl⟩, hs'⟩
      obtain ⟨bs, hbs⟩ := (ih (k + 1) _ (by omega)).1 hs'
      refine ⟨Function.update bs k b, fun j hj => ?_⟩
      rcases hbs j hj with (h | h) | ⟨i, h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, le_rfl, by omega, by simpa using h⟩
      · refine Or.inr ⟨i, by omega, by omega, ?_⟩
        rwa [Function.update_of_ne (by omega)]
    · rintro ⟨bs, hbs⟩
      refine ⟨_, ⟨bs k, rfl⟩, (ih (k + 1) _ (by omega)).2 ⟨bs, fun j hj => ?_⟩⟩
      rcases hbs j hj with h | ⟨i, h1, h2, h3⟩
      · exact Or.inl (Or.inl h)
      · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact Or.inl (Or.inr h3)
        · exact Or.inr ⟨i, by omega, by omega, h3⟩

theorem weakExec_range_iff :
    (satDesc φ).toProblem.WeakExec (List.range (nv φ + 1)) ∅ ↔ Satisfiable φ := by
  rw [List.range_succ, List.range_eq_range', weakExec_chain (nv φ) 0 ∅ (by omega)]
  simp only [Set.mem_empty_iff_false, false_or, zero_le, true_and, zero_add]
  constructor
  · rintro ⟨bs, hbs⟩
    refine ⟨fun x => bs ((vars φ).idxOf x), fun c hc => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
    obtain ⟨i, hi, hji⟩ := hbs j hj
    rw [mem_clauseIdx, List.getD_eq_getElem _ _ hj] at hji
    exact ⟨_, hji.2, by simp only; rw [idxOf_getI hi]⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨fun i => σ ((vars φ).getI i), fun j hj => ?_⟩
    obtain ⟨l, hl, hσl⟩ := hσ _ (List.getElem_mem hj)
    have hx := mem_vars (List.getElem_mem hj) (b := l.2) (x := l.1) (by simpa using hl)
    refine ⟨(vars φ).idxOf l.1, List.idxOf_lt_length_iff.2 hx, ?_⟩
    rw [mem_clauseIdx, List.getD_eq_getElem _ _ hj]
    simp only [getI_idxOf hx, hσl, Prod.mk.eta]
    exact ⟨hj, hl⟩

/-- The chain has exactly one linearisation. -/
theorem isLinearization_iff (l : List ℕ) :
    (satTn φ).toTaskNetwork.IsLinearization l ↔ l = List.range (nv φ + 1) := by
  constructor
  · rintro ⟨hnd, hmem, hpw⟩
    have hperm : l.Perm (List.range (nv φ + 1)) :=
      (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun x => by
        rw [hmem x, mem_T_satTn, List.mem_range]
    have hle : l.Pairwise (· ≤ ·) := by
      refine hpw.imp_of_mem fun {a b} ha hb h => ?_
      rw [ord_satTn] at h
      have := (List.mem_range.1 (hperm.subset ha))
      omega
    exact List.Perm.eq_of_sortedLE (List.sortedLE_iff_pairwise.2 hle)
      (List.sortedLE_iff_pairwise.2 List.pairwise_le_range) hperm
  · rintro rfl
    refine ⟨List.nodup_range, fun x => by rw [mem_T_satTn, List.mem_range], ?_⟩
    refine List.pairwise_lt_range.imp fun {a b} h hc => ?_
    rw [ord_satTn] at hc; omega

/-- **Correctness of the encoding.** -/
theorem weakLD_satDesc_iff : (satDesc φ).toProblem.WeakLDSolvable ↔ Satisfiable φ := by
  have hinit : (satDesc φ).toProblem.init = ∅ := by
    ext f; simp [FProbDesc.toProblem, satDesc, FProbDesc.init]
  rw [Problem.weakLDSolvable_iff_of_primitive _ prim_satDesc, ← weakExec_range_iff, hinit]
  have hseq : (satTn φ).toTaskNetwork.IsActionSeq (List.range (nv φ + 1))
      (List.range (nv φ + 1)) := by
    unfold TaskNetwork.IsActionSeq
    exact List.map_congr_left fun i hi => label_satTn (List.mem_range.1 hi)
  constructor
  · rintro ⟨l, as, hl, has, hex⟩
    rw [tnI_satDesc, isLinearization_iff] at hl
    subst hl
    rw [tnI_satDesc] at has
    have : as = List.range (nv φ + 1) := by
      unfold TaskNetwork.IsActionSeq at has hseq
      exact List.map_injective_iff.2 Sum.inl_injective (has.symm.trans hseq)
    subst this
    exact hex
  · intro hex
    exact ⟨_, _, (isLinearization_iff _).2 rfl, hseq, hex⟩

/-! ### Polynomial time -/

theorem pt_satAct : PT fun x : CNF × ℕ => satAct x.1 x.2 := by
  unfold satAct
  have hN : PT fun x : CNF × ℕ => nv x.1 := pt_nv.comp PT.fst
  have hC : ∀ b : Bool, PT fun x : CNF × ℕ => (clauseIdx x.1 x.2 b, ([] : List ℕ)) := fun b =>
    PT.pair (pt_clauseIdx.comp (PT.pair PT.fst (PT.pair PT.snd (PT.const b)))) PT.nil
  refine PT.ite (PT.lt PT.snd hN) ?_ ?_
  · exact PT.pair PT.snd (PT.pair PT.nil (PT.pair PT.nil
      (PT.cons (hC true) (PT.cons (hC false) PT.nil))))
  · exact PT.pair PT.snd (PT.pair (PT.rangeLength PT.fst) (PT.pair PT.nil (PT.const _)))

theorem pt_satDesc : PT satDesc := by
  have hlen : ∀ φ : CNF, (vars φ ++ [0]).length = nv φ + 1 := fun φ => by simp [nv]
  have hL : PT fun φ : CNF => vars φ ++ [0] := PT.append pt_vars (PT.const [0])
  have hR : PT fun φ : CNF => List.range (nv φ + 1) :=
    (PT.rangeLength hL).of_eq fun φ => by rw [hlen]
  have hord : PT fun φ : CNF => chainOrd (nv φ + 1) := by
    unfold chainOrd
    exact PT.flatMap hR (PT.map (PT.filter (hR.comp PT.fst) (PT.lt PT.snd (PT.snd.comp PT.fst)))
      (PT.pair PT.snd (PT.snd.comp PT.fst)))
  have htn : PT satTn := by
    unfold satTn
    exact PT.pair hR (PT.pair hord (PT.map hR (PT.pair PT.snd (PT.pair (PT.const false) PT.snd))))
  unfold satDesc
  exact PT.pair (PT.pair (PT.map hR pt_satAct) PT.nil) (PT.pair PT.nil htn)

end PrimHard

open PrimHard

/-! ## Hardness [CB21, Thm. 4.1] -/

/-- **[CB21, Thm. 4.1], hardness**: weak LD plan existence of primitive totally ordered problems
is NP-hard. -/
theorem weakLD_PRIM_TO_hard :
    Cx.Hard Cx.NP (PlanExFM .weakLD (FClass.inter FClass.PRIM FClass.TO)) := by
  intro L hL
  refine (sat_npHard L hL).trans ?_
  exact redP_codeLang (α := CNF) (β := FProbDesc)
    (R := fun p => p.Valid ∧ FClass.inter FClass.PRIM FClass.TO p.toProblem ∧
      FMCrit.Solvable .weakLD p.toProblem) pt_satDesc
    (fun φ => ⟨fun h => ⟨valid_satDesc, ⟨prim_satDesc, to_satDesc⟩, weakLD_satDesc_iff.2 h⟩,
      fun h => weakLD_satDesc_iff.1 h.2.2⟩) badDesc (fun h => badDesc_not_valid h.1)

theorem weakOD_PRIM_TO_hard :
    Cx.Hard Cx.NP (PlanExFM .weakOD (FClass.inter FClass.PRIM FClass.TO)) := by
  rw [planExFM_weakOD_eq]; exact weakLD_PRIM_TO_hard

/-! ## Membership -/

namespace Prim

/-- The certificate check with the total-order test of `tn_I`. -/
def weakCertTOB (x : FProbDesc × WCert) : Bool := weakCertB x && toB x.1.tnI

theorem pt_weakCertTOB : PT weakCertTOB :=
  PT.and pt_weakCertB (pt_toB.comp (PT.snd.comp (PT.snd.comp PT.fst)))

end Prim

open Prim in
theorem weakLD_PRIM_TO_mem :
    Cx.NP (PlanExFM .weakLD (FClass.inter FClass.PRIM FClass.TO)) :=
  inNP_codeLang (α := FProbDesc) (β := WCert)
    (Q := fun p => p.Valid ∧ FClass.inter FClass.PRIM FClass.TO p.toProblem ∧
      FMCrit.Solvable .weakLD p.toProblem)
    pt_weakCertTOB 4 fun p => by
      show (p.Valid ∧ (FClass.PRIM p.toProblem ∧ FClass.TO p.toProblem) ∧
        p.toProblem.WeakLDSolvable) ↔ _
      simp only [weakCertTOB, Bool.and_eq_true]
      constructor
      · rintro ⟨hv, ⟨hp, hto⟩, hs⟩
        obtain ⟨c, hc, hcB⟩ := exists_short_cert p ((Prim.iff_exists_cert p).1 ⟨hv, hp, hs⟩)
        exact ⟨c, hc, hcB, (toB_iff hv.tnI).2 ((to_iff_of_prim hp).1 hto)⟩
      · rintro ⟨c, -, hcB, hto⟩
        obtain ⟨hv, hp, hs⟩ := (Prim.iff_exists_cert p).2 ⟨c, hcB⟩
        exact ⟨hv, ⟨hp, (to_iff_of_prim hp).2 ((toB_iff hv.tnI).1 hto)⟩, hs⟩

theorem weakOD_PRIM_TO_mem :
    Cx.NP (PlanExFM .weakOD (FClass.inter FClass.PRIM FClass.TO)) := by
  rw [planExFM_weakOD_eq]; exact weakLD_PRIM_TO_mem

/-! ## Completeness -/

/-- **[CB21, Thm. 4.1]**: weak LD plan existence of primitive totally ordered problems is
NP-complete. -/
theorem weakLD_PRIM_TO_complete :
    Cx.Complete Cx.NP (PlanExFM .weakLD (FClass.inter FClass.PRIM FClass.TO)) :=
  ⟨weakLD_PRIM_TO_mem, weakLD_PRIM_TO_hard⟩

/-- **[CB21, Thm. 4.1]**, weak OD. -/
theorem weakOD_PRIM_TO_complete :
    Cx.Complete Cx.NP (PlanExFM .weakOD (FClass.inter FClass.PRIM FClass.TO)) :=
  ⟨weakOD_PRIM_TO_mem, weakOD_PRIM_TO_hard⟩

/-- **[CB21, Cor. 4.2]**: weak LD plan existence of primitive problems is NP-complete. -/
theorem weakLD_PRIM_complete : Cx.Complete Cx.NP (PlanExFM .weakLD FClass.PRIM) :=
  ⟨weakLD_PRIM_mem, hard_PRIM_fm .weakLD⟩

/-- **[CB21, Cor. 4.2]**, weak OD. -/
theorem weakOD_PRIM_complete : Cx.Complete Cx.NP (PlanExFM .weakOD FClass.PRIM) :=
  ⟨weakOD_PRIM_mem, hard_PRIM_fm .weakOD⟩

end FOND
