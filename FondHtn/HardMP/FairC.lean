import FondHtn.HardMP.MainC
import FondHtn.HardMP.FairTR
/-!
# The fair reading for the counter construction

Every step of the leftmost list game on `FOND.HardMP.descC` (from the reachable shapes of label
lists) strictly decreases a measure combining the counter and the position in the programs
(`FOND.HardMP.muC`).  Hence a fair strong cyclic solution — which, by the progression fixpoint
characterisation, gives a set of lists closed under one winning move each — yields a winning
strategy of the (acyclic, strong) list game: fair solvability of `descC p` is strong
solvability, i.e. plan existence of `p`.
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

variable (p : ProbDesc)

/-- The total length of the programs. -/
def LP : ℕ := ((prgsC p).map List.length).sum

open Classical in
/-- The counter of a state. -/
noncomputable def ctrS (s : Set ℕ) : ℕ :=
  bitsum (fun j => decide (fact (fSlot (cslot p) j) ∈ s)) (Nc p)

/-- The weight of a task name. -/
def wtC : ℕ ⊕ ℕ → ℕ
  | .inl _ => 1
  | .inr c => if c = roundN then 2 * LP p + 4 else
      2 * (((prgsC p).getI (Nat.unpair ((c - 2) / 2)).1).length - (Nat.unpair ((c - 2) / 2)).2) + 2

/-- Lists before the increment of the current round. -/
def IsPhase (xs : List (ℕ ⊕ ℕ)) : Prop :=
  xs.head? = some (.inr roundN) ∨ xs.head? = some (.inl finN) ∨
    (∃ r, xs.head? = some (.inr (cN (r + 1) 0))) ∨ ∃ r i, xs.head? = some (.inl (aN (r + 1) 0 i))

open Classical in
/-- **The measure.** -/
noncomputable def muC (xs : List (ℕ ⊕ ℕ)) (s : Set ℕ) : ℕ :=
  (2 ^ Nc p - ctrS p s - (if IsPhase xs then 1 else 0)) * (2 * LP p + 5) + (xs.map (wtC p)).sum

/-- The reachable shapes of label lists. -/
def ShapeC (xs : List (ℕ ⊕ ℕ)) : Prop :=
  xs = [] ∨ (∃ x, xs = [x]) ∨ ∃ r pc alt, r < (prgsC p).length ∧
    pc < ((prgsC p).getI r).length ∧ alt < (((prgsC p).getI r).getI pc).length ∧
    xs = [.inl (aN r pc alt), .inr (cN r (pc + 1))]

variable {p}

theorem ctrS_lt (s : Set ℕ) : ctrS p s < 2 ^ Nc p := bitsum_lt _ _

theorem wtC_cN (r pc : ℕ) : wtC p (.inr (cN r pc)) = 2 * (((prgsC p).getI r).length - pc) + 2 := by
  simp only [wtC, cN_ne_roundN, if_false]
  rw [show (cN r pc - 2) / 2 = Nat.pair r pc by unfold cN; omega, Nat.unpair_pair]

@[simp] theorem wtC_inl (a : ℕ) : wtC p (.inl a) = 1 := rfl
@[simp] theorem wtC_round : wtC p (.inr roundN) = 2 * LP p + 4 := by simp [wtC]

theorem length_le_LP {r : ℕ} : ((prgsC p).getI r).length ≤ LP p := by
  by_cases hr : r < (prgsC p).length
  · exact List.le_sum_of_mem (List.mem_map.2 ⟨_, getI_memS hr, rfl⟩)
  · rw [List.getI_eq_default _ (by omega)]; exact Nat.zero_le _

theorem isPhase_cN {r pc : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    IsPhase (.inr (cN r pc) :: xs) ↔ 1 ≤ r ∧ pc = 0 := by
  simp only [IsPhase, List.head?_cons, Option.some.injEq, Sum.inr.injEq, reduceCtorEq,
    false_or, cN_ne_roundN, cN_inj, exists_false, or_false]
  constructor
  · rintro ⟨r', rfl, rfl⟩; omega
  · rintro ⟨h, rfl⟩; exact ⟨r - 1, by omega, rfl⟩

theorem isPhase_aN {r pc alt : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    IsPhase (.inl (aN r pc alt) :: xs) ↔ 1 ≤ r ∧ pc = 0 := by
  simp only [IsPhase, List.head?_cons, Option.some.injEq, Sum.inl.injEq, reduceCtorEq,
    false_or, aN_ne_finN, exists_false]
  constructor
  · rintro ⟨r', i, h⟩; obtain ⟨rfl, rfl, -⟩ := aN_inj h; omega
  · rintro ⟨h, rfl⟩; exact ⟨r - 1, alt, by rw [show r - 1 + 1 = r by omega]⟩

theorem isPhase_round {xs : List (ℕ ⊕ ℕ)} : IsPhase (.inr roundN :: xs) := Or.inl rfl
theorem isPhase_fin {xs : List (ℕ ⊕ ℕ)} : IsPhase (.inl finN :: xs) := Or.inr (Or.inl rfl)

/-! ## Outcomes of program actions on states -/

theorem fact_mem_applyEff {s : Set ℕ} {f : ℕ} {e : List ℕ × List ℕ}
    {L₁ L₂ : List (Option (Bool × ℕ))} :
    fact f ∈ Action.applyEff ({x | x ∈ e.1.map fact ++ L₁.map curF},
      {x | x ∈ e.2.map fact ++ L₂.map curF}) s ↔ (fact f ∈ s ∧ f ∉ e.2) ∨ f ∈ e.1 := by
  simp only [Action.applyEff, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.mem_append,
    List.mem_map, fact_eq_fact, exists_eq_right]
  have h1 : ∀ L : List (Option (Bool × ℕ)), ¬ ∃ x ∈ L, curF x = fact f :=
    fun L ⟨x, _, h⟩ => fact_ne_curF f x h.symm
  simp [h1]

/-- The outcomes of the action of a specification, on arbitrary states. -/
theorem mem_outcomes_toFAct {nm : ℕ} {a : ASpec} {s s' : Set ℕ}
    (h : s' ∈ (toFAct nm a).toAction.outcomes s) :
    ∃ e ∈ a.effs, ∀ f, fact f ∈ s' ↔ (fact f ∈ s ∧ f ∉ e.2) ∨ f ∈ e.1 := by
  obtain ⟨e', ⟨x, hx, he'⟩, rfl⟩ := h
  simp only [toFAct, FActDesc.effs, List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨e, he, fun f => ?_⟩
  subst he'
  have : (bif a.2.2.2.2.isEmpty then ([] : List ℕ) else a.2.2.2.1.map curF) =
      (bif a.2.2.2.2.isEmpty then [] else a.2.2.2.1).map curF := by
    cases a.2.2.2.2.isEmpty <;> rfl
  simp only [this]
  exact fact_mem_applyEff

theorem ctrS_frame {nm : ℕ} {a : ASpec} {s s' : Set ℕ}
    (hs' : s' ∈ (toFAct nm a).toAction.outcomes s)
    (hfr : ∀ e ∈ a.effs, ∀ j, fSlot (cslot p) j ∉ e.1 ∧ fSlot (cslot p) j ∉ e.2) :
    ctrS p s' = ctrS p s := by
  obtain ⟨e, he, hm⟩ := mem_outcomes_toFAct hs'
  unfold ctrS
  refine bitsum_congr fun j _ => ?_
  have := hm (fSlot (cslot p) j)
  have h1 := hfr e he j
  simp only [h1.1, h1.2, not_false_eq_true, and_true, or_false] at this
  simp [this]

theorem ctrS_inc {nm i : ℕ} {s s' : Set ℕ} (hi : i < Nc p)
    (happ : (toFAct nm (incSpec p i)).toAction.Applicable s)
    (hs' : s' ∈ (toFAct nm (incSpec p i)).toAction.outcomes s) :
    ctrS p s' = ctrS p s + 1 := by
  classical
  obtain ⟨e, he, hm⟩ := mem_outcomes_toFAct hs'
  simp only [incSpec, ASpec.effs, List.mem_singleton] at he
  subst he
  obtain ⟨hpre, hneg⟩ := happ
  have hlo : ∀ j < i, fact (fSlot (cslot p) j) ∈ s := fun j hj => hpre (by
    simp only [toFAct, incSpec, FActDesc.toAction, Set.mem_setOf_eq, List.mem_append,
      List.mem_map, List.mem_range]
    exact Or.inl ⟨_, ⟨j, hj, rfl⟩, rfl⟩)
  have hb : fact (fSlot (cslot p) i) ∉ s := fun h => Set.disjoint_left.1 hneg (by
    simp only [toFAct, incSpec, FActDesc.toAction, Set.mem_setOf_eq, List.mem_map]
    exact ⟨_, List.mem_singleton_self _, rfl⟩) h
  unfold ctrS
  refine bitsum_inc (fun j hj => by simp [hlo j hj]) (by simp [hb]) (fun j hj => ?_) ?_
    (fun j hj => ?_) _ hi
  · rw [decide_eq_false_iff_not, hm]; simp; omega
  · rw [decide_eq_true_eq, hm]; simp
  · simp only [hm, List.mem_map, List.mem_range, fSlot_inj, true_and, List.mem_singleton]
    have h2 : j ≠ i := by omega
    simp [h2]
    intro _; omega

/-- The program actions: the increment, or actions keeping the counter. -/
theorem spec_cases {r pc alt : ℕ} (hr : r < (prgsC p).length)
    (hpc : pc < ((prgsC p).getI r).length) (halt : alt < (((prgsC p).getI r).getI pc).length) :
    (¬ (1 ≤ r ∧ pc = 0) ∧ ∀ e ∈ ((((prgsC p).getI r).getI pc).getI alt).effs, ∀ j,
        fSlot (cslot p) j ∉ e.1 ∧ fSlot (cslot p) j ∉ e.2) ∨
      (1 ≤ r ∧ pc = 0 ∧ alt < Nc p ∧ (((prgsC p).getI r).getI pc).getI alt = incSpec p alt) := by
  rcases r with _ | r
  · left
    refine ⟨by omega, fun e he j => frame_prgs p (progInit p) (List.mem_cons_self ..) _
      (getI_memS hpc) _ (getI_memS halt) e he j⟩
  · have hr' : r < (rules p).length := by simpa [prgsC, rulesC] using hr
    have hP : (prgsC p).getI (r + 1) = incI p :: (rules p).getI r := by
      rw [prgsC, List.getI_cons_succ, rulesC, List.getI_eq_getElem _ (by simpa using hr'),
        List.getElem_map, List.getI_eq_getElem _ hr']
    rw [hP] at hpc halt ⊢
    rcases pc with _ | pc
    · right
      simp only [List.getI_cons_zero] at halt ⊢
      have ha : alt < Nc p := by simpa [incI] using halt
      refine ⟨by omega, by trivial, ha, ?_⟩
      rw [List.getI_eq_getElem _ halt]
      simp [incI, incSpec]
    · left
      simp only [List.getI_cons_succ, List.length_cons] at hpc halt ⊢
      exact ⟨by omega, fun e he j => frame_prgs p _
        (List.mem_cons_of_mem _ (getI_memS hr')) _ (getI_memS (by omega)) _ (getI_memS halt) e he j⟩

/-- The method bodies of `descC`. -/
theorem body_casesC {c : ℕ} {bs : List (ℕ ⊕ ℕ)} (hb : (descC p).toProblem.SeqBodyF c bs) :
    (∃ r pc alt, r < (prgsC p).length ∧ pc < ((prgsC p).getI r).length ∧
      alt < (((prgsC p).getI r).getI pc).length ∧ c = cN r pc ∧
      bs = [.inl (aN r pc alt), .inr (cN r (pc + 1))]) ∨
    (∃ r < (prgsC p).length, c = cN r ((prgsC p).getI r).length ∧ bs = [.inr roundN]) ∨
    (c = roundN ∧ ∃ r < (rulesC p).length, bs = [.inr (cN (r + 1) 0)]) ∨
    (c = roundN ∧ bs = [.inl finN]) := by
  obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff (seqMeths_descC p)).1 hb
  rw [descC_methods, List.mem_append, List.mem_append] at hls
  rcases hls with h | h | h
  · obtain ⟨r, hr, ⟨pc, hpc, alt, halt, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := mem_chainMethsS.1 h
    · exact Or.inl ⟨r, pc, alt, hr, hpc, halt, rfl, by simp [toLab]⟩
    · exact Or.inr (Or.inl ⟨r, hr, rfl, by simp [toLab]⟩)
  · have hc := head_roundMeths h
    simp only [meth] at hc
    subst hc
    obtain ⟨r, hr, rfl⟩ := (mem_roundMethsC p).1 h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, r, hr, by simp [toLab]⟩))
  · rw [List.mem_singleton, meth_injS] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, by simp [toLab]⟩))

theorem uniform_height {O : Set (Set ℕ)} (hO : O.Finite) {Q : ℕ → Set ℕ → Prop}
    (hmono : ∀ n n' s, n ≤ n' → Q n s → Q n' s) (h : ∀ s ∈ O, ∃ n, Q n s) :
    ∃ N, ∀ s ∈ O, Q N s := by
  classical
  let g : Set ℕ → ℕ := fun s => if hs : s ∈ O then (h s hs).choose else 0
  obtain ⟨N, hN⟩ := (hO.image g).bddAbove
  refine ⟨N, fun s hs => hmono _ _ _ (hN ⟨s, hs, rfl⟩) ?_⟩
  simp only [g, dif_pos hs]
  exact (h s hs).choose_spec

theorem one_le_wtC (x : ℕ ⊕ ℕ) : 1 ≤ wtC p x := by
  rcases x with _ | c
  · simp [wtC]
  · simp only [wtC]; split_ifs <;> omega

/-- **The measure argument.** -/
theorem lrun_of_XL {X : Problem.NSet ℕ ℕ ℕ ℕ} (hX : Problem.NGood X)
    (hA : ∀ tn s, X tn s → ∃ n, (descC p).toProblem.FAttrH true X n tn s) :
    ∀ N (xs : List (ℕ ⊕ ℕ)) (s : Set ℕ), muC p xs s = N → Problem.XL X xs s → ShapeC p xs →
      ∃ n, (descC p).toProblem.LRunH n xs s Set.univ := by
  classical
  have hv := descC_valid p
  have hP := FProbDesc.toProblem_wf hv
  have hM := methods_TO (seqMeths_descC p)
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro xs s hN hXL hsh
  have hB := ctrS_lt (p := p) s
  rcases List.eq_nil_or_concat' xs with rfl | hne
  · exact ⟨0, .nil (Set.mem_univ _)⟩
  have hne' : xs ≠ [] := by rintro rfl; simp at hne
  rcases Problem.XL_step hP hM hX hA hXL hne' with
    ⟨a, xs', rfl, happ, hall⟩ | ⟨c, bs, xs', rfl, hb, hXb⟩
  · -- a primitive move
    rcases hsh with h | ⟨x, h⟩ | ⟨r, pc, alt, hr, hpc, halt, h⟩
    · simp at h
    · obtain ⟨-, rfl⟩ := List.cons_eq_cons.1 h
      exact ⟨1, .prim happ fun _ _ => .nil (Set.mem_univ _)⟩
    · simp only [List.cons.injEq, Sum.inl.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfin := Action.outcomes_finite (hP.actions (aN r pc alt)) s
      have key : ∀ s' ∈ ((descC p).toProblem.δ (aN r pc alt)).outcomes s,
          muC p [.inr (cN r (pc + 1))] s' < muC p [.inl (aN r pc alt), .inr (cN r (pc + 1))] s := by
        intro s' hs'
        have hB' := ctrS_lt (p := p) s'
        rw [δ_aN hv rfl hr hpc halt] at hs' happ
        have hph' : ¬ IsPhase [.inr (cN r (pc + 1))] := by rw [isPhase_cN]; omega
        unfold muC
        rw [if_neg hph']
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wtC_inl, wtC_cN]
        rcases spec_cases hr hpc halt with ⟨hn, hfr⟩ | ⟨h1, rfl, hi, heq⟩
        · rw [if_neg (by rw [isPhase_aN]; exact hn), ctrS_frame hs' hfr]
          omega
        · rw [heq] at hs' happ
          rw [if_pos (by rw [isPhase_aN]; omega), ctrS_inc hi happ hs']
          have e : 2 ^ Nc p - ctrS p s - 1 = 2 ^ Nc p - (ctrS p s + 1) - 0 := by omega
          rw [e]; omega
      obtain ⟨n, hn⟩ := uniform_height hfin
        (Q := fun n s' => (descC p).toProblem.LRunH n [.inr (cN r (pc + 1))] s' Set.univ)
        (fun n n' s' h h' => h'.mono h le_rfl)
        (fun s' hs' => ih _ (hN ▸ key s' hs') _ s' rfl (hall s' hs') (Or.inr (Or.inl ⟨_, rfl⟩)))
      exact ⟨n + 1, .prim happ hn⟩
  · -- a decomposition
    have hxs' : xs' = [] := by
      rcases hsh with h | ⟨x, h⟩ | ⟨r, pc, alt, -, -, -, h⟩
      · simp at h
      · exact (List.cons_eq_cons.1 h).2
      · simp at h
    subst hxs'
    rw [List.append_nil] at hXb
    have hdec : muC p bs s < muC p [.inr c] s ∧ ShapeC p bs := by
      unfold muC
      rcases body_casesC hb with ⟨r, pc, alt, hr, hpc, halt, rfl, rfl⟩ | ⟨r, hr, rfl, rfl⟩ |
          ⟨rfl, r, hr, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨?_, Or.inr (Or.inr ⟨r, pc, alt, hr, hpc, halt, rfl⟩)⟩
        have e1 : IsPhase [Sum.inr (cN r pc)] ↔ IsPhase [Sum.inl (aN r pc alt), .inr (cN r (pc + 1))] := by
          rw [isPhase_cN, isPhase_aN]
        rw [e1]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wtC_cN, wtC_inl]
        omega
      · refine ⟨?_, Or.inr (Or.inl ⟨_, rfl⟩)⟩
        have hL : 1 ≤ ((prgsC p).getI r).length := by
          rcases r with _ | r
          · simp [prgsC, progInit]
          · simp only [prgsC, List.getI_cons_succ, rulesC]
            rw [List.getI_eq_getElem _ (by simpa [prgsC, rulesC] using hr)]
            simp
        rw [if_pos isPhase_round, if_neg (by rw [isPhase_cN]; omega)]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wtC_cN, wtC_round,
          Nat.sub_self]
        obtain ⟨t, ht⟩ : ∃ t, 2 ^ Nc p - ctrS p s = t + 1 := ⟨2 ^ Nc p - ctrS p s - 1, by omega⟩
        rw [Nat.sub_zero, ht, Nat.add_sub_cancel, Nat.add_mul, one_mul]
        omega
      · refine ⟨?_, Or.inr (Or.inl ⟨_, rfl⟩)⟩
        rw [if_pos (by rw [isPhase_cN]; omega), if_pos isPhase_round]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wtC_cN, wtC_round]
        have := length_le_LP (p := p) (r := r + 1)
        omega
      · refine ⟨?_, Or.inr (Or.inl ⟨_, rfl⟩)⟩
        rw [if_pos isPhase_fin, if_pos isPhase_round]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wtC_inl, wtC_round]
        omega
    obtain ⟨n, hn⟩ := ih _ (hN ▸ hdec.1) bs s rfl hXb hdec.2
    exact ⟨n + 1, .comp hb (by simpa using hn)⟩

/-- **Fair strong cyclic solvability of the counter construction is plan existence.** -/
theorem descC_fair_iff {p : ProbDesc} (hp : p.Valid) (hto : p.toProblem.IsTO) :
    (descC p).toProblem.MPStrongCyclicFairSolvable ↔ p.toProblem.Solvable := by
  refine ⟨fun hf => ?_, fun h => Problem.fair_of_mpStrongSolvable ((descC_solvable_iff hp hto).2 h)⟩
  have hv := descC_valid p
  have hP := FProbDesc.toProblem_wf hv
  have hseq : (descC p).toProblem.tnI.IsSeqNet (List.range 1) [.inr (cN 0 0)] := by
    have : (descC p).toProblem.tnI = (seqTn [(true, cN 0 0)]).toTaskNetwork := rfl
    rw [this]; simpa [toLab] using isSeqNet_seqTn [(true, cN 0 0)]
  obtain ⟨X, hX, hA, hXL⟩ := Problem.XL_init hP hseq hf
  obtain ⟨n, hn⟩ := lrun_of_XL hX hA _ _ _ rfl hXL (Or.inr (Or.inl ⟨_, rfl⟩))
  refine (descC_solvable_iff hp hto).1 ?_
  rw [mpStrong_iff_lrun hv (seqMeths_descC p) (rfl : (descC p).tnI = _)]
  exact ⟨n, by simpa [toLab] using hn⟩

end HardMP

open HardMP HTN HTN.Syn HTN.Syn.PolyDom HTN.Article

/-- **[CB22, Thm. 3], strong cyclic (fair reading), hardness**: regular totally ordered
problems. -/
theorem hardFair_REG_TO_exp :
    Cx.Hard Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.REG FClass.TO)) :=
  HTN.Article.thm_4_3_6.of_redP (redP_TO_fair pt_descC descC_valid
    (fun p => ⟨descC_REG p, descC_TO p⟩) fun _ hp hto => descC_fair_iff hp hto)

/-- **[CB22, Thm. 3], strong cyclic (fair reading), hardness.** -/
theorem hardFair_REG_exp : Cx.Hard Cx.EXPTIME (PlanExMPFair FClass.REG) :=
  HTN.Article.thm_4_3_6.of_redP (redP_TO_fair pt_descC descC_valid descC_REG
    fun _ hp hto => descC_fair_iff hp hto)

/-- **[CB22, Thm. 3], strong cyclic (fair reading): EXPTIME-complete.** -/
theorem fairMP_REG_complete : Cx.Complete Cx.EXPTIME (PlanExMPFair FClass.REG) :=
  ⟨fairMP_REG_mem, hardFair_REG_exp⟩

theorem fairMP_REG_TO_complete :
    Cx.Complete Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.REG FClass.TO)) :=
  ⟨fairMP_REG_TO_mem, hardFair_REG_TO_exp⟩

end FOND
