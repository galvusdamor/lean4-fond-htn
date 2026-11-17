import FondHtn.HardMP.Desc
/-!
# Well-formedness and classes of the reduction descriptions

* `FOND.HardMP.prgs_spec` — all action specifications of the programs are well formed and have
  at least one effect;
* `FOND.HardMP.descA_valid`, `FOND.HardMP.descR_valid` — the descriptions are well formed;
* `FOND.HardMP.descA_TO`, `FOND.HardMP.descA_ACYC`, `FOND.HardMP.descA_TR` — the acyclic
  description is totally ordered, acyclic and tail-recursive;
* `FOND.HardMP.descR_REG`, `FOND.HardMP.descR_TO` — the regular description is regular and
  totally ordered.
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

/-! ## Specifications -/

/-- Every alternative of an instruction is well formed and has an effect. -/
def GoodIns (ins : List ASpec) : Prop := ∀ a ∈ ins, a.WF ∧ a.effs ≠ []

theorem goodIns_guess (f : ℕ) : GoodIns (guessI f) := by
  simp [GoodIns, guessI, ASpec.WF, ASpec.cnew, ASpec.effs]
theorem goodIns_eq (f g : ℕ) : GoodIns (eqI f g) := by
  simp [GoodIns, eqI, ASpec.WF, ASpec.cnew, ASpec.effs, noeff]
theorem goodIns_ccp (s f g : ℕ) : GoodIns (ccpI s f g) := by
  simp [GoodIns, ccpI, ASpec.WF, ASpec.cnew, ASpec.effs, noeff]
theorem goodIns_ccur (s : ℕ) (h y : Option (Bool × ℕ)) : GoodIns (ccurI s h y) := by
  simp [GoodIns, ccurI, ASpec.WF, ASpec.cnew, ASpec.cpre, ASpec.effs, noeff]
theorem goodIns_chk (pre neg : List ℕ) (cpre : List (Option (Bool × ℕ))) :
    GoodIns (chkI pre neg cpre) := by
  simp [GoodIns, chkI, ASpec.WF, ASpec.cnew, ASpec.effs, noeff]
theorem goodIns_set (d : ℕ) : GoodIns (setI d) := by
  simp [GoodIns, setI, ASpec.WF, ASpec.cnew, ASpec.effs]
theorem goodIns_pick (sel : ℕ → ℕ) {k : ℕ} (hk : k ≠ 0) : GoodIns (pickI sel k) := by
  simp [GoodIns, pickI, ASpec.WF, ASpec.cnew, ASpec.effs, hk]
theorem goodIns_bit (V : List ℕ) (act : ActDesc) (j : ℕ) : GoodIns (bitI V act j) := by
  unfold bitI
  cases decide (V.getI j ∈ act.2.2.2.1)
  · cases decide (V.getI j ∈ act.2.2.2.2)
    · exact goodIns_eq _ _
    · exact goodIns_chk _ _ _
  · exact goodIns_chk _ _ _
theorem goodIns_chkA (V : List ℕ) (act : ActDesc) (a : ℕ) : GoodIns (chkA V act a) := by
  unfold chkA
  cases act.2.1.all (fun f => decide (f ∈ V))
  · simp [GoodIns]
  · simp [GoodIns, ASpec.WF, ASpec.cnew, ASpec.effs]
theorem goodIns_goal (p : ProbDesc) : GoodIns (goalI p) := by
  unfold goalI
  cases p.goalPos.all (fun f => decide (f ∈ pfacts p))
  · simp [GoodIns]
  · exact goodIns_chk _ _ _

theorem progM_good (n : ℕ) (h : Option (Bool × ℕ)) (bs : List (Bool × ℕ)) :
    ∀ ins ∈ progM n h bs, GoodIns ins := by
  intro ins hins
  unfold progM at hins
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hins
  rcases hins with (((rfl | ⟨f, -, rfl⟩) | ⟨q, -, rfl⟩) | ⟨q, -, rfl⟩) | hins
  · exact goodIns_chk _ _ _
  · exact goodIns_guess _
  · exact goodIns_eq _ _
  · exact goodIns_eq _ _
  · rcases bs with _ | ⟨b, bs⟩
    · simp only [List.isEmpty_nil, cond_true, List.mem_singleton] at hins
      subst hins; exact goodIns_set _
    · simp only [List.isEmpty_cons, cond_false, List.mem_append, List.mem_singleton,
        List.mem_flatMap, List.mem_map] at hins
      rcases hins with (rfl | ⟨i, -, q, -, rfl⟩) | ⟨i, -, rfl⟩
      · exact goodIns_pick _ (by simp)
      · exact goodIns_ccp _ _ _
      · exact goodIns_ccur _ _ _

theorem progA_good (p : ProbDesc) (a : ℕ) : ∀ ins ∈ progA p a, GoodIns ins := by
  intro ins hins
  unfold progA at hins
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hins
  rcases hins with ⟨j, -, rfl⟩ | rfl
  · exact goodIns_bit _ _ _
  · exact goodIns_chkA _ _ _

theorem prgs_good (p : ProbDesc) : ∀ P ∈ prgs p, ∀ ins ∈ P, GoodIns ins := by
  intro P hP ins hins
  unfold prgs at hP
  rcases List.mem_cons.1 hP with rfl | hP
  · unfold progInit at hins
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hins
    rcases hins with ⟨f, -, rfl⟩ | rfl
    · exact goodIns_guess _
    · exact goodIns_goal _
  · unfold rules at hP
    rcases List.mem_append.1 hP with hP | hP
    · rcases List.mem_append.1 hP with hP | hP
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
        rcases hP with rfl | rfl
        · simp only [progNoop, List.mem_singleton] at hins
          subst hins; exact goodIns_chk _ _ _
        · exact progM_good _ _ _ _ hins
      · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hP
        exact progM_good _ _ _ _ hins
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hP
      exact progA_good _ _ _ hins

theorem prgs_spec (p : ProbDesc) : ∀ P ∈ prgs p, ∀ ins ∈ P, ∀ a ∈ ins, a.WF ∧ a.effs ≠ [] :=
  prgs_good p

/-! ## Names -/

theorem getI_mem' {α : Type} [Inhabited α] {l : List α} {i : ℕ} (hi : i < l.length) :
    l.getI i ∈ l := by
  rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

theorem aN_inj {r pc alt r' pc' alt' : ℕ} (h : aN r pc alt = aN r' pc' alt') :
    r = r' ∧ pc = pc' ∧ alt = alt' := by
  unfold aN at h
  have h1 : Nat.pair r (Nat.pair pc alt) = Nat.pair r' (Nat.pair pc' alt') := by omega
  obtain ⟨rfl, h2⟩ := Nat.pair_eq_pair.1 h1
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h2
  exact ⟨rfl, rfl, rfl⟩

theorem aN_ne_finN (r pc alt : ℕ) : aN r pc alt ≠ finN := by unfold aN finN; omega

/-- The indices of the program actions. -/
def actIdx (P : List (List (List ASpec))) : List (ℕ × ℕ × ℕ) :=
  (List.range P.length).flatMap fun r =>
    (List.range (P.getI r).length).flatMap fun pc =>
      (List.range ((P.getI r).getI pc).length).map fun alt => (r, pc, alt)

theorem mem_actIdx {P : List (List (List ASpec))} {t : ℕ × ℕ × ℕ} :
    t ∈ actIdx P ↔ t.1 < P.length ∧ t.2.1 < (P.getI t.1).length ∧
      t.2.2 < ((P.getI t.1).getI t.2.1).length := by
  obtain ⟨r, pc, alt⟩ := t
  simp only [actIdx, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨r', hr, pc', hpc, alt', halt, rfl, rfl, rfl⟩; exact ⟨hr, hpc, halt⟩
  · rintro ⟨hr, hpc, halt⟩; exact ⟨r, hr, pc, hpc, alt, halt, rfl, rfl, rfl⟩

theorem actIdx_nodup (P : List (List (List ASpec))) : (actIdx P).Nodup := by
  unfold actIdx
  refine List.nodup_flatMap.2 ⟨fun r _ => List.nodup_flatMap.2 ⟨fun pc _ =>
    (List.nodup_range).map fun a b h => by simpa using h, ?_⟩, ?_⟩
  · refine List.nodup_range.imp fun {a b} hab => ?_
    rw [Function.onFun, List.disjoint_left]
    intro x hx hx'
    simp only [List.mem_map, List.mem_range] at hx hx'
    obtain ⟨_, -, rfl⟩ := hx
    obtain ⟨_, -, h⟩ := hx'
    simp only [Prod.mk.injEq] at h
    exact hab h.2.1.symm
  · refine List.nodup_range.imp fun {a b} hab => ?_
    rw [Function.onFun, List.disjoint_left]
    intro x hx hx'
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx hx'
    obtain ⟨_, -, _, -, rfl⟩ := hx
    obtain ⟨_, -, _, -, h⟩ := hx'
    simp only [Prod.mk.injEq] at h
    exact hab h.1.symm

theorem acts_eq (P : List (List (List ASpec))) :
    acts P = toFAct finN finSpec :: (actIdx P).map fun t =>
      toFAct (aN t.1 t.2.1 t.2.2) (((P.getI t.1).getI t.2.1).getI t.2.2) := by
  simp [acts, actIdx, List.map_flatMap, Function.comp_def]

theorem names_acts (P : List (List (List ASpec))) :
    (acts P).map FActDesc.name = finN :: (actIdx P).map fun t => aN t.1 t.2.1 t.2.2 := by
  rw [acts_eq]; simp [List.map_map, Function.comp_def, toFAct, FActDesc.name]

theorem names_nodup_acts (P : List (List (List ASpec))) : ((acts P).map FActDesc.name).Nodup := by
  rw [names_acts, List.nodup_cons]
  refine ⟨fun h => ?_, (actIdx_nodup P).map_on fun a _ b _ h => ?_⟩
  · obtain ⟨t, -, ht⟩ := List.mem_map.1 h
    exact aN_ne_finN _ _ _ ht
  · obtain ⟨h1, h2, h3⟩ := aN_inj h
    obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b
    simp_all

theorem mem_names_acts {P : List (List (List ASpec))} {x : ℕ} :
    x ∈ (acts P).map FActDesc.name ↔ x = finN ∨ ∃ t ∈ actIdx P, x = aN t.1 t.2.1 t.2.2 := by
  rw [names_acts]; simp [eq_comm]

theorem effs_ne_acts {P : List (List (List ASpec))} (hP : ∀ Q ∈ P, ∀ ins ∈ Q, GoodIns ins) :
    ∀ a ∈ acts P, a.effs ≠ [] := by
  intro a ha
  rw [acts_eq] at ha
  rcases List.mem_cons.1 ha with rfl | ha
  · simp [toFAct, FActDesc.effs, finSpec, noeff]
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
    obtain ⟨h1, h2, h3⟩ := mem_actIdx.1 ht
    have := (hP _ (getI_mem' h1) _ (getI_mem' h2) _ (getI_mem' h3)).2
    simpa [toFAct, FActDesc.effs, ASpec.effs] using this

/-! ## Methods -/

theorem mem_chainMeths {P : List (List (List ASpec))} {ex : List (Bool × ℕ)} {e : MethodDesc} :
    e ∈ chainMeths P ex ↔
      (∃ t ∈ actIdx P, e = meth (cN t.1 t.2.1) [(false, aN t.1 t.2.1 t.2.2), (true, cN t.1 (t.2.1 + 1))]) ∨
      ∃ r < P.length, e = meth (cN r (P.getI r).length) ex := by
  simp only [chainMeths, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton]
  constructor
  · rintro ⟨r, hr, ⟨pc, hpc, alt, halt, rfl⟩ | rfl⟩
    · exact Or.inl ⟨(r, pc, alt), mem_actIdx.2 ⟨hr, hpc, halt⟩, rfl⟩
    · exact Or.inr ⟨r, hr, rfl⟩
  · rintro (⟨⟨r, pc, alt⟩, ht, rfl⟩ | ⟨r, hr, rfl⟩)
    · obtain ⟨hr, hpc, halt⟩ := mem_actIdx.1 ht
      exact ⟨r, hr, Or.inl ⟨pc, hpc, alt, halt, rfl⟩⟩
    · exact ⟨r, hr, Or.inr rfl⟩

/-- A method of the descriptions: a sequence body whose primitive labels are declared. -/
def MethOK (P : List (List (List ASpec))) (e : MethodDesc) : Prop :=
  ∃ c body, e = meth c body ∧ ∀ q ∈ body, q.1 = false → q.2 ∈ (acts P).map FActDesc.name

theorem methOK_chain {P : List (List (List ASpec))} {ex : List (Bool × ℕ)}
    (hex : ∀ q ∈ ex, q.1 = true) {e : MethodDesc} (he : e ∈ chainMeths P ex) : MethOK P e := by
  rcases mem_chainMeths.1 he with ⟨t, ht, rfl⟩ | ⟨r, -, rfl⟩
  · refine ⟨_, _, rfl, fun q hq hf => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact mem_names_acts.2 (Or.inr ⟨t, ht, rfl⟩)
    · simp at hf
  · exact ⟨_, _, rfl, fun q hq hf => by rw [hex q hq] at hf; simp at hf⟩

theorem methOK_round {P : List (List (List ASpec))} {e : MethodDesc} (he : e ∈ roundMeths P) :
    MethOK P e := by
  simp only [roundMeths, List.mem_map] at he
  obtain ⟨r, -, rfl⟩ := he
  exact ⟨_, _, rfl, fun q hq hf => by simp at hq; rw [hq] at hf; simp at hf⟩

theorem methOK_clock {P : List (List (List ASpec))} {N : ℕ} {e : MethodDesc}
    (he : e ∈ clockMeths N) : MethOK P e := by
  simp only [clockMeths, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨j, -, rfl⟩
  · exact ⟨_, _, rfl, fun q hq hf => by simp at hq; rw [hq] at hf; simp at hf⟩
  · exact ⟨_, _, rfl, fun q hq hf => by
      simp at hq; rcases hq with rfl | rfl <;> simp at hf⟩

theorem methOK_fin {P : List (List (List ASpec))} : MethOK P (meth roundN [(false, finN)]) :=
  ⟨_, _, rfl, fun q hq _ => by
    simp at hq; rw [hq]; exact mem_names_acts.2 (Or.inl rfl)⟩

theorem tnValid_of_methOK {P : List (List (List ASpec))} {d : FProbDesc} (hd : d.actions = acts P)
    {e : MethodDesc} (he : MethOK P e) : TnValid d.Declared e.2 := by
  obtain ⟨c, body, rfl, hb⟩ := he
  exact seqTn_valid fun q hq hf => by
    show q.2 ∈ d.actions.map FActDesc.name
    rw [hd]; exact hb q hq hf

/-! ## Validity -/

theorem descA_valid (p : ProbDesc) : (descA p).Valid where
  names_nodup := names_nodup_acts _
  effs_ne := effs_ne_acts (prgs_good p)
  tnI := tnValid_of_methOK (e := meth 0 [(true, cN 0 0), (true, clkN (Nclk p)), (false, finN)])
    (P := prgs p) rfl ⟨_, _, rfl, fun q hq hf => by
      simp at hq; rcases hq with rfl | rfl | rfl <;> simp at hf
      exact mem_names_acts.2 (Or.inl rfl)⟩
  methods := by
    intro e he
    refine tnValid_of_methOK (P := prgs p) rfl ?_
    simp only [descA, FProbDesc.methods, List.mem_append] at he
    rcases he with (he | he) | he
    · exact methOK_chain (by simp) he
    · exact methOK_round he
    · exact methOK_clock he

theorem descR_valid (p : ProbDesc) : (descR p).Valid where
  names_nodup := names_nodup_acts _
  effs_ne := effs_ne_acts (prgs_good p)
  tnI := tnValid_of_methOK (e := meth 0 [(true, cN 0 0)]) (P := prgs p) rfl
    ⟨_, _, rfl, fun q hq hf => by simp at hq; rw [hq] at hf; simp at hf⟩
  methods := by
    intro e he
    refine tnValid_of_methOK (P := prgs p) rfl ?_
    simp only [descR, FProbDesc.methods, List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | rfl
    · exact methOK_chain (by simp) he
    · exact methOK_round he
    · exact methOK_fin

/-! ## Classes -/

/-- All methods of the descriptions are sequence methods. -/
def SeqMeths (d : FProbDesc) : Prop := ∀ e ∈ d.methods, ∃ c body, e = meth c body

theorem seqMeths_descA (p : ProbDesc) : SeqMeths (descA p) := by
  intro e he
  simp only [descA, FProbDesc.methods, List.mem_append] at he
  rcases he with (he | he) | he
  · obtain ⟨c, b, h, -⟩ := methOK_chain (by simp) he; exact ⟨c, b, h⟩
  · obtain ⟨c, b, h, -⟩ := methOK_round (P := prgs p) he; exact ⟨c, b, h⟩
  · obtain ⟨c, b, h, -⟩ := methOK_clock (P := prgs p) he; exact ⟨c, b, h⟩

theorem seqMeths_descR (p : ProbDesc) : SeqMeths (descR p) := by
  intro e he
  simp only [descR, FProbDesc.methods, List.mem_append, List.mem_singleton] at he
  rcases he with (he | he) | rfl
  · obtain ⟨c, b, h, -⟩ := methOK_chain (by simp) he; exact ⟨c, b, h⟩
  · obtain ⟨c, b, h, -⟩ := methOK_round (P := prgs p) he; exact ⟨c, b, h⟩
  · exact ⟨_, _, rfl⟩

theorem to_of_seq {d : FProbDesc} (hm : SeqMeths d) {ls : List (Bool × ℕ)} (ht : d.tnI = seqTn ls) :
    FClass.TO d.toProblem := by
  refine ⟨?_, fun m hm' => ?_⟩
  · show d.tnI.toTaskNetwork.IsTotallyOrdered
    rw [ht]; exact seqTn_isTO ls
  · obtain ⟨⟨e, he, rfl⟩, -⟩ := hm'
    obtain ⟨c, body, rfl⟩ := hm e he
    exact seqTn_isTO body

theorem descA_TO (p : ProbDesc) : FClass.TO (descA p).toProblem := to_of_seq (seqMeths_descA p) rfl

theorem descR_TO (p : ProbDesc) : FClass.TO (descR p).toProblem := to_of_seq (seqMeths_descR p) rfl

theorem mem_T_seqTn {ls : List (Bool × ℕ)} {t : ℕ} :
    t ∈ (seqTn ls).toTaskNetwork.T ↔ t < ls.length := by
  simp [TnDesc.toTaskNetwork, seqTn_ids]

theorem fst_of_label_inr {ls : List (Bool × ℕ)} {t c : ℕ} (ht : t < ls.length)
    (h : (seqTn ls).toTaskNetwork.α t = Sum.inr c) : ls.getI t = (true, c) := by
  have : (seqTn ls).label t = Sum.inr c := h
  rw [label_seqTn ht] at this
  unfold toLab at this
  generalize ls.getI t = q at this ⊢
  obtain ⟨b, x⟩ := q
  cases b <;> simp_all

theorem mem_of_label_inr {ls : List (Bool × ℕ)} {t c : ℕ}
    (ht : t ∈ (seqTn ls).toTaskNetwork.T) (h : (seqTn ls).toTaskNetwork.α t = Sum.inr c) :
    (true, c) ∈ ls := by
  have ht' := mem_T_seqTn.1 ht
  rw [← fst_of_label_inr ht' h]; exact getI_mem' ht'

/-- **Rank criterion** for the descriptions. -/
theorem acyc_of_rank {d : FProbDesc} (hm : SeqMeths d) (rk : ℕ → ℕ)
    (h : ∀ c body, meth c body ∈ d.methods → ∀ c', (true, c') ∈ body → rk c' < rk c) :
    FClass.ACYC d.toProblem := by
  refine HTN.Problem.isAcyclic_of_rank _ rk fun m hm' t ht c hc => ?_
  obtain ⟨⟨e, he, rfl⟩, -⟩ := hm'
  obtain ⟨c₀, body, rfl⟩ := hm e he
  exact h c₀ body he c (mem_of_label_inr ht hc)

/-- The rank of a compound name of `descA`. -/
def rkA (P : List (List (List ASpec))) (c : ℕ) : ℕ :=
  if c = 0 then (P.map List.length).sum + 2
  else if c % 2 = 1 then (P.map List.length).sum + 3 + (c - 1) / 2
  else (P.getI (Nat.unpair ((c - 2) / 2)).1).length - (Nat.unpair ((c - 2) / 2)).2 + 1

theorem rkA_cN (P : List (List (List ASpec))) (r pc : ℕ) :
    rkA P (cN r pc) = (P.getI r).length - pc + 1 := by
  unfold rkA cN
  rw [if_neg (by omega), if_neg (by omega),
    show (2 * Nat.pair r pc + 2 - 2) / 2 = Nat.pair r pc by omega, Nat.unpair_pair]

theorem rkA_clk (P : List (List (List ASpec))) (j : ℕ) :
    rkA P (clkN j) = (P.map List.length).sum + 3 + j := by
  unfold rkA clkN
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem rkA_round (P : List (List (List ASpec))) : rkA P roundN = (P.map List.length).sum + 2 := by
  simp [rkA, roundN]

theorem length_getI_le_sum (P : List (List (List ASpec))) (r : ℕ) :
    (P.getI r).length ≤ (P.map List.length).sum := by
  by_cases hr : r < P.length
  · exact List.le_sum_of_mem (List.mem_map.2 ⟨_, getI_mem' hr, rfl⟩)
  · rw [List.getI_eq_default _ (by omega)]; exact Nat.zero_le _

theorem seqTn_inj {ls ls' : List (Bool × ℕ)} (h : seqTn ls = seqTn ls') : ls = ls' := by
  have hl : ls.length = ls'.length := by
    have := congrArg (fun t : TnDesc => t.1.length) h
    simpa [seqTn] using this
  have hm : ∀ i < ls.length, ls.getI i = ls'.getI i := by
    intro i hi
    have := congrArg (fun t : TnDesc => t.label i) h
    simp only [label_seqTn hi, label_seqTn (hl ▸ hi)] at this
    unfold toLab at this
    generalize ls.getI i = q at this ⊢
    generalize ls'.getI i = q' at this ⊢
    obtain ⟨b, x⟩ := q; obtain ⟨b', x'⟩ := q'
    cases b <;> cases b' <;> simp_all
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have := hm i h1
  rwa [← List.getD_default_eq_getI, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ h1,
    List.getD_eq_getElem _ _ h2] at this

theorem meth_inj {c c' : ℕ} {b b' : List (Bool × ℕ)} (h : meth c b = meth c' b') :
    c = c' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact ⟨h1, seqTn_inj h2⟩

theorem descA_ACYC (p : ProbDesc) : FClass.ACYC (descA p).toProblem := by
  refine acyc_of_rank (seqMeths_descA p) (rkA (prgs p)) fun c body he c' hc' => ?_
  simp only [descA, FProbDesc.methods, List.mem_append] at he
  rcases he with (he | he) | he
  · rcases mem_chainMeths.1 he with ⟨t, ht, he'⟩ | ⟨r, -, he'⟩
    · obtain ⟨rfl, rfl⟩ := meth_inj he'
      simp only [List.mem_cons, Prod.mk.injEq, Bool.true_eq_false, false_and, List.not_mem_nil,
        or_false, true_and, false_or] at hc'
      obtain ⟨-, hpc, -⟩ := mem_actIdx.1 ht
      rw [hc', rkA_cN, rkA_cN]
      omega
    · obtain ⟨rfl, rfl⟩ := meth_inj he'
      simp at hc'
  · simp only [roundMeths, List.mem_map, List.mem_range] at he
    obtain ⟨r, -, he'⟩ := he
    obtain ⟨rfl, rfl⟩ := meth_inj he'.symm
    simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hc'
    rw [hc', rkA_cN, rkA_round]
    have := length_getI_le_sum (prgs p) (r + 1)
    omega
  · simp only [clockMeths, List.mem_cons, List.mem_map, List.mem_range] at he
    rcases he with he | ⟨j, -, he⟩
    · obtain ⟨rfl, rfl⟩ := meth_inj he.symm
      simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hc'
      rw [hc', rkA_clk, rkA_round]; omega
    · obtain ⟨rfl, rfl⟩ := meth_inj he.symm
      simp only [List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false,
        or_self] at hc'
      rw [hc', rkA_clk, rkA_clk]; omega

theorem descA_TR (p : ProbDesc) : FClass.TR (descA p).toProblem :=
  HTN.Problem.IsAcyclic.isTailRecursive (descA_ACYC p)

theorem seqTn_regular {ls : List (Bool × ℕ)}
    (h : ∀ i < ls.length, (ls.getI i).1 = true → i + 1 = ls.length) :
    (seqTn ls).toTaskNetwork.IsRegular := by
  have hab : ∀ t ∈ (seqTn ls).toTaskNetwork.T, (seqTn ls).toTaskNetwork.IsAbstractId t →
      t + 1 = ls.length := by
    rintro t ht ⟨c, hc⟩
    have ht' := mem_T_seqTn.1 ht
    exact h t ht' (by rw [fst_of_label_inr ht' hc])
  refine ⟨fun t ht t' ht' ha ha' => ?_, fun t ht ha t' ht' hne => ?_⟩
  · have := hab t ht ha; have := hab t' ht' ha'; omega
  · have := hab t ht ha
    have := mem_T_seqTn.1 ht'
    show (seqTn ls).toTaskNetwork.ord t' t
    rw [ord_seqTn_iff]; omega

/-- A sequence body with at most one compound task, at the end. -/
def RegBody (body : List (Bool × ℕ)) : Prop :=
  ∀ i < body.length, (body.getI i).1 = true → i + 1 = body.length

theorem regBody_two (a c : ℕ) : RegBody [(false, a), (true, c)] := by
  intro i hi h
  simp at hi
  interval_cases i <;> simp_all

theorem regBody_one (b : Bool) (c : ℕ) : RegBody [(b, c)] := by
  intro i hi _; simp at hi; simp; omega

theorem regBody_nil : RegBody [] := by intro i hi; simp at hi

theorem descR_REG (p : ProbDesc) : FClass.REG (descR p).toProblem := by
  intro m hm
  obtain ⟨⟨e, he, rfl⟩, -⟩ := hm
  suffices ∃ c body, e = meth c body ∧ RegBody body by
    obtain ⟨c, body, rfl, hb⟩ := this
    exact seqTn_regular hb
  simp only [descR, FProbDesc.methods, List.mem_append, List.mem_singleton] at he
  rcases he with (he | he) | rfl
  · rcases mem_chainMeths.1 he with ⟨t, -, rfl⟩ | ⟨r, -, rfl⟩
    · exact ⟨_, _, rfl, regBody_two _ _⟩
    · exact ⟨_, _, rfl, regBody_one _ _⟩
  · simp only [roundMeths, List.mem_map] at he
    obtain ⟨r, -, rfl⟩ := he
    exact ⟨_, _, rfl, regBody_one _ _⟩
  · exact ⟨_, _, rfl, regBody_one _ _⟩

end HardMP

end FOND
