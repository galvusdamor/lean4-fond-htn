import FondHtn.Lang.Desc
import HtnComplexity.Article.NoHTNNP
import HtnComplexity.PT.NP
/-!
# Weak plan existence of primitive problems is in NP ([CB21, Cor. 4.2], membership)

For a primitive problem (`tn_I` contains no compound task) no decomposition step applies, so the
only achievable primitive task network is `tn_I` itself
(`FOND.Problem.achievablePrimitive_iff_of_primitive`).  A weak LD solution is then a
linearisation of `tn_I` together with a choice of one outcome per step that makes every action
applicable.  The certificate is the list of pairs `(task id, chosen effect)`; it is checked in
polynomial time (`FOND.Prim.weakCertB`, `FOND.Prim.pt_weakCertB`).

* **`FOND.weakLD_PRIM_mem`** — `PlanExFM weakLD PRIM ∈ NP`;
* **`FOND.weakOD_PRIM_mem`** — `PlanExFM weakOD PRIM ∈ NP` (weak LD = weak OD for well-formed
  problems, [CB21, Prop. 2.12], `FOND.planExFM_weakOD_eq`).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.Article.NoHTN PTime

/-! ## Primitive problems: the only achievable primitive network is `tn_I` -/

namespace Problem

variable {F A C I : Type*} [DecidableEq I] (P : Problem F A C I)

theorem decomposesTo_of_primitive {tn tn' : TaskNetwork I A C} (h : P.DecomposesTo tn tn')
    (hp : tn.IsPrimitive) : tn' = tn := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨t, m, -, ht, hlab, -⟩ := hs
    obtain ⟨a, ha⟩ := hp t ht
    rw [ha] at hlab
    exact absurd hlab (by simp)

/-- **For a primitive problem the achievable primitive task networks are just `tn_I`.** -/
theorem achievablePrimitive_iff_of_primitive (h : P.tnI.IsPrimitive) {tn : TaskNetwork I A C} :
    P.AchievablePrimitive tn ↔ tn = P.tnI :=
  ⟨fun ha => P.decomposesTo_of_primitive ha.1 h, fun e => e ▸ ⟨Relation.ReflTransGen.refl, h⟩⟩

/-- Weak LD solvability of a primitive problem: some linearisation of `tn_I` is weakly
executable. -/
theorem weakLDSolvable_iff_of_primitive (h : P.tnI.IsPrimitive) :
    P.WeakLDSolvable ↔ ∃ l as, P.tnI.IsLinearization l ∧ P.tnI.IsActionSeq l as ∧
      P.WeakExec as P.init := by
  constructor
  · rintro ⟨tn, l, hach, hl, as, has, hex⟩
    obtain rfl := (P.achievablePrimitive_iff_of_primitive h).1 hach
    exact ⟨l, as, hl, has, hex⟩
  · rintro ⟨l, as, hl, has, hex⟩
    exact ⟨P.tnI, l, (P.achievablePrimitive_iff_of_primitive h).2 rfl, hl, as, has, hex⟩

end Problem

/-! ## Weak LD = weak OD on the level of languages -/

/-- Weak LD and weak OD plan existence coincide for every class ([CB21, Prop. 2.12]). -/
theorem planExFM_weakOD_eq (Y : FClass) : PlanExFM .weakOD Y = PlanExFM .weakLD Y := by
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hp, hy, hs⟩
    exact ⟨p, rfl, hp, hy,
      (Problem.weakLDSolvable_iff_weakODSolvable (FProbDesc.toProblem_wf hp).tnI).2 hs⟩
  · rintro ⟨p, rfl, hp, hy, hs⟩
    exact ⟨p, rfl, hp, hy,
      (Problem.weakLDSolvable_iff_weakODSolvable (FProbDesc.toProblem_wf hp).tnI).1 hs⟩

namespace Prim

/-! ## Executing with chosen effects -/

/-- The lists of an action: `Π⁺`, `Π⁻`, effects. -/
abbrev ActL : Type := List ℕ × List ℕ × List (List ℕ × List ℕ)

/-- The no-op `(∅, ∅, {(∅, ∅)})` denoted by an undeclared name. -/
def defAct : ActL := ([], [], [([], [])])

/-- The lists of the action of a name (the first one declared, else the no-op). -/
def actL (p : FProbDesc) (a : ℕ) : ActL :=
  ((p.actions.filter fun x => x.name == a).map Prod.snd ++ [defAct]).headI

theorem δ_eq_actL (p : FProbDesc) (a : ℕ) : p.δ a = FActDesc.toAction (a, actL p a) := by
  unfold FProbDesc.δ actL
  induction p.actions with
  | nil =>
    apply Action.ext' <;> ext <;> simp [defAct, FActDesc.toAction, FActDesc.effs]
  | cons x l ih =>
    by_cases h : x.name = a
    · simp [h]
      rfl
    · simpa [List.find?_cons, h] using ih

/-- The state after an effect, as a list. -/
def nextL (s : List ℕ) (e : List ℕ × List ℕ) : List ℕ := s.filter (fun f => !decide (f ∈ e.2)) ++ e.1

theorem nextL_eq (s : List ℕ) (e : List ℕ × List ℕ) :
    {f | f ∈ nextL s e} = Action.applyEff ({f | f ∈ e.1}, {f | f ∈ e.2}) {f | f ∈ s} := by
  ext f; simp [nextL, Action.applyEff]

/-- One step: the action `q.1` is applicable and `q.2` is one of its effects; apply it. -/
def wStep (p : FProbDesc) (s : Bool × List ℕ) (q : ℕ × (List ℕ × List ℕ)) : Bool × List ℕ :=
  (s.1 && ((actL p q.1).1.all fun f => decide (f ∈ s.2)) &&
    ((actL p q.1).2.1.all fun f => !decide (f ∈ s.2)) && decide (q.2 ∈ (actL p q.1).2.2),
   nextL s.2 q.2)

theorem foldl_wStep_false (p : FProbDesc) (l : List (ℕ × (List ℕ × List ℕ))) (s : List ℕ) :
    (l.foldl (wStep p) (false, s)).1 = false := by
  induction l generalizing s with
  | nil => rfl
  | cons q l ih => exact ih _

theorem wStep_true_iff (p : FProbDesc) (s : List ℕ) (a : ℕ) (e : List ℕ × List ℕ) :
    (wStep p (true, s) (a, e)).1 = true ↔
      (p.δ a).Applicable {f | f ∈ s} ∧ e ∈ (actL p a).2.2 := by
  rw [δ_eq_actL]
  simp [wStep, Action.Applicable, FActDesc.toAction, Set.subset_def, Set.disjoint_left,
    and_assoc]

theorem foldl_cons_iff (p : FProbDesc) (q : ℕ × (List ℕ × List ℕ))
    (l : List (ℕ × (List ℕ × List ℕ))) (s : List ℕ) :
    ((q :: l).foldl (wStep p) (true, s)).1 = true ↔
      (wStep p (true, s) q).1 = true ∧ (l.foldl (wStep p) (true, nextL s q.2)).1 = true := by
  rw [List.foldl_cons]
  have h2 : (wStep p (true, s) q).2 = nextL s q.2 := rfl
  generalize wStep p (true, s) q = w at h2 ⊢
  obtain ⟨b, t⟩ := w
  simp only at h2
  subst h2
  cases b <;> simp [foldl_wStep_false]

variable (p : FProbDesc) (g : ℕ → ℕ)

/-- An accepted list of (id, effect) pairs gives a weak execution. -/
theorem weakExec_of_foldl (c : List (ℕ × (List ℕ × List ℕ))) (s : List ℕ)
    (h : ((c.map fun q => (g q.1, q.2)).foldl (wStep p) (true, s)).1 = true) :
    p.toProblem.WeakExec ((c.map Prod.fst).map g) {f | f ∈ s} := by
  induction c generalizing s with
  | nil => trivial
  | cons q c ih =>
    rw [List.map_cons, foldl_cons_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨happ, he⟩ := (wStep_true_iff p s _ _).1 h1
    show (p.δ (g q.1)).Applicable _ ∧ ∃ s' ∈ (p.δ (g q.1)).outcomes _, _
    refine ⟨happ, {f | f ∈ nextL s q.2}, ?_, ih _ h2⟩
    rw [δ_eq_actL]
    exact ⟨_, ⟨q.2, he, rfl⟩, nextL_eq s q.2⟩

/-- A weak execution gives an accepted list of (id, effect) pairs. -/
theorem foldl_of_weakExec (l : List ℕ) (s : List ℕ)
    (h : p.toProblem.WeakExec (l.map g) {f | f ∈ s}) :
    ∃ c : List (ℕ × (List ℕ × List ℕ)), c.map Prod.fst = l ∧
      (∀ q ∈ c, q.2 ∈ (actL p (g q.1)).2.2) ∧
      ((c.map fun q => (g q.1, q.2)).foldl (wStep p) (true, s)).1 = true := by
  induction l generalizing s with
  | nil => exact ⟨[], rfl, by simp, rfl⟩
  | cons i l ih =>
    obtain ⟨happ, s', hs', hrest⟩ := h
    change (p.δ (g i)).Applicable _ at happ
    change s' ∈ (p.δ (g i)).outcomes _ at hs'
    rw [δ_eq_actL] at hs'
    obtain ⟨e, ⟨x, hx, rfl⟩, rfl⟩ := hs'
    rw [← nextL_eq] at hrest
    obtain ⟨c, hc1, hc2, hc3⟩ := ih _ hrest
    refine ⟨(i, x) :: c, by simp [hc1], ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hx
      · exact hc2 q hq
    · rw [List.map_cons, foldl_cons_iff]
      exact ⟨(wStep_true_iff p s _ _).2 ⟨happ, hx⟩, hc3⟩

/-! ## The certificate check -/

/-- A certificate: the linearisation, each task with its chosen effect. -/
abbrev WCert : Type := List (ℕ × (List ℕ × List ℕ))

/-- The action name of a task id of `tn_I`. -/
def actOfId (p : FProbDesc) (i : ℕ) : ℕ := (labelB p.tnI i).2

/-- **The certificate check** for weak LD solvability of primitive problems. -/
def weakCertB (x : FProbDesc × WCert) : Bool :=
  x.1.validB && noHTNB x.1.tnI && linB x.1.tnI (x.2.map Prod.fst) &&
    ((x.2.map fun q => (actOfId x.1 q.1, q.2)).foldl (wStep x.1) (true, x.1.init)).1

theorem actsOf_eq (p : FProbDesc) (l : List ℕ) : actsOf p.tnI l = l.map (actOfId p) := rfl

theorem isActionSeq_iff {t : TnDesc} (hprim : t.toTaskNetwork.IsPrimitive) {l : List ℕ}
    (hl : ∀ i ∈ l, i ∈ t.ids) {as : List ℕ} :
    t.toTaskNetwork.IsActionSeq l as ↔ as = actsOf t l := by
  have key : l.map t.toTaskNetwork.α = (actsOf t l).map Sum.inl := by
    rw [actsOf, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨a, ha⟩ := hprim i (by simpa [TnDesc.toTaskNetwork] using hl i hi)
    change t.label i = Sum.inl a at ha
    show t.label i = Sum.inl (labelB t i).2
    rw [ha]
    rw [label_eq] at ha
    split_ifs at ha with hb
    simp_all
  unfold TaskNetwork.IsActionSeq
  rw [key]
  exact ⟨fun h => (List.map_injective_iff.2 Sum.inl_injective h).symm, fun h => h ▸ rfl⟩

theorem prim_iff (p : FProbDesc) : FClass.PRIM p.toProblem ↔ p.tnI.toTaskNetwork.IsPrimitive :=
  Iff.rfl

/-- **Soundness and completeness of the certificate check.** -/
theorem iff_exists_cert (p : FProbDesc) :
    (p.Valid ∧ FClass.PRIM p.toProblem ∧ p.toProblem.WeakLDSolvable) ↔
      ∃ c, weakCertB (p, c) = true := by
  have htn : p.toProblem.tnI = p.tnI.toTaskNetwork := rfl
  simp only [weakCertB, Bool.and_eq_true, FProbDesc.validB_iff, noHTNB_iff, prim_iff]
  constructor
  · rintro ⟨hv, hprim, hs⟩
    rw [Problem.weakLDSolvable_iff_of_primitive _ hprim] at hs
    obtain ⟨l, as, hl, has, hex⟩ := hs
    rw [htn] at hl has
    rw [isActionSeq_iff hprim (fun i hi => by simpa [TnDesc.toTaskNetwork] using (hl.2.1 i).1 hi),
      actsOf_eq] at has
    subst has
    obtain ⟨c, hc1, -, hc3⟩ := foldl_of_weakExec p (actOfId p) l p.init hex
    refine ⟨c, ⟨⟨⟨hv, hprim⟩, ?_⟩, hc3⟩⟩
    rw [hc1]; exact (linB_iff hv.tnI l).2 hl
  · rintro ⟨c, ⟨⟨⟨hv, hprim⟩, hlin⟩, hex⟩⟩
    refine ⟨hv, hprim, ?_⟩
    rw [Problem.weakLDSolvable_iff_of_primitive _ hprim]
    have hl := (linB_iff hv.tnI _).1 hlin
    refine ⟨c.map Prod.fst, (c.map Prod.fst).map (actOfId p), hl, ?_,
      weakExec_of_foldl p (actOfId p) c p.init hex⟩
    rw [htn, isActionSeq_iff hprim (fun i hi => by
      simpa [TnDesc.toTaskNetwork] using (hl.2.1 i).1 hi)]
    rfl

/-! ## Polynomial time -/

theorem pt_actL : PT fun x : FProbDesc × ℕ => actL x.1 x.2 := by
  unfold actL
  exact PT.headI (PT.append (PT.map (g := fun _ (y : FActDesc) => y.2)
    (PT.filter (p := fun (x : FProbDesc × ℕ) (y : FActDesc) => y.name == x.2)
      (PT.fst.comp (PT.fst.comp PT.fst)) (PT.beq (PT.fst.comp PT.snd) (PT.snd.comp PT.fst)))
    (PT.snd.comp PT.snd)) (PT.const _))

theorem pt_wStep :
    PT fun q : FProbDesc × (Bool × List ℕ) × (ℕ × (List ℕ × List ℕ)) => wStep q.1 q.2.1 q.2.2 := by
  unfold wStep nextL
  have hL : PT fun q : FProbDesc × (Bool × List ℕ) × (ℕ × (List ℕ × List ℕ)) =>
      actL q.1 q.2.2.1 := pt_actL.comp (PT.pair PT.fst (PT.fst.comp (PT.snd.comp PT.snd)))
  have hs : PT fun q : FProbDesc × (Bool × List ℕ) × (ℕ × (List ℕ × List ℕ)) => q.2.1.2 :=
    PT.snd.comp (PT.fst.comp PT.snd)
  have he : PT fun q : FProbDesc × (Bool × List ℕ) × (ℕ × (List ℕ × List ℕ)) => q.2.2.2 :=
    PT.snd.comp (PT.snd.comp PT.snd)
  exact PT.pair (PT.and (PT.and (PT.and (PT.fst.comp (PT.fst.comp PT.snd))
      (PT.all (PT.fst.comp hL) (PT.elem (hs.comp PT.fst) PT.snd)))
      (PT.all (PT.fst.comp (PT.snd.comp hL)) (PT.not (PT.elem (hs.comp PT.fst) PT.snd))))
      ((PT.elem (PT.snd.comp (PT.snd.comp hL)) he).of_eq fun _ => by congr))
    (PT.append (PT.filter hs (PT.not (PT.elem (PT.snd.comp (he.comp PT.fst)) PT.snd)))
      (PT.fst.comp he))

theorem sz_wStep_le (p : FProbDesc) (s : Bool × List ℕ) (q : ℕ × (List ℕ × List ℕ)) :
    sz (wStep p s q) ≤ sz s + sz q.2.1 := by
  unfold wStep nextL
  rw [sz_prod, sz_prod, sz_bool, sz_bool]
  have h1 := sz_append_le (s.2.filter fun f => !decide (f ∈ q.2.2)) q.2.1
  have h2 := sz_filter_le s.2 (fun f => !decide (f ∈ q.2.2))
  omega

theorem pt_actOfId : PT fun x : FProbDesc × ℕ => actOfId x.1 x.2 :=
  PT.snd.comp (pt_labelB.comp (PT.pair (PT.snd.comp (PT.snd.comp PT.fst)) PT.snd))

theorem pt_weakCertB : PT weakCertB := by
  unfold weakCertB
  have hp : PT fun x : FProbDesc × WCert => x.1 := PT.fst
  have htn : PT fun x : FProbDesc × WCert => x.1.tnI := PT.snd.comp (PT.snd.comp hp)
  have hl : PT fun x : FProbDesc × WCert => x.2.map fun q => (actOfId x.1 q.1, q.2) :=
    PT.map PT.snd (PT.pair (pt_actOfId.comp (PT.pair (PT.fst.comp PT.fst) (PT.fst.comp PT.snd)))
      (PT.snd.comp PT.snd))
  have hf : PT fun x : FProbDesc × WCert =>
      (x.2.map fun q => (actOfId x.1 q.1, q.2)).foldl (wStep x.1) (true, x.1.init) := by
    refine PT.foldl (α := FProbDesc × WCert) (β := ℕ × (List ℕ × List ℕ)) (σ := Bool × List ℕ)
      (g := fun x s q => wStep x.1 s q) hl
      (PT.pair (PT.const true) (PT.fst.comp (PT.snd.comp hp)))
      (pt_wStep.comp (PT.pair (PT.fst.comp PT.fst) PT.snd)) (c := 1) (d := 1) ?_
    intro x s q hq
    have h1 := sz_wStep_le x.1 s q
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
    have h2 : sz r.2.1 ≤ sz x := by
      have := sz_fst_le r.2
      have := sz_snd_le r
      have := sz_le_of_mem hr
      have := sz_snd_le x
      omega
    simp only [pow_one, one_mul] at h1 ⊢
    omega
  exact PT.and (PT.and (PT.and (FProbDesc.pt_validB.comp hp) (pt_noHTNB.comp htn))
    (pt_linB.comp (PT.pair htn (PT.map (g := fun _ (q : ℕ × (List ℕ × List ℕ)) => q.1) PT.snd (PT.fst.comp PT.snd))))) (PT.fst.comp hf)

/-! ## The size of a certificate -/

theorem sz_list_le {β : Type} [BEnc β] (l : List β) (B : ℕ) (h : ∀ b ∈ l, sz b ≤ B) :
    sz l ≤ l.length * (2 * B + 2) + 1 := by
  induction l with
  | nil => simp [sz_nil]
  | cons b l ih =>
    rw [sz_cons, List.length_cons]
    have := h b List.mem_cons_self
    have := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    nlinarith

theorem sz_eff_le (p : FProbDesc) (a : ℕ) {e : List ℕ × List ℕ} (he : e ∈ (actL p a).2.2) :
    sz e ≤ sz p + 5 := by
  unfold actL at he
  have hmem : ((p.actions.filter fun x => x.name == a).map Prod.snd ++ [defAct]).headI ∈
      (p.actions.filter fun x => x.name == a).map Prod.snd ++ [defAct] := by
    cases h : (p.actions.filter fun x => x.name == a).map Prod.snd with
    | nil => simp
    | cons y l => simp
  rcases List.mem_append.1 hmem with h | h
  · obtain ⟨x, hx, hxe⟩ := List.mem_map.1 h
    have hx' := (List.mem_filter.1 hx).1
    rw [← hxe] at he
    have := sz_le_of_mem he
    have := sz_snd_le x.2.2
    have := sz_snd_le x.2
    have := sz_snd_le x
    have := sz_le_of_mem hx'
    have := sz_fst_le p.1
    have := sz_fst_le p
    simp only [FProbDesc.actions] at *
    omega
  · rw [List.mem_singleton.1 h] at he
    simp only [defAct, List.mem_singleton] at he
    subst he
    have : sz (([], []) : List ℕ × List ℕ) = 2 := rfl
    omega

theorem sz_ids_le (p : FProbDesc) : sz p.tnI.ids ≤ sz p := by
  have := sz_fst_le p.tnI
  have := sz_snd_le p.2
  have := sz_snd_le p
  simp only [FProbDesc.tnI, TnDesc.ids] at *
  omega

theorem one_le_sz_list {β : Type} [BEnc β] (l : List β) : 1 ≤ sz l := by
  cases l with
  | nil => simp [sz_nil]
  | cons b l => rw [sz_cons]; omega

theorem six_le_sz (p : FProbDesc) : 6 ≤ sz p := by
  obtain ⟨⟨a, m⟩, i, ids, o, lb⟩ := p
  simp only [sz_prod]
  have := one_le_sz_list a
  have := one_le_sz_list m
  have := one_le_sz_list i
  have := one_le_sz_list ids
  have := one_le_sz_list o
  have := one_le_sz_list lb
  omega

/-- A short accepted certificate exists whenever some certificate is accepted. -/
theorem exists_short_cert (p : FProbDesc) (h : ∃ c, weakCertB (p, c) = true) :
    ∃ c : WCert, (enc c).length ≤ ((enc p).length + 1) ^ 4 ∧ weakCertB (p, c) = true := by
  rw [← iff_exists_cert] at h
  obtain ⟨hv, hprim, hs⟩ := h
  have htn : p.toProblem.tnI = p.tnI.toTaskNetwork := rfl
  rw [Problem.weakLDSolvable_iff_of_primitive _ hprim] at hs
  obtain ⟨l, as, hl, has, hex⟩ := hs
  rw [htn] at hl has
  rw [isActionSeq_iff hprim (fun i hi => by simpa [TnDesc.toTaskNetwork] using (hl.2.1 i).1 hi),
    actsOf_eq] at has
  subst has
  obtain ⟨c, hc1, hc2, hc3⟩ := foldl_of_weakExec p (actOfId p) l p.init hex
  refine ⟨c, ?_, ?_⟩
  · have hperm : l.Perm p.tnI.ids := (List.perm_ext_iff_of_nodup hl.1 hv.tnI.nodup).2
      fun x => (hl.2.1 x).trans (by simp [TnDesc.toTaskNetwork])
    have hlen : c.length ≤ sz p := by
      have : c.length = l.length := by rw [← hc1, List.length_map]
      rw [this]
      exact (length_le_sz l).trans (by rw [sz_perm hperm]; exact sz_ids_le p)
    have hB : ∀ q ∈ c, sz q ≤ 2 * sz p + 5 := by
      intro q hq
      have h1 : sz q.1 ≤ sz p := by
        have : q.1 ∈ l := hc1 ▸ List.mem_map_of_mem hq
        exact (sz_le_of_mem this).trans (by rw [sz_perm hperm]; exact sz_ids_le p)
      have h2 := sz_eff_le p _ (hc2 q hq)
      obtain ⟨i, e⟩ := q
      rw [sz_prod]
      simp only at h1 h2
      omega
    have hc := sz_list_le c _ hB
    have hn := six_le_sz p
    have h1 : (enc c).length = sz c := rfl
    have h2 : (enc p).length = sz p := rfl
    rw [h1, h2]
    have hm : c.length * (2 * (2 * sz p + 5) + 2) ≤ sz p * (2 * (2 * sz p + 5) + 2) :=
      Nat.mul_le_mul_right _ hlen
    have h25 : 25 ≤ (sz p + 1) ^ 2 := by nlinarith
    calc sz c ≤ sz p * (2 * (2 * sz p + 5) + 2) + 1 := by omega
      _ ≤ 25 * (sz p + 1) ^ 2 := by nlinarith
      _ ≤ (sz p + 1) ^ 2 * (sz p + 1) ^ 2 := Nat.mul_le_mul_right _ h25
      _ = (sz p + 1) ^ 4 := by ring
  · simp only [weakCertB, Bool.and_eq_true, FProbDesc.validB_iff, noHTNB_iff]
    refine ⟨⟨⟨hv, hprim⟩, ?_⟩, hc3⟩
    rw [hc1]; exact (linB_iff hv.tnI l).2 hl

end Prim

open Prim in
/-- **[CB21, Cor. 4.2], membership**: weak LD plan existence of primitive problems is in NP. -/
theorem weakLD_PRIM_mem : Cx.NP (PlanExFM .weakLD FClass.PRIM) :=
  inNP_codeLang (α := FProbDesc) (β := WCert)
    (Q := fun p => p.Valid ∧ FClass.PRIM p.toProblem ∧ FMCrit.Solvable .weakLD p.toProblem)
    pt_weakCertB 4 fun p => by
      show (p.Valid ∧ FClass.PRIM p.toProblem ∧ p.toProblem.WeakLDSolvable) ↔ _
      rw [Prim.iff_exists_cert]
      exact ⟨exists_short_cert p, fun ⟨c, _, hc⟩ => ⟨c, hc⟩⟩

/-- **[CB21, Cor. 4.2], membership, OD**: weak OD plan existence of primitive problems is in
NP. -/
theorem weakOD_PRIM_mem : Cx.NP (PlanExFM .weakOD FClass.PRIM) := by
  rw [planExFM_weakOD_eq]; exact weakLD_PRIM_mem

end FOND
