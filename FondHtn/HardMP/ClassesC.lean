import FondHtn.HardMP.DescC
import FondHtn.HardMP.Classes
import FondHtn.HardMP.PT
/-!
# Validity, classes, polynomial time and a frame property for the counter construction

* `FOND.HardMP.descC_valid`, `FOND.HardMP.descC_REG`, `FOND.HardMP.descC_TO`,
  `FOND.HardMP.pt_descC`;
* `FOND.HardMP.frame_prgs`: no program of `prgs p` writes a counter bit.
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn HTN.Syn.PolyDom PTime

/-! ## Specifications -/

theorem goodIns_inc (p : ProbDesc) : GoodIns (incI p) := by
  simp only [GoodIns, incI, List.mem_map]
  rintro a ⟨i, -, rfl⟩
  simp [ASpec.WF, ASpec.cnew, ASpec.effs]

theorem prgsC_good (p : ProbDesc) : ∀ P ∈ prgsC p, ∀ ins ∈ P, GoodIns ins := by
  intro P hP ins hins
  rcases List.mem_cons.1 hP with rfl | hP
  · exact prgs_good p _ (List.mem_cons_self ..) _ hins
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hP
    rcases List.mem_cons.1 hins with rfl | hins
    · exact goodIns_inc p
    · exact prgs_good p _ (List.mem_cons_of_mem _ hr) _ hins

theorem prgsC_spec (p : ProbDesc) : ∀ P ∈ prgsC p, ∀ ins ∈ P, ∀ a ∈ ins, a.WF ∧ a.effs ≠ [] :=
  prgsC_good p

/-! ## Validity and classes -/

theorem descC_valid (p : ProbDesc) : (descC p).Valid where
  names_nodup := names_nodup_acts _
  effs_ne := effs_ne_acts (prgsC_good p)
  tnI := tnValid_of_methOK (e := meth 0 [(true, cN 0 0)]) (P := prgsC p) rfl
    ⟨_, _, rfl, fun q hq hf => by simp at hq; rw [hq] at hf; simp at hf⟩
  methods := by
    intro e he
    refine tnValid_of_methOK (P := prgsC p) rfl ?_
    simp only [descC, FProbDesc.methods, List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | rfl
    · exact methOK_chain (by simp) he
    · exact methOK_round he
    · exact methOK_fin

theorem seqMeths_descC (p : ProbDesc) : SeqMeths (descC p) := by
  intro e he
  simp only [descC, FProbDesc.methods, List.mem_append, List.mem_singleton] at he
  rcases he with (he | he) | rfl
  · obtain ⟨c, b, h, -⟩ := methOK_chain (by simp) he; exact ⟨c, b, h⟩
  · obtain ⟨c, b, h, -⟩ := methOK_round (P := prgsC p) he; exact ⟨c, b, h⟩
  · exact ⟨_, _, rfl⟩

theorem descC_TO (p : ProbDesc) : FClass.TO (descC p).toProblem := to_of_seq (seqMeths_descC p) rfl

theorem descC_REG (p : ProbDesc) : FClass.REG (descC p).toProblem := by
  intro m hm
  obtain ⟨⟨e, he, rfl⟩, -⟩ := hm
  suffices ∃ c body, e = meth c body ∧ RegBody body by
    obtain ⟨c, body, rfl, hb⟩ := this
    exact seqTn_regular hb
  simp only [descC, FProbDesc.methods, List.mem_append, List.mem_singleton] at he
  rcases he with (he | he) | rfl
  · rcases mem_chainMeths.1 he with ⟨t, -, rfl⟩ | ⟨r, -, rfl⟩
    · exact ⟨_, _, rfl, regBody_two _ _⟩
    · exact ⟨_, _, rfl, regBody_one _ _⟩
  · simp only [roundMeths, List.mem_map] at he
    obtain ⟨r, -, rfl⟩ := he
    exact ⟨_, _, rfl, regBody_one _ _⟩
  · exact ⟨_, _, rfl, regBody_one _ _⟩

/-! ## Polynomial time -/

theorem pt_cslot : PT cslot :=
  (PT.add (PT.length (PT.flatMap (g := fun _ x => x) pt_rules PT.snd)) (PT.const 3)).of_eq
    fun _ => rfl

theorem pt_rangeNc : PT fun p : ProbDesc => List.range (Nc p) := by
  have h := PT.rangeLength (PT.append (PT.append (PT.append (PT.append pt_pfacts pt_pfacts) pt_numsOf)
    pt_numsOf) (PT.const [0, 0, 0]))
  exact h.of_eq fun p => by simp [Nc, Nclk]; ring_nf

theorem incI_eq (p : ProbDesc) : incI p = (List.range (Nc p)).map fun i =>
    ((((List.range (Nc p)).filter fun j => decide (j < i))).map (fSlot (cslot p)),
      [fSlot (cslot p) i],
      [([fSlot (cslot p) i], ((List.range (Nc p)).filter fun j => decide (j < i)).map
        (fSlot (cslot p)))], ([] : List (Option (Bool × ℕ))), ([] : List (Option (Bool × ℕ)))) := by
  unfold incI
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have : (List.range (Nc p)).filter (fun j => decide (j < i)) = List.range i := by
    rw [show Nc p = i + (Nc p - i) by omega, List.range_add, List.filter_append]
    rw [List.filter_eq_self.2 (fun j hj => by simpa using hj),
      List.filter_eq_nil_iff.2 (fun j hj => by simp at hj; simp; omega), List.append_nil]
  rw [this]

theorem pt_incI : PT incI := by
  rw [show incI = fun p => _ from funext incI_eq]
  have hR := pt_rangeNc
  have hF : PT fun q : ProbDesc × ℕ => ((List.range (Nc q.1)).filter fun j => decide (j < q.2)).map
      (fSlot (cslot q.1)) :=
    PT.map (PT.filter (hR.comp PT.fst) (PT.lt PT.snd (PT.snd.comp PT.fst)))
      (pt_fSlot (pt_cslot.comp (PT.fst.comp PT.fst)) PT.snd)
  have hS : PT fun q : ProbDesc × ℕ => fSlot (cslot q.1) q.2 := pt_fSlot (pt_cslot.comp PT.fst) PT.snd
  exact PT.map hR (PT.pair hF (PT.pair (PT.single hS) (PT.pair
    (PT.single (PT.pair (PT.single hS) hF)) (PT.pair PT.nil PT.nil))))

theorem pt_prgsC : PT prgsC :=
  PT.cons pt_progInit (PT.map pt_rules (PT.cons (pt_incI.comp PT.fst) PT.snd))

/-- **The counter description is computed in polynomial time.** -/
theorem pt_descC : PT descC := by
  unfold descC
  exact PT.pair (PT.pair (pt_acts pt_prgsC) (PT.append (PT.append
    (pt_chainMeths pt_prgsC (PT.const _)) (pt_roundMeths pt_prgsC)) (PT.const _)))
    (PT.pair pt_initFacts (PT.const _))

/-! ## Frame: the programs of `prgs p` do not write counter bits -/

/-- The fields written by an instruction satisfy `S`. -/
def EffIn (S : ℕ → Prop) (ins : List ASpec) : Prop :=
  ∀ a ∈ ins, ∀ e ∈ a.effs, ∀ f, (f ∈ e.1 ∨ f ∈ e.2) → S f

/-- Fields below slot `K`. -/
def LowF (K : ℕ) (f : ℕ) : Prop := f = fDone ∨ (∃ i, f = fSel i) ∨ ∃ k j, k < K ∧ f = fSlot k j

theorem effIn_chk {S : ℕ → Prop} (pre neg : List ℕ) (cpre : List (Option (Bool × ℕ))) :
    EffIn S (chkI pre neg cpre) := by
  simp [EffIn, chkI, ASpec.effs, noeff]

theorem effIn_eq {S : ℕ → Prop} (f g : ℕ) : EffIn S (eqI f g) := by
  simp [EffIn, eqI, ASpec.effs, noeff]

theorem effIn_guess {S : ℕ → Prop} {f : ℕ} (h : S f) : EffIn S (guessI f) := by
  simp only [EffIn, guessI, ASpec.effs, List.mem_cons, List.not_mem_nil, or_false]
  rintro a (rfl | rfl) e he x hx <;> simp at he <;> subst he <;> simp at hx <;> subst hx <;> exact h

theorem effIn_ccp {S : ℕ → Prop} (s f : ℕ) {g : ℕ} (h : S g) : EffIn S (ccpI s f g) := by
  simp only [EffIn, ccpI, ASpec.effs, noeff, List.mem_cons, List.not_mem_nil, or_false]
  rintro a (rfl | rfl | rfl) e he x hx <;> simp at he <;> subst he <;> simp at hx <;> subst hx <;>
    exact h

theorem effIn_ccur {S : ℕ → Prop} (s : ℕ) (h y : Option (Bool × ℕ)) : EffIn S (ccurI s h y) := by
  simp [EffIn, ccurI, ASpec.effs, noeff]

theorem effIn_set {S : ℕ → Prop} {d : ℕ} (h : S d) : EffIn S (setI d) := by
  simp only [EffIn, setI, ASpec.effs, List.mem_singleton]
  rintro a rfl e he x hx; simp at he; subst he; simp at hx; subst hx; exact h

theorem effIn_pick {K : ℕ} (k : ℕ) : EffIn (LowF K) (pickI fSel k) := by
  simp only [EffIn, pickI, ASpec.effs, List.mem_singleton]
  rintro a rfl e he x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  simp only [List.mem_singleton, List.mem_map, List.mem_range] at hx
  rcases hx with rfl | ⟨i', -, rfl⟩
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inl ⟨i', rfl⟩)

theorem effIn_bit {S : ℕ → Prop} (V : List ℕ) (act : ActDesc) (j : ℕ) : EffIn S (bitI V act j) := by
  unfold bitI
  cases decide (V.getI j ∈ act.2.2.2.1)
  · cases decide (V.getI j ∈ act.2.2.2.2)
    · exact effIn_eq _ _
    · exact effIn_chk _ _ _
  · exact effIn_chk _ _ _

theorem effIn_chkA {K : ℕ} (V : List ℕ) (act : ActDesc) (a : ℕ) : EffIn (LowF K) (chkA V act a) := by
  unfold chkA
  cases act.2.1.all (fun f => decide (f ∈ V))
  · simp [EffIn]
  · simp only [cond_true, EffIn, ASpec.effs, List.mem_singleton]
    rintro b rfl e he x hx; simp at he; subst he; simp at hx; subst hx; exact Or.inl rfl

theorem effIn_goal {S : ℕ → Prop} (p : ProbDesc) : EffIn S (goalI p) := by
  unfold goalI
  cases p.goalPos.all (fun f => decide (f ∈ pfacts p))
  · simp [EffIn]
  · exact effIn_chk _ _ _

theorem progM_effIn (n : ℕ) (h : Option (Bool × ℕ)) (bs : List (Bool × ℕ)) :
    ∀ ins ∈ progM n h bs, EffIn (LowF (bs.length + 3)) ins := by
  intro ins hins
  unfold progM at hins
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hins
  rcases hins with (((rfl | ⟨f, hf, rfl⟩) | ⟨q, -, rfl⟩) | ⟨q, -, rfl⟩) | hins
  · exact effIn_chk _ _ _
  · obtain ⟨k, hk, j, -, rfl⟩ := mem_slotFields.1 hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
    exact effIn_guess (Or.inr (Or.inr ⟨_, j, by simp at hi; omega, rfl⟩))
  · exact effIn_eq _ _
  · exact effIn_eq _ _
  · rcases bs with _ | ⟨b, bs⟩
    · simp only [List.isEmpty_nil, cond_true, List.mem_singleton] at hins
      subst hins; exact effIn_set (Or.inl rfl)
    · simp only [List.isEmpty_cons, cond_false, List.mem_append, List.mem_singleton,
        List.mem_flatMap, List.mem_map] at hins
      rcases hins with (rfl | ⟨i, -, q, hq, rfl⟩) | ⟨i, -, rfl⟩
      · exact effIn_pick _
      · refine effIn_ccp _ _ ?_
        rcases List.mem_append.1 hq with hq | hq <;> obtain ⟨j, -, rfl⟩ := mem_cpPairs.1 hq
        · exact Or.inr (Or.inr ⟨0, j, by omega, rfl⟩)
        · exact Or.inr (Or.inr ⟨1, j, by omega, rfl⟩)
      · exact effIn_ccur _ _ _

theorem length_progM (n : ℕ) (h : Option (Bool × ℕ)) (bs : List (Bool × ℕ)) :
    bs.length + 2 ≤ (progM n h bs).length := by
  unfold progM
  rcases bs with _ | ⟨b, bs⟩
  · simp; omega
  · simp only [List.isEmpty_cons, cond_false, List.length_append, List.length_cons,
      List.length_nil, List.length_map, List.length_range]
    omega

theorem LowF.mono {K K' : ℕ} (h : K ≤ K') {f : ℕ} (hf : LowF K f) : LowF K' f := by
  rcases hf with hf | hf | ⟨k, j, hk, rfl⟩
  · exact Or.inl hf
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr ⟨k, j, by omega, rfl⟩)

theorem effIn_mono {S S' : ℕ → Prop} (h : ∀ f, S f → S' f) {ins : List ASpec} (hi : EffIn S ins) :
    EffIn S' ins := fun a ha e he f hf => h f (hi a ha e he f hf)

theorem prgs_effIn (p : ProbDesc) : ∀ r ∈ prgs p, ∀ ins ∈ r, EffIn (LowF (cslot p)) ins := by
  intro P hP ins hins
  have hlen : ∀ r ∈ rules p, r.length ≤ ((rules p).flatMap id).length := by
    intro r hr
    rw [List.flatMap_id, List.length_flatten]
    exact List.le_sum_of_mem (List.mem_map.2 ⟨r, hr, rfl⟩)
  have hM : ∀ {n h bs}, progM n h bs ∈ rules p → ∀ ins ∈ progM n h bs,
      EffIn (LowF (cslot p)) ins := by
    intro n h bs hr ins hins
    refine effIn_mono (fun f hf => LowF.mono ?_ hf) (progM_effIn n h bs ins hins)
    have := (length_progM n h bs).trans (hlen _ hr)
    unfold cslot; omega
  rcases List.mem_cons.1 hP with rfl | hP
  · unfold progInit at hins
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hins
    rcases hins with ⟨f, hf, rfl⟩ | rfl
    · obtain ⟨j, -, rfl⟩ := hf
      exact effIn_guess (Or.inr (Or.inr ⟨1, j, by unfold cslot; omega, rfl⟩))
    · exact effIn_goal _
  · have hPr := hP
    unfold rules at hP
    rcases List.mem_append.1 hP with hP | hP
    · rcases List.mem_append.1 hP with hP | hP
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
        rcases hP with rfl | rfl
        · simp only [progNoop, List.mem_singleton] at hins
          subst hins; exact effIn_chk _ _ _
        · exact hM hPr ins hins
      · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hP
        exact hM hPr ins hins
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hP
      unfold progA at hins
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hins
      rcases hins with ⟨j, -, rfl⟩ | rfl
      · exact effIn_bit _ _ _
      · exact effIn_chkA _ _ _

/-- **Frame**: no program of `prgs p` writes a counter bit. -/
theorem frame_prgs (p : ProbDesc) : ∀ r ∈ prgs p, ∀ ins ∈ r, ∀ a ∈ ins, ∀ e ∈ a.effs, ∀ j,
    fSlot (cslot p) j ∉ e.1 ∧ fSlot (cslot p) j ∉ e.2 := by
  intro r hr ins hins a ha e he j
  have key : ∀ f, (f ∈ e.1 ∨ f ∈ e.2) → f ≠ fSlot (cslot p) j := by
    intro f hf h
    subst h
    rcases prgs_effIn p r hr ins hins a ha e he _ hf with h | ⟨i, h⟩ | ⟨k, j', hk, h⟩
    · exact fSlot_ne_fDone _ _ h
    · exact fSlot_ne_fSel _ _ _ h
    · rw [fSlot_inj] at h; omega
  exact ⟨fun h => key _ (Or.inl h) rfl, fun h => key _ (Or.inr h) rfl⟩

end HardMP

end FOND
