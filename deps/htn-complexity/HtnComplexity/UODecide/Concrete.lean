import HtnComplexity.UODecide.Abstract
import HtnComplexity.Computable.RegDecide
import HtnComplexity.SynClasses.UOHD
/-!
# The decision procedure for unordered HTN planning

For an unordered description (`DomDesc.MethodsUO`, `InstDesc.IsUO`) the search network of
`HtnComplexity/Computable/PoSearch.lean` never acquires an ordering constraint, so a search
configuration is determined, up to the identities of its tasks, by the current state and the
multiset of labels of its open tasks.  This file

* instantiates the abstract unordered problem of `HtnComplexity/UODecide/Abstract.lean`
  (`HTN.Syn.uoSys`) and proves that the abstraction map `HTN.Syn.uoAbs` is a bisimulation
  between the search and the abstract system;
* transfers the small-solution theorem `HTN.UOAbs.short_run`; and
* concludes that the bounded search `HTN.Syn.uoSolvableB` — the breadth-first search of the
  progression space for `HTN.Syn.uoBnd d q` rounds — **decides plan existence for `UO-HTN`**
  (`HTN.Syn.uoSolvableB_iff`).
-/

namespace HTN

namespace Syn

open UOAbs

/-! ### The abstract system of a description -/

/-- The abstract unordered problem of a domain and instance description. -/
def uoSys (d : DomDesc) (q : InstDesc) : Sys where
  meth c β := ∃ e ∈ d.methods, e.1 = c ∧ β = ((e.2.ids.dedup.map e.2.lblPair : List _) : Multiset _)
  app s a := ∀ f ∈ (actOf d a).1, f ∈ s
  nxt s a := s.filter (fun f => f ∉ (actOf d a).2.2) ∪ (actOf d a).2.1.toFinset
  goal s := ∀ f ∈ q.goalList, f ∈ s

/-- The multiset of labels of the open tasks of a search network. -/
def flagLbls (p : PNet) : Multiset (Bool × ℕ) :=
  (((p.filter (fun x => x.2.2.1)).map (fun x => x.2.1) : List _) : Multiset _)

/-- **The abstraction of a search configuration.** -/
def uoAbs (c : PConfig) : Cfg := (c.1.toFinset, flagLbls c.2)

/-- The invariant of the search on an unordered description: no ordering constraints. -/
def UOInv (c : PConfig) : Prop := PNet.Ok c.2 ∧ ∀ x ∈ c.2, x.2.2.2 = []

/-! ### Labels of open tasks -/

theorem flagLbls_filter_ne {p : PNet} (hnd : p.allIds.Nodup) {x : PItem} (hx : x ∈ p)
    (hfl : x.2.2.1 = true) :
    ((((p.filter (fun y => y.2.2.1 && decide (y.1 ≠ x.1))).map (fun y => y.2.1)) : List _) :
      Multiset _) = (flagLbls p).erase x.2.1 := by
  induction p with
  | nil => simp at hx
  | cons y ys ih =>
    have hnd0 : (y.1 :: PNet.allIds ys).Nodup := hnd
    have hy : y.1 ∉ PNet.allIds ys := (List.nodup_cons.1 hnd0).1
    have hnd' : (PNet.allIds ys).Nodup := (List.nodup_cons.1 hnd0).2
    have hall : ∀ z ∈ ys, z.1 ≠ y.1 := fun z hz he => hy (he ▸ List.mem_map_of_mem hz)
    rcases List.mem_cons.1 hx with rfl | hxs
    · -- the item itself
      have hfil : (ys.filter (fun z => z.2.2.1 && decide (z.1 ≠ x.1))) =
          ys.filter (fun z => z.2.2.1) := by
        refine List.filter_congr fun z hz => ?_
        simp [hall z hz]
      simp only [List.filter_cons, hfl, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, hfil, flagLbls, List.map_cons, ← Multiset.cons_coe,
        Multiset.erase_cons_head]
    · have hne : y.1 ≠ x.1 := fun he => hy (he ▸ List.mem_map_of_mem hxs)
      have ih' := ih hnd' hxs
      by_cases hyf : y.2.2.1 = true
      · simp only [List.filter_cons, hyf, ne_eq, hne, not_false_eq_true, decide_true,
          Bool.and_self, ↓reduceIte, List.map_cons, ← Multiset.cons_coe, flagLbls] at ih' ⊢
        rw [ih']
        by_cases hl : y.2.1 = x.2.1
        · rw [hl, Multiset.erase_cons_head, Multiset.cons_erase]
          simp only [Multiset.mem_coe, List.mem_map, List.mem_filter]
          exact ⟨x, ⟨hxs, hfl⟩, rfl⟩
        · rw [Multiset.erase_cons_tail _ hl]
      · simp only [List.filter_cons, hyf, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          flagLbls] at ih' ⊢
        exact ih'

theorem flagLbls_map_clear (p : PNet) (i : ℕ) (g : PItem → PItem)
    (hg : ∀ y, (g y).2.1 = y.2.1 ∧ (g y).2.2.1 = (y.2.2.1 && decide (y.1 ≠ i))) :
    flagLbls (p.map g) =
      (((p.filter (fun y => y.2.2.1 && decide (y.1 ≠ i))).map (fun y => y.2.1) : List _) :
        Multiset _) := by
  induction p with
  | nil => rfl
  | cons y ys ih =>
    simp only [flagLbls, List.map_cons, List.filter_cons, (hg y).2] at ih ⊢
    split_ifs with h
    · simp only [List.map_cons, ← Multiset.cons_coe, (hg y).1, ih]
    · exact ih

theorem flagLbls_append (p p' : PNet) : flagLbls (p ++ p') = flagLbls p + flagLbls p' := by
  simp [flagLbls, List.filter_append]

theorem mem_flagLbls {p : PNet} {b : Bool × ℕ} :
    b ∈ flagLbls p ↔ ∃ x ∈ p, x.2.2.1 = true ∧ x.2.1 = b := by
  simp [flagLbls, List.mem_filter, and_assoc]

theorem flagLbls_finish {p : PNet} (hnd : p.allIds.Nodup) {x : PItem} (hx : x ∈ p)
    (hfl : x.2.2.1 = true) : flagLbls (p.finish x.1) = (flagLbls p).erase x.2.1 := by
  rw [← flagLbls_filter_ne hnd hx hfl]
  refine flagLbls_map_clear p x.1 _ fun y => ?_
  by_cases h : y.1 = x.1 <;> simp [h]

theorem flagLbls_oldItems {p : PNet} (hnd : p.allIds.Nodup) {x : PItem} (hx : x ∈ p)
    (hfl : x.2.2.1 = true) (e : MethodDesc) :
    flagLbls (p.oldItems x.1 e) = (flagLbls p).erase x.2.1 := by
  rw [← flagLbls_filter_ne hnd hx hfl]
  refine flagLbls_map_clear p x.1 _ fun y => ?_
  by_cases h : y.1 = x.1 <;> simp [h]

theorem flagLbls_newItems (p : PNet) (i : ℕ) (e : MethodDesc) :
    flagLbls (p.newItems i e) = ((e.2.ids.dedup.map e.2.lblPair : List _) : Multiset _) := by
  simp [flagLbls, PNet.newItems, List.filter_map, Function.comp_def, List.map_map]

theorem flagLbls_expand {p : PNet} (hnd : p.allIds.Nodup) {x : PItem} (hx : x ∈ p)
    (hfl : x.2.2.1 = true) (e : MethodDesc) :
    flagLbls (p.expand x.1 e) =
      (flagLbls p).erase x.2.1 + ((e.2.ids.dedup.map e.2.lblPair : List _) : Multiset _) := by
  rw [PNet.expand, flagLbls_append, flagLbls_oldItems hnd hx hfl, flagLbls_newItems]

theorem ids_isEmpty_iff (p : PNet) : p.ids.isEmpty = true ↔ flagLbls p = 0 := by
  simp [PNet.ids, flagLbls, List.isEmpty_iff]

theorem toFinset_stepL (d : DomDesc) (l : List ℕ) (a : ℕ) :
    (stepL d l a).toFinset =
      l.toFinset.filter (fun f => f ∉ (actOf d a).2.2) ∪ (actOf d a).2.1.toFinset := by
  ext f
  simp [stepL]

theorem applB_iff_forall {d : DomDesc} {l : List ℕ} {a : ℕ} :
    applB d l a = true ↔ ∀ f ∈ (actOf d a).1, f ∈ l := by
  rw [applB_iff]
  simp only [ActionModel.Applicable, DomDesc.toDomain_prec, prec_eq_actOf]
  exact Iff.rfl

/-! ### The invariant -/

theorem deps_eq_nil_of_all {p : PNet} (h : ∀ x ∈ p, x.2.2.2 = []) (i : ℕ) : p.deps i = [] := by
  induction p with
  | nil => rfl
  | cons y ys ih =>
    simp only [PNet.deps, List.foldr_cons]
    split_ifs
    · exact h y List.mem_cons_self
    · exact ih fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem filter_ordB_eq_nil {t : TnDesc} (ht : t.toTaskNetwork.IsUnordered) {z : ℕ}
    (hz : z ∈ t.ids) : t.ids.dedup.filter (fun y => t.ordB y z) = [] := by
  rw [List.filter_eq_nil_iff]
  intro y hy hord
  exact ht y (by simpa using hy) z (by simpa using hz) (TnDesc.ordB_iff.1 hord)

theorem uoInv_initConfig {q : InstDesc} (hq : q.IsUO) : UOInv (initConfig q) := by
  refine ⟨ok_initConfig q, ?_⟩
  intro x hx
  simp only [initConfig, PNet.ofTnDesc, List.mem_map] at hx
  obtain ⟨z, -, rfl⟩ := hx
  show q.tnI.ids.dedup.filter (fun y => q.tnI.ordB y z) = []
  by_cases hz : z ∈ q.tnI.ids
  · exact filter_ordB_eq_nil hq hz
  · rw [List.filter_eq_nil_iff]
    intro y hy hord
    exact hz (TnDesc.ordB_iff.1 hord).2.1

theorem uoInv_step {d : DomDesc} (hd : d.MethodsUO) {c c' : PConfig} (hc : UOInv c)
    (h : PStep d c c') : UOInv c' := by
  refine ⟨ok_of_pStep hc.1 h, ?_⟩
  obtain ⟨x, hx, hcase⟩ := mem_succsOf_iff.1 h
  rcases hcase with ⟨e, he, -, -, rfl⟩ | ⟨-, -, rfl⟩
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · simp only [PNet.oldItems, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      split_ifs
      · rfl
      · show PNet.substDep _ _ z.2.2.2 = []
        rw [hc.2 z hz]
        rfl
    · simp only [PNet.newItems, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      show c.2.deps x.1 ++ _ = []
      rw [deps_eq_nil_of_all hc.2, filter_ordB_eq_nil (hd e he) (List.mem_dedup.1 hz)]
      rfl
  · intro y hy
    simp only [PNet.finish, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    split_ifs
    · rfl
    · show z.2.2.2.filter _ = []
      rw [hc.2 z hz]
      rfl

/-! ### Bisimulation -/

theorem step_of_pStep_uo {d : DomDesc} {q : InstDesc} {c c' : PConfig} (hc : UOInv c)
    (h : PStep d c c') : Step (uoSys d q) (uoAbs c) (uoAbs c') := by
  obtain ⟨x, hx, hcase⟩ := mem_succsOf_iff.1 h
  obtain ⟨hxm, hfl, -⟩ := mem_readyItems.1 hx
  have hlx : ∀ {b : Bool}, x.2.1.1 = b → x.2.1 = (b, x.2.1.2) := by
    intro b hb
    rw [← hb]
  rcases hcase with ⟨e, he, hk, hn, rfl⟩ | ⟨hk, happ, rfl⟩
  · have hmem : (true, e.1) ∈ (uoAbs c).2 := by
      rw [hn, ← hlx hk]
      exact mem_flagLbls.2 ⟨x, hxm, hfl, rfl⟩
    have := Step.dec (S := uoSys d q) (uoAbs c).1 (uoAbs c).2 e.1
      ((e.2.ids.dedup.map e.2.lblPair : List _) : Multiset _) hmem ⟨e, he, rfl, rfl⟩
    convert this using 2
    show flagLbls (c.2.expand x.1 e) = _
    rw [flagLbls_expand hc.1.nodup hxm hfl, hlx hk, hn]
    rfl
  · have hmem : (false, x.2.1.2) ∈ (uoAbs c).2 := by
      rw [← hlx hk]
      exact mem_flagLbls.2 ⟨x, hxm, hfl, rfl⟩
    have happ' : (uoSys d q).app (uoAbs c).1 x.2.1.2 := by
      intro f hf
      exact List.mem_toFinset.2 (applB_iff_forall.1 happ f hf)
    have := Step.exe (S := uoSys d q) (uoAbs c).1 (uoAbs c).2 x.2.1.2 hmem happ'
    convert this using 2
    · exact toFinset_stepL d c.1 x.2.1.2
    · show flagLbls (c.2.finish x.1) = _
      rw [flagLbls_finish hc.1.nodup hxm hfl, ← hlx hk]
      rfl

theorem pStep_of_step_uo {d : DomDesc} {q : InstDesc} {c : PConfig} (hc : UOInv c) {y : Cfg}
    (h : Step (uoSys d q) (uoAbs c) y) : ∃ c', PStep d c c' ∧ uoAbs c' = y := by
  generalize hz : uoAbs c = z at h
  cases h with
  | dec s M cn β hmem hmeth =>
    obtain ⟨e, he, rfl, rfl⟩ := hmeth
    have hM : M = flagLbls c.2 := (congrArg Prod.snd hz).symm
    have hs : s = c.1.toFinset := (congrArg Prod.fst hz).symm
    obtain ⟨x, hxm, hfl, hlbl⟩ := mem_flagLbls.1 (hM ▸ hmem)
    have hready : x ∈ readyItems c.2 := mem_readyItems.2 ⟨hxm, hfl, hc.2 x hxm⟩
    refine ⟨(c.1, c.2.expand x.1 e), mem_succsOf_iff.2 ⟨x, hready, Or.inl
      ⟨e, he, by rw [hlbl], by rw [hlbl], rfl⟩⟩, ?_⟩
    show (c.1.toFinset, flagLbls (c.2.expand x.1 e)) = _
    rw [flagLbls_expand hc.1.nodup hxm hfl, hlbl, hs, hM]
  | exe s M a hmem happ =>
    have hM : M = flagLbls c.2 := (congrArg Prod.snd hz).symm
    have hs : s = c.1.toFinset := (congrArg Prod.fst hz).symm
    obtain ⟨x, hxm, hfl, hlbl⟩ := mem_flagLbls.1 (hM ▸ hmem)
    have hready : x ∈ readyItems c.2 := mem_readyItems.2 ⟨hxm, hfl, hc.2 x hxm⟩
    have happB : applB d c.1 x.2.1.2 = true := by
      rw [hlbl]
      refine applB_iff_forall.2 fun f hf => ?_
      have := happ f hf
      rw [hs] at this
      exact List.mem_toFinset.1 this
    refine ⟨(stepL d c.1 x.2.1.2, c.2.finish x.1), mem_succsOf_iff.2 ⟨x, hready, Or.inr
      ⟨by rw [hlbl], happB, rfl⟩⟩, ?_⟩
    show ((stepL d c.1 x.2.1.2).toFinset, flagLbls (c.2.finish x.1)) = _
    rw [flagLbls_finish hc.1.nodup hxm hfl, hlbl, toFinset_stepL, hs, hM]
    rfl

theorem isGoalB_iff_uo {d : DomDesc} {q : InstDesc} {c : PConfig} :
    isGoalB q c = true ↔ IsGoal (uoSys d q) (uoAbs c) := by
  simp only [isGoalB, Bool.and_eq_true, ids_isEmpty_iff, List.all_eq_true, memB_iff, IsGoal,
    uoAbs, uoSys, List.mem_toFinset]

/-! ### Runs -/

theorem reachIn_of_ppath {d : DomDesc} {q : InstDesc} (hd : d.MethodsUO) :
    ∀ {c : PConfig} {cs : List PConfig}, UOInv c → PPath d c cs →
      ReachIn (uoSys d q) cs.length (uoAbs c) (uoAbs (endOf c cs)) := by
  intro c cs
  induction cs generalizing c with
  | nil => exact fun _ _ => ReachIn.refl _
  | cons x xs ih =>
    intro hc h
    exact ReachIn.step (step_of_pStep_uo hc h.1) (ih (uoInv_step hd hc h.1) h.2)

theorem ppath_of_reachIn {d : DomDesc} {q : InstDesc} (hd : d.MethodsUO) :
    ∀ {n : ℕ} {x y : Cfg}, ReachIn (uoSys d q) n x y → ∀ {c : PConfig}, UOInv c →
      uoAbs c = x → ∃ cs, PPath d c cs ∧ cs.length = n ∧ uoAbs (endOf c cs) = y := by
  intro n x y h
  induction h with
  | refl x =>
    intro c _ hx
    exact ⟨[], trivial, rfl, hx⟩
  | step hs _ ih =>
    intro c hc hx
    subst hx
    obtain ⟨c', hc', rfl⟩ := pStep_of_step_uo hc hs
    obtain ⟨cs, hcs, hlen, hend⟩ := ih (uoInv_step hd hc hc') rfl
    exact ⟨c' :: cs, ⟨hc', hcs⟩, by simp [hlen], hend⟩

/-! ### The bound -/

theorem zsB_mono {n n' a a' : ℕ} (hn : n ≤ n') (ha : a ≤ a') :
    ZeroSum.zsB n a ≤ ZeroSum.zsB n' a' := by
  unfold ZeroSum.zsB
  calc (2 * a + 2) ^ 3 ^ n ≤ (2 * a' + 2) ^ 3 ^ n := Nat.pow_le_pow_left (by omega) _
    _ ≤ (2 * a' + 2) ^ 3 ^ n' :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num) hn)

theorem uoBound_mono {k nA nA' M M' : ℕ} (hA : nA ≤ nA') (hM : M ≤ M') :
    uoBound k nA M ≤ uoBound k nA' M' := by
  unfold uoBound
  have h1 : (M + 1) ^ (k * 2 ^ k + 1) ≤ (M' + 1) ^ (k * 2 ^ k + 1) :=
    Nat.pow_le_pow_left (by omega) _
  have h2 : (M + 1) ^ (k * 2 ^ k + 2) ≤ (M' + 1) ^ (k * 2 ^ k + 2) :=
    Nat.pow_le_pow_left (by omega) _
  have h3 := zsB_mono hA h2
  exact Nat.add_le_add h1 (Nat.mul_le_mul h3 h2)

/-- **The number of search rounds for an unordered description**: the bound of the
small-solution theorem, with the numbers of compound names, actions and states bounded by the
lengths of the vocabularies `allLbls` and `allFacts`. -/
def uoBnd (d : DomDesc) (q : InstDesc) : ℕ :=
  uoBound (1 + (allLbls d q).length + 2 ^ (allFacts d q).length) (allLbls d q).length
    (q.tnI.ids.length + maxBody d + 2)

/-- **The decision procedure for unordered descriptions**: the bounded progression search. -/
def uoSolvableB (d : DomDesc) (q : InstDesc) : Bool :=
  (bfs d (initConfig q) (uoBnd d q)).any (isGoalB q)

/-- The relevant names: the second components of the possible labels. -/
def uoNames (d : DomDesc) (q : InstDesc) : Finset ℕ := ((allLbls d q).map Prod.snd).toFinset

theorem closed_uoSys (d : DomDesc) (q : InstDesc) :
    Closed (uoSys d q) (uoNames d q) (uoNames d q) (allFacts d q).toFinset (maxBody d) where
  meth_lab := by
    rintro c β ⟨e, he, -, rfl⟩ x hx
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hx)
    have h : (e.2.lblPair z).2 ∈ uoNames d q :=
      List.mem_toFinset.2 (List.mem_map_of_mem (lblPair_method_mem_allLbls he z))
    exact ⟨fun _ => h, fun _ => h⟩
  meth_card := by
    rintro c β ⟨e, he, -, rfl⟩
    simpa using length_le_maxBody he
  nxt_sub := by
    intro s a hs f hf
    simp only [uoSys, Finset.mem_union, Finset.mem_filter, List.mem_toFinset] at hf
    rcases hf with ⟨hf, -⟩ | hf
    · exact hs hf
    · exact List.mem_toFinset.2 (mem_allFacts_of_mem_add hf)

theorem labOK_init (d : DomDesc) (q : InstDesc) :
    LabOK (uoNames d q) (uoNames d q) (uoAbs (initConfig q)).2 := by
  intro x hx
  obtain ⟨y, hy, -, rfl⟩ := mem_flagLbls.1 hx
  simp only [initConfig, PNet.ofTnDesc, List.mem_map] at hy
  obtain ⟨z, -, rfl⟩ := hy
  have h : (q.tnI.lblPair z).2 ∈ uoNames d q :=
    List.mem_toFinset.2 (List.mem_map_of_mem (lblPair_tnI_mem_allLbls d q z))
  exact ⟨fun _ => h, fun _ => h⟩

theorem card_init_le (q : InstDesc) :
    Multiset.card (uoAbs (initConfig q)).2 ≤ q.tnI.ids.length := by
  show Multiset.card (flagLbls (PNet.ofTnDesc q.tnI)) ≤ _
  simp only [flagLbls, Multiset.coe_card, List.length_map]
  have hsub : ((PNet.ofTnDesc q.tnI).filter (fun x => x.2.2.1)).map (fun x => x.1) ⊆
      q.tnI.ids := by
    intro i hi
    exact PNet.mem_ids_ofTnDesc.1 hi
  have hnd : (((PNet.ofTnDesc q.tnI).filter (fun x => x.2.2.1)).map (fun x => x.1)).Nodup := by
    have := PNet.nodup_ofTnDesc q.tnI
    exact (List.filter_sublist.map _).nodup this
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

/-- **The bounded search decides plan existence for unordered descriptions.** -/
theorem uoSolvableB_iff {d : DomDesc} {q : InstDesc} (hd : d.MethodsUO) (hq : q.IsUO) :
    uoSolvableB d q = true ↔ Solvable d q := by
  constructor
  · intro h
    obtain ⟨c, hc, hg⟩ := List.any_eq_true.1 h
    exact solvable_of_pReach (pReach_of_mem_bfs _ hc) hg
  · intro h
    obtain ⟨c, hr, hg⟩ := exists_pReach_of_solvable h
    obtain ⟨cs, hcs, hend⟩ := exists_ppath_of_pReach hr
    have hinv := uoInv_initConfig hq
    have hrun := reachIn_of_ppath (q := q) hd hinv hcs
    rw [hend] at hrun
    have hgoal : IsGoal (uoSys d q) (uoAbs c) := isGoalB_iff_uo.1 hg
    have hs₀ : (uoAbs (initConfig q)).1 ⊆ (allFacts d q).toFinset := by
      intro f hf
      simp only [uoAbs, initConfig, List.mem_toFinset] at hf ⊢
      simp [allFacts, hf]
    have hk : 1 + (uoNames d q).card + 2 ^ (allFacts d q).toFinset.card ≤
        1 + (allLbls d q).length + 2 ^ (allFacts d q).length := by
      have h1 : (uoNames d q).card ≤ (allLbls d q).length := by
        simpa using List.toFinset_card_le ((allLbls d q).map Prod.snd)
      have h2 : 2 ^ (allFacts d q).toFinset.card ≤ 2 ^ (allFacts d q).length :=
        Nat.pow_le_pow_right (by norm_num) (List.toFinset_card_le _)
      omega
    obtain ⟨m, hm, y', hy', hgy'⟩ :=
      short_run (closed_uoSys d q) hs₀ (labOK_init d q) hk hrun hgoal
    obtain ⟨cs', hcs', hlen, hend'⟩ := ppath_of_reachIn hd hy' hinv rfl
    have hmb : m ≤ uoBnd d q := by
      refine le_trans hm (uoBound_mono ?_ ?_)
      · simpa [uoNames] using List.toFinset_card_le ((allLbls d q).map Prod.snd)
      · have := card_init_le q
        omega
    refine List.any_eq_true.2 ⟨_, mem_bfs_of_ppath hcs' _ (by omega), ?_⟩
    exact isGoalB_iff_uo.2 (hend' ▸ hgy')

end Syn

end HTN
