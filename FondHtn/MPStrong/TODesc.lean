import FondHtn.MPStrong.TOGame
import FondHtn.MPStrong.Acyc
import HtnPlanning.Core.DecompPersist
/-!
# Strong method-based plan existence for totally ordered problems is in `2-EXPTIME`

The table of the ideas file ("Total order — Membership"): `(c, s, S')` — the compound task `c`,
started in state `s`, can be completed against all outcomes, ending in a state of `S'` — as an
AND-OR game over configurations of exponential size (`S'` is an explicit list of states).

Configurations `(kind, c, s, d, tgt, mid)` (`FOND.TO.TCfg`):

* `kind = 0`, **sequence** `(s, d, tgt)`: the (totally ordered) network `d` is to be executed
  from the state `s`, ending in a state of the target `tgt` (`(true, _)`: any state;
  `(false, L)`: a state of `L`).  Accepting if `d` is empty and `s` is in the target.  If the
  first task is primitive and applicable, the configuration is universal over its outcomes; if
  it is compound (`c`), the planner chooses a list `mid` of states and moves to the split.
* `kind = 1`, **goal** `(c, s, tgt)`: choose a method of `c` and execute its network.
* `kind = 2`, **split** `(c, s, d, tgt, mid)`: universal — the goal `(c, s, mid)` and the
  sequences `(l, d, tgt)` for all `l ∈ mid`.

Correctness rests on the sequential-composition lemmas of `FondHtn/MPStrong/TOGame.lean` (the
"rank argument" of the ideas file): a strategy for `c ; rest` plays `c` to completion, ending in
the states from which `rest` is won (`FOND.Problem.MPProgTH.first_comp`), and strategies compose
(`FOND.Problem.MPProgTH.first_comp_of`).  The game is the least fixpoint, decided by
`HTN.Syn.PolyDom.inExp2Time_codeLang_of_andOr`.

* **`FOND.strongMP_TO_mem`** — `PlanExMP .strong TO ∈ 2-EXPTIME`.
-/

namespace FOND

namespace TO

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS

/-- A configuration: kind, compound name, state, network, target, chosen intermediate states. -/
abbrev TCfg : Type := ℕ × ℕ × List ℕ × TnDesc × (Bool × List (List ℕ)) × List (List ℕ)

instance decEqTgt : DecidableEq (Bool × List (List ℕ)) := inferInstance
instance decEqTCfg4 : DecidableEq (TnDesc × (Bool × List (List ℕ)) × List (List ℕ)) :=
  inferInstance
instance decEqTCfg : DecidableEq TCfg := inferInstance
instance bEncTCfg : BEnc TCfg := inferInstance
instance bDecTCfg : BDec TCfg := inferInstance
instance bEncTStepArg : BEnc (FProbDesc × TCfg × TCfg) := inferInstance
instance bEncTStepArgM : BEnc ((FProbDesc × TCfg × TCfg) × MethodDesc) := inferInstance

/-- The empty network description. -/
def emptyD : TnDesc := ([], [], [])

/-- `l` and `s` describe the same state. -/
def sameSet (l s : List ℕ) : Bool := l.all (fun f => decide (f ∈ s)) && s.all fun f => decide (f ∈ l)

theorem sameSet_iff (l s : List ℕ) : sameSet l s = true ↔ {f | f ∈ l} = {f | f ∈ s} := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    ext f; exact ⟨h1 f, h2 f⟩
  · intro h
    exact ⟨fun f hf => (Set.ext_iff.1 h f).1 hf, fun f hf => (Set.ext_iff.1 h f).2 hf⟩

/-- The state `s` lies in the target. -/
def inTgt (tgt : Bool × List (List ℕ)) (s : List ℕ) : Bool := tgt.1 || tgt.2.any fun l => sameSet l s

/-- The set of states of a target. -/
def tgtSet (tgt : Bool × List (List ℕ)) : Set (Set ℕ) :=
  {S | tgt.1 = true ∨ ∃ l ∈ tgt.2, S = {f | f ∈ l}}

theorem inTgt_iff (tgt : Bool × List (List ℕ)) (s : List ℕ) :
    inTgt tgt s = true ↔ {f | f ∈ s} ∈ tgtSet tgt := by
  simp only [inTgt, Bool.or_eq_true, List.any_eq_true, sameSet_iff, tgtSet, Set.mem_setOf_eq]
  exact or_congr Iff.rfl (exists_congr fun l => and_congr Iff.rfl eq_comm)

/-- The size bound for lists of states. -/
def Mx (p : FProbDesc) : ℕ := 2 ^ (4 * sz p + 8)

/-- Admissible lists of states: bounded size, duplicate-free states of facts of the
description. -/
def wfStates (p : FProbDesc) (L : List (List ℕ)) : Bool :=
  decide (sz L ≤ Mx p) && L.all fun l => nodupB l && l.all fun f => decide (f ∈ ffacts p)

theorem wfStates_iff (p : FProbDesc) (L : List (List ℕ)) :
    wfStates p L = true ↔ sz L ≤ Mx p ∧ ∀ l ∈ L, l.Nodup ∧ ∀ f ∈ l, f ∈ ffacts p := by
  simp [wfStates, List.all_eq_true, nodupB_iff]

/-- **The moves.** -/
def tStep (x : FProbDesc × TCfg × TCfg) : Bool :=
  bif x.2.1.1 == 0 then
    (x.2.1.2.2.2.1.ids.any fun y => unc x.2.1.2.2.2.1 y && (lblOf x.2.1.2.2.2.1 y).1 &&
      decide (x.2.2 = (2, (lblOf x.2.1.2.2.2.1 y).2, x.2.1.2.2.1, progDesc x.2.1.2.2.2.1 y,
        x.2.1.2.2.2.2.1, x.2.2.2.2.2.2.2)) && wfStates x.1 x.2.2.2.2.2.2.2) ||
    (x.2.1.2.2.2.1.ids.any fun y => unc x.2.1.2.2.2.1 y && !(lblOf x.2.1.2.2.2.1 y).1 &&
      fApp x.1 (lblOf x.2.1.2.2.2.1 y).2 x.2.1.2.2.1 &&
      (outs x.1 (lblOf x.2.1.2.2.2.1 y).2 x.2.1.2.2.1).any fun s'' =>
        decide (x.2.2 = (0, 0, s'', progDesc x.2.1.2.2.2.1 y, x.2.1.2.2.2.2.1, [])))
  else bif x.2.1.1 == 1 then
    decide (x.2.2 ∈ (x.1.methods.filter fun e => e.1 == x.2.1.2.1).map fun e =>
      ((0, 0, x.2.1.2.2.1, e.2, x.2.1.2.2.2.2.1, []) : TCfg))
  else bif x.2.1.1 == 2 then
    decide (x.2.2 = (1, x.2.1.2.1, x.2.1.2.2.1, emptyD, (false, x.2.1.2.2.2.2.2), [])) ||
      x.2.1.2.2.2.2.2.any fun l => decide (x.2.2 = (0, 0, l, x.2.1.2.2.2.1, x.2.1.2.2.2.2.1, []))
  else false

/-- Universal configurations. -/
def tUni (x : FProbDesc × TCfg) : Bool :=
  (x.2.1 == 0 && x.2.2.2.2.1.ids.any fun y => unc x.2.2.2.2.1 y && !(lblOf x.2.2.2.2.1 y).1 &&
    fApp x.1 (lblOf x.2.2.2.2.1 y).2 x.2.2.2.1) || x.2.1 == 2

/-- Accepting configurations. -/
def tAcc (x : FProbDesc × TCfg) : Bool :=
  x.2.1 == 0 && x.2.2.2.2.1.ids.isEmpty && inTgt x.2.2.2.2.2.1 x.2.2.2.1

/-- The initial configuration. -/
def tInit0 (p : FProbDesc) : TCfg := (0, 0, p.init.dedup, (initF p).2, (true, []), [])

/-- The initial test. -/
def tInit (x : FProbDesc × TCfg) : Bool :=
  FProbDesc.validB x.1 && fTOB x.1 && decide (x.2 = tInit0 x.1)

/-! ## Invariants -/

/-- The skeleton problem of the class definitions. -/
abbrev QP (p : FProbDesc) : HTN.Problem (ℕ ⊕ ℕ) ℕ ℕ ℕ := p.toProblem.toArt.toPos

/-- Invariant of network descriptions: duplicate-free ids, well formed, totally ordered by the
listed pairs, compound names reachable, small. -/
structure DInv (p : FProbDesc) (d : TnDesc) : Prop where
  nodup : d.ids.Nodup
  wf : (cfgNet d).WF
  total : ∀ a ∈ d.ids, ∀ b ∈ d.ids, a ≠ b → (a, b) ∈ d.ordList ∨ (b, a) ∈ d.ordList
  names : ∀ y ∈ d.ids, ∀ c, lblOf d y = (true, c) → (QP p).ReachableName c
  size : sz d ≤ sz p

/-- States: duplicate-free lists of facts of the description. -/
def SInv (p : FProbDesc) (s : List ℕ) : Prop := s.Nodup ∧ ∀ f ∈ s, f ∈ ffacts p

/-- **The invariant of reachable configurations.** -/
structure TInv (p : FProbDesc) (g : TCfg) : Prop where
  kind : g.1 ≤ 2
  st : SInv p g.2.2.1
  d : DInv p g.2.2.2.1
  tgt : ∀ l ∈ g.2.2.2.2.1.2, SInv p l
  tgtsz : sz g.2.2.2.2.1.2 ≤ Mx p
  mid : wfStates p g.2.2.2.2.2 = true
  name : g.1 ≠ 0 → (QP p).ReachableName g.2.1
  namesz : sz g.2.1 ≤ sz p + 5

theorem lookup_mem {β : Type} {l : List (ℕ × β)} {y : ℕ} {q : β} (h : l.lookup y = some q) :
    (y, q) ∈ l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    obtain ⟨k, b⟩ := a
    by_cases hk : y = k
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h; simp
    · have : (y == k) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem sz_lblOf_le (d : TnDesc) (y : ℕ) : sz (lblOf d y).2 ≤ sz d + 5 := by
  unfold lblOf
  cases h : d.lbl.lookup y with
  | none => simp only [Option.getD_none]; exact (sz_nat_le_two (by norm_num)).trans (by omega)
  | some q =>
    simp only [Option.getD_some]
    have h1 := sz_le_of_mem (lookup_mem h)
    have h2 : sz q.2 ≤ sz (y, q) := by
      rw [sz_prod, show sz q = sz q.1 + sz q.2 from sz_prod _ _]; omega
    have h3 : sz d.lbl ≤ sz d := by rw [sz_tnDesc]; omega
    omega

theorem sz_progDesc_le (d : TnDesc) (x : ℕ) : sz (progDesc d x) ≤ sz d := by
  unfold progDesc
  rw [sz_tnDesc, sz_tnDesc]
  simp only [TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have := sz_filter_le d.1 (fun y => decide (y ≠ x))
  have := sz_filter_le d.2.1 (fun q => decide (q.1 ≠ x ∧ q.2 ≠ x))
  have := sz_filter_le d.2.2 (fun q => decide (q.1 ≠ x))
  exact Nat.add_le_add (by assumption) (Nat.add_le_add (by assumption) (by assumption))

theorem sz_sublist_le {β : Type} [BEnc β] {l l' : List β} (h : l.Sublist l') : sz l ≤ sz l' := by
  induction h with
  | slnil => rfl
  | cons a _ ih => rw [sz_cons]; omega
  | cons₂ a _ ih => rw [sz_cons, sz_cons]; omega

theorem agree_tn {prim : ℕ → Prop} {t : TnDesc} (ht : TnValid prim t) :
    t.toTaskNetwork.Agree (cfgNet t) := by
  refine ⟨rfl, ?_, fun _ _ => rfl⟩
  funext a b
  simp only [TnDesc.toTaskNetwork, cfgNet, eq_iff_iff]
  exact ht.ordOf_iff

/-- The progression of the first task keeps the invariant. -/
theorem DInv.prog {p : FProbDesc} {d : TnDesc} (h : DInv p d) {x : ℕ} (hx : x ∈ d.ids)
    (hu : ∀ q ∈ d.ordList, q.2 ≠ x) : DInv p (progDesc d x) where
  nodup := h.nodup.filter _
  wf := Problem.wf_of_agree (TaskNetwork.progress_wf h.wf (unconstrained_cfgNet hx hu)) (agree_progDesc hu)
  total := by
    intro a ha b hb hab
    simp only [Article.progDesc, TnDesc.ids, List.mem_filter, decide_eq_true_eq] at ha hb
    rcases h.total a ha.1 b hb.1 hab with h' | h'
    · exact Or.inl (List.mem_filter.2 ⟨h', by simp [ha.2, hb.2]⟩)
    · exact Or.inr (List.mem_filter.2 ⟨h', by simp [ha.2, hb.2]⟩)
  names := by
    intro y hy c hc
    have hyx : y ≠ x := (by simpa [Article.progDesc, TnDesc.ids] using hy : y ∈ d.ids ∧ y ≠ x).2
    have hy' : y ∈ d.ids := (by simpa [Article.progDesc, TnDesc.ids] using hy : y ∈ d.ids ∧ y ≠ x).1
    refine h.names y hy' c ?_
    rw [← hc]
    unfold lblOf
    rw [show (progDesc d x).lbl = d.lbl.filter fun q => decide (q.1 ≠ x) from rfl,
      lookup_filter_ne _ hyx]
  size := (sz_progDesc_le d x).trans h.size

/-! ### Sources of the invariant -/

theorem one_le_sz_l {β : Type} [BEnc β] (l : List β) : 1 ≤ sz l := by
  cases l with
  | nil => simp [sz_nil]
  | cons b l => rw [sz_cons]; omega

theorem sz_methods_le (p : FProbDesc) : sz p.methods ≤ sz p := by
  obtain ⟨⟨acts, ms⟩, init, tn⟩ := p
  rw [sz_fprob]; simp only [FProbDesc.methods]; omega

theorem sz_tnI_le (p : FProbDesc) : sz p.tnI ≤ sz p := by
  obtain ⟨⟨acts, ms⟩, init, tn⟩ := p
  rw [sz_fprob]; simp only [FProbDesc.tnI]; omega

theorem three_le_sz (p : FProbDesc) : sz emptyD ≤ sz p := by
  obtain ⟨⟨acts, ms⟩, init, tn⟩ := p
  rw [sz_fprob]
  have h1 := one_le_sz_l acts
  have h2 := one_le_sz_l ms
  have h3 := one_le_sz_l init
  have h4 : sz tn ≥ 1 := by
    obtain ⟨i, o, l⟩ := tn
    rw [sz_prod]; have := one_le_sz_l i; omega
  have : sz emptyD = 3 := by simp [emptyD, sz_prod, sz_nil]
  omega

theorem dInv_method {p : FProbDesc} (hp : p.Valid) (hTO : FClass.TO p.toProblem) {e : MethodDesc}
    (he : e ∈ p.methods) (hr : (QP p).ReachableName e.1) : DInv p e.2 where
  nodup := (hp.methods e he).nodup
  wf := Problem.wf_of_agree (TnDesc.toTaskNetwork_wf e.2) (agree_tn (hp.methods e he))
  total := by
    intro a ha b hb hab
    have := hTO.2 e.toMethod ⟨⟨e, he, rfl⟩, hr⟩ a (List.mem_toFinset.2 ha) b
      (List.mem_toFinset.2 hb) hab
    simp only [MethodDesc.toMethod, TnDesc.toTaskNetwork] at this
    rwa [(hp.methods e he).ordOf_iff, (hp.methods e he).ordOf_iff] at this
  names := by
    intro y hy c hc
    refine HTN.Problem.ReachableName.method (m := e.toMethod) ⟨e, he, rfl⟩ hr
      (List.mem_toFinset.2 hy) ?_
    show e.2.label y = _
    rw [label_eq_toSum, hc]; rfl
  size := by
    have h1 := sz_le_of_mem he
    have h2 : sz e.2 ≤ sz e := by rw [show sz e = sz e.1 + sz e.2 from sz_prod _ _]; omega
    have h3 := sz_methods_le p
    omega

theorem dInv_init {p : FProbDesc} (hp : p.Valid) (hTO : FClass.TO p.toProblem) :
    DInv p (initF p).2 where
  nodup := hp.tnI.nodup
  wf := by
    have h0 := inv_initCfg (skDesc_valid hp)
    rw [initCfg_skDesc] at h0
    exact h0.wf
  total := by
    intro a ha b hb hab
    have := hTO.1 a (List.mem_toFinset.2 ha) b (List.mem_toFinset.2 hb) hab
    simp only [initF, TnDesc.ordList, List.mem_dedup]
    change p.tnI.ordOf a b ∨ p.tnI.ordOf b a at this
    rwa [hp.tnI.ordOf_iff, hp.tnI.ordOf_iff] at this
  names := by
    intro y hy c hc
    refine HTN.Problem.ReachableName.tnI (P := QP p) (List.mem_toFinset.2 hy) ?_
    show p.tnI.label y = _
    rw [label_eq_toSum]
    exact (congrArg toSum hc).trans rfl
  size := by
    have h1 : sz (initF p).2 ≤ sz p.tnI := by
      simp only [initF]
      rw [sz_tnDesc, sz_tnDesc]
      simp only [TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
      have := sz_sublist_le (List.dedup_sublist p.tnI.2.1)
      omega
    exact h1.trans (sz_tnI_le p)

theorem dInv_empty (p : FProbDesc) : DInv p emptyD where
  nodup := List.nodup_nil
  wf := ⟨fun h => by simp [cfgNet, emptyD, TnDesc.ordList] at h,
    fun h => by simp [cfgNet, emptyD, TnDesc.ordList] at h,
    fun _ h => by simp [cfgNet, emptyD, TnDesc.ordList] at h,
    fun h => by simp [cfgNet, emptyD, TnDesc.ordList] at h⟩
  total := by simp [emptyD, TnDesc.ids]
  names := by simp [emptyD, TnDesc.ids]
  size := three_le_sz p

/-! ### The moves -/

theorem tStep_cases {p : FProbDesc} {k c : ℕ} {s : List ℕ} {d : TnDesc}
    {tgt : Bool × List (List ℕ)} {mid : List (List ℕ)} {g' : TCfg}
    (h : tStep (p, (k, c, s, d, tgt, mid), g') = true) :
    (k = 0 ∧ ((∃ y ∈ d.ids, unc d y = true ∧ (lblOf d y).1 = true ∧
        g' = (2, (lblOf d y).2, s, progDesc d y, tgt, g'.2.2.2.2.2) ∧
        wfStates p g'.2.2.2.2.2 = true) ∨
      (∃ y ∈ d.ids, unc d y = true ∧ (lblOf d y).1 = false ∧ fApp p (lblOf d y).2 s = true ∧
        ∃ s'' ∈ outs p (lblOf d y).2 s, g' = (0, 0, s'', progDesc d y, tgt, [])))) ∨
    (k = 1 ∧ ∃ e ∈ p.methods, e.1 = c ∧ g' = (0, 0, s, e.2, tgt, [])) ∨
    (k = 2 ∧ (g' = (1, c, s, emptyD, (false, mid), []) ∨ ∃ l ∈ mid, g' = (0, 0, l, d, tgt, []))) := by
  unfold tStep at h
  rcases k with _ | _ | _ | k
  · left
    refine ⟨rfl, ?_⟩
    simp only [beq_self_eq_true, cond_true, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true'] at h
    rcases h with ⟨y, hy, ⟨⟨hu, hl⟩, he⟩, hw⟩ | ⟨y, hy, ⟨⟨hu, hl⟩, ha⟩, s'', hs'', he⟩
    · exact Or.inl ⟨y, hy, hu, hl, he, hw⟩
    · exact Or.inr ⟨y, hy, hu, hl, ha, s'', hs'', he⟩
  · right; left
    rw [show ((1 : ℕ) == 0) = false from rfl, show ((1 : ℕ) == 1) = true from rfl] at h
    simp only [cond_false, cond_true] at h
    have h' := of_decide_eq_true h
    simp only [List.mem_map, List.mem_filter, beq_iff_eq] at h'
    obtain ⟨e, ⟨he, hc⟩, rfl⟩ := h'
    exact ⟨rfl, e, he, hc, rfl⟩
  · right; right
    rw [show ((2 : ℕ) == 0) = false from rfl, show ((2 : ℕ) == 1) = false from rfl,
      show ((2 : ℕ) == 2) = true from rfl] at h
    simp only [cond_false, cond_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    exact ⟨rfl, h⟩
  · simp at h

theorem mem_ffacts_of_outs {p : FProbDesc} {a : ℕ} {s s' : List ℕ} (hs : SInv p s)
    (h : s' ∈ outs p a s) : SInv p s' := by
  refine ⟨nodup_of_mem_outs h, fun f hf => ?_⟩
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 h
  rcases List.mem_append.1 (List.mem_dedup.1 hf) with hf | hf
  · exact hs.2 f (List.mem_filter.1 hf).1
  · exact mem_ffacts_of_effect hz hf

theorem sz_zero_le (p : FProbDesc) : sz (0 : ℕ) ≤ sz p + 5 :=
  (sz_nat_le_two (by norm_num)).trans (by omega)

theorem wfStates_nil (p : FProbDesc) : wfStates p [] = true := by
  rw [wfStates_iff]
  refine ⟨?_, by simp⟩
  simp only [sz_nil, Mx]
  exact Nat.one_le_two_pow

/-- **The invariant is preserved.** -/
theorem TInv.step {p : FProbDesc} (hp : p.Valid) (hTO : FClass.TO p.toProblem) {g g' : TCfg}
    (h : TInv p g) (hs : tStep (p, g, g') = true) : TInv p g' := by
  obtain ⟨k, c, s, d, tgt, mid⟩ := g
  obtain ⟨hk, hst, hd, htgt, htgtsz, hmid, hname, hnamesz⟩ := h
  simp only at hk hst hd htgt htgtsz hmid hname hnamesz
  rcases tStep_cases hs with ⟨rfl, ⟨y, hy, hu, hl, heq, hw⟩ | ⟨y, hy, hu, hl, -, s'', hs'', rfl⟩⟩ |
    ⟨rfl, e, he, hc, rfl⟩ | ⟨rfl, rfl | ⟨l, hl, rfl⟩⟩
  · rw [heq]
    exact ⟨by simp, hst, hd.prog hy ((unc_iff _ _).1 hu), htgt, htgtsz, hw,
      fun _ => hd.names y hy _ (Prod.ext hl rfl), (sz_lblOf_le d y).trans (by have := hd.size; omega)⟩
  · exact ⟨by simp, mem_ffacts_of_outs hst hs'', hd.prog hy ((unc_iff _ _).1 hu), htgt, htgtsz,
      wfStates_nil p, fun h => absurd rfl h, sz_zero_le p⟩
  · exact ⟨by simp, hst, dInv_method hp hTO he (hc ▸ hname (by decide)), htgt, htgtsz,
      wfStates_nil p, fun h => absurd rfl h, sz_zero_le p⟩
  · have hm := (wfStates_iff p mid).1 hmid
    exact ⟨by simp, hst, dInv_empty p, fun l hl => ⟨(hm.2 l hl).1, (hm.2 l hl).2⟩, hm.1,
      wfStates_nil p, fun _ => hname (by decide), hnamesz⟩
  · have hm := (wfStates_iff p mid).1 hmid
    exact ⟨by simp, ⟨(hm.2 l hl).1, (hm.2 l hl).2⟩, hd, htgt, htgtsz, wfStates_nil p,
      fun h => absurd rfl h, sz_zero_le p⟩

/-- The reachable configurations. -/
def TReach (p : FProbDesc) (g : TCfg) : Prop :=
  Relation.ReflTransGen (fun g g' => tStep (p, g, g') = true) (tInit0 p) g

theorem tInv_init {p : FProbDesc} (hp : p.Valid) (hTO : FClass.TO p.toProblem) :
    TInv p (tInit0 p) :=
  ⟨Nat.zero_le _, ⟨List.nodup_dedup _, fun f hf => List.mem_append_left _ (List.mem_dedup.1 hf)⟩,
    dInv_init hp hTO, by simp [tInit0], by
      show sz ([] : List (List ℕ)) ≤ Mx p
      simp only [sz_nil, Mx]; exact Nat.one_le_two_pow,
    wfStates_nil p, fun h => absurd rfl h, sz_zero_le p⟩

theorem tInv_of_reach {p : FProbDesc} (hp : p.Valid) (hTO : FClass.TO p.toProblem) {g : TCfg}
    (h : TReach p g) : TInv p g := by
  induction h with
  | refl => exact tInv_init hp hTO
  | tail _ hs ih => exact ih.step hp hTO hs

/-- The bound on configurations. -/
def cfgBound (p : FProbDesc) : ℕ := 2 * Mx p + 3 * sz p + sz p * (2 * sz p + 2) + 13

theorem sz_le_of_tInv {p : FProbDesc} {g : TCfg} (h : TInv p g) : sz g ≤ cfgBound p := by
  obtain ⟨k, c, s, d, tgt, mid⟩ := g
  obtain ⟨hk, hst, hd, -, htgtsz, hmid, -, hnamesz⟩ := h
  simp only at hk hst hd htgtsz hmid hnamesz
  have h1 : sz k ≤ 5 := sz_nat_le_two hk
  have h2 := sz_state_le hst.1 hst.2
  have h3 := hd.size
  have h4 := ((wfStates_iff p mid).1 hmid).1
  have h5 : sz tgt = 1 + sz tgt.2 := by
    rw [show sz tgt = sz tgt.1 + sz tgt.2 from sz_prod _ _, sz_bool]
  have hsz : sz ((k, c, s, d, tgt, mid) : TCfg) = sz k + sz c + sz s + sz d + sz tgt + sz mid := by
    simp only [sz_prod]; ring
  rw [hsz, h5]
  unfold cfgBound
  omega

/-! ## Semantics -/

section Sem

variable {p : FProbDesc}

theorem isFirst_of {d : TnDesc} (hd : DInv p d) {y : ℕ} (hy : y ∈ d.ids) (hu : unc d y = true) :
    Problem.IsFirst (cfgNet d) y := by
  refine ⟨List.mem_toFinset.2 hy, fun b hb hby => ?_⟩
  have hb' : b ∈ d.ids := List.mem_toFinset.1 hb
  rcases hd.total y hy b hb' (Ne.symm hby) with h | h
  · exact h
  · exact absurd rfl ((unc_iff _ _).1 hu _ h)

theorem unc_of_unconstrained {d : TnDesc} (hd : DInv p d) {y : ℕ}
    (h : (cfgNet d).Unconstrained y) : y ∈ d.ids ∧ unc d y = true := by
  refine ⟨List.mem_toFinset.1 h.1, (unc_iff _ _).2 fun q hq e => ?_⟩
  have h1 : (cfgNet d).ord q.1 y := by rw [← e]; exact hq
  exact h.2 q.1 (hd.wf.mem_left h1) h1

theorem mem_methods_iff {m : Method ℕ ℕ ℕ} :
    m ∈ p.toProblem.methods ↔ ∃ e ∈ p.methods, e.toMethod = m := Iff.rfl

theorem exists_uniform {β : Type} {L : List β} {Q : ℕ → β → Prop}
    (hmono : ∀ n n' b, n ≤ n' → Q n b → Q n' b) (h : ∀ b ∈ L, ∃ n, Q n b) :
    ∃ N, ∀ b ∈ L, Q N b := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a L ih =>
    obtain ⟨n₁, h₁⟩ := h a (by simp)
    obtain ⟨n₂, h₂⟩ := ih fun b hb => h b (by simp [hb])
    refine ⟨max n₁ n₂, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hmono _ _ _ (le_max_left _ _) h₁
    · exact hmono _ _ _ (le_max_right _ _) (h₂ b hb)

theorem outcome_sub {a : ℕ} {S S' : Set ℕ} (hS : S ⊆ {f | f ∈ ffacts p})
    (h : S' ∈ (p.δ a).outcomes S) : S' ⊆ {f | f ∈ ffacts p} := by
  rw [← toAction_fActOf] at h
  obtain ⟨e, ⟨y, hy, rfl⟩, rfl⟩ := h
  intro f hf
  rcases hf with ⟨hf, -⟩ | hf
  · exact hS hf
  · exact mem_ffacts_of_effect hy hf

theorem MPProgTH.restrict_ff {G : Set (Set ℕ)} {n : ℕ} {N : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ}
    (h : p.toProblem.MPProgTH G n N S) (hS : S ⊆ {f | f ∈ ffacts p}) :
    p.toProblem.MPProgTH {S' | S' ∈ G ∧ S' ⊆ {f | f ∈ ffacts p}} n N S := by
  induction h with
  | empty he hs => exact .empty he ⟨hs, hS⟩
  | prim hu hα happ _ ih =>
    exact .prim hu hα happ fun s' hs' => ih s' hs' (outcome_sub hS hs')
  | decomp hu hd _ ih => exact .decomp hu hd (ih hS)

theorem inv_progDesc' {d : TnDesc} (hd : DInv p d) {y : ℕ} (hy : y ∈ d.ids)
    (hu : unc d y = true) : ((cfgNet d).progress y).WF :=
  TaskNetwork.progress_wf hd.wf (unconstrained_cfgNet hy ((unc_iff _ _).1 hu))

/-- The semantics of a configuration. -/
def Sem (p : FProbDesc) (g : TCfg) : Prop :=
  (g.1 = 0 → ∃ n, p.toProblem.MPProgTH (tgtSet g.2.2.2.2.1) n (cfgNet g.2.2.2.1)
      {f | f ∈ g.2.2.1}) ∧
  (g.1 = 1 → ∃ e ∈ p.methods, e.1 = g.2.1 ∧ ∃ n,
      p.toProblem.MPProgTH (tgtSet g.2.2.2.2.1) n (cfgNet e.2) {f | f ∈ g.2.2.1}) ∧
  (g.1 = 2 → (∃ e ∈ p.methods, e.1 = g.2.1 ∧ ∃ n,
      p.toProblem.MPProgTH (tgtSet (false, g.2.2.2.2.2)) n (cfgNet e.2) {f | f ∈ g.2.2.1}) ∧
    ∀ l ∈ g.2.2.2.2.2, ∃ n, p.toProblem.MPProgTH (tgtSet g.2.2.2.2.1) n (cfgNet g.2.2.2.1)
      {f | f ∈ l})

theorem tUni_zero {k c : ℕ} {s : List ℕ} {d : TnDesc} {tgt : Bool × List (List ℕ)}
    {mid : List (List ℕ)} (hk : k = 0) :
    tUni (p, (k, c, s, d, tgt, mid)) = true ↔
      ∃ y ∈ d.ids, unc d y = true ∧ (lblOf d y).1 = false ∧ fApp p (lblOf d y).2 s = true := by
  subst hk
  simp only [tUni, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', show ((0 : ℕ) == 2) = false from rfl,
    Bool.false_eq_true, or_false]
  exact exists_congr fun y => and_congr Iff.rfl (by tauto)

theorem tUni_one {c : ℕ} {s : List ℕ} {d : TnDesc} {tgt : Bool × List (List ℕ)}
    {mid : List (List ℕ)} : tUni (p, (1, c, s, d, tgt, mid)) = false := rfl

theorem tUni_two {c : ℕ} {s : List ℕ} {d : TnDesc} {tgt : Bool × List (List ℕ)}
    {mid : List (List ℕ)} : tUni (p, (2, c, s, d, tgt, mid)) = true := rfl

variable (hp : p.Valid) (hTO : FClass.TO p.toProblem)
include hp hTO

/-- **Soundness of the game.** -/
theorem tSound {B : ℕ} (hsz : ∀ g, TReach p g → sz g ≤ B) {g : TCfg}
    (hw : AOWin B tAcc tUni tStep p g) : TReach p g → Sem p g := by
  have hM := (FProbDesc.toProblem_wf hp).methods
  induction hw with
  | @acc c _ ha =>
    intro _
    obtain ⟨k, c, s, d, tgt, mid⟩ := c
    simp only [tAcc, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at ha
    obtain ⟨⟨rfl, hids⟩, hin⟩ := ha
    refine ⟨fun _ => ⟨0, .empty (by simp [cfgNet, hids]) ((inTgt_iff _ _).1 hin)⟩,
      fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  | @ex c c' _ hu _ hs _ ih =>
    intro hr
    have hr' : TReach p c' := hr.tail hs
    have ih' := ih hr'
    have hinv := tInv_of_reach hp hTO hr
    obtain ⟨k, c, s, d, tgt, mid⟩ := c
    have hd := hinv.d
    simp only at hd
    rcases tStep_cases hs with ⟨rfl, ⟨y, hy, huy, hl, heq, -⟩ | ⟨y, hy, huy, hl, ha, -⟩⟩ |
      ⟨rfl, e, he, hc, rfl⟩ | ⟨rfl, -⟩
    · refine ⟨fun _ => ?_, fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
      rw [heq] at ih'
      obtain ⟨-, -, h2⟩ := ih'
      obtain ⟨⟨e, he, hc, n₁, hn₁⟩, hrest⟩ := h2 rfl
      simp only at hc hn₁ hrest
      obtain ⟨N, hN⟩ := exists_uniform (Q := fun n l => p.toProblem.MPProgTH (tgtSet tgt) n
        (cfgNet (progDesc d y)) {f | f ∈ l}) (fun n n' b hle h => h.mono hle) hrest
      have hfirst := isFirst_of hd hy huy
      have hev := hp.methods e he
      have hwe : (cfgNet e.2).WF := Problem.wf_of_agree (TnDesc.toTaskNetwork_wf e.2) (agree_tn hev)
      have hk : p.toProblem.MPProgTH (tgtSet (false, c'.2.2.2.2.2)) n₁ e.toMethod.subtasks
          {f | f ∈ s} := hn₁.of_agree hwe (agree_tn hev).symm
      have hwp := TaskNetwork.progress_wf hd.wf (hfirst.unconstrained hd.wf)
      refine ⟨_, Problem.MPProgTH.first_comp_of hd.wf hfirst (c := (lblOf d y).2)
        (by rw [cfgNet_label]; simp [toSum, hl]) ⟨e, he, rfl⟩ hc (hM _ ⟨e, he, rfl⟩) hk
        (j := N) fun s' hs' => ?_⟩
      rcases hs' with h | ⟨l, hl', rfl⟩
      · simp at h
      · exact (hN l hl').of_agree (hd.prog hy ((unc_iff _ _).1 huy)).wf
          (agree_progDesc ((unc_iff _ _).1 huy)).symm
    · exfalso
      have : tUni (p, (0, c, s, d, tgt, mid)) = true := (tUni_zero rfl).2 ⟨y, hy, huy, hl, ha⟩
      rw [this] at hu; cases hu
    · refine ⟨fun h => absurd h (by simp), fun _ => ⟨e, he, hc, (ih'.1 rfl)⟩,
        fun h => absurd h (by simp)⟩
    · exact absurd hu (by rw [tUni_two]; simp)
  | @univ c _ hu _ ih =>
    intro hr
    have hinv := tInv_of_reach hp hTO hr
    obtain ⟨k, c, s, d, tgt, mid⟩ := c
    have hd := hinv.d
    have hk := hinv.kind
    simp only at hd hk
    rcases k with _ | _ | _ | k
    · obtain ⟨y, hy, huy, hl, ha⟩ := (tUni_zero rfl).1 hu
      refine ⟨fun _ => ?_, fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
      have hstep : ∀ s'' ∈ outs p (lblOf d y).2 s,
          tStep (p, (0, c, s, d, tgt, mid), (0, 0, s'', progDesc d y, tgt, [])) = true := by
        intro s'' hs''
        unfold tStep
        simp only [beq_self_eq_true, cond_true, Bool.or_eq_true, List.any_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
        exact Or.inr ⟨y, hy, ⟨⟨huy, hl⟩, ha⟩, s'', hs'', rfl⟩
      have hall : ∀ s'' ∈ outs p (lblOf d y).2 s, ∃ n, p.toProblem.MPProgTH (tgtSet tgt) n
          (cfgNet (progDesc d y)) {f | f ∈ s''} := fun s'' hs'' =>
        (ih _ (hsz _ (hr.tail (hstep s'' hs''))) (hstep s'' hs'') (hr.tail (hstep s'' hs''))).1 rfl
      obtain ⟨N, hN⟩ := exists_uniform (Q := fun n l => p.toProblem.MPProgTH (tgtSet tgt) n
        (cfgNet (progDesc d y)) {f | f ∈ l}) (fun n n' b hle h => h.mono hle) hall
      refine ⟨N + 1, .prim (unconstrained_cfgNet hy ((unc_iff _ _).1 huy))
        (by rw [cfgNet_label]; simp [toSum, hl]) ((fApp_iff _ _ _).1 ha) fun S' hS' => ?_⟩
      obtain ⟨s'', hs'', rfl⟩ := outs_complete hS'
      exact (hN s'' hs'').of_agree (hd.prog hy ((unc_iff _ _).1 huy)).wf
        (agree_progDesc ((unc_iff _ _).1 huy)).symm
    · exact absurd hu (by rw [tUni_one]; simp)
    · refine ⟨fun h => absurd h (by simp), fun h => absurd h (by simp), fun _ => ⟨?_, ?_⟩⟩
      · have hs : tStep (p, (2, c, s, d, tgt, mid), (1, c, s, emptyD, (false, mid), [])) = true := by
          unfold tStep; simp
        exact (ih _ (hsz _ (hr.tail hs)) hs (hr.tail hs)).2.1 rfl
      · intro l hl
        have hs : tStep (p, (2, c, s, d, tgt, mid), (0, 0, l, d, tgt, [])) = true := by
          unfold tStep
          simp only [show ((2 : ℕ) == 0) = false from rfl, show ((2 : ℕ) == 1) = false from rfl,
            show ((2 : ℕ) == 2) = true from rfl, cond_false, cond_true, Bool.or_eq_true,
            decide_eq_true_eq, List.any_eq_true]
          exact Or.inr ⟨l, hl, rfl⟩
        exact (ih _ (hsz _ (hr.tail hs)) hs (hr.tail hs)).1 rfl
    · exact absurd hk (by omega)

end Sem

/-! ## Completeness -/

section Complete

variable {p : FProbDesc}

theorem sz_sublists_le (p : FProbDesc) (q : List ℕ → Bool) :
    sz (((ffacts p).dedup.sublists).filter q) ≤ Mx p := by
  set L := (ffacts p).dedup
  set S := sz p
  have hL : sz L ≤ S * (2 * S + 2) + 1 :=
    sz_state_le (List.nodup_dedup _) fun f hf => List.mem_dedup.1 hf
  have hlen : L.length ≤ S := (List.Sublist.length_le (List.dedup_sublist _)).trans
    (length_ffacts_le p)
  have h1 := sz_filter_le L.sublists q
  have h2 : sz L.sublists ≤ L.sublists.length * (2 * sz L + 2) + 1 :=
    sz_list_le fun l hl => sz_sublist_le (List.mem_sublists.1 hl)
  rw [List.length_sublists] at h2
  have hX : 2 ^ L.length ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hlen
  have hS1 : S + 1 ≤ 2 ^ S := Nat.lt_two_pow_self
  have hpos : 1 ≤ 2 ^ S := Nat.one_le_two_pow
  have h3 : 2 * sz L + 2 ≤ 4 * (2 ^ S) ^ 2 := by
    have : S * (2 * S + 2) + 1 ≤ (S + 1) * (S + 1) * 2 := by nlinarith
    have : (S + 1) * (S + 1) ≤ 2 ^ S * 2 ^ S := Nat.mul_le_mul hS1 hS1
    nlinarith
  have h4 : Mx p = 256 * (2 ^ S) ^ 4 := by
    unfold Mx; rw [← pow_mul, show 4 * sz p + 8 = 8 + S * 4 by ring, pow_add]; norm_num
  rw [h4]
  have h5 : 2 ^ L.length * (2 * sz L + 2) ≤ 2 ^ S * (4 * (2 ^ S) ^ 2) := Nat.mul_le_mul hX h3
  have h6 : 1 ≤ (2 ^ S) ^ 4 := Nat.one_le_pow _ _ hpos
  have h7 : 2 ^ S * (4 * (2 ^ S) ^ 2) ≤ 4 * (2 ^ S) ^ 4 := by
    have : (2 ^ S) ^ 3 ≤ (2 ^ S) ^ 4 := Nat.pow_le_pow_right hpos (by norm_num)
    nlinarith
  omega

variable (hp : p.Valid) (hTO : FClass.TO p.toProblem)
include hp hTO

/-- **Completeness of the game.** -/
theorem tComplete {B : ℕ} (hsz : ∀ g, TReach p g → sz g ≤ B) (n : ℕ) :
    ∀ {g : TCfg}, TReach p g → g.1 = 0 →
      p.toProblem.MPProgTH (tgtSet g.2.2.2.2.1) n (cfgNet g.2.2.2.1) {f | f ∈ g.2.2.1} →
        AOWin B tAcc tUni tStep p g := by
  classical
  have hM := (FProbDesc.toProblem_wf hp).methods
  induction n with
  | zero =>
    intro g hr hk h
    have hinv := tInv_of_reach hp hTO hr
    obtain ⟨k0, c, s, d, tgt, mid⟩ := g
    simp only at hk h
    subst hk
    have hd := hinv.d
    simp only at hd
    by_cases hids : d.ids = []
    · refine AOWin.acc (hsz _ hr) ?_
      have := h.of_empty (by simp [cfgNet, hids])
      simp [tAcc, hids, (inTgt_iff _ _).2 this]
    · obtain ⟨y, hy⟩ := TaskNetwork.exists_unconstrained hd.wf (by
        obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hids
        exact ⟨z, List.mem_toFinset.2 hz⟩)
      obtain ⟨hyd, huy⟩ := unc_of_unconstrained hd hy
      have hfirst := isFirst_of hd hyd huy
      rcases hl : lblOf d y with ⟨_ | _, a⟩
      · obtain ⟨k, hk, -⟩ := Problem.MPProgTH.first_prim hd.wf hfirst
          (by rw [cfgNet_label, hl]; rfl) h
        omega
      · obtain ⟨k, hk, -⟩ := Problem.MPProgTH.first_comp hM hd.wf hfirst
          (by rw [cfgNet_label, hl]; rfl) h
        omega
  | succ n ih =>
    intro g hr hk h
    have hinv := tInv_of_reach hp hTO hr
    obtain ⟨k0, c, s, d, tgt, mid⟩ := g
    simp only at hk h
    subst hk
    have hd := hinv.d
    have hst := hinv.st
    simp only at hd hst
    by_cases hids : d.ids = []
    · refine AOWin.acc (hsz _ hr) ?_
      have := h.of_empty (by simp [cfgNet, hids])
      simp [tAcc, hids, (inTgt_iff _ _).2 this]
    obtain ⟨y, hy⟩ := TaskNetwork.exists_unconstrained hd.wf (by
      obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hids
      exact ⟨z, List.mem_toFinset.2 hz⟩)
    obtain ⟨hyd, huy⟩ := unc_of_unconstrained hd hy
    have hfirst := isFirst_of hd hyd huy
    have huniq : ∀ y', unc d y' = true → y' ∈ d.ids → y' = y := fun y' hu' hy' =>
      hfirst.eq (unconstrained_cfgNet hy' ((unc_iff _ _).1 hu'))
    have hwp := TaskNetwork.progress_wf hd.wf (hfirst.unconstrained hd.wf)
    have hag := agree_progDesc ((unc_iff _ _).1 huy)
    rcases hl : lblOf d y with ⟨_ | _, a⟩
    · -- the first task is primitive
      obtain ⟨k, hk, happ, hall⟩ := Problem.MPProgTH.first_prim hd.wf hfirst
        (by rw [cfgNet_label, hl]; rfl) h
      obtain rfl : k = n := by omega
      have huni : tUni (p, (0, c, s, d, tgt, mid)) = true :=
        (tUni_zero rfl).2 ⟨y, hyd, huy, by rw [hl], by rw [hl]; exact (fApp_iff _ _ _).2 happ⟩
      refine AOWin.univ (hsz _ hr) huni fun g' _ hs' => ?_
      rcases tStep_cases hs' with ⟨-, ⟨y', hy', hu', hl', -⟩ | ⟨y', hy', hu', -, -, s'', hs'', heq⟩⟩ |
        ⟨h1, -⟩ | ⟨h1, -⟩
      · obtain rfl := huniq y' hu' hy'
        rw [hl] at hl'; cases hl'
      · obtain rfl := huniq y' hu' hy'
        subst heq
        rw [hl] at hs''
        exact ih (hr.tail hs') rfl ((hall _ (outs_sound hs'')).of_agree hwp hag)
      · cases h1
      · cases h1
    · -- the first task is compound
      obtain ⟨k, hk, m, hm, hc, hkm⟩ := Problem.MPProgTH.first_comp hM hd.wf hfirst
        (by rw [cfgNet_label, hl]; rfl) h
      obtain rfl : k = n := by omega
      obtain ⟨e, he, rfl⟩ := (mem_methods_iff (p := p)).1 hm
      have hev := hp.methods e he
      set mid' := ((ffacts p).dedup.sublists).filter fun l => decide (p.toProblem.MPProgTH
        (tgtSet tgt) k ((cfgNet d).progress y) {f | f ∈ l}) with hmid'
      have hwf : wfStates p mid' = true := by
        rw [wfStates_iff]
        refine ⟨sz_sublists_le p _, fun l hl => ?_⟩
        have hsub := List.mem_sublists.1 (List.mem_filter.1 hl).1
        exact ⟨(List.nodup_dedup _).sublist hsub, fun f hf => List.mem_dedup.1 (hsub.subset hf)⟩
      have hs₁ : tStep (p, (0, c, s, d, tgt, mid), (2, a, s, progDesc d y, tgt, mid')) = true := by
        unfold tStep
        simp only [beq_self_eq_true, cond_true, Bool.or_eq_true, List.any_eq_true,
          Bool.and_eq_true, decide_eq_true_eq]
        exact Or.inl ⟨y, hyd, ⟨⟨huy, by rw [hl]⟩, by rw [hl]⟩, hwf⟩
      have hnuni : tUni (p, (0, c, s, d, tgt, mid)) = false := by
        by_contra hc'
        simp only [Bool.not_eq_false] at hc'
        obtain ⟨y', hy', hu', hl', -⟩ := (tUni_zero rfl).1 hc'
        obtain rfl := huniq y' hu' hy'
        rw [hl] at hl'; cases hl'
      have hr₁ := hr.tail hs₁
      refine AOWin.ex (hsz _ hr) hnuni (hsz _ hr₁) hs₁
        (AOWin.univ (hsz _ hr₁) tUni_two fun g'' _ hs'' => ?_)
      have hr₂ := hr₁.tail hs''
      rcases tStep_cases hs'' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl | ⟨l, hl'', rfl⟩⟩
      · cases h1
      · cases h1
      · -- the goal: choose the method `e`
        have hs₂ : tStep (p, (1, a, s, emptyD, (false, mid'), []),
            (0, 0, s, e.2, (false, mid'), [])) = true := by
          unfold tStep
          rw [show ((1 : ℕ) == 0) = false from rfl, show ((1 : ℕ) == 1) = true from rfl]
          simp only [cond_false, cond_true, decide_eq_true_eq, List.mem_map, List.mem_filter,
            beq_iff_eq]
          exact ⟨e, ⟨he, hc⟩, rfl⟩
        have hr₃ := hr₂.tail hs₂
        refine AOWin.ex (hsz _ hr₂) tUni_one (hsz _ hr₃) hs₂ (ih hr₃ rfl ?_)
        have h1 := MPProgTH.restrict_ff hkm hst.2
        have h2 := h1.monoG (G' := tgtSet (false, mid')) fun S' hS' => by
          obtain ⟨hT, hff⟩ := hS'
          refine Or.inr ⟨(ffacts p).dedup.filter fun f => decide (f ∈ S'), ?_, ?_⟩
          · have hset : {f | f ∈ (ffacts p).dedup.filter fun f => decide (f ∈ S')} = S' := by
              ext f
              simp only [Set.mem_setOf_eq, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
              exact ⟨fun h => h.2, fun h => ⟨hff h, h⟩⟩
            refine List.mem_filter.2 ⟨List.mem_sublists.2 (List.filter_sublist), ?_⟩
            rw [hset]
            simpa using hT
          · ext f
            simp only [Set.mem_setOf_eq, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
            exact ⟨fun h => ⟨hff h, h⟩, fun h => h.2⟩
        exact h2.of_agree (TnDesc.toTaskNetwork_wf e.2) (agree_tn hev)
      · -- a state of `mid'`
        have hcond := (List.mem_filter.1 hl'').2
        simp only [decide_eq_true_eq] at hcond
        exact ih hr₂ rfl (hcond.of_agree hwp hag)

end Complete

/-! ## Polynomial time -/

section PTs

theorem pt_ffacts : PT ffacts := by
  unfold ffacts
  exact PT.append (PT.fst.comp PT.snd) (PT.flatMap (PT.fst.comp PT.fst)
    (PT.flatMap (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))) (PT.fst.comp PT.snd)))

theorem pt_Mx : PT Mx := by
  have h := pt_two_pow_poly (4 * Polynomial.X + 8)
  exact h.of_eq fun p => by simp [Mx]

theorem pt_wfStates : PT fun x : FProbDesc × List (List ℕ) => wfStates x.1 x.2 := by
  unfold wfStates
  exact PT.and (PT.le (pt_sz.comp PT.snd) (pt_Mx.comp PT.fst))
    (PT.all PT.snd (PT.and (pt_nodupB PT.snd) (PT.all PT.snd
      (PT.elem (pt_ffacts.comp (PT.fst.comp (PT.fst.comp PT.fst))) PT.snd))))

theorem pt_tStep : PT tStep := by
  -- projections on `x : FProbDesc × TCfg × TCfg`
  have hP : PT fun x : FProbDesc × TCfg × TCfg => x.1 := PT.fst
  have hg : PT fun x : FProbDesc × TCfg × TCfg => x.2.1 := PT.fst.comp PT.snd
  have hg' : PT fun x : FProbDesc × TCfg × TCfg => x.2.2 := PT.snd.comp PT.snd
  have hk : PT fun x : FProbDesc × TCfg × TCfg => x.2.1.1 := PT.fst.comp hg
  have hc : PT fun x : FProbDesc × TCfg × TCfg => x.2.1.2.1 := PT.fst.comp (PT.snd.comp hg)
  have hs : PT fun x : FProbDesc × TCfg × TCfg => x.2.1.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp hg))
  have hd : PT fun x : FProbDesc × TCfg × TCfg => x.2.1.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hg)))
  have htgt : PT fun x : FProbDesc × TCfg × TCfg => x.2.1.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hg))))
  have hmid : PT fun x : FProbDesc × TCfg × TCfg => x.2.1.2.2.2.2.2 :=
    PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hg))))
  have hgmid : PT fun x : FProbDesc × TCfg × TCfg => x.2.2.2.2.2.2.2 :=
    PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hg'))))
  -- context `z : (FProbDesc × TCfg × TCfg) × ℕ`
  have zunc : PT fun z : (FProbDesc × TCfg × TCfg) × ℕ => unc z.1.2.1.2.2.2.1 z.2 :=
    pt_unc.comp (PT.pair (hd.comp PT.fst) PT.snd)
  have zl : PT fun z : (FProbDesc × TCfg × TCfg) × ℕ => lblOf z.1.2.1.2.2.2.1 z.2 :=
    pt_lblOf (hd.comp PT.fst) PT.snd
  have zprog : PT fun z : (FProbDesc × TCfg × TCfg) × ℕ => progDesc z.1.2.1.2.2.2.1 z.2 :=
    pt_progDesc.comp (PT.pair (hd.comp PT.fst) PT.snd)
  have hA : PT fun x : FProbDesc × TCfg × TCfg =>
      x.2.1.2.2.2.1.ids.any fun y => unc x.2.1.2.2.2.1 y && (lblOf x.2.1.2.2.2.1 y).1 &&
        decide (x.2.2 = (2, (lblOf x.2.1.2.2.2.1 y).2, x.2.1.2.2.1, progDesc x.2.1.2.2.2.1 y,
          x.2.1.2.2.2.2.1, x.2.2.2.2.2.2.2)) && wfStates x.1 x.2.2.2.2.2.2.2 :=
    PT.any (PT.fst.comp hd) (PT.and (PT.and (PT.and zunc (PT.fst.comp zl))
      (PT.eq (hg'.comp PT.fst) (PT.pair (PT.const 2) (PT.pair (PT.snd.comp zl)
        (PT.pair (hs.comp PT.fst) (PT.pair zprog (PT.pair (htgt.comp PT.fst)
          (hgmid.comp PT.fst))))))))
      (pt_wfStates.comp (PT.pair (hP.comp PT.fst) (hgmid.comp PT.fst))))
  have zarg : PT fun z : (FProbDesc × TCfg × TCfg) × ℕ =>
      ((z.1.1, (lblOf z.1.2.1.2.2.2.1 z.2).2), z.1.2.1.2.2.1) :=
    PT.pair (PT.pair (hP.comp PT.fst) (PT.snd.comp zl)) (hs.comp PT.fst)
  have hB : PT fun x : FProbDesc × TCfg × TCfg =>
      x.2.1.2.2.2.1.ids.any fun y => unc x.2.1.2.2.2.1 y && !(lblOf x.2.1.2.2.2.1 y).1 &&
        fApp x.1 (lblOf x.2.1.2.2.2.1 y).2 x.2.1.2.2.1 &&
        (outs x.1 (lblOf x.2.1.2.2.2.1 y).2 x.2.1.2.2.1).any fun s'' =>
          decide (x.2.2 = (0, 0, s'', progDesc x.2.1.2.2.2.1 y, x.2.1.2.2.2.2.1, [])) := by
    refine PT.any (PT.fst.comp hd) (PT.and (PT.and (PT.and zunc (PT.not (PT.fst.comp zl)))
      (pt_fApp.comp zarg)) (PT.any (pt_outs.comp zarg) ?_))
    exact PT.eq (hg'.comp (PT.fst.comp PT.fst)) (PT.pair (PT.const 0) (PT.pair (PT.const 0)
      (PT.pair PT.snd (PT.pair (zprog.comp PT.fst) (PT.pair (htgt.comp (PT.fst.comp PT.fst))
        (PT.const []))))))
  have hC : PT fun x : FProbDesc × TCfg × TCfg =>
      decide (x.2.2 ∈ (x.1.methods.filter fun e => e.1 == x.2.1.2.1).map fun e =>
        ((0, 0, x.2.1.2.2.1, e.2, x.2.1.2.2.2.2.1, []) : TCfg)) := by
    refine PT.elemL (I := fun _ => inferInstance) (PT.map (PT.filter (PT.snd.comp (PT.fst.comp hP))
      (PT.beqL (PT.fst.comp PT.snd) (hc.comp PT.fst))) ?_) hg'
    exact PT.pair (PT.const 0) (PT.pair (PT.const 0) (PT.pair (hs.comp PT.fst)
      (PT.pair (PT.snd.comp PT.snd) (PT.pair (htgt.comp PT.fst) (PT.const [])))))
  have hD : PT fun x : FProbDesc × TCfg × TCfg =>
      decide (x.2.2 = (1, x.2.1.2.1, x.2.1.2.2.1, emptyD, (false, x.2.1.2.2.2.2.2), [])) ||
        x.2.1.2.2.2.2.2.any fun l => decide (x.2.2 = (0, 0, l, x.2.1.2.2.2.1, x.2.1.2.2.2.2.1, [])) :=
    PT.or (PT.eq hg' (PT.pair (PT.const 1) (PT.pair hc (PT.pair hs (PT.pair (PT.const emptyD)
      (PT.pair (PT.pair (PT.const false) hmid) (PT.const [])))))))
      (PT.any hmid (PT.eq (hg'.comp PT.fst) (PT.pair (PT.const 0) (PT.pair (PT.const 0)
        (PT.pair PT.snd (PT.pair (hd.comp PT.fst) (PT.pair (htgt.comp PT.fst) (PT.const []))))))))
  exact (PT.cond (PT.beqL hk (PT.const 0)) (PT.or hA hB) (PT.cond (PT.beqL hk (PT.const 1)) hC
    (PT.cond (PT.beqL hk (PT.const 2)) hD (PT.const false)))).of_eq fun _ => rfl

theorem pt_tUni : PT tUni := by
  have hk : PT fun x : FProbDesc × TCfg => x.2.1 := PT.fst.comp PT.snd
  have hs : PT fun x : FProbDesc × TCfg => x.2.2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hd : PT fun x : FProbDesc × TCfg => x.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))
  have zl : PT fun z : (FProbDesc × TCfg) × ℕ => lblOf z.1.2.2.2.2.1 z.2 :=
    pt_lblOf (hd.comp PT.fst) PT.snd
  unfold tUni
  exact PT.or (PT.and (PT.beqL hk (PT.const 0)) (PT.any (PT.fst.comp hd)
    (PT.and (PT.and (pt_unc.comp (PT.pair (hd.comp PT.fst) PT.snd)) (PT.not (PT.fst.comp zl)))
      (pt_fApp.comp (PT.pair (PT.pair (PT.fst.comp PT.fst) (PT.snd.comp zl)) (hs.comp PT.fst))))))
    (PT.beqL hk (PT.const 2))

theorem pt_tAcc : PT tAcc := by
  have hk : PT fun x : FProbDesc × TCfg => x.2.1 := PT.fst.comp PT.snd
  have hs : PT fun x : FProbDesc × TCfg => x.2.2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hd : PT fun x : FProbDesc × TCfg => x.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))
  have htgt : PT fun x : FProbDesc × TCfg => x.2.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))))
  unfold tAcc inTgt sameSet
  exact PT.and (PT.and (PT.beqL hk (PT.const 0)) (PT.isEmpty (PT.fst.comp hd)))
    (PT.or (PT.fst.comp htgt) (PT.any (PT.snd.comp htgt) (PT.and
      (PT.all PT.snd (PT.elem (hs.comp (PT.fst.comp PT.fst)) PT.snd))
      (PT.all (hs.comp PT.fst) (PT.elem (PT.snd.comp PT.fst) PT.snd)))))

theorem pt_tInit : PT tInit := by
  unfold tInit tInit0
  exact PT.and (PT.and (FProbDesc.pt_validB.comp PT.fst) (pt_fTOB.comp PT.fst))
    (PT.eq PT.snd (PT.pair (PT.const 0) (PT.pair (PT.const 0) (PT.pair
      (PT.dedup (PT.fst.comp (PT.snd.comp PT.fst))) (PT.pair (PT.snd.comp (pt_initF.comp PT.fst))
        (PT.pair (PT.const _) (PT.const _)))))))

end PTs

end TO

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime

/-- **The ideas file, "Total order — Membership"**: strong method-based plan existence for
totally ordered problems (arbitrary recursion) is in `2-EXPTIME`. -/
theorem strongMP_TO_mem : HTN.Cx.EXPTIME2 (PlanExMP .strong FClass.TO) := by
  let q : Polynomial ℕ := 4 * Polynomial.X + 10
  have hq : ∀ n, q.eval n = 4 * n + 10 := fun n => by simp [q]
  have hbound : ∀ p : FProbDesc, TO.cfgBound p ≤ 2 ^ q.eval (sz p) := by
    intro p
    rw [hq]
    unfold TO.cfgBound TO.Mx
    set S := sz p
    have hX : S + 1 ≤ 2 ^ S := Nat.lt_two_pow_self
    have h1 : 2 ^ (4 * S + 10) = 4 * 2 ^ (4 * S + 8) := by
      rw [show 4 * S + 10 = 2 + (4 * S + 8) by ring, pow_add]; norm_num
    have h2 : 2 ^ (4 * S + 8) = 256 * (2 ^ S) ^ 4 := by
      rw [← pow_mul, show 4 * S + 8 = 8 + S * 4 by ring, pow_add]; norm_num
    rw [h1, h2]
    have h3 : 1 ≤ 2 ^ S := Nat.one_le_two_pow
    have h4 : (S + 1) ^ 2 ≤ (2 ^ S) ^ 2 := Nat.pow_le_pow_left hX 2
    have h5 : (2 ^ S) ^ 2 ≤ (2 ^ S) ^ 4 := Nat.pow_le_pow_right h3 (by norm_num)
    nlinarith
  refine inExp2Time_codeLang_of_andOr (α := FProbDesc) (σ := TO.TCfg)
    (Q := fun p => p.Valid ∧ FClass.TO p.toProblem ∧ p.toProblem.MPStrongSolvable)
    TO.pt_tInit TO.pt_tAcc TO.pt_tUni TO.pt_tStep q fun p => ?_
  have htgt : TO.tgtSet (true, []) = Set.univ := by ext; simp [TO.tgtSet]
  constructor
  · rintro ⟨hp, hTO, hsol⟩
    have hsz : ∀ g, TO.TReach p g → sz g ≤ 2 ^ q.eval (sz p) := fun g hg =>
      (TO.sz_le_of_tInv (TO.tInv_of_reach hp hTO hg)).trans (hbound p)
    refine ⟨TO.tInit0 p, hsz _ .refl, ?_, ?_⟩
    · simp [TO.tInit, (FProbDesc.validB_iff p).2 hp, (fTOB_iff hp).2 hTO]
    · have h := (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).1 hsol
      obtain ⟨n, hn⟩ := h.toH (FProbDesc.toProblem_wf hp).actions
      have h1 := Problem.mpProgTH_univ_iff.2 hn
      have h2 := h1.of_agree (FProbDesc.toProblem_wf hp).tnI (MPS.agree_initF hp)
      rw [MPS.init_state, ← htgt] at h2
      exact TO.tComplete hp hTO hsz n .refl rfl h2
  · rintro ⟨c₀, -, hi, hw⟩
    simp only [TO.tInit, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hv, hto⟩, rfl⟩ := hi
    have hp := (FProbDesc.validB_iff p).1 hv
    have hTO := (fTOB_iff hp).1 hto
    have hsz : ∀ g, TO.TReach p g → sz g ≤ 2 ^ q.eval (sz p) := fun g hg =>
      (TO.sz_le_of_tInv (TO.tInv_of_reach hp hTO hg)).trans (hbound p)
    refine ⟨hp, hTO, ?_⟩
    obtain ⟨n, hn⟩ := (TO.tSound hp hTO hsz hw .refl).1 rfl
    simp only [TO.tInit0, htgt] at hn
    have hinv := (TO.tInv_init hp hTO).d
    have h1 := (Problem.mpProgTH_univ_iff.1 hn).toProg
    have h2 := h1.isoVia hinv.wf (FProbDesc.toProblem_wf hp).tnI
      (MPS.isoVia_art (isoVia_id_of_agree (MPS.agree_initF hp).symm))
    have hi : p.toProblem.init = {f | f ∈ p.init.dedup} := MPS.init_state p
    rw [← hi] at h2
    exact (Problem.mpStrongSolvable_iff_mpProg (FProbDesc.toProblem_wf hp)).2 h2

end FOND
