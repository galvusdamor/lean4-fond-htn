import HtnComplexity.Article.CFGPrimrec
import HtnComplexity.Computable.AddRoot
/-!
# Undecidability of HTN plan existence (Section 4.1)

* **Theorem 4.1.1** (`HTN.Article.thm_4_1_1`): `PlanEx^UNRES-REC_htn` is undecidable.
* **Corollary 4.1.2** (`HTN.Article.cor_4_1_2`): undecidable already for the problems whose
  initial task network has at most two tasks and all of whose reachable methods are totally
  ordered with at most two tasks (`HTN.Article.UNRES₂`).
* **Corollary 4.1.3** (`HTN.Article.cor_4_1_3`): undecidable already for the problems with a
  totally ordered initial task network all of whose reachable methods but one are totally ordered
  (`HTN.Article.UNRES₃`).  As in the article, the problem of Thm. 4.1.1 is given a single initial
  compound task (Prop. 2.1.1) whose only method yields the two unordered start symbols.

Both follow the article: the intersection problem of context-free grammars
(`ComplexityTheory/CFG/Undec.lean`) reduces to plan existence by the encoding of
`HtnComplexity/Article/CFGEnc.lean`.  The article assumes Chomsky normal form; here the grammars
of the reduction have right-hand sides of length at most two, which is what Cor. 4.1.2 needs.
-/

namespace HTN

namespace Article

open CFG Syn CFGEnc Undec

/-- **Theorem 4.1.1.** `PlanEx^UNRES-REC_htn` is undecidable. -/
theorem thm_4_1_1 : ¬ Cx.Decidable (PlanEx UNRES) :=
  not_decidable_planEx_of not_computablePred_inter_fixed
    (f := fun g => cfgProb gram₁ g)
    (primrec_cfgProb.comp (Primrec.const gram₁) Primrec.id).to_comp
    (fun _ => ⟨valid_cfgProb, trivial⟩) (fun _ => solvable_cfgProb_iff)

/-! ### Corollary 4.1.2 -/

/-- The class of Cor. 4.1.2: at most two tasks in the initial task network, and every reachable
method totally ordered with at most two tasks. -/
def UNRES₂ : PClass := fun P =>
  P.tnI.T.card ≤ 2 ∧ ∀ m, P.toPos.ReachableMethod m →
    m.subtasks.IsTotallyOrdered ∧ m.subtasks.T.card ≤ 2

theorem cellIds_single (l : List (Bool × ℕ)) :
    cellIds [l] = (List.range l.length).map (Nat.pair 0) := by
  simp [cellIds, gridRow]

theorem gridDescFullOf_single_T (l : List (ℕ ⊕ ℕ)) :
    (gridDescFullOf id id [l]).toTaskNetwork.T = ((List.range l.length).map (Nat.pair 0)).toFinset := by
  show (cellIds [l.map (encLabel id id)]).toFinset = _
  rw [cellIds_single]; simp

theorem card_gridDescFullOf_single (l : List (ℕ ⊕ ℕ)) :
    (gridDescFullOf id id [l]).toTaskNetwork.T.card = l.length := by
  rw [gridDescFullOf_single_T, List.toFinset_card_of_nodup]
  · simp
  · exact List.Nodup.map (fun a b h => (Nat.pair_eq_pair.1 h).2) List.nodup_range

theorem isTotallyOrdered_gridDescFullOf_single (l : List (ℕ ⊕ ℕ)) :
    (gridDescFullOf id id [l]).toTaskNetwork.IsTotallyOrdered := by
  intro x hx y hy hxy
  rw [gridDescFullOf_single_T] at hx hy
  simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hx hy
  obtain ⟨j, hj, rfl⟩ := hx
  obtain ⟨j', hj', rfl⟩ := hy
  rw [toTaskNetwork_gridDescFullOf]
  unfold gridDescOf
  rw [gridDesc_ord, gridDesc_ord]
  have hne : j ≠ j' := fun h => hxy (by rw [h])
  have hrow : (gridRow ([l].map fun row => row.map (encLabel id id)) 0).length = l.length := by
    simp [gridRow]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact Or.inl ⟨0, j, j', by simp, h, by rw [hrow]; exact hj', rfl, rfl⟩
  · exact Or.inr ⟨0, j', j, by simp, h, by rw [hrow]; exact hj, rfl, rfl⟩

theorem card_cfgInst_tnI (g₁ g₂ : Grammar) :
    (gridDescFullOf id id [[Sum.inr (2 * g₁.start)], [Sum.inr (2 * g₂.start + 1)]]).toTaskNetwork.T.card
      ≤ 2 := by
  show (cellIds _).toFinset.card ≤ 2
  refine (List.toFinset_card_le _).trans ?_
  simp [cellIds, gridRow, List.sum_range_succ]

/-- The problems of the reduction from binary grammars lie in the class of Cor. 4.1.2. -/
theorem unres₂_cfgProb {g₁ g₂ : Grammar} (h₁ : g₁.IsBinary) (h₂ : g₂.IsBinary) :
    UNRES₂ (cfgProb g₁ g₂).toProblem := by
  refine ⟨card_cfgInst_tnI g₁ g₂, ?_⟩
  rintro m ⟨hm, -⟩
  obtain ⟨e, he, rfl⟩ := hm
  simp only [cfgProb, ofSyn, ProbDesc.methods, cfgDom, DomDesc.methods, List.mem_append,
    List.mem_map] at he
  rcases he with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · refine ⟨isTotallyOrdered_gridDescFullOf_single _, ?_⟩
    show (gridDescFullOf id id [r.2.map (trS 0)]).toTaskNetwork.T.card ≤ 2
    rw [card_gridDescFullOf_single, List.length_map]; exact h₁ r hr
  · refine ⟨isTotallyOrdered_gridDescFullOf_single _, ?_⟩
    show (gridDescFullOf id id [r.2.map (trS 1)]).toTaskNetwork.T.card ≤ 2
    rw [card_gridDescFullOf_single, List.length_map]; exact h₂ r hr

/-- **Corollary 4.1.2.** Plan existence is undecidable already for problems whose initial task
network has at most two tasks and all of whose reachable methods are totally ordered and have at
most two tasks. -/
theorem cor_4_1_2 : ¬ Cx.Decidable (PlanEx UNRES₂) :=
  not_decidable_planEx_of not_computablePred_inter_stack
    (f := fun s => cfgProb gram₁ (gram undecTSM true s))
    (primrec_cfgProb.comp (Primrec.const gram₁) (primrec_gram undecTSM true)).to_comp
    (fun _ => ⟨valid_cfgProb, unres₂_cfgProb isBinary_gram isBinary_gram⟩)
    (fun _ => solvable_cfgProb_iff)

/-! ### Corollary 4.1.3 -/

/-- The class of Cor. 4.1.3: a totally ordered initial task network, and all reachable methods
but one totally ordered. -/
def UNRES₃ : PClass := fun P =>
  P.tnI.IsTotallyOrdered ∧ ∃ m₀ : Method ℕ ℕ ℕ, ∀ m, P.toPos.ReachableMethod m → m ≠ m₀ →
    m.subtasks.IsTotallyOrdered

namespace CFGEnc

/-- The nonterminals of a grammar (the start symbol, the left- and right-hand sides). -/
def nts (g : Grammar) : List ℕ :=
  g.1 :: g.2.flatMap fun r => r.1 :: r.2.flatMap fun x => Sum.elim (fun _ => []) (fun X => [X]) x

/-- A fresh compound name: even and above all names of the first grammar. -/
def root (g₁ : Grammar) : ℕ := 2 * ((nts g₁).foldr max 0 + 1)

/-- **The rooted encoding.** -/
def cfgProbR (g₁ g₂ : Grammar) : ProbDesc :=
  ofSyn (addRootDom (root g₁) (cfgInst g₁ g₂).tnI (cfgDom g₁ g₂))
    (addRootInst (root g₁) (cfgInst g₁ g₂))

theorem mem_labelList_true {l : List (ℕ × Bool × ℕ)} {i c : ℕ} (h : c ∈ TnDesc.labelList true l i) :
    (i, true, c) ∈ l := by
  induction l with
  | nil => simp [TnDesc.labelList] at h
  | cons p l ih =>
    obtain ⟨n, b, e⟩ := p
    simp only [TnDesc.labelList, List.foldr_cons] at h
    by_cases hn : n = i
    · subst hn
      simp only [if_true] at h
      by_cases hb : b = true
      · subst hb; simp at h; subst h; exact List.mem_cons_self
      · simp [hb] at h
    · simp only [hn, if_false] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem mem_compoundNames_gridDescFullOf {ls : List (List (ℕ ⊕ ℕ))} {c : ℕ}
    (h : c ∈ (gridDescFullOf id id ls).compoundNames) : ∃ row ∈ ls, Sum.inr c ∈ row := by
  unfold TnDesc.compoundNames at h
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 h
  have hmem := mem_labelList_true hi
  simp only [gridDescFullOf, gridDescFull, TnDesc.lbl, cellLbl, List.mem_flatMap, List.mem_map,
    List.mem_range] at hmem
  obtain ⟨k, hk, j, hj, hp⟩ := hmem
  obtain ⟨-, he⟩ := Prod.mk.inj hp
  have hk' : k < ls.length := by simpa using hk
  have hrow : gridRow (ls.map fun row => row.map (encLabel id id)) k =
      (ls[k]).map (encLabel id id) := by
    simp [gridRow, List.getD_eq_getElem _ _ hk, hk']
  rw [hrow] at hj he
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map] at he
  refine ⟨ls[k], List.getElem_mem hk', ?_⟩
  have hx := List.getElem_mem (l := ls[k]) (by simpa using hj)
  generalize (ls[k])[j]'(by simpa using hj) = x at he hx
  rcases x with a | X
  · simp [encLabel] at he
  · simp only [encLabel, id, Prod.mk.injEq, true_and] at he
    rw [← he]; exact hx

theorem le_foldr_nts {g : Grammar} {X : ℕ} (h : X ∈ nts g) : X < (nts g).foldr max 0 + 1 :=
  Nat.lt_succ_of_le (le_foldr_max h)

theorem trS0_ne_root {g₁ : Grammar} {r : Rule} (hr : r ∈ g₁.rules) {x : Sym}
    (hx : x ∈ r.2) : trS 0 x ≠ Sum.inr (root g₁) := by
  rcases x with a | X
  · simp [trS]
  · simp only [trS, ne_eq, Sum.inr.injEq, root]
    have : X ∈ nts g₁ := List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨r, hr,
      List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨Sum.inr X, hx, by simp⟩)⟩)
    have := le_foldr_nts this
    omega

theorem trS1_ne_root {g₁ : Grammar} (x : Sym) : trS 1 x ≠ Sum.inr (root g₁) := by
  rcases x with a | X
  · simp [trS]
  · simp only [trS, ne_eq, Sum.inr.injEq, root]; omega

theorem fresh_root {g₁ g₂ : Grammar} :
    (∀ e ∈ (cfgDom g₁ g₂).methods, e.1 ≠ root g₁) ∧
    (∀ e ∈ (cfgDom g₁ g₂).methods, root g₁ ∉ e.2.compoundNames) ∧
    root g₁ ∉ (cfgInst g₁ g₂).tnI.compoundNames := by
  have hstart : g₁.1 ∈ nts g₁ := List.mem_cons_self
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simp only [cfgDom, DomDesc.methods, List.mem_append, List.mem_map] at he
    rcases he with ⟨r, hr, rfl⟩ | ⟨r, -, rfl⟩
    · have : r.1 ∈ nts g₁ := List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨r, hr, List.mem_cons_self⟩)
      have := le_foldr_nts this
      simp only [methD, root]; omega
    · simp only [methD, root]; omega
  · intro e he hc
    simp only [cfgDom, DomDesc.methods, List.mem_append, List.mem_map] at he
    rcases he with ⟨r, hr, rfl⟩ | ⟨r, -, rfl⟩
    · obtain ⟨row, hrow, hx⟩ := mem_compoundNames_gridDescFullOf hc
      simp only [List.mem_singleton] at hrow; subst hrow
      obtain ⟨x, hx, he⟩ := List.mem_map.1 hx
      exact trS0_ne_root hr hx he
    · obtain ⟨row, hrow, hx⟩ := mem_compoundNames_gridDescFullOf hc
      simp only [List.mem_singleton] at hrow; subst hrow
      obtain ⟨x, -, he⟩ := List.mem_map.1 hx
      exact trS1_ne_root x he
  · intro hc
    obtain ⟨row, hrow, hx⟩ := mem_compoundNames_gridDescFullOf hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    have := le_foldr_nts hstart
    have hs : g₁.start = g₁.1 := rfl
    rcases hrow with rfl | rfl <;> simp only [List.mem_singleton, Sum.inr.injEq, root] at hx <;>
      omega

/-- **The rooted encoding has a solution iff the grammars have a common word.** -/
theorem solvable_cfgProbR_iff {g₁ g₂ : Grammar} :
    (cfgProbR g₁ g₂).toProblem.Solvable ↔ Inter g₁ g₂ := by
  rw [cfgProbR, solvable_ofSyn_iff]
  obtain ⟨h₁, h₂, h₃⟩ := fresh_root (g₁ := g₁) (g₂ := g₂)
  rw [solvable_addRoot_iff h₁ h₂ h₃]
  exact solvable_cfgDom_iff

theorem tnValid_singleTn {prim : ℕ → Prop} (r : ℕ) : TnValid prim (singleTn r) where
  nodup := by simp [singleTn, TnDesc.ids]
  ord_mem := by simp [singleTn, TnDesc.ordList]
  irrefl := by simp [singleTn, TnDesc.ordList]
  trans := by simp [singleTn, TnDesc.ordList]
  lbl_perm := by simp [singleTn, TnDesc.lbl, TnDesc.ids]
  prim_ok := by simp [singleTn, TnDesc.lbl]

theorem valid_cfgProbR {g₁ g₂ : Grammar} : (cfgProbR g₁ g₂).Valid := by
  have hv := valid_cfgProb (g₁ := g₁) (g₂ := g₂)
  refine valid_ofSyn ?_ (tnValid_singleTn _) ?_
  · simpa [cfgProb, ofSyn, ProbDesc.actions, ofSynAct, ActDesc.name, Function.comp_def] using
      hv.names_nodup
  · intro m hm
    simp only [addRootDom_methods, List.mem_append, List.mem_singleton] at hm
    have hdecl : (cfgProb g₁ g₂).Declared = (· ∈ (cfgDom g₁ g₂).actions.map Prod.fst) := by
      funext a
      simp [ProbDesc.Declared, cfgProb, ofSyn, ProbDesc.actions, ofSynAct, ActDesc.name,
        Function.comp_def]
    rcases hm with hm | rfl
    · have := hv.methods m (by simpa [cfgProb, ofSyn, ProbDesc.methods] using hm)
      rwa [hdecl] at this
    · have := hv.tnI
      rw [hdecl] at this
      exact this

theorem unres₃_cfgProbR {g₁ g₂ : Grammar} : UNRES₃ (cfgProbR g₁ g₂).toProblem := by
  refine ⟨?_, MethodDesc.toMethod (root g₁, (cfgInst g₁ g₂).tnI), ?_⟩
  · intro x hx y hy hxy
    exfalso
    have hx' : x = 0 := by
      have : x ∈ ([0] : List ℕ).toFinset := hx
      simpa using this
    have hy' : y = 0 := by
      have : y ∈ ([0] : List ℕ).toFinset := hy
      simpa using this
    exact hxy (hx'.trans hy'.symm)
  · rintro m ⟨⟨e, he, rfl⟩, -⟩ hne
    simp only [cfgProbR, ofSyn, ProbDesc.methods, addRootDom_methods, List.mem_append,
      List.mem_singleton] at he
    rcases he with he | rfl
    · simp only [cfgDom, DomDesc.methods, List.mem_append, List.mem_map] at he
      rcases he with ⟨r, -, rfl⟩ | ⟨r, -, rfl⟩ <;> exact isTotallyOrdered_gridDescFullOf_single _
    · exact absurd rfl hne

theorem primrec_nts : Primrec nts := by
  have hel : Primrec fun p : (Grammar × Rule) × Sym =>
      Sum.elim (fun _ => ([] : List ℕ)) (fun X => [X]) p.2 := by
    have : (fun p : (Grammar × Rule) × Sym => Sum.elim (fun _ => ([] : List ℕ)) (fun X => [X]) p.2) =
        fun p => Sum.casesOn p.2 (fun _ => ([] : List ℕ)) (fun X => [X]) := by
      funext p; cases p.2 <;> rfl
    rw [this]
    exact Primrec.sumCasesOn Primrec.snd (Primrec.const []).to₂
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂
  have hin : Primrec fun p : Grammar × Rule =>
      p.2.1 :: p.2.2.flatMap fun x => Sum.elim (fun _ => []) (fun X => [X]) x :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) hel.to₂)
  exact Primrec.list_cons.comp Primrec.fst (Primrec.list_flatMap Primrec.snd hin.to₂)

theorem primrec_root : Primrec root := by
  unfold root
  exact Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp (Primrec.list_foldr primrec_nts
    (Primrec.const 0) (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂))

theorem primrec_cfgProbR : Primrec₂ cfgProbR := by
  unfold cfgProbR addRootDom addRootInst singleTn
  have hr : Primrec fun p : Grammar × Grammar => root p.1 := primrec_root.comp Primrec.fst
  have hd := primrec_cfgDom
  have hq := primrec_cfgInst
  refine primrec_ofSyn.comp ?_ ?_
  · exact Primrec.pair (Primrec.fst.comp hd) (Primrec.list_append.comp (Primrec.snd.comp hd)
      (Primrec.list_cons.comp (Primrec.pair hr (Primrec.snd.comp (Primrec.snd.comp hq)))
        (Primrec.const [])))
  · exact Primrec.pair (Primrec.fst.comp hq) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hq))
      (Primrec.pair (Primrec.const [0]) (Primrec.pair (Primrec.const [])
        (Primrec.list_cons.comp (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) hr))
          (Primrec.const [])))))

end CFGEnc

/-- **Corollary 4.1.3.** Plan existence is undecidable already for problems with a totally
ordered initial task network all of whose reachable methods but one are totally ordered. -/
theorem cor_4_1_3 : ¬ Cx.Decidable (PlanEx UNRES₃) :=
  not_decidable_planEx_of not_computablePred_inter_fixed
    (f := fun g => cfgProbR gram₁ g)
    (primrec_cfgProbR.comp (Primrec.const gram₁) Primrec.id).to_comp
    (fun _ => ⟨valid_cfgProbR, unres₃_cfgProbR⟩) (fun _ => solvable_cfgProbR_iff)

end Article

end HTN
