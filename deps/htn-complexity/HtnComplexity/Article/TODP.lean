import HtnComplexity.Article.TOVec
/-!
# The dynamic program of Thm. 4.2.1

The table (`HTN.Article.dpTab`) consists of triples `(v, n, v')` of state vectors and a raw task
name: `n` refines from the state of `v` into the state of `v'`.  One round
(`HTN.Article.dpStep`) keeps the candidate triples whose rule holds in the current table: a
primitive name by its action (`HTN.Article.okV`, `HTN.Article.apV`), a compound name if some
method of it has its tasks, in the order of `HTN.Syn.TnDesc.lin`, refine one after the other in
the table (`HTN.Article.chainSet`).  `|candidates| + 1` rounds from the empty table reach the
least fixpoint (`HTN.Article.dpStep_dpTab`).

* `HTN.Article.sound_dpTab` — a triple of the table for a reachable or primitive name is a
  refinement (`HTN.Article.RefT`), for problems whose reachable methods are totally ordered;
* `HTN.Article.complete_dpTab` — every refinement by a valid tree of such a name, between states
  of relevant facts, is in the table.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- A triple of the table. -/
abbrev Trip : Type := List Bool × (Bool × ℕ) × List Bool

/-- The state of a vector, as a set. -/
def setV (V : List ℕ) (v : List Bool) : Set ℕ := {f | f ∈ sv V v}

section Defs

variable (p : ProbDesc) (allV : List (List Bool))

/-- The vector after the action `a`. -/
def apV (a : ℕ) (v : List Bool) : List Bool :=
  vecOf (pfacts p) (runStep p (true, sv (pfacts p) v) a).2

/-- The action `a` is applicable in the state of `v`. -/
def okV (a : ℕ) (v : List Bool) : Bool := (runStep p (true, sv (pfacts p) v) a).1

/-- The vectors reached from `S` by a triple for `n` of the table `X`. -/
def stepSet (X : List Trip) (S : List (List Bool)) (n : Bool × ℕ) : List (List Bool) :=
  allV.filter fun t => S.any fun u => decide ((u, n, t) ∈ X)

/-- The vectors reached from `S` by the tasks of `t`, one after the other. -/
def chainSet (X : List Trip) (t : TnDesc) (S : List (List Bool)) : List (List Bool) :=
  (TnDesc.lin t).foldl (fun S x => stepSet allV X S (lblOf t x)) S

/-- **The rule of a triple.** -/
def ruleB (X : List Trip) (q : Trip) : Bool :=
  bif q.2.1.1 then p.methods.any fun e => (e.1 == q.2.1.2) && decide (q.2.2 ∈ chainSet allV X e.2 [q.1])
  else okV p q.2.1.2 q.1 && (apV p q.2.1.2 q.1 == q.2.2)

/-- The raw names. -/
def namesB : List (Bool × ℕ) := (numsOf p).flatMap fun x => [(false, x), (true, x)]

/-- The candidate triples. -/
def cand : List Trip :=
  allV.flatMap fun v => (namesB p).flatMap fun n => allV.map fun v' => (v, n, v')

/-- **One round.** -/
def dpStep (X : List Trip) : List Trip := (cand p allV).filter (ruleB p allV X)

/-- **The table**: `|candidates| + 1` rounds from the empty table. -/
def dpTab : List Trip := (cand p allV ++ [default]).foldl (fun X _ => dpStep p allV X) []

end Defs

variable {p : ProbDesc} {allV : List (List Bool)}

/-! ### Chains in the table -/

/-- The tasks `l`, labelled by `lab`, are chained by triples of `X`. -/
inductive ChainX (X : List Trip) (allV : List (List Bool)) (lab : ℕ → Bool × ℕ) :
    List ℕ → List Bool → List Bool → Prop
  | nil (u : List Bool) : ChainX X allV lab [] u u
  | cons {x : ℕ} {l : List ℕ} {u u₁ w : List Bool} (h : (u, lab x, u₁) ∈ X) (h₁ : u₁ ∈ allV)
      (h₂ : ChainX X allV lab l u₁ w) : ChainX X allV lab (x :: l) u w

theorem mem_stepSet {X : List Trip} {S : List (List Bool)} {n : Bool × ℕ} {t : List Bool} :
    t ∈ stepSet allV X S n ↔ t ∈ allV ∧ ∃ u ∈ S, (u, n, t) ∈ X := by
  simp [stepSet]

theorem mem_foldl_stepSet {X : List Trip} {lab : ℕ → Bool × ℕ} : ∀ (l : List ℕ)
    (S : List (List Bool)) (w : List Bool),
    w ∈ l.foldl (fun S x => stepSet allV X S (lab x)) S ↔ ∃ u ∈ S, ChainX X allV lab l u w
  | [], S, w => by
    simp only [List.foldl_nil]
    exact ⟨fun h => ⟨w, h, .nil w⟩, fun ⟨u, hu, hc⟩ => by cases hc; exact hu⟩
  | x :: l, S, w => by
    rw [List.foldl_cons, mem_foldl_stepSet l]
    constructor
    · rintro ⟨u₁, hu₁, hc⟩
      obtain ⟨hall, u, hu, hx⟩ := mem_stepSet.1 hu₁
      exact ⟨u, hu, .cons hx hall hc⟩
    · rintro ⟨u, hu, hc⟩
      cases hc with
      | cons hx hall hc => exact ⟨_, mem_stepSet.2 ⟨hall, u, hu, hx⟩, hc⟩

theorem mem_chainSet {X : List Trip} {t : TnDesc} {S : List (List Bool)} {w : List Bool} :
    w ∈ chainSet allV X t S ↔ ∃ u ∈ S, ChainX X allV (lblOf t) (TnDesc.lin t) u w :=
  mem_foldl_stepSet _ _ _

theorem ChainX.mono {X Y : List Trip} (hXY : ∀ q ∈ X, q ∈ Y) {lab : ℕ → Bool × ℕ} {l : List ℕ}
    {u w : List Bool} (h : ChainX X allV lab l u w) : ChainX Y allV lab l u w := by
  induction h with
  | nil u => exact .nil u
  | cons hx hall _ ih => exact .cons (hXY _ hx) hall ih

theorem ruleB_mono {X Y : List Trip} (hXY : ∀ q ∈ X, q ∈ Y) {q : Trip} (h : ruleB p allV X q = true) :
    ruleB p allV Y q = true := by
  unfold ruleB at h ⊢
  cases hq : q.2.1.1
  · simpa [hq] using h
  · simp only [hq, cond_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      at h ⊢
    obtain ⟨e, he, h1, h2⟩ := h
    obtain ⟨u, hu, hc⟩ := mem_chainSet.1 h2
    exact ⟨e, he, h1, mem_chainSet.2 ⟨u, hu, hc.mono hXY⟩⟩

theorem ruleB_congr {X Y : List Trip} (hXY : ∀ q, q ∈ X ↔ q ∈ Y) : ruleB p allV X = ruleB p allV Y := by
  have : X.Subset Y ∧ Y.Subset X := ⟨fun q h => (hXY q).1 h, fun q h => (hXY q).2 h⟩
  funext q
  rw [Bool.eq_iff_iff]
  exact ⟨ruleB_mono this.1, ruleB_mono this.2⟩

/-! ### Stabilisation -/

theorem dpTab_eq : dpTab p allV = (dpStep p allV)^[(cand p allV).length + 1] [] := by
  rw [dpTab, foldl_const_iterate]; simp

theorem iterate_mono (k : ℕ) : ∀ q ∈ (dpStep p allV)^[k] [], q ∈ (dpStep p allV)^[k + 1] [] := by
  induction k with
  | zero => intro q h; simp at h
  | succ k ih =>
    intro q h
    rw [Function.iterate_succ_apply'] at h ⊢
    obtain ⟨hc, hr⟩ := List.mem_filter.1 h
    exact List.mem_filter.2 ⟨hc, ruleB_mono ih hr⟩

theorem iterate_sub (k : ℕ) : ∀ q ∈ (dpStep p allV)^[k] [], q ∈ cand p allV := by
  cases k with
  | zero => intro q h; simp at h
  | succ k =>
    intro q h
    rw [Function.iterate_succ_apply'] at h
    exact (List.mem_filter.1 h).1

/-- The number of candidates in the table after `k` rounds. -/
def cnt (p : ProbDesc) (allV : List (List Bool)) (k : ℕ) : ℕ :=
  ((cand p allV).filter fun q => decide (q ∈ (dpStep p allV)^[k] [])).length

theorem cnt_le (k : ℕ) : cnt p allV k ≤ (cand p allV).length := List.length_filter_le _ _

theorem cnt_mono (k : ℕ) : cnt p allV k ≤ cnt p allV (k + 1) :=
  length_filter_le_of_imp fun q _ h => by simpa using iterate_mono k q (by simpa using h)

theorem stable_of_cnt {k : ℕ} (h : cnt p allV (k + 1) ≤ cnt p allV k) :
    ∀ q, q ∈ (dpStep p allV)^[k + 1] [] ↔ q ∈ (dpStep p allV)^[k] [] := by
  intro q
  refine ⟨fun hq => ?_, iterate_mono k q⟩
  by_contra hn
  have := length_filter_lt (l := cand p allV) (p := fun q => decide (q ∈ (dpStep p allV)^[k] []))
    (q := fun q => decide (q ∈ (dpStep p allV)^[k + 1] [])) (x := q)
    (fun r _ hr => by simpa using iterate_mono k r (by simpa using hr)) (iterate_sub _ q hq)
    (by simpa using hq) (by simpa using hn)
  unfold cnt at h
  omega

/-- **The table is a fixpoint of a round.** -/
theorem dpStep_dpTab : ∀ q, q ∈ dpStep p allV (dpTab p allV) ↔ q ∈ dpTab p allV := by
  set N := (cand p allV).length
  obtain ⟨k, hk, hst⟩ : ∃ k ≤ N, ∀ q, q ∈ (dpStep p allV)^[k + 1] [] ↔ q ∈ (dpStep p allV)^[k] [] := by
    by_contra hn
    have : ∀ k ≤ N + 1, k ≤ cnt p allV k := by
      intro k hk'
      induction k with
      | zero => exact Nat.zero_le _
      | succ k ih =>
        have h1 := ih (by omega)
        have h2 := cnt_mono (p := p) (allV := allV) k
        rcases Nat.lt_or_ge (cnt p allV k) (cnt p allV (k + 1)) with h | h
        · omega
        · exact absurd ⟨k, by omega, stable_of_cnt h⟩ hn
    have := this (N + 1) le_rfl
    have := cnt_le (p := p) (allV := allV) (N + 1)
    omega
  -- from `k` on, the iteration is constant
  have hconst : ∀ j, (dpStep p allV)^[k + 1 + j] [] = (dpStep p allV)^[k + 1] [] := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have e : dpStep p allV ((dpStep p allV)^[k + 1] []) = dpStep p allV ((dpStep p allV)^[k] []) := by
        exact congrArg (fun r => (cand p allV).filter r) (ruleB_congr hst)
      rw [show k + 1 + (j + 1) = (k + 1 + j) + 1 by omega, Function.iterate_succ_apply', ih, e]
      exact (Function.iterate_succ_apply' _ _ _).symm
  intro q
  rw [dpTab_eq, ← Function.iterate_succ_apply' (dpStep p allV)]
  have e1 : ((cand p allV).length + 1).succ = k + 1 + ((cand p allV).length + 1 - k) := by omega
  rw [e1, hconst]
  have e2 : (cand p allV).length + 1 = k + 1 + ((cand p allV).length - k) := by omega
  rw [e2, hconst]

/-! ### Soundness and completeness -/

/-- A raw name is primitive or a reachable compound name. -/
def RP (p : ProbDesc) (n : Bool × ℕ) : Prop := n.1 = true → p.toProblem.toPos.ReachableName n.2

open Classical in
/-- The vector of a set of facts. -/
noncomputable def vecSet (V : List ℕ) (S : Set ℕ) : List Bool := V.map fun f => decide (f ∈ S)

theorem setV_vecSet {V : List ℕ} {S : Set ℕ} (h : S ⊆ {f | f ∈ V}) : setV V (vecSet V S) = S := by
  ext f
  simp only [setV, vecSet, sv_map, List.mem_filter, decide_eq_true_eq, Set.mem_setOf_eq]
  exact ⟨fun h' => h'.2, fun h' => ⟨h h', h'⟩⟩

theorem vecSet_setV {V : List ℕ} (hV : V.Nodup) {u : List Bool} (hu : u.length = V.length) :
    vecSet V (setV V u) = u := by
  conv_rhs => rw [← vecOf_sv hV hu]
  unfold vecSet vecOf setV
  refine List.map_congr_left fun f _ => ?_
  by_cases h : f ∈ sv V u <;> simp [h]

theorem setV_sub (V : List ℕ) (u : List Bool) : setV V u ⊆ {f | f ∈ V} := fun _ h => sv_sub h

theorem toSum_lblOf (t : TnDesc) : (fun y => toSum (lblOf t y)) = t.label := by
  funext y; exact (label_eq_toSum t y).symm

variable (hp : p.Valid) (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length)
  (hTO : ∀ e ∈ p.methods, p.toProblem.toPos.ReachableName e.1 → e.2.toTaskNetwork.IsTotallyOrdered)
include hp hall hTO

theorem okV_iff {a : ℕ} {v : List Bool} :
    okV p a v = true ↔ (p.toProblem.δ a).Applicable (setV (pfacts p) v) := by
  rw [okV, runStep_flag]; simp [setV]

theorem setV_apV {a : ℕ} {v : List Bool} :
    setV (pfacts p) (apV p a v) = (p.toProblem.δ a).apply (setV (pfacts p) v) := by
  ext f
  have h1 := runStep_state p true (sv (pfacts p) v) a
  simp only [setV, apV, Set.mem_setOf_eq, mem_sv_vecOf]
  constructor
  · rintro ⟨-, hf⟩
    have : f ∈ {f | f ∈ (runStep p (true, sv (pfacts p) v) a).2} := hf
    rwa [h1] at this
  · intro hf
    have hV := apply_subset_pfacts p a (setV_sub (pfacts p) v) hf
    have : f ∈ (p.toProblem.δ a).apply {f | f ∈ sv (pfacts p) v} := hf
    rw [← h1] at this
    exact ⟨hV, this⟩

theorem rp_child {e : MethodDesc} (he : e ∈ p.methods) (hr : p.toProblem.toPos.ReachableName e.1)
    {x : ℕ} (hx : x ∈ e.2.ids) : RP p (lblOf e.2 x) := by
  intro hb
  have hα : (MethodDesc.toMethod e).subtasks.α x = Sum.inr (lblOf e.2 x).2 :=
    label_eq_inr.2 (Prod.ext hb rfl)
  have hxT : x ∈ (MethodDesc.toMethod e).subtasks.T := by
    simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hx
  exact HTN.Problem.ReachableName.method
    (show MethodDesc.toMethod e ∈ p.toProblem.methods from ⟨e, he, rfl⟩) hr hxT hα

theorem chainT_of_chainX {X : List Trip}
    (hX : ∀ q ∈ X, RP p q.2.1 → RefT p (toSum q.2.1) (setV (pfacts p) q.1) (setV (pfacts p) q.2.2))
    {lab : ℕ → Bool × ℕ} {l : List ℕ} {u w : List Bool} (hl : ∀ y ∈ l, RP p (lab y))
    (h : ChainX X allV lab l u w) :
    ChainT p (fun y => toSum (lab y)) l (setV (pfacts p) u) (setV (pfacts p) w) := by
  induction h with
  | nil u => exact .nil _
  | @cons x l u u₁ w hx _ _ ih =>
    exact .cons (hX _ hx (hl x (by simp))) (ih fun y hy => hl y (by simp [hy]))

/-- **Soundness of the table.** -/
theorem sound_iter : ∀ k, ∀ q ∈ (dpStep p allV)^[k] [], RP p q.2.1 →
    RefT p (toSum q.2.1) (setV (pfacts p) q.1) (setV (pfacts p) q.2.2) := by
  intro k
  induction k with
  | zero => intro q h; simp at h
  | succ k ih =>
    intro q h hrp
    rw [Function.iterate_succ_apply'] at h
    obtain ⟨-, hr⟩ := List.mem_filter.1 h
    obtain ⟨v, ⟨b, x⟩, v'⟩ := q
    unfold ruleB at hr
    cases b
    · simp only [cond_false, Bool.and_eq_true, beq_iff_eq] at hr
      obtain ⟨hok, rfl⟩ := hr
      exact refT_inl_iff.2 ⟨(okV_iff hp hall hTO).1 hok, setV_apV hp hall hTO⟩
    · simp only [cond_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      obtain ⟨e, he, rfl, hc⟩ := hr
      have hreach : p.toProblem.toPos.ReachableName e.1 := hrp rfl
      obtain ⟨u, hu, hcx⟩ := mem_chainSet.1 hc
      rw [List.mem_singleton] at hu
      subst hu
      have hch := chainT_of_chainX hp hall hTO ih
        (fun y hy => rp_child hp hall hTO he hreach ((TnDesc.isLinearization_lin
          (hTO e he hreach)).2.1 y |>.1 hy |> fun h => by simpa [TnDesc.toTaskNetwork] using h)) hcx
      rw [toSum_lblOf] at hch
      exact refT_of_chain he (hTO e he hreach) hch

omit hp hall hTO in
theorem mem_cand {v v' : List Bool} {n : Bool × ℕ} (hv : v ∈ allV) (hv' : v' ∈ allV)
    (hn : n.2 ∈ numsOf p) : (v, n, v') ∈ cand p allV := by
  refine List.mem_flatMap.2 ⟨v, hv, List.mem_flatMap.2 ⟨n, ?_, List.mem_map.2 ⟨v', hv', rfl⟩⟩⟩
  obtain ⟨b, x⟩ := n
  exact List.mem_flatMap.2 ⟨x, hn, by cases b <;> simp⟩

theorem vecSet_mem (S : Set ℕ) : vecSet (pfacts p) S ∈ allV := by
  rw [hall]; simp [vecSet]

theorem mem_dpTab_of_rule {q : Trip} (hc : q ∈ cand p allV) (hr : ruleB p allV (dpTab p allV) q = true) :
    q ∈ dpTab p allV :=
  (dpStep_dpTab q).1 (List.mem_filter.2 ⟨hc, hr⟩)

/-- **Completeness of the table.** -/
theorem complete_dpTab : ∀ (dt : DTree ℕ ℕ ℕ) (n : Bool × ℕ) (v : List Bool) (S' : Set ℕ)
    (ys : List ℕ), dt.Valid p.toProblem.methods (toSum n) → dt.Yield ys →
    p.toProblem.Run ys (setV (pfacts p) v) S' → RP p n → n.2 ∈ numsOf p → v ∈ allV →
    (v, n, vecSet (pfacts p) S') ∈ dpTab p allV := by
  intro dt
  induction dt with
  | leaf a =>
    intro n v S' ys hv hy hr hrp hn hvA
    have hn' : n = (false, a) := toSum_eq_inl.1 hv.leaf_inv
    subst hn'
    obtain rfl := hy.leaf_inv
    obtain ⟨happ, hr⟩ := hr
    cases hr
    refine mem_dpTab_of_rule hp hall hTO (mem_cand hvA (vecSet_mem hp hall hTO _) hn) ?_
    unfold ruleB
    simp only [cond_false, Bool.and_eq_true, beq_iff_eq]
    refine ⟨(okV_iff hp hall hTO).2 happ, ?_⟩
    rw [← setV_apV hp hall hTO, vecSet_setV (V := pfacts p) (List.nodup_dedup _)]
    simp [apV, length_vecOf]
  | node c m ch ih =>
    intro n v S' ys hv hy hr hrp hn hvA
    obtain ⟨hs, ⟨e, he, rfl⟩, hc, hch⟩ := hv.node_inv
    have hn' : n = (true, c) := toSum_eq_inr.1 hs
    subst hn'
    subst hc
    have hreach : p.toProblem.toPos.ReachableName e.1 := hrp rfl
    have hto := hTO e he hreach
    have hl := TnDesc.isLinearization_lin hto
    obtain ⟨ys', hys, hm⟩ := hy.node_inv
    rw [(ordMerge_lin_iff (TnDesc.toTaskNetwork_wf _) hto hl).1 hm] at hr
    have hT : ∀ x, x ∈ (MethodDesc.toMethod e).subtasks.T ↔ x ∈ e.2.ids := fun x => by
      simp [MethodDesc.toMethod, TnDesc.toTaskNetwork]
    have aux : ∀ (l : List ℕ), (∀ x ∈ l, x ∈ e.2.ids) → ∀ u, u ∈ allV → ∀ S'',
        p.toProblem.Run (l.map ys').flatten (setV (pfacts p) u) S'' →
        ChainX (dpTab p allV) allV (lblOf e.2) l u (vecSet (pfacts p) S'') := by
      intro l
      induction l with
      | nil =>
        intro _ u hu S'' h
        cases h
        rw [vecSet_setV (V := pfacts p) (List.nodup_dedup _) ((hall u).1 hu)]
        exact .nil u
      | cons x l ihl =>
        intro hl' u hu S'' h
        rw [List.map_cons, List.flatten_cons, run_append] at h
        obtain ⟨S₁, h1, h2⟩ := h
        have hx := hl' x (by simp)
        have hS₁ : S₁ ⊆ {f | f ∈ pfacts p} := run_subset_pfacts p _ _ _ h1 (setV_sub _ u)
        have htr := ih x (lblOf e.2 x) u S₁ (ys' x)
          (by rw [← label_eq_toSum]; exact hch x ((hT x).2 hx)) (hys x ((hT x).2 hx)) h1
          (rp_child hp hall hTO he hreach hx)
          (mem_numsOf_method he (List.mem_cons_of_mem _ (List.mem_append_right _
            (lblOf_mem (hp.methods e he) hx)))) hu
        refine .cons htr (vecSet_mem hp hall hTO _) (ihl (fun y hy => hl' y (by simp [hy])) _
          (vecSet_mem hp hall hTO _) S'' ?_)
        rwa [setV_vecSet hS₁]
    have hcx := aux (TnDesc.lin e.2) (fun x hx => (hT x).1 ((hl.2.1 x).1 hx)) v hvA S' hr
    refine mem_dpTab_of_rule hp hall hTO (mem_cand hvA (vecSet_mem hp hall hTO _)
      (reach_numsOf hp hreach)) ?_
    unfold ruleB
    simp only [cond_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨e, he, rfl, mem_chainSet.2 ⟨v, List.mem_singleton_self _, hcx⟩⟩

omit hp hall hTO in
theorem chainT_sub {lab : ℕ → ℕ ⊕ ℕ} {l : List ℕ} {S S' : Set ℕ} (h : ChainT p lab l S S')
    (hS : S ⊆ {f | f ∈ pfacts p}) : S' ⊆ {f | f ∈ pfacts p} := by
  induction h with
  | nil => exact hS
  | cons h₁ _ ih =>
    obtain ⟨_, _, _, _, hr⟩ := h₁
    exact ih (run_subset_pfacts p _ _ _ hr hS)

/-- **The dynamic program decides plan existence of totally ordered descriptions.** -/
theorem dp_iff (htn : p.tnI.toTaskNetwork.IsTotallyOrdered) :
    p.toProblem.Solvable ↔ (chainSet allV (dpTab p allV) p.tnI [vecOf (pfacts p) p.init]).any
      (fun w => goalB p (sv (pfacts p) w)) = true := by
  have hinit : setV (pfacts p) (vecOf (pfacts p) p.init) = p.toProblem.init := by
    ext f
    simp only [setV, Set.mem_setOf_eq, mem_sv_vecOf]
    exact ⟨fun h => h.2, fun h => ⟨init_subset_pfacts p h, h⟩⟩
  have hiA : vecOf (pfacts p) p.init ∈ allV := by rw [hall, length_vecOf]
  have hl := TnDesc.isLinearization_lin htn
  have hT : ∀ x, x ∈ p.tnI.toTaskNetwork.T ↔ x ∈ p.tnI.ids := fun x => by
    simp [TnDesc.toTaskNetwork]
  have hrp : ∀ x ∈ p.tnI.ids, RP p (lblOf p.tnI x) := fun x hx hb =>
    HTN.Problem.ReachableName.tnI (P := p.toProblem.toPos)
      (by simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx)
      (label_eq_inr.2 (Prod.ext hb rfl))
  have hnm : ∀ x ∈ p.tnI.ids, (lblOf p.tnI x).2 ∈ numsOf p := fun x hx =>
    mem_numsOf_tnI (List.mem_append_right _ (lblOf_mem hp.tnI hx))
  rw [solvable_iff_chain hp htn, List.any_eq_true]
  constructor
  · rintro ⟨s', hc, hg⟩
    have aux : ∀ (l : List ℕ) (S S'' : Set ℕ), ChainT p p.tnI.label l S S'' →
        (∀ x ∈ l, x ∈ p.tnI.ids) → ∀ u ∈ allV, setV (pfacts p) u = S →
        ChainX (dpTab p allV) allV (lblOf p.tnI) l u (vecSet (pfacts p) S'') := by
      intro l S S'' h
      induction h with
      | nil S =>
        intro _ u hu hS
        rw [← hS, vecSet_setV (V := pfacts p) (List.nodup_dedup _) ((hall u).1 hu)]
        exact .nil u
      | @cons x l S S₁ S'' h₁ _ ih =>
        intro hl' u hu hS
        obtain ⟨dt, ys, hv, hy, hr⟩ := h₁
        have hx := hl' x (by simp)
        have hS₁ : S₁ ⊆ {f | f ∈ pfacts p} :=
          run_subset_pfacts p _ _ _ hr (hS ▸ setV_sub _ u)
        have htr := complete_dpTab hp hall hTO dt (lblOf p.tnI x) u S₁ ys
          (by rw [← label_eq_toSum]; exact hv) hy (hS ▸ hr) (hrp x hx) (hnm x hx) hu
        exact .cons htr (vecSet_mem hp hall hTO _) (ih (fun y hy => hl' y (by simp [hy])) _
          (vecSet_mem hp hall hTO _) (setV_vecSet hS₁))
    have hcx := aux _ _ _ hc (fun x hx => (hT x).1 ((hl.2.1 x).1 hx)) _ hiA hinit
    refine ⟨vecSet (pfacts p) s', mem_chainSet.2 ⟨_, List.mem_singleton_self _, hcx⟩, ?_⟩
    have hs' := chainT_sub hc (init_subset_pfacts p)
    rw [goalB_iff]
    show p.toProblem.GoalState (setV (pfacts p) (vecSet (pfacts p) s'))
    rwa [setV_vecSet hs']
  · rintro ⟨w, hw, hg⟩
    obtain ⟨u, hu, hcx⟩ := mem_chainSet.1 hw
    rw [List.mem_singleton] at hu
    subst hu
    have hsound : ∀ q ∈ dpTab p allV, RP p q.2.1 →
        RefT p (toSum q.2.1) (setV (pfacts p) q.1) (setV (pfacts p) q.2.2) := by
      rw [dpTab_eq]; exact sound_iter hp hall hTO _
    have hch := chainT_of_chainX hp hall hTO hsound
      (fun y hy => hrp y ((hT y).1 ((hl.2.1 y).1 hy))) hcx
    rw [toSum_lblOf, hinit] at hch
    exact ⟨_, hch, (goalB_iff p _).1 hg⟩

end Article

end HTN
