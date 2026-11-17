import FondHtn.Weak.LabelMap
import FondHtn.FixedMethods
import HtnPlanning.Article.DTree
/-!
# Weak solvability as deterministic plan existence ([CB21, Lemma 4.3])

Every primitive task `a` becomes a compound task `c_a = wr a`, with one method `c_a → (a, e)` per
effect `e` of `a`; the deterministic action `(a, e)` has the precondition of `a` and the single
effect `e`.  Compound tasks `c` are renamed `cw c`, and the methods are mapped accordingly.

The construction is parametrised (`FOND.WeakData`) by the new action names `A'` (each naming an
action `act x` and one of its effects `eff x`), the compound names `C'` with the injections `wr`,
`cw` and a common left inverse `un`, and the set `leaf ⊆ A'` of action names that get a method.
The description-level version instantiates all of this with natural numbers.

* `FOND.Problem.weakDet` — the deterministic problem (no goal), for given methods `M'`, initial
  task network `tn_I'` and actions `δ'` that agree with the construction up to isomorphism of
  method networks and on the leaf actions (`FOND.WeakSpec`) — descriptions denote such problems;
* **`FOND.Problem.weakLDSolvable_iff_weakDet`** — `P` has a weak LD solution iff `weakDet` is
  solvable, provided every effect of every action used in the problem has a leaf method.
-/

namespace FOND

open HTN HTN.TaskNetwork

variable {F A C I A' C' : Type}

/-- The data of the weak compilation. -/
structure WeakData (P : Problem F A C I) (A' C' : Type) where
  act : A' → A
  eff : A' → Set F × Set F
  heff : ∀ x, eff x ∈ (P.δ (act x)).effs
  wr : A → C'
  cw : C → C'
  un : C' → A ⊕ C
  un_wr : ∀ a, un (wr a) = Sum.inl a
  un_cw : ∀ c, un (cw c) = Sum.inr c
  leaf : Set A'
  i₀ : I

namespace WeakData

variable {P : Problem F A C I} (D : WeakData P A' C')

/-- The label map of the compilation: primitive `a` ↦ compound `wr a`, compound `c` ↦ `cw c`. -/
def e : A ⊕ C → A' ⊕ C' := Sum.elim (fun a => Sum.inr (D.wr a)) (fun c => Sum.inr (D.cw c))

/-- The projection back. -/
def ψ : A' ⊕ C' → A ⊕ C := Sum.elim (fun x => Sum.inl (D.act x)) D.un

theorem ψ_e : D.ψ ∘ D.e = id := by
  funext y; cases y <;> simp [e, ψ, D.un_wr, D.un_cw]

/-- The single-task network `i ↦ y`. -/
def single (i : I) (y : A' ⊕ C') : TaskNetwork I A' C' := ⟨{i}, fun _ _ => False, fun _ => y⟩

theorem single_wf (i : I) (y : A' ⊕ C') : (single i y).WF :=
  ⟨fun h => h.elim, fun h => h.elim, fun _ h => h, fun h => h.elim⟩

/-- An original method, mapped. -/
def wrapM (m : Method I A C) : Method I A' C' := Method.mapL D.e (D.cw m.abstractTask) m

/-- The method `c_{act x} → x`. -/
def leafM (x : A') : Method I A' C' := ⟨D.wr (D.act x), single D.i₀ (Sum.inl x)⟩

/-- The deterministic action `x`: the precondition of `act x` and the single effect `eff x`. -/
def detAct (x : A') : HTN.Article.Action F :=
  ⟨(P.δ (D.act x)).pre, (P.δ (D.act x)).preNeg, (D.eff x).1, (D.eff x).2⟩

end WeakData

namespace Problem

variable (P : Problem F A C I)

/-- A primitive task name occurring in `tn_I` or in a method. -/
def Used (a : A) : Prop :=
  (∃ t ∈ P.tnI.T, P.tnI.α t = Sum.inl a) ∨
    ∃ m ∈ P.methods, ∃ t ∈ m.subtasks.T, m.subtasks.α t = Sum.inl a

end Problem

variable {P : Problem F A C I} (D : WeakData P A' C')

/-- Every effect of every used action has a leaf method. -/
def WeakData.Covers : Prop :=
  ∀ a, P.Used a → ∀ e ∈ (P.δ a).effs, ∃ x ∈ D.leaf, D.act x = a ∧ D.eff x = e

/-- The methods, initial task network and actions of the compiled problem, up to isomorphism of
networks and on the relevant actions. -/
structure WeakSpec (M' : Set (Method I A' C')) (tnI' : TaskNetwork I A' C')
    (δ' : A' → HTN.Article.Action F) : Prop where
  wrap : ∀ m ∈ P.methods, ∃ m' ∈ M', m'.abstractTask = D.cw m.abstractTask ∧
    (m.subtasks.mapL D.e).Iso m'.subtasks
  leaf : ∀ x ∈ D.leaf, ∃ m' ∈ M', m'.abstractTask = D.wr (D.act x) ∧ m'.subtasks.WF ∧
    ∃ i, m'.subtasks.T = {i} ∧ m'.subtasks.α i = Sum.inl x
  meth : ∀ m' ∈ M', m'.subtasks.WF ∧
    ((∃ m ∈ P.methods, D.un m'.abstractTask = Sum.inr m.abstractTask ∧
        (m'.subtasks.mapL D.ψ).Iso m.subtasks ∧ ∀ t ∈ m'.subtasks.T, ∃ c, m'.subtasks.α t = Sum.inr c) ∨
      ∃ x ∈ D.leaf, m'.abstractTask = D.wr (D.act x) ∧
        ∃ i, m'.subtasks.T = {i} ∧ m'.subtasks.α i = Sum.inl x)
  tnI : tnI'.Iso (P.tnI.mapL D.e)
  tnI_wf : tnI'.WF
  act : ∀ x ∈ D.leaf, δ' x = D.detAct x

namespace Problem

/-- **The deterministic problem of weak solutions.** -/
def weakDet (M' : Set (Method I A' C')) (tnI' : TaskNetwork I A' C')
    (δ' : A' → HTN.Article.Action F) : HTN.Article.Problem F A' C' I where
  δ := δ'
  methods := M'
  init := P.init
  tnI := tnI'
  goalPos := ∅
  goalNeg := ∅

variable {M' : Set (Method I A' C')} {tnI' : TaskNetwork I A' C'} {δ' : A' → HTN.Article.Action F}

theorem run_weakExec (hS : WeakSpec D M' tnI' δ') : ∀ (xs : List A') (s s' : Set F),
    (∀ x ∈ xs, x ∈ D.leaf) → (P.weakDet M' tnI' δ').Run xs s s' → P.WeakExec (xs.map D.act) s := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _; trivial
  | cons x xs ih =>
    rintro s s' hl ⟨happ, hrun⟩
    have hx : δ' x = D.detAct x := hS.act x (hl x (List.mem_cons_self ..))
    change (δ' x).Applicable s at happ
    change (P.weakDet M' tnI' δ').Run xs ((δ' x).apply s) s' at hrun
    rw [hx] at happ hrun
    exact ⟨happ, _, ⟨D.eff x, D.heff x, rfl⟩,
      ih _ _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hrun⟩

theorem exists_run (hS : WeakSpec D M' tnI' δ') (hD : D.Covers) :
    ∀ (as : List A) (s : Set F), (∀ a ∈ as, P.Used a) →
    P.WeakExec as s → ∃ xs : List A', xs.map D.act = as ∧ (∀ x ∈ xs, x ∈ D.leaf) ∧
      ∃ s', (P.weakDet M' tnI' δ').Run xs s s' := by
  intro as
  induction as with
  | nil => intro s _ _; exact ⟨[], rfl, by simp, s, rfl⟩
  | cons a as ih =>
    rintro s hu ⟨happ, s₁, ⟨e, he, rfl⟩, hex⟩
    obtain ⟨x, hx, hxa, hxe⟩ := hD a (hu a (List.mem_cons_self ..)) e he
    obtain ⟨xs, hxs, hl, s', hrun⟩ := ih _ (fun b hb => hu b (List.mem_cons_of_mem _ hb)) hex
    refine ⟨x :: xs, by simp [hxs, hxa], ?_, s', ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hl y hy
    · show (δ' x).Applicable s
      rw [hS.act x hx]
      show (P.δ (D.act x)).pre ⊆ s ∧ Disjoint (P.δ (D.act x)).preNeg s
      rw [hxa]; exact happ
    · show (P.weakDet M' tnI' δ').Run xs ((δ' x).apply s) s'
      rw [hS.act x hx]
      show (P.weakDet M' tnI' δ').Run xs ((s \ (D.eff x).2) ∪ (D.eff x).1) s'
      rw [hxe]; exact hrun

variable [DecidableEq I]

theorem getD_idxOf {l : List I} {xs : List A'} (hl : l.Nodup) (hlen : l.length = xs.length)
    (d : A') : l.map (fun t => xs.getD (l.idxOf t) d) = xs := by
  apply List.ext_getElem (by simp [hlen])
  intro k hk _
  simp only [List.getElem_map]
  rw [List.idxOf_getElem hl]
  simp at hk
  rw [List.getD_eq_getElem]

omit [DecidableEq I] in
theorem weakDet_wf (hS : WeakSpec D M' tnI' δ') : (P.weakDet M' tnI' δ').WF :=
  ⟨hS.tnI_wf, fun m' hm' => (hS.meth m' hm').1⟩

theorem decomposesTo_iso [Infinite I] {M : Set (Method I A' C')} {tn₁ tn₂ tn₁' : TaskNetwork I A' C'}
    (h : HTN.DecomposesTo M tn₁ tn₂) (h₁ : tn₁.WF) (h₁' : tn₁'.WF) (hiso : tn₁.Iso tn₁') :
    ∃ tn₂', HTN.DecomposesTo M tn₁' tn₂' ∧ tn₂.Iso tn₂' := by
  obtain ⟨n, hn⟩ := HTN.exists_decomposesToN h
  obtain ⟨tn₂', h', hiso'⟩ := hn.iso h₁ h₁' hiso
  exact ⟨tn₂', h'.decomposesTo, hiso'⟩

/-- **[CB21, Lemma 4.3]**: weak LD solvability is plan existence of the compiled problem. -/
theorem weakLDSolvable_iff_weakDet [Infinite I] [Inhabited A'] (hP : P.WF) (hD : D.Covers)
    (hS : WeakSpec D M' tnI' δ') :
    P.WeakLDSolvable ↔ (P.weakDet M' tnI' δ').Solvable := by
  rw [HTN.Article.Problem.solvable_iff_decomp _ (weakDet_wf D hS)]
  have hgoal : ∀ s, (P.weakDet M' tnI' δ').GoalState s := fun s =>
    ⟨Set.empty_subset _, Set.empty_disjoint _⟩
  constructor
  · rintro ⟨tn, l, ⟨hd, hprim⟩, hl, as, has, hex⟩
    have hwf : tn.WF := hd.wf hP.tnI
    -- labels of `tn` are used
    have hlab := HTN.DecomposesTo.labels_mem (L := {y | ∀ a, y = Sum.inl a → P.Used a}) hd
      (fun t ht a ha => Or.inl ⟨t, ht, ha⟩)
      (fun m hm t ht a ha => Or.inr ⟨m, hm, t, ht, ha⟩)
    have hlen : l.length = as.length := by
      have := congrArg List.length has; simpa using this
    have hasl : ∀ k (hk : k < l.length), tn.α l[k] = Sum.inl (as[k]'(hlen ▸ hk)) := by
      intro k hk
      have := congrArg (fun z => z[k]?) has
      simp only [List.getElem?_map] at this
      rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (hlen ▸ hk)] at this
      simpa using this
    have hused : ∀ a ∈ as, P.Used a := by
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      have hk' : k < l.length := hlen ▸ hk
      exact hlab _ ((hl.2.1 _).1 (List.getElem_mem hk')) _ (hasl k hk')
    obtain ⟨xs, hxs, hleaf, s', hrun⟩ := exists_run D hS hD as _ hused hex
    have hlen' : l.length = xs.length := by rw [hlen, ← hxs, List.length_map]
    let f : I → A' ⊕ C' := fun t => Sum.inl (xs.getD (l.idxOf t) default)
    -- the wrapped decomposition, from the wrapped initial network
    have hN := HTN.decomposesTo_mapL (M' := M') (e := D.e) (eC := D.cw)
      (fun _ => rfl) hS.wrap hd
    -- expand all wrapped tasks
    obtain ⟨N', hN', hiso, hwf'⟩ := HTN.exists_decomposesTo_setLabels (M' := M')
      (N := tn.mapL D.e) (mapL_wf hwf) f (by
        intro t ht
        have htl : t ∈ l := (hl.2.1 t).2 ht
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem htl
        have hidx : l.idxOf l[k] = k := List.idxOf_getElem hl.1 _ _
        have hkx : k < xs.length := hlen' ▸ hk
        obtain ⟨m', hm', hc, hmwf, i, hiT, hiα⟩ := hS.leaf _ (hleaf _ (List.getElem_mem hkx))
        refine ⟨m', hm', ?_, hmwf, i, hiT, ?_⟩
        · have hact : D.act (xs[k]'hkx) = as[k]'(hlen ▸ hk) := by
            have := congrArg (fun z => z[k]?) hxs
            simp only [List.getElem?_map] at this
            rw [List.getElem?_eq_getElem hkx, List.getElem?_eq_getElem (hlen ▸ hk)] at this
            simpa using this
          simp [WeakData.e, hasl k hk, hact, hc]
        · simp [f, hidx, List.getElem?_eq_getElem hkx, hiα])
    -- move to the given initial network
    obtain ⟨N'', hN'', hiso''⟩ := decomposesTo_iso (hN.trans hN') (mapL_wf hP.tnI) hS.tnI_wf
      hS.tnI.symm
    have hprimN : (tn.mapL D.e).setLabels f |>.IsPrimitive := fun t _ => ⟨_, rfl⟩
    obtain ⟨σ, hσ⟩ := hiso.symm.trans hiso''
    obtain ⟨hl', has'⟩ := TaskNetwork.Iso.map_isLinearization hσ.1 hσ.2.1 hσ.2.2
      (tn := (tn.mapL D.e).setLabels f) (l := l) hl
    refine ⟨N'', hN'', (hiso.symm.trans hiso'').isPrimitive hprimN, l.map σ, xs, s', hl',
      has' xs ?_, hrun, hgoal _⟩
    show l.map f = xs.map Sum.inl
    rw [← getD_idxOf hl.1 hlen' default, List.map_map]
    rfl
  · rintro ⟨tn₀, hd₀, hprim₀, l₀, xs, s, hl₀, has₀, hrun, -⟩
    -- move to the wrapped initial network
    obtain ⟨tn', hd', hiso₀⟩ := decomposesTo_iso hd₀ hS.tnI_wf (mapL_wf hP.tnI) hS.tnI
    obtain ⟨σ₀, hσ₀⟩ := hiso₀
    obtain ⟨hl', has'₀⟩ := TaskNetwork.Iso.map_isLinearization hσ₀.1 hσ₀.2.1 hσ₀.2.2 hl₀
    have has' := has'₀ xs has₀
    have hprim' : tn'.IsPrimitive := TaskNetwork.Iso.isPrimitive (tn := tn₀) ⟨σ₀, hσ₀⟩ hprim₀
    -- the actions are leaf actions
    have hlab := HTN.DecomposesTo.labels_mem (L := {y | ∀ x, y = Sum.inl x → x ∈ D.leaf}) hd'
      (fun t _ x hx => by simp [WeakData.e] at hx; cases h : P.tnI.α t <;> simp [h] at hx)
      (fun m' hm' t ht x hx => by
        rcases (hS.meth m' hm').2 with ⟨-, -, -, -, hc⟩ | ⟨y, hy, -, i, hiT, hiα⟩
        · obtain ⟨c, hc⟩ := hc t ht; rw [hc] at hx; cases hx
        · rw [hiT, Finset.mem_singleton] at ht; subst ht; rw [hiα] at hx; cases hx; exact hy)
    have hleaf : ∀ x ∈ xs, x ∈ D.leaf := by
      intro x hx
      have : Sum.inl x ∈ (l₀.map σ₀).map tn'.α := by rw [has']; exact List.mem_map_of_mem hx
      obtain ⟨t, ht, hte⟩ := List.mem_map.1 this
      exact hlab t ((hl'.2.1 t).1 ht) x hte
    have hproj : ∀ m' ∈ M', HTN.ProjOK P.methods D.ψ m' := by
      intro m' hm'
      rcases (hS.meth m' hm').2 with ⟨m, hm, hc, hiso, -⟩ | ⟨x, -, hc, i, hiT, hiα⟩
      · exact Or.inl ⟨m, hm, by simp [WeakData.ψ, hc], hiso⟩
      · exact Or.inr ⟨i, hiT, by simp [WeakData.ψ, hiα, hc, D.un_wr]⟩
    obtain ⟨X, hX, hiso, -⟩ := HTN.exists_decomposesTo_mapL_of hproj
      (fun m' hm' => (hS.meth m' hm').1) hd' (mapL_wf hP.tnI)
    have htnI : (P.tnI.mapL D.e).mapL D.ψ = P.tnI := by rw [mapL_mapL, D.ψ_e, mapL_id]
    rw [htnI] at hX
    have hprimP : (tn'.mapL D.ψ).IsPrimitive := by
      intro t ht
      obtain ⟨x, hx⟩ := hprim' t ht
      exact ⟨D.act x, by simp [hx, WeakData.ψ]⟩
    obtain ⟨σ, hσ⟩ := hiso.symm
    obtain ⟨hl'', has''⟩ := TaskNetwork.Iso.map_isLinearization hσ.1 hσ.2.1 hσ.2.2
      (tn := tn'.mapL D.ψ) (l := l₀.map σ₀) hl'
    refine ⟨X, (l₀.map σ₀).map σ, ⟨hX, hiso.symm.isPrimitive hprimP⟩, hl'', xs.map D.act,
      has'' _ ?_, run_weakExec D hS xs _ _ hleaf hrun⟩
    show (l₀.map σ₀).map (fun t => D.ψ (tn'.α t)) = (xs.map D.act).map Sum.inl
    have : (l₀.map σ₀).map (fun t => D.ψ (tn'.α t)) = ((l₀.map σ₀).map tn'.α).map D.ψ := by
      simp only [List.map_map]; rfl
    rw [this, has', List.map_map, List.map_map]
    rfl

end Problem

end FOND
