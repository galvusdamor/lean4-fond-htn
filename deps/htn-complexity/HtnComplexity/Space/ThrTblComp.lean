import HtnComplexity.Space.ThrTblSound
/-!
# The thread table simulates the thread system: completeness

Every step of the thread system is matched by a run of the table (the silent rows first derive
the `ok` facts the step needs), and a solution of the thread system extends to one of the table
(close the idle running threads, then sweep).  Together with `ThrTblSound.lean`:

    HTN.Space.Thr.tsolv_iff_solvF : TSolv P s₀ {v | v ∈ g} ↔ SolvF (thrTbl P.d N) (initG P G s₀) (goalF g)
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG

/-- **The hypotheses of completeness**: those of soundness, room for all threads and nodes, and
a certificate for every pair of slots that are not connected. -/
structure HypC (P : Par) (G : Gr) (N : ℕ) : Prop extends Hyp P G N where
  kN' : P.k < N
  edgeN : ∀ x y, G.E x y → x < N ∧ y < N
  ncC : ∀ i < P.k, ∀ j < P.k, ¬ Relation.TransGen G.E i j → G.NC i j

variable {P : Par} {G : Gr} {N : ℕ}

/-! ### Rows of the table -/

section Mem

variable (d : DomDesc)

theorem mem_rOks {i j : ℕ} (hi : i < N) (hj : j < N) {r : Rw} (hr : r ∈ rOks i j) :
    r ∈ thrTbl d N :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
      List.mem_append_left _ hr⟩⟩)))

theorem mem_rZok {i j μ : ℕ} (hi : i < N) (hj : j < N) (hμ : μ < d.methods.length) {r : Rw}
    (hr : r ∈ rZok d i j μ) : r ∈ thrTbl d N :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
      List.mem_append_right _ (List.mem_flatMap.2 ⟨μ, List.mem_range.2 hμ, hr⟩)⟩⟩)))

theorem mem_rRch {x y z : ℕ} (hx : x < N) (hy : y < N) (hz : z < N) {r : Rw}
    (hr : r ∈ rRch x y z) : r ∈ thrTbl d N :=
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨x, List.mem_range.2 hx, List.mem_flatMap.2 ⟨y, List.mem_range.2 hy,
      List.mem_flatMap.2 ⟨z, List.mem_range.2 hz, hr⟩⟩⟩))

theorem mem_rCnt {p : ℕ} (hp : p < N) {r : Rw} (hr : r ∈ rCnt p) : r ∈ thrTbl d N :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨p, List.mem_range.2 hp, hr⟩)

theorem mem_rThread {j μ : ℕ} (hj : j < N) (hμ : μ < d.methods.length) {r : Rw}
    (hr : r ∈ [rExpP d N j μ, rExpC d j μ, rClose d j μ] ++ (primsL d μ).flatMap (rExecs d j μ)) :
    r ∈ thrTbl d N :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_flatMap.2 ⟨μ, List.mem_range.2 hμ, hr⟩⟩))))

theorem mem_rPrim {j : ℕ} (hj : j < N) {r : Rw}
    (hr : r ∈ (vocA d).map (rExecP d N j) ++ [rNop N j]) : r ∈ thrTbl d N :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, hr⟩))))

end Mem

/-! ### Growing a fact set by silent rows -/

/-- The fact set `s` grows, by rows of the table and still related to `c`, into one with `Q`. -/
def Grow (P : Par) (G : Gr) (N : ℕ) (c : Cfg) (s : Set TF) (Q : Set TF → Prop) : Prop :=
  ∃ s', Relation.ReflTransGen (StepF (thrTbl P.d N)) s s' ∧ TRel P G c s' ∧ s ⊆ s' ∧ Q s'

theorem grow_silent {c : Cfg} {s : Set TF} {pre : List TF} {f : TF}
    (hr : (pre, [f], []) ∈ thrTbl P.d N) (hpre : ∀ g ∈ pre, g ∈ s) (h : TRel P G c (insert f s)) :
    Grow P G N c s (fun s' => f ∈ s') :=
  ⟨insert f s, .single ⟨_, hr, hpre, (apply_silent pre f s).symm⟩, h,
    Set.subset_insert f s, Set.mem_insert f s⟩

theorem Grow.trans {c : Cfg} {s : Set TF} {Q Q' : Set TF → Prop} (h : Grow P G N c s Q)
    (hmono : ∀ s₁ s₂, s₁ ⊆ s₂ → Q s₁ → Q s₂)
    (h' : ∀ s', TRel P G c s' → s ⊆ s' → Q s' → Grow P G N c s' Q') :
    Grow P G N c s (fun s' => Q s' ∧ Q' s') := by
  obtain ⟨s₁, hr₁, ht₁, hs₁, hq₁⟩ := h
  obtain ⟨s₂, hr₂, ht₂, hs₂, hq₂⟩ := h' s₁ ht₁ hs₁ hq₁
  exact ⟨s₂, hr₁.trans hr₂, ht₂, hs₁.trans hs₂, hmono _ _ hs₂ hq₁, hq₂⟩

theorem grow_refl {c : Cfg} {s : Set TF} (h : TRel P G c s) {Q : Set TF → Prop} (hq : Q s) :
    Grow P G N c s Q :=
  ⟨s, .refl, h, subset_rfl, hq⟩

/-- A family of facts, each of which can be grown, can be grown together. -/
theorem grow_list {c : Cfg} (F : ℕ → TF) {l : List ℕ}
    (hF : ∀ i ∈ l, ∀ s, TRel P G c s → Grow P G N c s (fun s' => F i ∈ s')) :
    ∀ s, TRel P G c s → Grow P G N c s (fun s' => ∀ i ∈ l, F i ∈ s') := by
  induction l with
  | nil => intro s h; exact grow_refl h (by simp)
  | cons a l ih =>
    intro s h
    obtain ⟨s₁, hr₁, ht₁, hs₁, hq₁⟩ := hF a (by simp) s h
    obtain ⟨s₂, hr₂, ht₂, hs₂, hq₂⟩ := ih (fun i hi => hF i (by simp [hi])) s₁ ht₁
    refine ⟨s₂, hr₁.trans hr₂, ht₂, hs₁.trans hs₂, ?_⟩
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hs₂ hq₁
    · exact hq₂ i hi

theorem Grow.bind {c : Cfg} {s : Set TF} {Q Q' : Set TF → Prop} (h : Grow P G N c s Q)
    (h' : ∀ s', TRel P G c s' → Q s' → Grow P G N c s' Q') : Grow P G N c s Q' := by
  obtain ⟨s₁, hr₁, ht₁, hs₁, hq₁⟩ := h
  obtain ⟨s₂, hr₂, ht₂, hs₂, hq₂⟩ := h' s₁ ht₁ hq₁
  exact ⟨s₂, hr₁.trans hr₂, ht₂, hs₁.trans hs₂, hq₂⟩

/-! ### The silent facts -/

theorem grow_unused (hC : HypC P G N) {c : Cfg} {s : Set TF} (h : TRel P G c s) :
    ∀ p, P.k ≤ p → p < N → Grow P G N c s (fun s' => TF.unused p ∈ s') := by
  intro p hkp
  induction p, hkp using Nat.le_induction with
  | base =>
    intro hp
    exact grow_silent (pre := [TF.len P.k]) (mem_rCnt P.d hp (by simp [rCnt])) (by simp [h.len])
      (h.insert_unused le_rfl)
  | succ p hkp ih =>
    intro hp
    exact (ih (by omega)).bind fun s' h' hu =>
      grow_silent (pre := [TF.unused p]) (mem_rCnt P.d (p := p) (by omega) (by simp [rCnt]))
        (by simpa using hu)
        (h'.insert_unused (by omega))

theorem lt_of_transGen (hC : HypC P G N) {x y : ℕ} (h : Relation.TransGen G.E x y) :
    x < N ∧ y < N := by
  induction h with
  | single h => exact hC.edgeN _ _ h
  | tail _ he ih => exact ⟨ih.1, (hC.edgeN _ _ he).2⟩

theorem grow_rch (hC : HypC P G N) {c : Cfg} {x y : ℕ} (hxy : Relation.TransGen G.E x y) :
    ∀ s, TRel P G c s → Grow P G N c s (fun s' => TF.rch x y ∈ s') := by
  induction hxy with
  | @single y he =>
    intro s h
    have hN := hC.edgeN _ _ he
    exact grow_silent (pre := [TF.edge x y]) (mem_rRch P.d hN.1 hN.2 hN.1 (z := x) (by simp [rRch]))
      (by simp [h.edge, he]) (h.insert_rch (.single he))
  | @tail y z hxy he ih =>
    intro s h
    have hN := lt_of_transGen hC hxy
    have hz := (hC.edgeN _ _ he).2
    exact (ih s h).bind fun s' h' hr =>
      grow_silent (pre := [TF.rch x y, TF.edge y z]) (mem_rRch P.d hN.1 hN.2 hz (by simp [rRch]))
        (by simp [hr, h'.edge, he]) (h'.insert_rch (hxy.tail he))

theorem tail_none_of_idle {th : ℕ → TSt} {i μ : ℕ} {D : Finset ℕ}
    (hs : th i = .run μ D) (hD : D ⊆ prims P.d μ) (hidle : Idle P th i) :
    tail P.d μ = none := by
  unfold Idle at hidle
  rw [hs, thTasks_run_eq_empty] at hidle
  exact tail_eq_none fun z hz => (mem_prims.1 (hD (hidle z hz))).2

theorem grow_ok (hC : HypC P G N) {c : Cfg} {i j : ℕ} (hiN : i < N) (hj : j < P.k)
    (hpre : i < P.k → P.O i j → Idle P c.th i) :
    ∀ s, TRel P G c s → Grow P G N c s (fun s' => TF.ok i j ∈ s') := by
  intro s h
  have hjN : j < N := by have := hC.kN'; omega
  by_cases hik : i < P.k
  · by_cases hO : P.O i j
    · have hidle := hpre hik hO
      rcases hth : c.th i with _ | cc | ⟨μ, D⟩ | _
      · unfold Idle at hidle; rw [hth] at hidle; simp [thTasks] at hidle
      · unfold Idle at hidle; rw [hth] at hidle; simp [thTasks] at hidle
      · obtain ⟨hμ, hD⟩ := h.inv.run i hik μ D hth
        have ht : tail P.d μ = none := tail_none_of_idle hth hD hidle
        refine grow_silent (pre := doneL P.d i μ)
          (mem_rZok P.d hiN hjN hμ (by simp [rZok, ht])) ?_
          (h.insert_ok fun _ _ => Or.inr hidle)
        intro f hf
        simp only [doneL, List.mem_cons, List.mem_map, mem_primsL] at hf
        rcases hf with rfl | ⟨x, hx, rfl⟩
        · exact (h.blk i μ).2 ⟨hik, D, hth⟩
        · refine (h.don i μ x).2 ⟨hik, D, hth, ?_⟩
          unfold Idle at hidle
          rw [hth, thTasks_run_eq_empty] at hidle
          exact hidle x (mem_prims.1 hx).1
      · exact grow_silent (pre := [TF.fin i]) (mem_rOks P.d hiN hjN (by simp [rOks]))
          (by simp [h.fin, hik, hth])
          (h.insert_ok fun _ _ => Or.inr (idle_fin _ hth))
    · have := (not_congr (hC.hO i hik j hj)).1 hO
      by_cases hr : Relation.TransGen G.E i j
      · have hji : Relation.TransGen G.E j i := by
          by_contra hn; exact this ⟨hr, hn⟩
        exact (grow_rch hC hji s h).bind fun s' h' hm =>
          grow_silent (pre := [TF.rch j i]) (mem_rOks P.d hiN hjN (by simp [rOks]))
            (by simpa using hm)
            (h'.insert_ok fun _ _ => Or.inl hO)
      · exact grow_silent (pre := [TF.nc i j]) (mem_rOks P.d hiN hjN (by simp [rOks]))
          (by simp [h.nc, hC.ncC i hik j hj hr]) (h.insert_ok fun _ _ => Or.inl hO)
  · exact (grow_unused hC h i (by omega) hiN).bind fun s' h' hu =>
      grow_silent (pre := [TF.unused i]) (mem_rOks P.d hiN hjN (by simp [rOks]))
        (by simpa using hu)
        (h'.insert_ok fun hi _ => absurd hi hik)

theorem grow_oks (hC : HypC P G N) {c : Cfg} {j : ℕ} (hj : j < P.k)
    (hpre : ∀ i < P.k, P.O i j → Idle P c.th i) {s : Set TF} (h : TRel P G c s) :
    Grow P G N c s (fun s' => ∀ f ∈ oks N j, f ∈ s') := by
  have := grow_list (P := P) (G := G) (N := N) (c := c) (fun i => TF.ok i j)
    (l := (List.range N).filter (· ≠ j)) (fun i hi s h => by
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
      exact grow_ok hC hi.1 hj (fun hik hO => hpre i hik hO) s h) s h
  obtain ⟨s', hr, ht, hs, hq⟩ := this
  refine ⟨s', hr, ht, hs, fun f hf => ?_⟩
  simp only [oks, List.mem_map] at hf
  obtain ⟨i, hi, rfl⟩ := hf
  exact hq i hi

/-! ### Completeness of a step -/

theorem stepF_row {d : DomDesc} {r : Rw} (hr : r ∈ thrTbl d N) {s : Set TF}
    (hpre : ∀ f ∈ r.1, f ∈ s) : StepF (thrTbl d N) s (apply r s) := ⟨r, hr, hpre, rfl⟩

theorem TRel.inst_of_prec {c : Cfg} {s : Set TF} (h : TRel P G c s) {a : ℕ}
    (happ : P.d.prec a ⊆ c.st) : ∀ v ∈ (actOf P.d a).1, TF.inst v ∈ s := by
  intro v hv
  refine (h.inst v).2 (happ ?_)
  simp only [DomDesc.prec_eq, precList_eq_actOf, Set.mem_setOf_eq]
  exact hv

/-- **Completeness of a step**: a step of the thread system is matched by a run of the table. -/
theorem complete_stepF (hC : HypC P G N) {c c' : Cfg} {s : Set TF} (h : TRel P G c s)
    (hst : TStep P c c') :
    ∃ s', Relation.ReflTransGen (StepF (thrTbl P.d N)) s s' ∧ TRel P G c' s' := by
  have hP := hC.good
  have hkN := hC.kN'
  cases hst with
  | @expandP j μ hj hs hl hμ hpre =>
    obtain ⟨s₁, hr₁, h₁, -, ho⟩ := grow_oks hC hj hpre h
    refine ⟨_, hr₁.tail (stepF_row (r := rExpP P.d N j μ)
      (mem_rThread P.d (j := j) (by omega) hμ (by simp)) ?_), h₁.expP hP hj hs hl hμ hpre N⟩
    intro f hf
    simp only [rExpP, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact (h₁.lab _ _).2 ⟨hj, hl.symm, Or.inl hs⟩
    · exact ho f hf
  | @expandC j μ hj hs hμ =>
    refine ⟨_, .single (stepF_row (r := rExpC P.d j μ)
      (mem_rThread P.d (j := j) (by omega) hμ (by simp)) ?_), h.expC hP hj hs hμ⟩
    intro f hf
    simp only [rExpC, List.mem_singleton] at hf
    subst hf
    exact (h.cur _ _).2 ⟨hj, hs⟩
  | @exec j μ x a D hj hs hx hxD hpre hl happ =>
    obtain ⟨hμ, hD⟩ := h.inv.run j hj μ D hs
    refine ⟨_, .single (stepF_row (r := rExec P.d j μ x a)
      (mem_rThread P.d (j := j) (by omega) hμ ?_) ?_), h.exec hP hj hs hx hxD hpre hl happ⟩
    · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨x, (mem_primsL P.d).2 hx, ?_⟩)
      simp [rExecs, hl]
    · intro f hf
      simp only [rExec, List.mem_cons, List.mem_append, List.mem_map, mem_predsL] at hf
      rcases hf with (rfl | ⟨y, hy, rfl⟩) | ⟨v, hv, rfl⟩
      · exact (h.tok _ _ _).2 ⟨hj, D, hs, hx, hxD⟩
      · exact (h.don _ _ _).2 ⟨hj, D, hs, hpre y hy⟩
      · exact h.inst_of_prec happ v hv
  | @close j μ D hj hs hD =>
    obtain ⟨hμ, -⟩ := h.inv.run j hj μ D hs
    refine ⟨_, .single (stepF_row (r := rClose P.d j μ)
      (mem_rThread P.d (j := j) (by omega) hμ (by simp)) ?_), h.close hP hj hs hD⟩
    intro f hf
    simp only [rClose, doneL, List.mem_cons, List.mem_map, mem_primsL] at hf
    rcases hf with rfl | ⟨x, hx, rfl⟩
    · exact (h.blk _ _).2 ⟨hj, D, hs⟩
    · exact (h.don _ _ _).2 ⟨hj, D, hs, hD hx⟩
  | @execP j a hj hs hl hpre happ =>
    obtain ⟨s₁, hr₁, h₁, -, ho⟩ := grow_oks hC hj hpre h
    by_cases ha : a ∈ vocA P.d
    · refine ⟨_, hr₁.tail (stepF_row (r := rExecP P.d N j a)
        (mem_rPrim P.d (j := j) (by omega) (List.mem_append_left _ (List.mem_map_of_mem ha))) ?_), h₁.execP hP hj hs hl ha hpre happ N⟩
      intro f hf
      simp only [rExecP, List.mem_cons, List.mem_append, List.mem_map] at hf
      rcases hf with (rfl | hf) | ⟨v, hv, rfl⟩
      · exact (h₁.lab _ _).2 ⟨hj, hl.symm, Or.inl hs⟩
      · exact ho f hf
      · exact h₁.inst_of_prec happ v hv
    · have hu : Unk P.d (Sum.inl a) := by simpa [Unk, unknownPrimB] using ha
      refine ⟨_, hr₁.tail (stepF_row (r := rNop N j)
        (mem_rPrim P.d (j := j) (by omega) (by simp)) ?_), h₁.skip hP hj hs hl hu hpre N⟩
      intro f hf
      simp only [rNop, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact (h₁.nop _).2 ⟨hj, hl ▸ hu, hs⟩
      · exact ho f hf

/-! ### Completeness -/

theorem swp_nmem_del {d : DomDesc} {r : Rw} (hr : r ∈ thrTbl d N) (p : ℕ) : TF.swp p ∉ r.2.2 := by
  simp only [thrTbl, rOks, rRch, rCnt, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hr
  rcases hr with ((((⟨j, -, μ, -, (rfl | rfl | rfl) | ⟨x, -, hr⟩⟩ | ⟨j, -, ⟨a, -, rfl⟩ | rfl⟩) |
      ⟨i, -, j, -, (rfl | rfl | rfl | rfl) | ⟨μ, -, hr⟩⟩) | ⟨x, -, y, -, z, -, rfl | rfl⟩) |
      ⟨q, -, rfl | rfl | rfl | rfl⟩) <;>
    try simp [rExpP, rExpC, rClose, doneL, rExecP, rNop]
  · unfold rExecs at hr
    split at hr <;> simp at hr
    subst hr
    simp [rExec]
  · unfold rZok at hr
    split at hr <;> simp at hr
    subst hr
    simp

theorem swp_persist {d : DomDesc} {s s' : Set TF}
    (h : Relation.ReflTransGen (StepF (thrTbl d N)) s s') {p : ℕ} (hp : TF.swp p ∈ s) :
    TF.swp p ∈ s' := by
  induction h with
  | refl => exact hp
  | tail _ hst ih =>
    obtain ⟨r, hr, -, rfl⟩ := hst
    exact Or.inr ⟨ih, swp_nmem_del hr p⟩

theorem reach_of_tstep (hC : HypC P G N) {c c' : Cfg} (hcc : Relation.ReflTransGen (TStep P) c c')
    {s : Set TF} (h : TRel P G c s) :
    ∃ s', Relation.ReflTransGen (StepF (thrTbl P.d N)) s s' ∧ TRel P G c' s' := by
  induction hcc with
  | refl => exact ⟨s, .refl, h⟩
  | tail _ hst ih =>
    obtain ⟨s₁, hr₁, h₁⟩ := ih
    obtain ⟨s₂, hr₂, h₂⟩ := complete_stepF hC h₁ hst
    exact ⟨s₂, hr₁.trans hr₂, h₂⟩

/-- Closing the idle running threads, one by one. -/
theorem close_idle (hC : HypC P G N) {c : Cfg} {s : Set TF} (h : TRel P G c s)
    (hidle : ∀ i < P.k, Idle P c.th i) :
    ∀ n ≤ P.k, ∃ c' s', Relation.ReflTransGen (TStep P) c c' ∧
      Relation.ReflTransGen (StepF (thrTbl P.d N)) s s' ∧ TRel P G c' s' ∧
      c'.st = c.st ∧ (∀ i < P.k, Idle P c'.th i) ∧ ∀ i < n, c'.th i = .fin := by
  intro n hn
  induction n with
  | zero => exact ⟨c, s, .refl, .refl, h, rfl, hidle, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨c₁, s₁, hc₁, hr₁, h₁, hst₁, hid₁, hf₁⟩ := ih (by omega)
    have hnk : n < P.k := by omega
    by_cases hfin : c₁.th n = .fin
    · refine ⟨c₁, s₁, hc₁, hr₁, h₁, hst₁, hid₁, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hf₁ i hi
      · exact hfin
    · have hi := hid₁ n hnk
      rcases hth : c₁.th n with _ | cc | ⟨μ, D⟩ | _
      · unfold Idle at hi; rw [hth] at hi; simp [thTasks] at hi
      · unfold Idle at hi; rw [hth] at hi; simp [thTasks] at hi
      · have hD : D ⊆ prims P.d μ := (h₁.inv.run n hnk μ D hth).2
        have hsup : prims P.d μ ⊆ D := by
          intro x hx
          unfold Idle at hi
          rw [hth, thTasks_run_eq_empty] at hi
          exact hi x (mem_prims.1 hx).1
        have hst : TStep P c₁ ⟨c₁.st, Function.update c₁.th n (closed P.d μ)⟩ :=
          TStep.close hnk hth hsup
        have hcl : closed P.d μ = .fin := closed_of_idle hth hD hi
        obtain ⟨s₂, hr₂, h₂⟩ := complete_stepF hC h₁ hst
        refine ⟨_, s₂, hc₁.tail hst, hr₁.trans hr₂, h₂, hst₁,
          fun i hik => idle_of_step h₁.inv hst hik (hid₁ i hik), fun i hi' => ?_⟩
        show Function.update c₁.th n (closed P.d μ) i = .fin
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
        · rw [Function.update_of_ne (by omega)]; exact hf₁ i hi'
        · rw [Function.update_self, hcl]
      · exact absurd hth hfin

theorem grow_swp (hC : HypC P G N) {c : Cfg} {s : Set TF} (h : TRel P G c s)
    (hfin : ∀ i < P.k, c.th i = .fin) (h0 : TF.swp 0 ∈ s) :
    ∀ p ≤ P.k, Grow P G N c s (fun s' => TF.swp p ∈ s') := by
  intro p hp
  induction p with
  | zero => exact grow_refl h h0
  | succ p ih =>
    have hpk : p < P.k := by omega
    exact (ih (by omega)).bind fun s' h' hw =>
      grow_silent (pre := [TF.swp p, TF.fin p]) (mem_rCnt P.d (p := p) (by have := hC.kN'; omega)
        (by simp [rCnt])) (by simp [hw, h'.fin, hpk, hfin p hpk])
        (h'.insert_swp fun i hi hik => idle_fin _ (hfin i hik))

/-- **Completeness of the thread table.** -/
theorem solvF_of_tsolv (hC : HypC P G N) {s₀ : Set ℕ} {g : List ℕ}
    (h : TSolv P s₀ {v | v ∈ g}) : SolvF (thrTbl P.d N) (initG P G s₀) (goalF g) := by
  obtain ⟨c, hc, hidle, hg⟩ := h
  obtain ⟨s₁, hr₁, h₁⟩ := reach_of_tstep hC hc (trel_init (G := G) s₀)
  obtain ⟨c₂, s₂, -, hr₂, h₂, hst, -, hf₂⟩ := close_idle hC h₁ hidle P.k le_rfl
  have h0 : TF.swp 0 ∈ s₂ := swp_persist (hr₁.trans hr₂) (by simp [initG, initF])
  obtain ⟨s₃, hr₃, h₃, -, hw⟩ := grow_swp hC h₂ hf₂ h0 P.k le_rfl
  refine ⟨insert TF.done s₃, (hr₁.trans hr₂).trans (hr₃.tail (by
    rw [← apply_silent [TF.swp P.k, TF.len P.k]]
    exact stepF_row (mem_rCnt P.d hC.kN' (by simp [rCnt])) (by simp [hw, h₃.len]))), ?_⟩
  intro f hf
  simp only [goalF, List.mem_append, List.mem_map, List.mem_singleton] at hf
  rcases hf with ⟨v, hv, rfl⟩ | rfl
  · refine Or.inr ((h₃.inst v).2 ?_)
    rw [hst]
    exact hg hv
  · exact Set.mem_insert _ _

/-- **The thread system and the thread table agree.** -/
theorem tsolv_iff_solvF (hC : HypC P G N) {s₀ : Set ℕ} {g : List ℕ} :
    TSolv P s₀ {v | v ∈ g} ↔ SolvF (thrTbl P.d N) (initG P G s₀) (goalF g) :=
  ⟨solvF_of_tsolv hC, tsolv_of_solvF hC.toHyp⟩

end Thr

end Space

end HTN
