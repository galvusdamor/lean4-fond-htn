import HtnComplexity.Space.ThrTbl
/-!
# The thread table simulates the thread system: the relation and soundness

`HTN.Space.Thr.TRel P G c s` relates a thread configuration `c` to a fact set `s`: the facts of
the state and of the threads are exactly those of `c`, the static facts are those of the graph
data `G`, and the silent facts (`ok`, `rch`, `unused`, `swp`, `done`) are justified.

`HTN.Space.Thr.sound_stepF`: a row step from a related fact set is matched by at most one step of
the thread system.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG

/-- The graph data of the initial fact set: the ordering graph on node numbers, the guessed
closed relation, the certificate pairs and the inert witness pairs. -/
structure Gr where
  E : ℕ → ℕ → Prop
  Cl : ℕ → ℕ → Prop
  NC : ℕ → ℕ → Prop
  W : ℕ → ℕ → Prop

/-- The initial fact set of graph data. -/
def initG (P : Par) (G : Gr) (s₀ : Set ℕ) : Set TF := initF P G.E G.Cl G.NC G.W s₀

/-- **The hypotheses of soundness**: a good thread system with at most `N` threads, whose slot
order is the strict part of the reachability of the graph, a closed superset `Cl` of the graph
and certificate pairs outside it. -/
structure Hyp (P : Par) (G : Gr) (N : ℕ) : Prop where
  good : Good P
  kN : P.k ≤ N
  hO : ∀ i < P.k, ∀ j < P.k, (P.O i j ↔ Relation.TransGen G.E i j ∧ ¬ Relation.TransGen G.E j i)
  cl1 : ∀ x y, G.E x y → G.Cl x y
  cl2 : ∀ x y z, G.Cl x y → G.E y z → G.Cl x z
  nc : ∀ x y, G.NC x y → ¬ G.Cl x y

/-- **The simulation relation.** -/
structure TRel (P : Par) (G : Gr) (c : Cfg) (s : Set TF) : Prop where
  inv : Inv P c
  inst : ∀ v, TF.inst v ∈ s ↔ v ∈ c.st
  lab : ∀ j x, TF.lab j x ∈ s ↔ j < P.k ∧ x = P.lab j ∧ (c.th j = .pend ∨ Unk P.d x)
  nop : ∀ j, TF.nop j ∈ s ↔ j < P.k ∧ Unk P.d (P.lab j) ∧ c.th j = .pend
  len : ∀ p, TF.len p ∈ s ↔ p = P.k
  wit : ∀ p a, TF.wit p a ∈ s ↔ G.W p a
  edge : ∀ x y, TF.edge x y ∈ s ↔ G.E x y
  cl : ∀ x y, TF.cl x y ∈ s ↔ G.Cl x y
  nc : ∀ x y, TF.nc x y ∈ s ↔ G.NC x y
  cur : ∀ j c', TF.cur j c' ∈ s ↔ j < P.k ∧ c.th j = .cur c'
  blk : ∀ j μ, TF.blk j μ ∈ s ↔ j < P.k ∧ ∃ D, c.th j = .run μ D
  tok : ∀ j μ x, TF.tok j μ x ∈ s ↔ j < P.k ∧ ∃ D, c.th j = .run μ D ∧ x ∈ prims P.d μ ∧ x ∉ D
  don : ∀ j μ x, TF.don j μ x ∈ s ↔ j < P.k ∧ ∃ D, c.th j = .run μ D ∧ x ∈ D
  fin : ∀ j, TF.fin j ∈ s ↔ j < P.k ∧ c.th j = .fin
  ok : ∀ i j, TF.ok i j ∈ s → i < P.k → j < P.k → ¬ P.O i j ∨ Idle P c.th i
  rch : ∀ x y, TF.rch x y ∈ s → Relation.TransGen G.E x y
  unused : ∀ p, TF.unused p ∈ s → P.k ≤ p
  swp : ∀ p, TF.swp p ∈ s → ∀ i < p, i < P.k → Idle P c.th i
  done : TF.done ∈ s → ∀ i < P.k, Idle P c.th i
  pend : ∀ j, P.k ≤ j → c.th j = .pend

variable {P : Par} {G : Gr}

theorem trel_init (s₀ : Set ℕ) : TRel P G (initCfg s₀) (initG P G s₀) where
  inv := inv_init s₀
  inst v := Iff.rfl
  lab j x := by simp [initG, initF, initCfg, eq_comm]
  nop j := by simp [initG, initF, initCfg]
  len p := Iff.rfl
  wit p a := Iff.rfl
  edge x y := Iff.rfl
  cl x y := Iff.rfl
  nc x y := Iff.rfl
  cur j c' := by simp [initG, initF, initCfg]
  blk j μ := by simp [initG, initF, initCfg]
  tok j μ x := by simp [initG, initF, initCfg]
  don j μ x := by simp [initG, initF, initCfg]
  fin j := by simp [initG, initF, initCfg]
  ok i j h := by simp [initG, initF] at h
  rch x y h := by simp [initG, initF] at h
  unused p h := by simp [initG, initF] at h
  swp p h := by
    simp only [initG, initF, Set.mem_setOf_eq] at h
    subst h
    intro i hi
    omega
  done h := by simp [initG, initF] at h
  pend j _ := rfl

/-! ### Helpers -/

theorem idle_fin (th : ℕ → TSt) {i : ℕ} (h : th i = .fin) : Idle P th i := by
  unfold Idle; rw [h]; rfl

theorem not_unk_inr (d : DomDesc) (c : ℕ) : ¬ Unk d (Sum.inr c) := by
  simp [Unk, unknownPrimB]

theorem not_unk_of_mem_vocA {d : DomDesc} {a : ℕ} (ha : a ∈ vocA d) : ¬ Unk d (Sum.inl a) := by
  simp [Unk, unknownPrimB, ha]

theorem lookup_eq_none_of_nmem {β : Type} (l : List (ℕ × β)) (a : ℕ) (h : a ∉ l.map Prod.fst) :
    l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨b, y⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hb : (a == b) = false := by simpa using h.1
    simp only [List.lookup, hb]
    exact ih h.2

theorem actOf_of_unk {d : DomDesc} {a : ℕ} (h : Unk d (Sum.inl a)) : actOf d a = ([], [], []) := by
  have ha : a ∉ vocA d := by simpa [Unk, unknownPrimB] using h
  have hn : a ∉ d.actions.map Prod.fst := fun h' => ha (names_actions_subset_vocA d h')
  rw [actOf_eq]
  rw [lookup_eq_none_of_nmem _ _ hn]
  rfl

/-! ### Silent rows -/

theorem apply_silent (pre : List TF) (f : TF) (s : Set TF) :
    apply (pre, [f], []) s = insert f s := by
  ext g; simp [or_comm]

theorem TRel.insert_ok {c : Cfg} {s : Set TF} (h : TRel P G c s) {i j : ℕ}
    (hij : i < P.k → j < P.k → ¬ P.O i j ∨ Idle P c.th i) : TRel P G c (insert (TF.ok i j) s) where
  inv := h.inv
  inst v := by simp [h.inst]
  lab j x := by simp [h.lab]
  nop j := by simp [h.nop]
  len p := by simp [h.len]
  wit p a := by simp [h.wit]
  edge x y := by simp [h.edge]
  cl x y := by simp [h.cl]
  nc x y := by simp [h.nc]
  cur j c' := by simp [h.cur]
  blk j μ := by simp [h.blk]
  tok j μ x := by simp [h.tok]
  don j μ x := by simp [h.don]
  fin j := by simp [h.fin]
  ok i' j' hm := by
    rcases hm with hm | hm
    · simp only [TF.ok.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact hij
    · exact h.ok i' j' hm
  rch x y hm := h.rch x y (by simpa using hm)
  unused p hm := h.unused p (by simpa using hm)
  swp p hm := h.swp p (by simpa using hm)
  done hm := h.done (by simpa using hm)
  pend := h.pend

theorem TRel.insert_rch {c : Cfg} {s : Set TF} (h : TRel P G c s) {x y : ℕ}
    (hxy : Relation.TransGen G.E x y) :
    TRel P G c (insert (TF.rch x y) s) where
  inv := h.inv
  inst v := by simp [h.inst]
  lab j x := by simp [h.lab]
  nop j := by simp [h.nop]
  len p := by simp [h.len]
  wit p a := by simp [h.wit]
  edge x y := by simp [h.edge]
  cl x y := by simp [h.cl]
  nc x y := by simp [h.nc]
  cur j c' := by simp [h.cur]
  blk j μ := by simp [h.blk]
  tok j μ x := by simp [h.tok]
  don j μ x := by simp [h.don]
  fin j := by simp [h.fin]
  ok i' j' hm := h.ok i' j' (by simpa using hm)
  rch x' y' hm := by
    rcases hm with hm | hm
    · simp only [TF.rch.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact hxy
    · exact h.rch x' y' hm
  unused p hm := h.unused p (by simpa using hm)
  swp p hm := h.swp p (by simpa using hm)
  done hm := h.done (by simpa using hm)
  pend := h.pend

theorem TRel.insert_unused {c : Cfg} {s : Set TF} (h : TRel P G c s) {p : ℕ} (hp : P.k ≤ p) :
    TRel P G c (insert (TF.unused p) s) where
  inv := h.inv
  inst v := by simp [h.inst]
  lab j x := by simp [h.lab]
  nop j := by simp [h.nop]
  len p := by simp [h.len]
  wit p a := by simp [h.wit]
  edge x y := by simp [h.edge]
  cl x y := by simp [h.cl]
  nc x y := by simp [h.nc]
  cur j c' := by simp [h.cur]
  blk j μ := by simp [h.blk]
  tok j μ x := by simp [h.tok]
  don j μ x := by simp [h.don]
  fin j := by simp [h.fin]
  ok i' j' hm := h.ok i' j' (by simpa using hm)
  rch x y hm := h.rch x y (by simpa using hm)
  unused p' hm := by
    rcases hm with hm | hm
    · simp only [TF.unused.injEq] at hm
      subst hm
      exact hp
    · exact h.unused p' hm
  swp p hm := h.swp p (by simpa using hm)
  done hm := h.done (by simpa using hm)
  pend := h.pend

theorem TRel.insert_swp {c : Cfg} {s : Set TF} (h : TRel P G c s) {p : ℕ}
    (hp : ∀ i < p, i < P.k → Idle P c.th i) :
    TRel P G c (insert (TF.swp p) s) where
  inv := h.inv
  inst v := by simp [h.inst]
  lab j x := by simp [h.lab]
  nop j := by simp [h.nop]
  len p := by simp [h.len]
  wit p a := by simp [h.wit]
  edge x y := by simp [h.edge]
  cl x y := by simp [h.cl]
  nc x y := by simp [h.nc]
  cur j c' := by simp [h.cur]
  blk j μ := by simp [h.blk]
  tok j μ x := by simp [h.tok]
  don j μ x := by simp [h.don]
  fin j := by simp [h.fin]
  ok i' j' hm := h.ok i' j' (by simpa using hm)
  rch x y hm := h.rch x y (by simpa using hm)
  unused p hm := h.unused p (by simpa using hm)
  swp p' hm := by
    rcases hm with hm | hm
    · simp only [TF.swp.injEq] at hm
      subst hm
      exact hp
    · exact h.swp p' hm
  done hm := h.done (by simpa using hm)
  pend := h.pend

theorem TRel.insert_done {c : Cfg} {s : Set TF} (h : TRel P G c s) 
    (hp : ∀ i < P.k, Idle P c.th i) :
    TRel P G c (insert (TF.done) s) where
  inv := h.inv
  inst v := by simp [h.inst]
  lab j x := by simp [h.lab]
  nop j := by simp [h.nop]
  len p := by simp [h.len]
  wit p a := by simp [h.wit]
  edge x y := by simp [h.edge]
  cl x y := by simp [h.cl]
  nc x y := by simp [h.nc]
  cur j c' := by simp [h.cur]
  blk j μ := by simp [h.blk]
  tok j μ x := by simp [h.tok]
  don j μ x := by simp [h.don]
  fin j := by simp [h.fin]
  ok i' j' hm := h.ok i' j' (by simpa using hm)
  rch x y hm := h.rch x y (by simpa using hm)
  unused p hm := h.unused p (by simpa using hm)
  swp p hm := h.swp p (by simpa using hm)
  done hm := hp
  pend := h.pend

end Thr

end Space

end HTN

set_option hygiene false in
/-- Closes the silent fields of a thread step. -/
macro "silent_close" : tactic => `(tactic| first
  | (rcases hok _ _ ‹_› ‹_› ‹_› with h1 | h1
     · exact Or.inl h1
     · exact Or.inr (hid _ ‹_› h1))
  | exact hrch _ _ ‹_›
  | exact hunused _ ‹_›
  | exact hid _ ‹_› (hswp _ ‹_› _ ‹_› ‹_›)
  | exact hid _ ‹_› (hdone ‹_› _ ‹_›)
  | (rw [Function.update_of_ne (by omega)]; exact hpend _ ‹_›))

set_option hygiene false in
/-- Proves the fields of the relation after a thread step (all but the invariant). -/
macro "thr_auto" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  all_goals obtain ⟨-, hinst, hlab, hnop, hlen, hwit, hedge, hcl, hnc, hcur, hblk, htok, hdon, hfin, hok,
    hrch, hunused, hswp, hdone, hpend⟩ := h
  all_goals intros
  all_goals simp only [mem_apply, rExpC, rExpP, rClose, rExec, rExecP, rNop, startL, doneL, oks,
    List.mem_cons, List.mem_map, List.mem_append, List.not_mem_nil, reduceCtorEq, false_or, or_false,
    and_false, and_true, not_false_eq_true, exists_false, TF.cur.injEq, TF.blk.injEq, TF.tok.injEq,
    TF.lab.injEq, TF.don.injEq, TF.fin.injEq, TF.nop.injEq, TF.inst.injEq] at *
  all_goals try silent_close
  all_goals try simp only [Function.update_apply]
  all_goals try split_ifs with hjj
  all_goals try subst hjj
  all_goals try simp [hinst, hlab, hnop, hlen, hwit, hedge, hcl, hnc, hcur, hblk, htok, hdon, hfin, hj,
    mem_primsL, $ts,*]
  all_goals first | tauto | aesop))

namespace HTN.Space.Thr
open Syn SeqG
variable {P : Par} {G : Gr}

@[simp] theorem unk_inr (d : DomDesc) (c : ℕ) : Unk d (Sum.inr c) ↔ False :=
  iff_false_intro (not_unk_inr d c)

theorem TRel.expC (hP : Good P) {c : Cfg} {s : Set TF} (h : TRel P G c s) {j μ : ℕ} (hj : j < P.k)
    (hs : c.th j = .cur (head P.d μ)) (hμ : μ < P.d.methods.length) :
    TRel P G ⟨c.st, Function.update c.th j (.run μ ∅)⟩ (apply (rExpC P.d j μ) s) := by
  have hstep : TStep P c ⟨c.st, Function.update c.th j (.run μ ∅)⟩ := TStep.expandC hj hs hμ
  have hid : ∀ i < P.k, Idle P c.th i → Idle P (Function.update c.th j (.run μ ∅)) i :=
    fun i hi => idle_of_step h.inv hstep hi
  refine ⟨inv_step hP h.inv hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  thr_auto [hs]

theorem TRel.expP (hP : Good P) {c : Cfg} {s : Set TF} (h : TRel P G c s) {j μ : ℕ} (hj : j < P.k)
    (hs : c.th j = .pend) (hl : P.lab j = Sum.inr (head P.d μ)) (hμ : μ < P.d.methods.length)
    (hpre : ∀ i < P.k, P.O i j → Idle P c.th i) (N : ℕ) :
    TRel P G ⟨c.st, Function.update c.th j (.run μ ∅)⟩ (apply (rExpP P.d N j μ) s) := by
  have hstep : TStep P c ⟨c.st, Function.update c.th j (.run μ ∅)⟩ := TStep.expandP hj hs hl hμ hpre
  have hid : ∀ i < P.k, Idle P c.th i → Idle P (Function.update c.th j (.run μ ∅)) i :=
    fun i hi => idle_of_step h.inv hstep hi
  refine ⟨inv_step hP h.inv hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  thr_auto [hs, hl]

theorem precList_eq_actOf (d : DomDesc) (a : ℕ) : d.precList a = (actOf d a).1 := by
  rw [actOf_eq, DomDesc.precList]; cases d.actions.lookup a <;> rfl

theorem addList_eq_actOf (d : DomDesc) (a : ℕ) : d.addList a = (actOf d a).2.1 := by
  rw [actOf_eq, DomDesc.addList]; cases d.actions.lookup a <;> rfl

theorem delList_eq_actOf (d : DomDesc) (a : ℕ) : d.delList a = (actOf d a).2.2 := by
  rw [actOf_eq, DomDesc.delList]; cases d.actions.lookup a <;> rfl

theorem TRel.close (hP : Good P) {c : Cfg} {s : Set TF} (h : TRel P G c s) {j μ : ℕ} {D : Finset ℕ}
    (hj : j < P.k) (hs : c.th j = .run μ D) (hD : prims P.d μ ⊆ D) :
    TRel P G ⟨c.st, Function.update c.th j (closed P.d μ)⟩ (apply (rClose P.d j μ) s) := by
  have hstep : TStep P c ⟨c.st, Function.update c.th j (closed P.d μ)⟩ := TStep.close hj hs hD
  have hid : ∀ i < P.k, Idle P c.th i → Idle P (Function.update c.th j (closed P.d μ)) i :=
    fun i hi => idle_of_step h.inv hstep hi
  have hsub : ∀ x ∈ D, x ∈ prims P.d μ := fun x hx => (h.inv.run j hj μ D hs).2 hx
  have hsup : ∀ x ∈ prims P.d μ, x ∈ D := fun x hx => hD hx
  have hcF : closedF P.d j μ = match tail P.d μ with
    | some cc => TF.cur j cc
    | none => TF.fin j := rfl
  have hc : closed P.d μ = match tail P.d μ with
    | some cc => TSt.cur cc
    | none => TSt.fin := rfl
  rcases ht : tail P.d μ with _ | cc
  all_goals simp only [ht] at hc hcF
  all_goals rw [hc] at hstep hid ⊢
  all_goals refine ⟨inv_step hP h.inv hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  all_goals simp only [rClose, hcF]
  all_goals thr_auto [hs, hsub, hsup]

theorem TRel.exec (hP : Good P) {c : Cfg} {s : Set TF} (h : TRel P G c s) {j μ x a : ℕ}
    {D : Finset ℕ} (hj : j < P.k) (hs : c.th j = .run μ D) (hx : x ∈ prims P.d μ) (hxD : x ∉ D)
    (hpre : ∀ y, (body P.d μ).ordOf y x → y ∈ D) (hl : (body P.d μ).label x = Sum.inl a)
    (happ : P.d.prec a ⊆ c.st) :
    TRel P G ⟨(c.st \ P.d.del a) ∪ P.d.add a, Function.update c.th j (.run μ (insert x D))⟩
      (apply (rExec P.d j μ x a) s) := by
  have hstep : TStep P c ⟨(c.st \ P.d.del a) ∪ P.d.add a,
      Function.update c.th j (.run μ (insert x D))⟩ := TStep.exec hj hs hx hxD hpre hl happ
  have hid : ∀ i < P.k, Idle P c.th i → Idle P (Function.update c.th j (.run μ (insert x D))) i :=
    fun i hi => idle_of_step h.inv hstep hi
  refine ⟨inv_step hP h.inv hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals thr_auto [hs, addList_eq_actOf, delList_eq_actOf]

theorem TRel.execP (hP : Good P) {c : Cfg} {s : Set TF} (h : TRel P G c s) {j a : ℕ}
    (hj : j < P.k) (hs : c.th j = .pend) (hl : P.lab j = Sum.inl a) (ha : a ∈ vocA P.d)
    (hpre : ∀ i < P.k, P.O i j → Idle P c.th i) (happ : P.d.prec a ⊆ c.st) (N : ℕ) :
    TRel P G ⟨(c.st \ P.d.del a) ∪ P.d.add a, Function.update c.th j .fin⟩
      (apply (rExecP P.d N j a) s) := by
  have hstep : TStep P c ⟨(c.st \ P.d.del a) ∪ P.d.add a, Function.update c.th j .fin⟩ :=
    TStep.execP hj hs hl hpre happ
  have hid : ∀ i < P.k, Idle P c.th i → Idle P (Function.update c.th j .fin) i :=
    fun i hi => idle_of_step h.inv hstep hi
  have hna := not_unk_of_mem_vocA ha
  refine ⟨inv_step hP h.inv hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals thr_auto [hs, hl, hna, addList_eq_actOf, delList_eq_actOf]

theorem TRel.skip (hP : Good P) {c : Cfg} {s : Set TF} (h : TRel P G c s) {j a : ℕ}
    (hj : j < P.k) (hs : c.th j = .pend) (hl : P.lab j = Sum.inl a) (hu : Unk P.d (Sum.inl a))
    (hpre : ∀ i < P.k, P.O i j → Idle P c.th i) (N : ℕ) :
    TRel P G ⟨(c.st \ P.d.del a) ∪ P.d.add a, Function.update c.th j .fin⟩
      (apply (rNop N j) s) := by
  have hact := actOf_of_unk hu
  have happ : P.d.prec a ⊆ c.st := by simp [precList_eq_actOf, hact]
  have hstep : TStep P c ⟨(c.st \ P.d.del a) ∪ P.d.add a, Function.update c.th j .fin⟩ :=
    TStep.execP hj hs hl hpre happ
  have hid : ∀ i < P.k, Idle P c.th i → Idle P (Function.update c.th j .fin) i :=
    fun i hi => idle_of_step h.inv hstep hi
  refine ⟨inv_step hP h.inv hstep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals thr_auto [hs, hl, hu, hact, addList_eq_actOf, delList_eq_actOf]

/-! ### Soundness of a step -/

theorem cl_of_transGen {N : ℕ} (hH : Hyp P G N) {x y : ℕ} (h : Relation.TransGen G.E x y) :
    G.Cl x y := by
  induction h with
  | single h => exact hH.cl1 _ _ h
  | tail _ hyz ih => exact hH.cl2 _ _ _ ih hyz

theorem TRel.pre_of_oks {N : ℕ} (hH : Hyp P G N) {c : Cfg} {s : Set TF} (h : TRel P G c s) {j : ℕ}
    (hj : j < P.k) (ho : ∀ f ∈ oks N j, f ∈ s) : ∀ i < P.k, P.O i j → Idle P c.th i := by
  intro i hi hO
  have hij : i ≠ j := fun e => hH.good.irrefl i (e ▸ hO)
  have hm : TF.ok i j ∈ s := ho _ (by
    simp only [oks, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨i, ⟨by have := hH.kN; omega, hij⟩, rfl⟩)
  rcases h.ok i j hm hi hj with h1 | h1
  · exact absurd hO h1
  · exact h1

theorem isLeft_of_tail_none {d : DomDesc} {μ : ℕ} (ht : tail d μ = none) {z : ℕ}
    (hz : z ∈ (body d μ).ids) : ((body d μ).label z).isLeft := by
  unfold tail at ht
  rcases hl : (body d μ).label z with a | cc
  · rfl
  · have : cc ∈ (body d μ).compoundNames := TnDesc.mem_compoundNames.2 ⟨z, hz, hl⟩
    rcases hh : (body d μ).compoundNames with _ | ⟨c', l⟩
    · rw [hh] at this; simp at this
    · rw [hh] at ht; simp at ht

theorem TRel.run_of_blk {c : Cfg} {s : Set TF} (h : TRel P G c s) {j μ : ℕ}
    (hb : TF.blk j μ ∈ s) : j < P.k ∧ ∃ D, c.th j = .run μ D := (h.blk j μ).1 hb

theorem TRel.mem_of_don {c : Cfg} {s : Set TF} (h : TRel P G c s) {j μ x : ℕ} {D : Finset ℕ}
    (hs : c.th j = .run μ D) (hd : TF.don j μ x ∈ s) : x ∈ D := by
  obtain ⟨-, D', hs', hx⟩ := (h.don j μ x).1 hd
  rw [hs] at hs'
  cases hs'
  exact hx

theorem TRel.prec_sub {c : Cfg} {s : Set TF} (h : TRel P G c s) {a : ℕ}
    (hp : ∀ f ∈ (actOf P.d a).1.map TF.inst, f ∈ s) : P.d.prec a ⊆ c.st := by
  intro v hv
  simp only [DomDesc.prec_eq, precList_eq_actOf, Set.mem_setOf_eq] at hv
  exact (h.inst v).1 (hp _ (List.mem_map_of_mem hv))

theorem exists_inl_of_unk {d : DomDesc} {x : ℕ ⊕ ℕ} (h : Unk d x) : ∃ a, x = Sum.inl a := by
  rcases x with a | cc
  · exact ⟨a, rfl⟩
  · exact absurd h (not_unk_inr d cc)

/-- **Soundness of a row step**: it is matched by at most one step of the thread system. -/
theorem sound_stepF {N : ℕ} (hH : Hyp P G N) {c : Cfg} {s s' : Set TF} (h : TRel P G c s)
    (hst : StepF (thrTbl P.d N) s s') :
    ∃ c', Relation.ReflTransGen (TStep P) c c' ∧ TRel P G c' s' := by
  obtain ⟨r, hr, hpre, rfl⟩ := hst
  have hP := hH.good
  simp only [thrTbl, rOks, rRch, rCnt, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hr
  rcases hr with ((((⟨j, hjN, μ, hμ, (rfl | rfl | rfl) | ⟨x, hx, hr⟩⟩ |
      ⟨j, hjN, ⟨a, ha, rfl⟩ | rfl⟩) |
      ⟨i, hiN, j, hjN, (rfl | rfl | rfl | rfl) | ⟨μ, hμ, hr⟩⟩) |
      ⟨x, -, y, -, z, -, rfl | rfl⟩) |
      ⟨p, -, rfl | rfl | rfl | rfl⟩)
  · -- expand a pending task
    have hl := hpre (TF.lab j (Sum.inr (head P.d μ))) (by simp [rExpP])
    obtain ⟨hj, hl, hs⟩ := (h.lab _ _).1 hl
    have hs : c.th j = .pend := by simpa using hs
    have ho : ∀ f ∈ oks N j, f ∈ s := fun f hf => hpre f (by simp [rExpP, hf])
    exact ⟨_, .single (TStep.expandP hj hs hl.symm hμ (h.pre_of_oks hH hj ho)),
      h.expP hP hj hs hl.symm hμ (h.pre_of_oks hH hj ho) N⟩
  · -- expand a current task
    obtain ⟨hj, hs⟩ := (h.cur _ _).1 (hpre (TF.cur j (head P.d μ)) (by simp [rExpC]))
    exact ⟨_, .single (TStep.expandC hj hs hμ), h.expC hP hj hs hμ⟩
  · -- close a body
    obtain ⟨hj, D, hs⟩ := h.run_of_blk (hpre (TF.blk j μ) (by simp [rClose, doneL]))
    have hD : prims P.d μ ⊆ D := fun x hx =>
      h.mem_of_don hs (hpre (TF.don j μ x) (by simp [rClose, doneL, mem_primsL, hx]))
    exact ⟨_, .single (TStep.close hj hs hD), h.close hP hj hs hD⟩
  · -- execute a primitive subtask
    unfold rExecs at hr
    rcases hlx : (body P.d μ).label x with a | cc
    · rw [hlx] at hr
      simp only [List.mem_singleton] at hr
      subst hr
      obtain ⟨hj, D, hs, hxp, hxD⟩ := (h.tok _ _ _).1 (hpre (TF.tok j μ x) (by simp [rExec]))
      have hpd : ∀ y, (body P.d μ).ordOf y x → y ∈ D := fun y hy =>
        h.mem_of_don hs (hpre (TF.don j μ y) (by simp [rExec, mem_predsL, hy]))
      have happ : P.d.prec a ⊆ c.st := h.prec_sub fun f hf => hpre f (by simp [rExec, hf])
      exact ⟨_, .single (TStep.exec hj hs hxp hxD hpd hlx happ),
        h.exec hP hj hs hxp hxD hpd hlx happ⟩
    · rw [hlx] at hr
      simp at hr
  · -- execute a pending primitive task
    obtain ⟨hj, hl, hs⟩ := (h.lab _ _).1 (hpre (TF.lab j (Sum.inl a)) (by simp [rExecP]))
    have hs : c.th j = .pend := by
      rcases hs with hs | hs
      · exact hs
      · exact absurd hs (not_unk_of_mem_vocA ha)
    have ho : ∀ f ∈ oks N j, f ∈ s := fun f hf => hpre f (by simp [rExecP, hf])
    have happ : P.d.prec a ⊆ c.st := h.prec_sub fun f hf => hpre f (by simp [rExecP, hf])
    exact ⟨_, .single (TStep.execP hj hs hl.symm (h.pre_of_oks hH hj ho) happ),
      h.execP hP hj hs hl.symm ha (h.pre_of_oks hH hj ho) happ N⟩
  · -- skip an unknown primitive task
    obtain ⟨hj, hu, hs⟩ := (h.nop _).1 (hpre (TF.nop j) (by simp [rNop]))
    obtain ⟨a, hl⟩ := exists_inl_of_unk hu
    rw [hl] at hu
    have ho : ∀ f ∈ oks N j, f ∈ s := fun f hf => hpre f (by simp [rNop, hf])
    have happ : P.d.prec a ⊆ c.st := by simp [precList_eq_actOf, actOf_of_unk hu]
    exact ⟨_, .single (TStep.execP hj hs hl (h.pre_of_oks hH hj ho) happ),
      h.skip hP hj hs hl hu (h.pre_of_oks hH hj ho) N⟩
  · -- ok from a finished thread
    obtain ⟨-, hf⟩ := (h.fin i).1 (hpre (TF.fin i) (by simp))
    exact ⟨c, .refl, by rw [apply_silent]; exact h.insert_ok fun _ _ => Or.inr (idle_fin _ hf)⟩
  · -- ok from a certificate
    have hnc := (h.nc i j).1 (hpre (TF.nc i j) (by simp))
    refine ⟨c, .refl, ?_⟩
    rw [apply_silent]
    refine h.insert_ok fun hi hj => Or.inl fun hO => ?_
    exact hH.nc _ _ hnc (cl_of_transGen hH ((hH.hO i hi j hj).1 hO).1)
  · -- ok from reachability
    have hr := h.rch j i (hpre (TF.rch j i) (by simp))
    refine ⟨c, .refl, ?_⟩
    rw [apply_silent]
    refine h.insert_ok fun hi hj => Or.inl fun hO => ?_
    exact ((hH.hO i hi j hj).1 hO).2 hr
  · -- ok from an unused slot
    have hu := h.unused i (hpre (TF.unused i) (by simp))
    exact ⟨c, .refl, by rw [apply_silent]; exact h.insert_ok fun hi _ => absurd hi (by omega)⟩
  · -- ok from an idle running thread
    unfold rZok at hr
    rcases ht : tail P.d μ with _ | cc
    · rw [ht] at hr
      simp only [List.mem_singleton] at hr
      subst hr
      obtain ⟨hi, D, hs⟩ := h.run_of_blk (hpre (TF.blk i μ) (by simp [doneL]))
      have hidle : Idle P c.th i := by
        unfold Idle
        rw [hs, thTasks_run_eq_empty]
        intro z hz
        exact h.mem_of_don hs (hpre (TF.don i μ z) (by
          simp [doneL, mem_primsL, mem_prims, hz, isLeft_of_tail_none ht hz]))
      exact ⟨c, .refl, by rw [apply_silent]; exact h.insert_ok fun _ _ => Or.inr hidle⟩
    · rw [ht] at hr
      simp at hr
  · -- reachability from an edge
    have he := (h.edge x y).1 (hpre (TF.edge x y) (by simp))
    exact ⟨c, .refl, by rw [apply_silent]; exact h.insert_rch (.single he)⟩
  · -- reachability along an edge
    have hr := h.rch x y (hpre (TF.rch x y) (by simp))
    have he := (h.edge y z).1 (hpre (TF.edge y z) (by simp))
    exact ⟨c, .refl, by rw [apply_silent]; exact h.insert_rch (hr.tail he)⟩
  · -- the first unused slot
    have hl := (h.len p).1 (hpre (TF.len p) (by simp))
    exact ⟨c, .refl, by rw [apply_silent]; exact h.insert_unused (by omega)⟩
  · -- the next unused slot
    have hu := h.unused p (hpre (TF.unused p) (by simp))
    exact ⟨c, .refl, by rw [apply_silent]; exact h.insert_unused (by omega)⟩
  · -- the sweep advances
    have hw := h.swp p (hpre (TF.swp p) (by simp))
    obtain ⟨-, hf⟩ := (h.fin p).1 (hpre (TF.fin p) (by simp))
    refine ⟨c, .refl, ?_⟩
    rw [apply_silent]
    refine h.insert_swp fun i hi hik => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hw i hi hik
    · exact idle_fin _ hf
  · -- the sweep ends
    have hw := h.swp p (hpre (TF.swp p) (by simp))
    have hl := (h.len p).1 (hpre (TF.len p) (by simp))
    subst hl
    exact ⟨c, .refl, by rw [apply_silent]; exact h.insert_done fun i hi => hw i hi hi⟩

/-- **Soundness of the thread table.** -/
theorem tsolv_of_solvF {N : ℕ} (hH : Hyp P G N) {s₀ : Set ℕ} {g : List ℕ}
    (h : SolvF (thrTbl P.d N) (initG P G s₀) (goalF g)) : TSolv P s₀ {v | v ∈ g} := by
  obtain ⟨s, hs, hg⟩ := h
  have key : ∀ s', Relation.ReflTransGen (StepF (thrTbl P.d N)) (initG P G s₀) s' →
      ∃ c', Relation.ReflTransGen (TStep P) (initCfg s₀) c' ∧ TRel P G c' s' := by
    intro s' hs'
    induction hs' with
    | refl => exact ⟨_, .refl, trel_init s₀⟩
    | tail _ hst ih =>
      obtain ⟨c', hc', hr⟩ := ih
      obtain ⟨c'', hc'', hr'⟩ := sound_stepF hH hr hst
      exact ⟨c'', hc'.trans hc'', hr'⟩
  obtain ⟨c, hc, hr⟩ := key s hs
  refine ⟨c, hc, hr.done (hg _ (by simp [goalF])), fun v hv => ?_⟩
  exact (hr.inst v).1 (hg _ (by simp [goalF]; exact hv))

end HTN.Space.Thr
