import FondHtn.Weak.Compile
import FondHtn.Hardness.FromDet
/-!
# The weak compilation on descriptions

`FOND.weakDesc : FProbDesc → ProbDesc`, the description-level version of [CB21, Lemma 4.3]:

* the deterministic action `⟨a, j⟩ = Nat.pair a j` is action `a` with its `j`-th effect;
* a compound name `c` becomes `2c`, a primitive name `a` becomes the compound name `2a + 1`;
* every method is kept with its labels mapped, and `2a + 1 → ⟨a, j⟩` is added for each effect `j`
  of each declared action `a`.

`FOND.weakLD_iff_weakDesc`: a well-formed description has a weak LD solution iff its translation
is solvable.  `FOND.pt_weakDesc`: the translation runs in polynomial time.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.TaskNetwork

/-! ## The translation -/

/-- The mapped label of a description entry: every task becomes compound. -/
def wLbl (q : ℕ × Bool × ℕ) : ℕ × Bool × ℕ :=
  (q.1, true, bif q.2.1 then 2 * q.2.2 else 2 * q.2.2 + 1)

/-- The task network with mapped labels. -/
def wrapTn (t : TnDesc) : TnDesc := (t.1, t.2.1, t.2.2.map wLbl)

/-- A method with mapped labels. -/
def wrapMD (m : MethodDesc) : MethodDesc := (2 * m.1, wrapTn m.2)

/-- The deterministic actions of an action description, one per effect. -/
def detActs (y : FActDesc) : List ActDesc :=
  (List.range y.effs.length).map fun j =>
    (Nat.pair y.1 j, y.2.1, y.2.2.1, (y.effs.getI j).1, (y.effs.getI j).2)

/-- The leaf methods of an action description, one per effect. -/
def leafMDs (y : FActDesc) : List MethodDesc :=
  (List.range y.effs.length).map fun j => (2 * y.1 + 1, ([0], [], [(0, false, Nat.pair y.1 j)]))

/-- **The translation.** -/
def weakDesc (p : FProbDesc) : ProbDesc :=
  ((p.actions.flatMap detActs, p.methods.map wrapMD ++ p.actions.flatMap leafMDs),
    (p.init, wrapTn p.tnI, [], []))

/-! ## Polynomial time -/

theorem pt_wrapTn : PT wrapTn := by
  unfold wrapTn
  refine PT.pair PT.fst (PT.pair (PT.fst.comp PT.snd) (PT.map (PT.snd.comp PT.snd) ?_))
  unfold wLbl
  exact PT.pair (PT.fst.comp PT.snd) (PT.pair (PT.const true)
    (PT.cond (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.affine 2 0 (PT.snd.comp (PT.snd.comp PT.snd)) |>.of_eq fun _ => by ring)
      (PT.affine 2 1 (PT.snd.comp (PT.snd.comp PT.snd)))))

theorem pt_weakDesc : PT weakDesc := by
  have hacts : PT fun p : FProbDesc => p.actions := PT.fst.comp PT.fst
  have hE : PT fun y : FActDesc => y.effs := PT.snd.comp (PT.snd.comp PT.snd)
  have hdet : PT detActs := by
    unfold detActs
    refine PT.map (PT.rangeLength hE) ?_
    have hg : PT fun q : FActDesc × ℕ => q.1.effs.getI q.2 := PT.getI (hE.comp PT.fst) PT.snd
    exact PT.pair (PT.natPair (PT.fst.comp PT.fst) PT.snd)
      (PT.pair (PT.fst.comp (PT.snd.comp PT.fst)) (PT.pair (PT.fst.comp (PT.snd.comp (PT.snd.comp
        PT.fst))) (PT.pair (PT.fst.comp hg) (PT.snd.comp hg))))
  have hleaf : PT leafMDs := by
    unfold leafMDs
    refine PT.map (PT.rangeLength hE) ?_
    exact PT.pair (PT.affine 2 1 (PT.fst.comp PT.fst)) (PT.pair (PT.const _) (PT.pair (PT.const _)
      (PT.single (PT.pair (PT.const 0) (PT.pair (PT.const false)
        (PT.natPair (PT.fst.comp PT.fst) PT.snd))))))
  have hwrapMD : PT wrapMD := by
    unfold wrapMD
    exact PT.pair (PT.affine 2 0 PT.fst |>.of_eq fun _ => by ring) (pt_wrapTn.comp PT.snd)
  unfold weakDesc
  exact PT.pair (PT.pair (PT.flatMap hacts (hdet.comp PT.snd))
      (PT.append (PT.map (PT.snd.comp PT.fst) (hwrapMD.comp PT.snd))
        (PT.flatMap hacts (hleaf.comp PT.snd))))
    (PT.pair (PT.fst.comp PT.snd) (PT.pair (pt_wrapTn.comp (PT.snd.comp PT.snd)) (PT.const _)))

/-! ## Lists and lookups -/

theorem lookup_map_wLbl (l : List (ℕ × Bool × ℕ)) (x : ℕ) :
    (l.map wLbl).lookup x = (l.lookup x).map fun b => (true, bif b.1 then 2 * b.2 else 2 * b.2 + 1) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons, List.lookup, wLbl]
    split
    · rfl
    · exact ih

theorem lookup_isSome_of_mem {β : Type} {l : List (ℕ × β)} {x : ℕ} (h : x ∈ l.map Prod.fst) :
    (l.lookup x).isSome := by
  induction l with
  | nil => simp at h
  | cons q l ih =>
    simp only [List.map_cons, List.mem_cons] at h
    simp only [List.lookup]
    split
    · rfl
    · rename_i hq
      rcases h with h | h
      · rw [h] at hq; simp at hq
      · exact ih h

theorem label_inl_of_mem {prim : ℕ → Prop} {t : TnDesc} (h : TnValid prim t) {x n : ℕ}
    (hx : x ∈ t.ids) (hl : t.label x = Sum.inl n) : prim n := by
  have hs := lookup_isSome_of_mem ((h.lbl_perm.mem_iff).2 hx)
  unfold TnDesc.label at hl
  split at hl
  · cases hl
  · rename_i b hb; cases hl; exact h.prim_ok _ (lookup_mem hb) rfl
  · rename_i hb; rw [hb] at hs; cases hs

/-- The coding of names of the compilation. -/
def wUn (n : ℕ) : ℕ ⊕ ℕ := if n % 2 = 1 then Sum.inl (n / 2) else Sum.inr (n / 2)

/-- The label map `e` of the compilation on `ℕ`. -/
def wE : ℕ ⊕ ℕ → ℕ ⊕ ℕ := Sum.elim (fun a => Sum.inr (2 * a + 1)) (fun c => Sum.inr (2 * c))

theorem label_wrapTn {prim : ℕ → Prop} {t : TnDesc} (h : TnValid prim t) {x : ℕ}
    (hx : x ∈ t.ids) : (wrapTn t).label x = wE (t.label x) := by
  have hs := lookup_isSome_of_mem ((h.lbl_perm.mem_iff).2 hx)
  unfold TnDesc.label
  simp only [wrapTn, TnDesc.lbl, lookup_map_wLbl]
  obtain ⟨⟨b, n⟩, hb⟩ := Option.isSome_iff_exists.1 hs
  simp only [TnDesc.lbl] at hb
  rw [hb]
  cases b <;> simp [wE]

theorem wrapTn_toTaskNetwork_iso {prim : ℕ → Prop} {t : TnDesc} (h : TnValid prim t) :
    (t.toTaskNetwork.mapL wE).Iso (wrapTn t).toTaskNetwork :=
  ⟨id, Set.bijOn_id _, fun _ _ _ _ => Iff.rfl, fun x hx => by
    simp only [mapL_α, id]
    exact (label_wrapTn h (by simpa [TnDesc.toTaskNetwork] using hx)).symm⟩

theorem wrapTn_label_inr {prim : ℕ → Prop} {t : TnDesc} (h : TnValid prim t) {x : ℕ}
    (hx : x ∈ t.ids) : ∃ c, (wrapTn t).label x = Sum.inr c := by
  rw [label_wrapTn h hx]
  cases t.label x <;> simp [wE]

theorem find?_of_mem {β : Type} {name : β → ℕ} {l : List β} (hl : (l.map name).Nodup) {y : β}
    (hy : y ∈ l) : l.find? (fun x => name x == name y) = some y := by
  obtain ⟨x, hx⟩ : ∃ x, l.find? (fun x => name x == name y) = some x := by
    cases h : l.find? (fun x => name x == name y) with
    | none => exact absurd (List.find?_eq_none.1 h y hy) (by simp)
    | some x => exact ⟨x, rfl⟩
  rw [hx]
  have hxm := List.mem_of_find?_eq_some hx
  have hxn : name x = name y := by simpa using List.find?_some hx
  rw [List.inj_on_of_nodup_map hl hxm hy hxn]

/-! ## The compilation data -/

/-- The `j`-th effect of the action named `a` (the first one if `j` is too large; `(∅, ∅)` for an
undeclared name). -/
def effL (p : FProbDesc) (a j : ℕ) : List ℕ × List ℕ :=
  match p.actions.find? (fun x => x.name == a) with
  | some x => x.effs.getD j x.effs.headI
  | none => ([], [])

theorem effL_of_mem {p : FProbDesc} (hp : p.Valid) {y : FActDesc} (hy : y ∈ p.actions) (j : ℕ) :
    effL p y.name j = y.effs.getD j y.effs.headI := by
  unfold effL; rw [find?_of_mem hp.names_nodup hy]

theorem getD_mem_of_ne {β : Type} {l : List β} (hl : l ≠ []) (j : ℕ) [Inhabited β] :
    l.getD j l.headI ∈ l := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
  · rw [List.getD_eq_default _ _ (by omega)]
    obtain ⟨y, l', rfl⟩ := List.exists_cons_of_ne_nil hl
    simp

/-- The data of the weak compilation of a well-formed description. -/
def wData (p : FProbDesc) (hp : p.Valid) : WeakData p.toProblem ℕ ℕ where
  act x := x.unpair.1
  eff x := ({f | f ∈ (effL p x.unpair.1 x.unpair.2).1}, {f | f ∈ (effL p x.unpair.1 x.unpair.2).2})
  heff x := by
    show _ ∈ (p.δ x.unpair.1).effs
    by_cases hd : p.Declared x.unpair.1
    · obtain ⟨y, hy, hyn⟩ := List.mem_map.1 hd
      rw [← hyn, FProbDesc.δ_of_mem hp hy, effL_of_mem hp hy]
      exact ⟨_, getD_mem_of_ne (hp.effs_ne y hy) _, rfl⟩
    · have hnone : p.actions.find? (fun z => z.name == x.unpair.1) = none := by
        rw [List.find?_eq_none]
        intro z hz hza
        exact hd (List.mem_map.2 ⟨z, hz, by simpa using hza⟩)
      simp only [FProbDesc.δ, effL, hnone]
      simp
  wr a := 2 * a + 1
  cw c := 2 * c
  un := wUn
  un_wr a := by simp [wUn]; omega
  un_cw c := by simp [wUn]
  leaf := {x | ∃ y ∈ p.actions, ∃ j < y.effs.length, x = Nat.pair y.name j}
  i₀ := 0

theorem wData_e (p : FProbDesc) (hp : p.Valid) : (wData p hp).e = wE := rfl

/-! ## Well-formedness -/

theorem detActs_names (y : FActDesc) :
    (detActs y).map ActDesc.name = (List.range y.effs.length).map (Nat.pair y.name) := by
  simp [detActs, ActDesc.name, FActDesc.name, Function.comp_def]

theorem weakDesc_names (p : FProbDesc) :
    (weakDesc p).actions.map ActDesc.name =
      p.actions.flatMap fun y => (List.range y.effs.length).map (Nat.pair y.name) := by
  simp only [weakDesc, ProbDesc.actions, List.map_flatMap, detActs_names]

theorem mem_weakDesc_names {p : FProbDesc} {n : ℕ} :
    n ∈ (weakDesc p).actions.map ActDesc.name ↔
      ∃ y ∈ p.actions, ∃ j < y.effs.length, n = Nat.pair y.name j := by
  rw [weakDesc_names]
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨y, hy, j, hj, rfl⟩; exact ⟨y, hy, j, hj, rfl⟩
  · rintro ⟨y, hy, j, hj, rfl⟩; exact ⟨y, hy, j, hj, rfl⟩

theorem weakDesc_names_nodup {p : FProbDesc} (hp : p.Valid) :
    ((weakDesc p).actions.map ActDesc.name).Nodup := by
  rw [weakDesc_names]
  refine List.nodup_flatMap.2 ⟨fun y _ => (List.nodup_range).map (fun a b h => by
    simpa using Nat.pair_eq_pair.1 h), ?_⟩
  have hn : p.actions.Pairwise (fun a b => a.name ≠ b.name) :=
    List.pairwise_map.1 hp.names_nodup
  refine hn.imp fun {a b} hab => ?_
  show List.Disjoint _ _
  rw [List.disjoint_left]
  intro n hna hnb
  simp only [List.mem_map, List.mem_range] at hna hnb
  obtain ⟨j, -, rfl⟩ := hna
  obtain ⟨j', -, h⟩ := hnb
  exact hab (Nat.pair_eq_pair.1 h).1.symm

theorem wrapTn_valid {prim prim' : ℕ → Prop} {t : TnDesc} (h : TnValid prim t) :
    TnValid prim' (wrapTn t) where
  nodup := h.nodup
  ord_mem := h.ord_mem
  irrefl := h.irrefl
  trans := h.trans
  lbl_perm := by simpa [wrapTn, TnDesc.lbl, TnDesc.ids, wLbl, Function.comp_def] using h.lbl_perm
  prim_ok := by
    intro q hq hq'
    simp only [wrapTn, TnDesc.lbl, List.mem_map] at hq
    obtain ⟨r, -, rfl⟩ := hq
    simp [wLbl] at hq'

theorem weakDesc_valid {p : FProbDesc} (hp : p.Valid) : (weakDesc p).Valid where
  names_nodup := weakDesc_names_nodup hp
  tnI := wrapTn_valid hp.tnI
  methods := by
    intro m hm
    simp only [weakDesc, ProbDesc.methods, List.mem_append, List.mem_map, List.mem_flatMap] at hm
    rcases hm with ⟨e, he, rfl⟩ | ⟨y, hy, hm⟩
    · exact wrapTn_valid (hp.methods e he)
    · simp only [leafMDs, List.mem_map, List.mem_range] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      refine ⟨by simp [TnDesc.ids], by simp [TnDesc.ordList], by simp [TnDesc.ordList],
        by simp [TnDesc.ordList], by simp [TnDesc.lbl, TnDesc.ids], ?_⟩
      intro q hq _
      simp only [TnDesc.lbl, List.mem_singleton] at hq
      subst hq
      exact mem_weakDesc_names.2 ⟨y, hy, j, hj, rfl⟩

/-! ## The described problem -/

theorem mem_leaf {p : FProbDesc} (hp : p.Valid) {x : ℕ} :
    x ∈ (wData p hp).leaf ↔ ∃ y ∈ p.actions, ∃ j < y.effs.length, x = Nat.pair y.name j := Iff.rfl

theorem weakDesc_δ {p : FProbDesc} (hp : p.Valid) {x : ℕ} (hx : x ∈ (wData p hp).leaf) :
    (weakDesc p).toProblem.δ x = (wData p hp).detAct x := by
  obtain ⟨y, hy, j, hj, rfl⟩ := hx
  let z : ActDesc := (Nat.pair y.1 j, y.2.1, y.2.2.1, (y.effs.getI j).1, (y.effs.getI j).2)
  have hz : z ∈ (weakDesc p).actions := by
    simp only [weakDesc, ProbDesc.actions, List.mem_flatMap]
    exact ⟨y, hy, by simp [detActs, z, hj]⟩
  have hfind := find?_of_mem (weakDesc_names_nodup hp) hz
  change ProbDesc.δ (weakDesc p) (Nat.pair y.name j) = (wData p hp).detAct (Nat.pair y.name j)
  have hf : (weakDesc p).actions.find? (fun x => x.name == Nat.pair y.name j) = some z := hfind
  unfold ProbDesc.δ
  rw [hf]
  have hget : y.effs.getI j = y.effs.getD j y.effs.headI := by
    rw [List.getI_eq_getElem _ hj, List.getD_eq_getElem _ _ hj]
  simp only [WeakData.detAct, wData, Nat.unpair_pair]
  rw [show p.toProblem.δ y.name = y.toAction from FProbDesc.δ_of_mem hp hy, effL_of_mem hp hy, ← hget]
  rfl

theorem weakSpec {p : FProbDesc} (hp : p.Valid) :
    WeakSpec (wData p hp) (weakDesc p).toProblem.methods (weakDesc p).toProblem.tnI
      (weakDesc p).toProblem.δ where
  wrap := by
    rintro m ⟨e, he, rfl⟩
    refine ⟨(wrapMD e).toMethod, ⟨wrapMD e, ?_, rfl⟩, rfl, ?_⟩
    · exact List.mem_append_left _ (List.mem_map_of_mem he)
    · rw [wData_e]; exact wrapTn_toTaskNetwork_iso (hp.methods e he)
  leaf := by
    rintro x ⟨y, hy, j, hj, rfl⟩
    refine ⟨MethodDesc.toMethod (2 * y.1 + 1, ([0], [], [(0, false, Nat.pair y.1 j)])), ⟨_, ?_, rfl⟩, ?_,
      TnDesc.toTaskNetwork_wf _, 0, ?_, ?_⟩
    · simp only [weakDesc, ProbDesc.methods, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨y, hy, by simp [leafMDs, hj]⟩
    · simp [MethodDesc.toMethod, wData, Nat.unpair_pair, FActDesc.name]
    · simp [MethodDesc.toMethod, TnDesc.toTaskNetwork, TnDesc.ids]
    · simp [MethodDesc.toMethod, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup,
        FActDesc.name]
  meth := by
    rintro m' ⟨e', he', rfl⟩
    refine ⟨TnDesc.toTaskNetwork_wf _, ?_⟩
    simp only [weakDesc, ProbDesc.methods, List.mem_append, List.mem_map, List.mem_flatMap] at he'
    rcases he' with ⟨e, he, rfl⟩ | ⟨y, hy, hm⟩
    · left
      refine ⟨e.toMethod, ⟨e, he, rfl⟩, by simp [wrapMD, MethodDesc.toMethod, wData, wUn], ?_, ?_⟩
      · refine ⟨id, Set.bijOn_id _, fun _ _ _ _ => Iff.rfl, fun x hx => ?_⟩
        have hx' : x ∈ e.2.ids := by simpa [MethodDesc.toMethod, wrapMD, TnDesc.toTaskNetwork,
          wrapTn, TnDesc.ids] using hx
        simp only [mapL_α, id, MethodDesc.toMethod, wrapMD, TnDesc.toTaskNetwork]
        rw [label_wrapTn (hp.methods e he) hx', ← wData_e p hp, ← Function.comp_apply (f := (wData p hp).ψ),
          (wData p hp).ψ_e]
        rfl
      · intro x hx
        have hx' : x ∈ e.2.ids := by simpa [MethodDesc.toMethod, wrapMD, TnDesc.toTaskNetwork,
          wrapTn, TnDesc.ids] using hx
        exact wrapTn_label_inr (hp.methods e he) hx'
    · right
      simp only [leafMDs, List.mem_map, List.mem_range] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      refine ⟨Nat.pair y.1 j, ⟨y, hy, j, hj, rfl⟩, by simp [MethodDesc.toMethod, wData, FActDesc.name], 0,
        by simp [MethodDesc.toMethod, TnDesc.toTaskNetwork, TnDesc.ids], ?_⟩
      simp [MethodDesc.toMethod, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup]
  tnI := by
    rw [wData_e]
    exact (wrapTn_toTaskNetwork_iso hp.tnI).symm
  tnI_wf := TnDesc.toTaskNetwork_wf _
  act x hx := weakDesc_δ hp hx

theorem wData_covers {p : FProbDesc} (hp : p.Valid) : (wData p hp).Covers := by
  intro a hu e he
  have hdecl : p.Declared a := by
    rcases hu with ⟨t, ht, hta⟩ | ⟨m, ⟨em, hem, rfl⟩, t, ht, hta⟩
    · exact label_inl_of_mem hp.tnI (List.mem_toFinset.1 ht) hta
    · exact label_inl_of_mem (hp.methods em hem)
        (List.mem_toFinset.1 ht) hta
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hdecl
  change e ∈ (p.δ y.name).effs at he
  rw [FProbDesc.δ_of_mem hp hy] at he
  obtain ⟨z, hz, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
  refine ⟨Nat.pair y.name j, ⟨y, hy, j, hj, rfl⟩, by simp [wData], ?_⟩
  simp only [wData, Nat.unpair_pair, effL_of_mem hp hy, List.getD_eq_getElem _ _ hj]

/-- **[CB21, Lemma 4.3] on descriptions.** -/
theorem weakLD_iff_weakDesc {p : FProbDesc} (hp : p.Valid) :
    p.toProblem.WeakLDSolvable ↔ (weakDesc p).toProblem.Solvable := by
  have h := Problem.weakLDSolvable_iff_weakDet (wData p hp) (FProbDesc.toProblem_wf hp)
    (wData_covers hp) (weakSpec hp)
  have heq : p.toProblem.weakDet (weakDesc p).toProblem.methods (weakDesc p).toProblem.tnI
      (weakDesc p).toProblem.δ = (weakDesc p).toProblem := by
    unfold Problem.weakDet ProbDesc.toProblem
    congr 1 <;> ext <;> simp [weakDesc, ProbDesc.goalPos, ProbDesc.goalNeg, ProbDesc.init,
      FProbDesc.toProblem, FProbDesc.init]
  rw [h, heq]

end FOND
