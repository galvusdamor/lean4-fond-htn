import HtnComplexity.AcVerify.VerSound
/-!
# Completeness of the verifier

`HTN.Syn.AcVer.acV_certOf`: for a path witness `W` whose dummy steps are normalised to `(k, 0)`
(which `HTN.Syn.AcVer.exists_pathOK0_of_solvable` provides), the certificate `certOf d q W` — the
records of the paths, the states after the entries (computed as lists by `nextL`), and the lists
of the actions — is accepted by the verifier.  Together with soundness,
`HTN.Syn.AcVer.solvable_iff_exists_acV`: a described problem is solvable iff some certificate is
accepted.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc} {q : InstDesc}

/-! ### The certificate -/

/-- The state list after applying the action `a` to the state list `L`. -/
def stepL (d : DomDesc) (a : ℕ) (L : List ℕ) : List ℕ :=
  ((L.filter fun f => decide (f ∉ (actLists d a).2.2)) ++ (actLists d a).2.1).dedup

/-- The state list after an entry. -/
def nextL (d : DomDesc) (q : InstDesc) (L : List ℕ) (u : Entry) : List ℕ :=
  if u.2 then L else stepL d (leafAct d q u.1) L

/-- The parsed certificate entry of the entry `u`, with the state list `L'` after it. -/
def ceOf (d : DomDesc) (q : InstDesc) (u : Entry) (L' : List ℕ) : CE where
  recs := u.1.map (recOf d q)
  st := L'.map bitsOfNat
  pr := if u.2 then [] else preS d (leafAct d q u.1)
  ad := if u.2 then [] else addS d (leafAct d q u.1)
  de := if u.2 then [] else delS d (leafAct d q u.1)
  f := u.2

/-- The parsed certificate of a witness, from the state list `L`. -/
def certL (d : DomDesc) (q : InstDesc) : List ℕ → List Entry → List CE
  | _, [] => []
  | L, u :: r => ceOf d q u (nextL d q L u) :: certL d q (nextL d q L u) r

/-- **The certificate of a witness.** -/
noncomputable def certOf (d : DomDesc) (q : InstDesc) (W : List Entry) : List Bool :=
  blist ((certL d q q.initList W).map CE.enc)

theorem stepsOf_ceOf (u : Entry) (L' : List ℕ) : stepsOf d q (ceOf d q u L') = u.1 :=
  stepsOf_eq rfl

theorem map_certL : ∀ (L : List ℕ) (W : List Entry),
    (certL d q L W).map (fun e => (stepsOf d q e, e.f)) = W
  | _, [] => rfl
  | L, u :: r => by
    simp only [certL, List.map_cons, stepsOf_ceOf, map_certL _ r]
    rfl

theorem recs_certL : ∀ (L : List ℕ) (W : List Entry), ∀ e ∈ certL d q L W,
    e.recs = (stepsOf d q e).map (recOf d q)
  | _, [] => by simp [certL]
  | L, u :: r => by
    intro e he
    simp only [certL, List.mem_cons] at he
    rcases he with rfl | he
    · rw [stepsOf_ceOf]; rfl
    · exact recs_certL _ r e he

theorem mem_certL : ∀ (L : List ℕ) (W : List Entry), ∀ e ∈ certL d q L W,
    ∃ u ∈ W, ∃ L', e = ceOf d q u L'
  | _, [] => by simp [certL]
  | L, u :: r => by
    intro e he
    simp only [certL, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨u, by simp, _, rfl⟩
    · obtain ⟨v, hv, L', rfl⟩ := mem_certL _ r e he
      exact ⟨v, by simp [hv], L', rfl⟩

/-! ### Execution -/

theorem mem_actLists_pre {a f : ℕ} : f ∈ (actLists d a).1 ↔ f ∈ (problem d q).prec a := by
  rw [← mem_map_bitsOfNat_iff (l := (actLists d a).1)]
  exact mem_preS

theorem mem_actLists_add {a f : ℕ} : f ∈ (actLists d a).2.1 ↔ f ∈ (problem d q).add a := by
  rw [← mem_map_bitsOfNat_iff (l := (actLists d a).2.1)]
  exact mem_addS

theorem mem_actLists_del {a f : ℕ} : f ∈ (actLists d a).2.2 ↔ f ∈ (problem d q).del a := by
  rw [← mem_map_bitsOfNat_iff (l := (actLists d a).2.2)]
  exact mem_delS

theorem setOf_stepL (a : ℕ) (L : List ℕ) :
    {f | f ∈ stepL d a L} = (problem d q).transition a {f | f ∈ L} := by
  ext f
  simp only [stepL, Set.mem_setOf_eq, List.mem_dedup, List.mem_append, List.mem_filter,
    decide_eq_true_eq, ActionModel.transition, Set.mem_union, Set.mem_diff]
  rw [mem_actLists_del (q := q), mem_actLists_add (q := q)]

theorem transL_ceOf (u : Entry) (L : List ℕ)
    (happ : u.2 = false → (problem d q).Applicable (leafAct d q u.1) {f | f ∈ L}) :
    TransL (ceOf d q u (nextL d q L u)) (L.map bitsOfNat) := by
  rcases hf : u.2
  · have happ := happ hf
    simp only [TransL, ceOf, nextL, hf, Bool.false_eq_true, if_false]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨f, hf', rfl⟩ := List.mem_map.1 hw
      exact mem_map_bitsOfNat_iff.2 (happ ((mem_actLists_pre (q := q)).1 hf'))
    · intro w hw
      obtain ⟨f, hf', rfl⟩ := List.mem_map.1 hw
      exact mem_map_bitsOfNat_iff.2 (by simp [stepL, hf'])
    · intro w hw
      obtain ⟨f, hf', rfl⟩ := List.mem_map.1 hw
      by_cases hd : f ∈ (actLists d (leafAct d q u.1)).2.2
      · exact Or.inl (mem_map_bitsOfNat_iff.2 hd)
      · exact Or.inr (mem_map_bitsOfNat_iff.2 (by simp [stepL, hf', hd]))
    · intro w hw
      obtain ⟨f, hf', rfl⟩ := List.mem_map.1 hw
      simp only [stepL, List.mem_dedup, List.mem_append, List.mem_filter,
        decide_eq_true_eq] at hf'
      rcases hf' with ⟨h1, h2⟩ | h3
      · exact Or.inr ⟨mem_map_bitsOfNat_iff.2 h1, fun h => h2 (mem_map_bitsOfNat_iff.1 h)⟩
      · exact Or.inl (mem_map_bitsOfNat_iff.2 h3)
  · simp only [TransL, ceOf, nextL, hf, if_true]
    refine ⟨by simp, by simp, fun w hw => Or.inr hw, fun w hw => Or.inr ⟨hw, by simp⟩⟩

theorem rowB_ceOf {u : Entry} (hu : EntryOK d q u) (L' : List ℕ) :
    rowB (advOf d) (ceOf d q u L').enc = true := by
  obtain ⟨i, s, hs⟩ := first_of_entryOK hu
  obtain ⟨p', x, hpx⟩ : ∃ p' x, u.1 = p' ++ [x] := by
    rcases u.1.eq_nil_or_concat with h0 | ⟨p', x, h1⟩
    · rw [h0] at hs; simp at hs
    · exact ⟨p', x, by simpa using h1⟩
  have hlast : u.1.getLast? = some x := by rw [hpx]; simp
  have hrecs : (ceOf d q u L').recs = u.1.map (recOf d q) := rfl
  refine (rowB_iff (ceOf d q u L') u.1 x (leafAct d q u.1) hrecs hlast (fun hf => ?_)).2 ?_
  · have hE := hu
    unfold EntryOK at hE
    simp only [show u.2 = false from hf, Bool.false_eq_true, if_false] at hE
    obtain ⟨a, ha⟩ := hE.2
    have hl : lastLabel d q u.1 = stepLabel d q x := by simp [lastLabel, hlast]
    rw [hl] at ha
    simp [leafAct, hl, ha]
  · unfold RowOK
    rcases hf : u.2 <;> simp [ceOf, hf]

theorem actsOf_cons (u : Entry) (W : List Entry) :
    actsOf d q (u :: W) = if u.2 then actsOf d q W else leafAct d q u.1 :: actsOf d q W := by
  rcases hf : u.2 <;> simp [actsOf, hf]

theorem execChain_certL {W : List Entry} (hW : ∀ u ∈ W, EntryOK d q u) :
    ∀ (L : List ℕ) (z : List Bool) (W' : List Entry), (∀ u ∈ W', u ∈ W) →
    (problem d q).SeqApplicable (actsOf d q W') {f | f ∈ L} →
    (problem d q).GoalState ((problem d q).transitionSeq (actsOf d q W') {f | f ∈ L}) →
    ExecChain d q (blist (L.map bitsOfNat) ++ z) (certL d q L W')
  | L, z, [], _, _, hg => by
    simp only [certL, ExecChain]
    rw [yB_instSer, zB, subEntB_iff]
    intro w hw
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hw
    exact mem_map_bitsOfNat_iff.2 (hg (by simpa [problem, Domain.mkProblem,
      InstDesc.toInstance] using hf))
  | L, z, u :: r, hsub, ha, hg => by
    have huW := hsub u (by simp)
    simp only [certL, ExecChain]
    rw [actsOf_cons] at ha hg
    have hst : stOf (ceOf d q u (nextL d q L u)).enc =
        blist ((nextL d q L u).map bitsOfNat) ++ prOf (ceOf d q u (nextL d q L u)).enc :=
      enc_eq_st _
    refine ⟨(transB_iff _ _ z).2 ⟨transL_ceOf u L (fun hf => ?_), rowB_ceOf (hW u huW) _⟩, ?_⟩
    · rw [hf] at ha; exact ha.1
    · rw [hst]
      refine execChain_certL hW _ _ r (fun v hv => hsub v (by simp [hv])) ?_ ?_
      · rcases hf : u.2
        · rw [hf] at ha
          simp only [nextL, hf, Bool.false_eq_true, if_false, setOf_stepL (q := q)]
          exact ha.2
        · rw [hf] at ha; simpa [nextL, hf] using ha
      · rcases hf : u.2
        · rw [hf] at hg
          simp only [nextL, hf, Bool.false_eq_true, if_false, setOf_stepL (q := q)]
          exact hg
        · rw [hf] at hg; simpa [nextL, hf] using hg

/-! ### Acceptance -/

/-- **Completeness of the verifier**: the certificate of a path witness with normalised dummy
steps is accepted. -/
theorem acV_certOf {W : List Entry} (hW : PathOK d q W)
    (h0 : ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) :
    acV [instSer q, advOf d, certOf d q W] = true := by
  set cs := certL d q q.initList W with hcs_def
  have hmap : cs.map (fun e => (stepsOf d q e, e.f)) = W := map_certL _ _
  have hrec : ∀ e ∈ cs, e.recs = (stepsOf d q e).map (recOf d q) := recs_certL _ _
  have hent : ∀ e ∈ cs, EntryOK0 d q (stepsOf d q e, e.f) := by
    intro e he
    obtain ⟨u, hu, L', rfl⟩ := mem_certL _ _ e he
    rw [stepsOf_ceOf]
    exact ⟨hW.entries u hu, h0 u hu⟩
  have hmemW : ∀ e ∈ cs, (stepsOf d q e, e.f) ∈ W := fun e he => by
    rw [← hmap]; exact List.mem_map_of_mem he
  unfold acV certOf
  rw [← hcs_def]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
  refine ⟨⟨⟨⟨blistB_iff.2 ⟨_, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- per entry
    have key : ∀ c ∈ cs.map CE.enc, (parseB c && recsB (instSer q) (advOf d) c &&
        childB (advOf d) (blist (cs.map CE.enc)) c) = true := by
      intro c hc
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      simp only [Bool.and_eq_true]
      refine ⟨⟨parseB_encEnt _ _ _ _ _ _, ?_⟩, ?_⟩
      · exact (recsB_iff d q e _ (hrec e he)).2 ((recs_iff_entryOK0 _ _).2 (hent e he))
      · refine (childB_iff cs hrec e _ (hrec e he)).2 ?_
        intro l₁ y l₂ hsplit hne j hj hk
        obtain ⟨P, x, rfl⟩ := (List.eq_nil_or_concat l₁).resolve_left hne
        have hu := hmemW e he
        have hj' : j ∈ (netOf d q y.1).ids := by rw [netOf_of_ne (mIdx_ne_zero hk)]; exact hj
        obtain ⟨v, hv, s', hvs⟩ := hW.children _ hu P x y l₂ (by rw [hsplit]; simp) j hj'
        rw [← hmap] at hv
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 hv
        exact ⟨e', he', s', by simpa using hvs⟩
    have := (entAll_mem (fun E => parseB (cont E) && recsB (instSer q) (advOf d) (cont E) &&
        childB (advOf d) (blist (cs.map CE.enc)) (cont E)) (cs.map CE.enc) []).2
      (fun c hc => by simp only [cont_entry]; exact key c hc)
    rw [List.append_nil] at this
    exact this
  · -- roots
    refine (rootsB_iff cs hrec).2 ?_
    rw [hmap]; exact hW.roots
  · -- pairs
    have hp : W.Pairwise (PairOK d q) := hW.pairs
    rw [← hmap, List.pairwise_map, pairwise_iff_splits] at hp
    rw [show blist (cs.map CE.enc) = blist (cs.map CE.enc) ++ [] by simp]
    unfold pairsB
    rw [entAll_iff, forall_split_map CE.enc cs (fun l₁ w l₂ => _ = true)]
    intro m₁ eu m₂ hsplit
    rw [entAll_iff, forall_split_map CE.enc m₂ (fun l₁ w l₂ => _ = true)]
    intro n₁ ev n₂ hn
    rw [cont_entry, cont_entry]
    have heu : eu ∈ cs := by rw [hsplit]; simp
    have hevm : ev ∈ cs := by rw [hsplit, hn]; simp
    have hpo := hp m₁ eu m₂ hsplit ev (by rw [hn]; simp)
    refine (pairB_iff (d := d) (q := q) (stepsOf d q eu) (stepsOf d q ev) _ _ _ _
      (enc_eq_recs eu |>.trans (by rw [hrec eu heu]))
      (enc_eq_recs ev |>.trans (by rw [hrec ev hevm]))
      eu.f ev.f (CE.flagOf_enc _) (CE.flagOf_enc _) ?_).2 hpo
    intro hfu hfv
    have h1 := (hent eu heu).1
    have h2 := (hent ev hevm).1
    rw [hfu] at h1; rw [hfv] at h2
    exact ⟨leafSteps_of_entryOK h1, leafSteps_of_entryOK h2⟩
  · -- execution
    refine (execB_iff cs).2 ?_
    have hex := hW.exec
    unfold ExecOK at hex
    have hinit : (problem d q).init = {f | f ∈ q.initList} := rfl
    rw [hinit] at hex
    rw [instSer_eq]
    exact execChain_certL hW.entries q.initList (zB q) W (fun _ h => h) hex.1 hex.2

/-- **Plan existence is the existence of an accepted certificate.** -/
theorem solvable_iff_exists_acV :
    Solvable d q ↔ ∃ w, acV [instSer q, advOf d, w] = true := by
  constructor
  · intro h
    obtain ⟨W, hW, h0⟩ := exists_pathOK0_of_solvable h
    exact ⟨_, acV_certOf hW h0⟩
  · rintro ⟨w, hw⟩
    exact solvable_of_acV hw

end AcVer

end Syn

end HTN
