import HtnComplexity.HDDecide.Rep
import HtnComplexity.HDDecide.SemLemmas
import HtnComplexity.HDDecide.Sound
/-!
# Completeness of the search on pieces for one-hole-digging problems

This is Lemma 6 of Dekker and Behnke: a solvable one-hole-digging problem is solved by the
bidirectional search that decomposes the compound task only when it is isolated.

The proof is by induction on the pair (number of decomposition steps of the solution, length of
its linearization), ordered lexicographically.  Given a network `tn` (represented by pieces), a
decomposition sequence `tn →ⁿ tn*` into a primitive network and an executable linearization `l`
of `tn*`:

* if `tn` has no compound task, the search progresses the first task of `l`;
* if the compound task `x` of `tn` is isolated, the decomposition sequence can be reordered to
  decompose `x` first (`HTN.DecomposesToN.pull_out`), and the search decomposes it;
* if `x` has a predecessor, then the first task of `l` is not produced by `x` (everything `x`
  produces lies after that predecessor, `HTN.DecomposesTo.ord_after`), so it is a task of `tn`
  without predecessors, and the search progresses it;
* if `x` has a successor, symmetrically the last task of `l` is a task of `tn` without
  successors, and the search regresses it.
-/

namespace HTN

namespace HD

open Syn

variable {d : DomDesc} {q : InstDesc}

/-! ### Finite state sequences -/

/-- The state a sequence of actions reaches, on finite states. -/
def nxtSeq (d : DomDesc) (s : Finset ℕ) (as : List ℕ) : Finset ℕ := as.foldl (nxtF d) s

@[simp] theorem nxtSeq_nil (s : Finset ℕ) : nxtSeq d s [] = s := rfl

@[simp] theorem nxtSeq_cons (s : Finset ℕ) (a : ℕ) (as : List ℕ) :
    nxtSeq d s (a :: as) = nxtSeq d (nxtF d s a) as := rfl

theorem nxtSeq_concat (s : Finset ℕ) (as : List ℕ) (a : ℕ) :
    nxtSeq d s (as ++ [a]) = nxtF d (nxtSeq d s as) a := by
  simp [nxtSeq, List.foldl_append]

theorem coe_nxtF' (s : Finset ℕ) (a : ℕ) :
    ({f | f ∈ nxtF d s a} : Set ℕ) = (problem d q).transition a {f | f ∈ s} :=
  coe_nxtF d s a

theorem coe_nxtSeq : ∀ (as : List ℕ) (s : Finset ℕ),
    ({f | f ∈ nxtSeq d s as} : Set ℕ) = (problem d q).transitionSeq as {f | f ∈ s} := by
  intro as
  induction as with
  | nil => intro s; rfl
  | cons a as ih =>
    intro s
    rw [nxtSeq_cons, ih]
    show _ = (problem d q).transitionSeq as ((problem d q).transition a _)
    rw [coe_nxtF' (q := q)]

theorem nxtF_subset {s : Finset ℕ} (hs : s ⊆ facts d q) (a : ℕ) : nxtF d s a ⊆ facts d q := by
  intro f hf
  simp only [nxtF, Finset.mem_union, Finset.mem_filter, List.mem_toFinset] at hf
  rcases hf with ⟨hf, -⟩ | hf
  · exact hs hf
  · exact List.mem_toFinset.2 (mem_allFacts_of_mem_add hf)

theorem nxtSeq_subset : ∀ (as : List ℕ) {s : Finset ℕ}, s ⊆ facts d q →
    nxtSeq d s as ⊆ facts (d := d) q := by
  intro as
  induction as with
  | nil => exact fun hs => hs
  | cons a as ih => exact fun hs => ih (nxtF_subset hs a)

theorem seqApplicable_concat {as : List ℕ} {a : ℕ} :
    ∀ {S : Set ℕ}, (problem d q).SeqApplicable (as ++ [a]) S →
      (problem d q).SeqApplicable as S ∧
        (problem d q).Applicable a ((problem d q).transitionSeq as S) := by
  induction as with
  | nil => intro S h; exact ⟨trivial, h.1⟩
  | cons b as ih =>
    intro S h
    obtain ⟨hb, h'⟩ := h
    obtain ⟨h1, h2⟩ := ih h'
    exact ⟨⟨hb, h1⟩, h2⟩

/-! ### Representation of a dropped task -/

theorem RepW.drop {tn : TaskNetwork ℕ ℕ ℕ} {M : Multiset Piece} {U : Finset ℕ}
    {inst loc kind : ℕ → ℕ} (hw : RepW d q tn tn.T M U inst loc kind) {t : ℕ} (ht : t ∈ tn.T) :
    RepW d q (tn.drop t) (tn.drop t).T (M.erase (kind (inst t), Sof tn.T inst loc (inst t)) +
        piece (kind (inst t)) ((Sof tn.T inst loc (inst t)).erase (loc t))) U inst loc kind :=
  (hw.erase ht).transfer (fun _ _ => rfl) (fun a ha b hb => by
    simp only [TaskNetwork.drop_ord]
    exact ⟨fun h => h.1, fun h => ⟨h, Finset.ne_of_mem_erase ha, Finset.ne_of_mem_erase hb⟩⟩)

/-! ### The induction -/

/-- **Completeness of the search on pieces**, the inductive statement. -/
theorem comp_main (hd : d.MethodsHD1) : ∀ (n L : ℕ) (tn tnS : TaskNetwork ℕ ℕ ℕ)
    (l as : List ℕ) (sf : Finset ℕ) (M : Multiset Piece),
    l.length = L → tn.WF → Rep d q tn tn.T M → tn.IsOneHole →
    DecomposesToN (problem d q).methods n tn tnS → tnS.IsPrimitive → tnS.IsLinearization l →
    tnS.IsActionSeq l as → (problem d q).SeqApplicable as {f | f ∈ sf} → sf ⊆ facts d q →
    ∃ s, HReach d q (sf, nxtSeq d sf as, M) (s, s, 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ihL =>
  intro tn tnS l as sf M hL hwf hrep h1 hdec hprimS hlin has happ hsf
  obtain ⟨U, inst, loc, kind, hw⟩ := hrep
  have hdecT := hdec.decomposesTo
  -- progressing the first task of the linearization
  have headCase : ∀ h l', l = h :: l' → h ∈ tn.T → tn.IsPrimitiveId h →
      (∀ y ∈ tn.T, ¬ tn.ord y h) → ∃ s, HReach d q (sf, nxtSeq d sf as, M) (s, s, 0) := by
    intro h l' hl hT hp hmin
    subst hl
    have hαS : tnS.α h = tn.α h := DecomposesTo.α_eq_of_prim hdecT hT hp
    obtain ⟨a, as', rfl, hα, has'⟩ : ∃ a as', as = a :: as' ∧ tn.α h = Sum.inl a ∧
        l'.map tnS.α = as'.map Sum.inl := by
      cases as with
      | nil => simp [TaskNetwork.IsActionSeq] at has
      | cons a as' =>
        simp only [TaskNetwork.IsActionSeq, List.map_cons, List.cons.injEq] at has
        exact ⟨a, as', rfl, hαS ▸ has.1, has.2⟩
    obtain ⟨happa, happ'⟩ := happ
    have happF : appF d sf a := (appF_iff d sf a).2 happa
    have hstep := HStep.prog sf (nxtSeq d sf (a :: as')) M _ _ _ a (hw.mem_M hT)
      (RepW.loc_mem_Sof hT) (hw.min_of_not_ord hT hmin) (by rw [← hw.lbl h hT]; exact hα) happF
    obtain ⟨s, hs⟩ := ihL l'.length (by rw [← hL]; simp) (tn.drop h) (tnS.drop h) l' as' (nxtF d sf a) _
      rfl (TaskNetwork.drop_wf hwf h) ⟨U, inst, loc, kind, hw.drop hT⟩ (h1.drop h)
      (hdec.drop hT hp) (hprimS.drop h) (TaskNetwork.isLinearization_drop_head hlin)
      (by simpa [TaskNetwork.IsActionSeq] using has')
      (by rw [coe_nxtF' (q := q)]; exact happ') (nxtF_subset hsf a)
    exact ⟨s, Relation.ReflTransGen.head hstep hs⟩
  -- regressing the last task of the linearization
  have lastCase : ∀ h l', l = l' ++ [h] → h ∈ tn.T → tn.IsPrimitiveId h →
      (∀ y ∈ tn.T, ¬ tn.ord h y) → ∃ s, HReach d q (sf, nxtSeq d sf as, M) (s, s, 0) := by
    intro h l' hl hT hp hmax
    subst hl
    have hαS : tnS.α h = tn.α h := DecomposesTo.α_eq_of_prim hdecT hT hp
    obtain ⟨as', a, rfl, hα, has'⟩ : ∃ as' a, as = as' ++ [a] ∧ tn.α h = Sum.inl a ∧
        l'.map tnS.α = as'.map Sum.inl := by
      simp only [TaskNetwork.IsActionSeq, List.map_append, List.map_cons, List.map_nil] at has
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 has.symm
      obtain ⟨a, rfl, ha⟩ := List.map_eq_singleton_iff.1 h₂
      exact ⟨l₁, a, rfl, hαS ▸ ha.symm, h₁.symm⟩
    obtain ⟨happ', happa⟩ := seqApplicable_concat happ
    rw [← coe_nxtSeq] at happa
    have happF : appF d (nxtSeq d sf as') a := (appF_iff d _ a).2 happa
    have hstep := HStep.regr sf (nxtSeq d sf (as' ++ [a])) (nxtSeq d sf as') M _ _ _ a
      (hw.mem_M hT) (RepW.loc_mem_Sof hT) (hw.max_of_not_ord hT hmax)
      (by rw [← hw.lbl h hT]; exact hα) (nxtSeq_subset as' hsf) happF
      (nxtSeq_concat sf as' a).symm
    obtain ⟨s, hs⟩ := ihL l'.length (by rw [← hL]; simp) (tn.drop h) (tnS.drop h) l' as' sf _
      rfl (TaskNetwork.drop_wf hwf h) ⟨U, inst, loc, kind, hw.drop hT⟩ (h1.drop h)
      (hdec.drop hT hp) (hprimS.drop h) (TaskNetwork.isLinearization_drop_last hlin)
      (by simpa [TaskNetwork.IsActionSeq] using has') happ' hsf
    exact ⟨s, Relation.ReflTransGen.head hstep hs⟩
  have hmemS : ∀ y, y ∈ l ↔ y ∈ tnS.T := hlin.2.1
  by_cases hab : ∃ x ∈ tn.T, tn.IsAbstractId x
  · obtain ⟨x, hx, hxa⟩ := hab
    have hprimOf : ∀ y ∈ tn.T, y ≠ x → tn.IsPrimitiveId y :=
      fun y hy hyx => isPrimitiveId_of_ne h1 hx hxa hy hyx
    by_cases hpred : ∃ u0 ∈ tn.T, tn.ord u0 x
    · -- progress
      obtain ⟨u0, hu0, ho⟩ := hpred
      have hu0x : u0 ≠ x := by rintro rfl; exact hwf.irrefl _ ho
      have hu0p := hprimOf u0 hu0 hu0x
      have hu0S : u0 ∈ tnS.T := (DecomposesTo.mem_of_isPrimitiveId hdecT hu0 hu0p).1
      obtain ⟨h, l', rfl⟩ : ∃ h l', l = h :: l' := by
        cases l with
        | nil => exact absurd ((hmemS u0).2 hu0S) (by simp)
        | cons h l' => exact ⟨h, l', rfl⟩
      have hpw := List.pairwise_cons.1 hlin.2.2
      have hafter := DecomposesTo.ord_after hdecT hwf h1 hx hxa hu0 ho
      have hhS : h ∈ tnS.T := (hmemS h).1 (List.mem_cons_self)
      have inl' : ∀ y ∈ tnS.T, y ≠ h → y ∈ l' := by
        intro y hy hyh
        rcases List.mem_cons.1 ((hmemS y).2 hy) with rfl | hy'
        · exact absurd rfl hyh
        · exact hy'
      have hhT : h ∈ tn.T ∧ h ≠ x := by
        by_contra hcon
        have hcon' : h ∉ tn.T ∨ h = x := by tauto
        have hu0h : u0 ≠ h := by
          rintro rfl
          rcases hcon' with hc | hc
          · exact hc hu0
          · exact hu0x hc
        exact hpw.1 u0 (inl' u0 hu0S hu0h) (hafter h hhS hcon')
      have hhp := hprimOf h hhT.1 hhT.2
      refine headCase h l' rfl hhT.1 hhp fun y hy hyh => ?_
      by_cases hyx : y = x
      · subst hyx
        have hu0h' : tn.ord u0 h := hwf.trans ho hyh
        have hu0h : u0 ≠ h := by rintro rfl; exact hwf.irrefl _ hu0h'
        exact hpw.1 u0 (inl' u0 hu0S hu0h)
          ((DecomposesTo.ord_iff_of_prim hdecT hwf hu0 hu0p hhT.1 hhp).2 hu0h')
      · have hyp := hprimOf y hy hyx
        have hyS := (DecomposesTo.mem_of_isPrimitiveId hdecT hy hyp).1
        have hyh' : y ≠ h := by rintro rfl; exact hwf.irrefl _ hyh
        exact hpw.1 y (inl' y hyS hyh')
          ((DecomposesTo.ord_iff_of_prim hdecT hwf hy hyp hhT.1 hhp).2 hyh)
    by_cases hsucc : ∃ v0 ∈ tn.T, tn.ord x v0
    · -- regress
      obtain ⟨v0, hv0, ho⟩ := hsucc
      have hv0x : v0 ≠ x := by rintro rfl; exact hwf.irrefl _ ho
      have hv0p := hprimOf v0 hv0 hv0x
      have hv0S : v0 ∈ tnS.T := (DecomposesTo.mem_of_isPrimitiveId hdecT hv0 hv0p).1
      obtain ⟨l', h, rfl⟩ : ∃ l' h, l = l' ++ [h] := by
        rcases List.eq_nil_or_concat l with hl | ⟨l', h, hl⟩
        · subst hl; exact absurd ((hmemS v0).2 hv0S) (by simp)
        · exact ⟨l', h, by rw [hl, List.concat_eq_append]⟩
      have hpw := List.pairwise_append.1 hlin.2.2
      have hbefore := DecomposesTo.ord_before hdecT hwf h1 hx hxa hv0 ho
      have hhS : h ∈ tnS.T := (hmemS h).1 (by simp)
      have inl' : ∀ y ∈ tnS.T, y ≠ h → y ∈ l' := by
        intro y hy hyh
        rcases List.mem_append.1 ((hmemS y).2 hy) with hy' | hy'
        · exact hy'
        · exact absurd (List.mem_singleton.1 hy') hyh
      have hlast : ∀ y ∈ l', ¬ tnS.ord h y := fun y hy =>
        hpw.2.2 y hy h (List.mem_singleton_self h)
      have hhT : h ∈ tn.T ∧ h ≠ x := by
        by_contra hcon
        have hcon' : h ∉ tn.T ∨ h = x := by tauto
        have hv0h : v0 ≠ h := by
          rintro rfl
          rcases hcon' with hc | hc
          · exact hc hv0
          · exact hv0x hc
        exact hlast v0 (inl' v0 hv0S hv0h) (hbefore h hhS hcon')
      have hhp := hprimOf h hhT.1 hhT.2
      refine lastCase h l' rfl hhT.1 hhp fun y hy hhy => ?_
      by_cases hyx : y = x
      · subst hyx
        have hhv0' : tn.ord h v0 := hwf.trans hhy ho
        have hv0h : v0 ≠ h := by rintro rfl; exact hwf.irrefl _ hhv0'
        exact hlast v0 (inl' v0 hv0S hv0h)
          ((DecomposesTo.ord_iff_of_prim hdecT hwf hhT.1 hhp hv0 hv0p).2 hhv0')
      · have hyp := hprimOf y hy hyx
        have hyS := (DecomposesTo.mem_of_isPrimitiveId hdecT hy hyp).1
        have hyh' : y ≠ h := by rintro rfl; exact hwf.irrefl _ hhy
        exact hlast y (inl' y hyS hyh')
          ((DecomposesTo.ord_iff_of_prim hdecT hwf hhT.1 hhp hy hyp).2 hhy)
    -- the compound task is isolated: decompose it
    push_neg at hpred hsucc
    have hiso : ∀ y ∈ tn.T, ¬ tn.ord y x ∧ ¬ tn.ord x y := fun y hy => ⟨hpred y hy, hsucc y hy⟩
    obtain ⟨c, hc⟩ := hxa
    have hnot : x ∈ tnS.T → ¬ tnS.IsAbstractId x := by
      rintro hxS ⟨c', hc'⟩
      obtain ⟨a, ha⟩ := hprimS x hxS
      rw [ha] at hc'
      exact Sum.inl_ne_inr hc'
    obtain ⟨m, tn₁, tnS', k', hk', hstepD, hdec', hisoS⟩ :=
      hdec.pull_out hwf hx hc hnot
    obtain ⟨hm, -, hαx, u, hu, huiso, hdisj, rfl⟩ := hstepD
    obtain ⟨e, he, rfl⟩ := hm
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem he
    have hget : d.methods.getD j default = e := by rw [List.getD_eq_getElem _ _ hj, hje]
    have hnet : net d q (j + 1) = e.2 := by
      show (d.methods.getD j default).2 = e.2
      rw [hget]
    have huiso' : u.Iso (net d q (j + 1)).toTaskNetwork := by rw [hnet]; exact huiso
    obtain ⟨σ, hbij, hord, hσα⟩ := huiso'
    obtain ⟨i', hi'⟩ := Infinite.exists_notMem_finset U
    have hw' := hw.decompose hwf (subset_refl _) hx hiso hu hbij hord hσα hdisj hi'
    have hce : c = e.1 := by
      rw [hc] at hαx
      exact Sum.inr_injective hαx
    have hstep := HStep.dec sf (nxtSeq d sf as) M _ _ _ c j (hw.mem_M hx) (RepW.loc_mem_Sof hx)
      (fun y hy => ⟨hw.min_of_not_ord hx (fun y hy => hpred y hy) y hy,
        hw.max_of_not_ord hx (fun y hy => hsucc y hy) y hy⟩)
      (by rw [← hw.lbl x hx]; exact hc) hj (by rw [hget, hce])
    -- the solution, transported to the reordered decomposition sequence
    obtain ⟨τ, hτbij, hτord, hτα⟩ := hisoS
    obtain ⟨hlin', has''⟩ := TaskNetwork.Iso.map_isLinearization hτbij hτord hτα hlin
    have hprimS' : tnS'.IsPrimitive := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hτbij.surjOn hy
      obtain ⟨a, ha⟩ := hprimS z hz
      exact ⟨a, by rw [← hτα z hz]; exact ha⟩
    have h1' : (decomposeWith tn x u).IsOneHole :=
      isOneHole_decomposeWith h1 hx ⟨c, hc⟩ (huiso.isOneHole (hd e he)) hdisj
    obtain ⟨s, hs⟩ := ihn k' hk' (l.map τ).length (decomposeWith tn x u) tnS' (l.map τ) as sf _ rfl
      (decomposeWith_wf hwf hu hdisj) ⟨_, _, _, _, hw'⟩ h1' hdec' hprimS' hlin'
      (has'' as has) happ hsf
    exact ⟨s, Relation.ReflTransGen.head hstep hs⟩
  · -- no compound task: progress the first task of the linearization
    push_neg at hab
    obtain ⟨-, htn⟩ := hdec.eq_of_noAbstract hab
    have hmemS' : ∀ y, y ∈ l ↔ y ∈ tn.T := fun y => by rw [hmemS, htn]
    have hpwS : l.Pairwise (fun a b => ¬ tn.ord b a) := htn ▸ hlin.2.2
    have hprimOf : ∀ y ∈ tn.T, tn.IsPrimitiveId y := by
      intro y hy
      rcases h : tn.α y with a | c
      · exact ⟨a, h⟩
      · exact absurd ⟨c, h⟩ (hab y hy)
    cases l with
    | nil =>
      have hT : tn.T = ∅ := by
        ext y
        simp [← hmemS' y]
      have hM : M = 0 := hw.eq_zero_iff.2 hT
      have has0 : as = [] := by simpa [TaskNetwork.IsActionSeq] using has.symm
      subst hM has0
      exact ⟨sf, Relation.ReflTransGen.refl⟩
    | cons h l' =>
      have hhT : h ∈ tn.T := (hmemS' h).1 List.mem_cons_self
      have hpw := List.pairwise_cons.1 hpwS
      refine headCase h l' rfl hhT (hprimOf h hhT) fun y hy hyh => ?_
      have hyh' : y ≠ h := by rintro rfl; exact hwf.irrefl _ hyh
      rcases List.mem_cons.1 ((hmemS' y).2 hy) with rfl | hy'
      · exact hyh' rfl
      · exact hpw.1 y hy' hyh

/-- **Completeness of the pieces criterion** for one-hole-digging descriptions (Lemma 6 of
Dekker and Behnke). -/
theorem piecesSolvable_of_solvable (hd : d.MethodsHD1) (hq : q.IsHD1) (h : Solvable d q) :
    PiecesSolvable d q := by
  obtain ⟨tnS, hreach, hprim, l, as, hl, has, happ, hgoal⟩ := h
  obtain ⟨n, hn⟩ := exists_decomposesToN hreach
  have hinit : (problem d q).init = {f | f ∈ q.initList.toFinset} := by ext f; simp
  rw [hinit] at happ hgoal
  have hsf : q.initList.toFinset ⊆ facts d q := by
    intro f hf
    simp only [facts, allFacts, List.mem_toFinset, List.mem_append] at hf ⊢
    exact Or.inl hf
  obtain ⟨s, hs⟩ := comp_main hd n l.length q.tnI.toTaskNetwork tnS l as q.initList.toFinset
    (initPieces q) rfl (problem_wf d q).tnI ⟨_, _, _, _, repW_init⟩ hq hn hprim hl has happ hsf
  refine ⟨nxtSeq d q.initList.toFinset as, s, nxtSeq_subset as hsf, fun f hf => ?_, hs⟩
  have := hgoal (show f ∈ (problem d q).goal from hf)
  rw [← coe_nxtSeq (q := q)] at this
  exact this

/-- **The pieces criterion characterises plan existence** for one-hole-digging descriptions. -/
theorem solvable_iff_piecesSolvable (hd : d.MethodsHD1) (hq : q.IsHD1) :
    Solvable d q ↔ PiecesSolvable d q :=
  ⟨piecesSolvable_of_solvable hd hq, solvable_of_piecesSolvable⟩

end HD

end HTN
