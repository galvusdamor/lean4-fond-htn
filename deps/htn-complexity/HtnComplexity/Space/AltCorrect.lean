import HtnComplexity.Space.AltMachine
/-!
# Correctness of the alternating target-side machine

    HTN.Space.altMachine_accepts_iff :
      altMachine.Accepts (instSer q) (tblAdv true tbl) ↔
        ASolvable kPush kRet tbl {f | f ∈ regInitR q} {f | f ∈ regGoalR q}

*Soundness* (`HTN.Space.acc_sound`) is an induction on the alternating acceptance of the machine:
an accepting `E`-configuration is a reachability, an accepting `G`-configuration a call, an
accepting `R`-configuration a return.  *Completeness* (`HTN.Space.acc_complete`) is an induction
on `HTN.Space.AReach`; every state it passes through contains only facts of the initial state and
facts some row adds (`HTN.Space.AReach.subset_union_adds`), so it has a representative of
polynomial length, and that representative is what the machine guesses.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### Well-formed components -/

/-- A state component of admissible length for the input `x` and the advice `a`. -/
def WfC (x a X : List Bool) : Prop := wfB X (cubeF 0 1 [x, a]) = true

theorem blist_injective {S S' : List (List Bool)} (h : blist S = blist S') : S = S' :=
  (blist_parse (r := []) (s := []) (by simpa using h)).1

theorem canon_of_wfC {x a : List Bool} {S : List (List Bool)} (h : WfC x a (blist S)) :
    ∀ w ∈ S, IsCanon w := by
  obtain ⟨S₀, hS₀, hcan, -⟩ := wfB_iff.1 h
  rw [blist_injective hS₀]
  exact hcan

theorem exists_of_wfC {x a X : List Bool} (h : WfC x a X) :
    ∃ S, X = blist S ∧ ∀ w ∈ S, IsCanon w := by
  obtain ⟨S₀, hS₀, hcan, -⟩ := wfB_iff.1 h
  exact ⟨S₀, hS₀, hcan⟩

theorem tE_ne_tG : tE ≠ tG := by decide
theorem tE_ne_tR : tE ≠ tR := by decide
theorem tG_ne_tR : tG ≠ tR := by decide

/-! ### The tests on explicit configurations -/

theorem step_iff (x a tg' u' A' B' C' tg u A B C : List Bool) :
    altMachine.stepB (x :: a :: ([tg', u', A', B', C'] ++ [tg, u, A, B, C])) = true ↔
      (tg = tE ∧ tg' = tE ∧ u' = [] ∧ C' = [] ∧ WfC x a A' ∧ WfC x a B' ∧ B' = B ∧
          plainStepB a A A' = true) ∨
      (tg = tE ∧ tg' = tG ∧ u'.length ≤ a.length ∧ WfC x a A' ∧ WfC x a B' ∧ WfC x a C' ∧
          C' = B ∧ pushStepB a u' A A' = true) ∨
      (tg = tG ∧ tg' = tE ∧ u' = [] ∧ C' = [] ∧ WfC x a A' ∧ WfC x a B' ∧ A' = A ∧ B' = B) ∨
      (tg = tG ∧ tg' = tR ∧ u'.length ≤ a.length ∧ u' = u ∧ C' = [] ∧ WfC x a A' ∧
          WfC x a B' ∧ A' = B ∧ B' = C) ∨
      (tg = tR ∧ tg' = tE ∧ u' = [] ∧ C' = [] ∧ WfC x a A' ∧ WfC x a B' ∧ B' = B ∧
          retStepB a u A A' = true) := by
  show (brPlain _ || brPush _ || brCallee _ || brCont _ || brRet _) = true ↔ _
  simp only [brPlain, brPush, brCallee, brCont, brRet, List.cons_append, List.nil_append,
    List.getD_cons_succ, List.getD_cons_zero, cubeF_cons, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, WfC]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exact Or.inl (by tauto)
    · exact Or.inr (Or.inl (by tauto))
    · exact Or.inr (Or.inr (Or.inl (by tauto)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by tauto))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by tauto))))
  · rintro (h | h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl (by tauto))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (by tauto))))
    · exact Or.inl (Or.inl (Or.inr (by tauto)))
    · exact Or.inl (Or.inr (by tauto))
    · exact Or.inr (by tauto)

theorem acc_test_iff (x a tg u A B C : List Bool) :
    altMachine.accB (x :: a :: [tg, u, A, B, C]) = true ↔
      tg = tE ∧ subEntB A B = true ∧ subEntB B A = true := by
  show (decide _ && subEntB _ _ && subEntB _ _) = true ↔ _
  simp [and_assoc]

theorem univ_test_iff (x a tg u A B C : List Bool) :
    altMachine.univB (x :: a :: [tg, u, A, B, C]) = true ↔ tg = tG := by
  show decide _ = true ↔ _
  simp

theorem init_test_iff (x a tg u A B C : List Bool) :
    altMachine.initB (x :: a :: [tg, u, A, B, C]) = true ↔
      tg = tE ∧ u = [] ∧ C = [] ∧ WfC x a A ∧ WfC x a B ∧ initCoreR A x = true ∧
        accCoreR B x a = true := by
  show (decide _ && decide _ && decide _ && wfB _ _ && wfB _ _ && initCoreR _ _ &&
    accCoreR _ _ _) = true ↔ _
  simp only [List.getD_cons_succ, List.getD_cons_zero, cubeF_cons, Bool.and_eq_true,
    decide_eq_true_eq, WfC]
  tauto

theorem length_five {c : Args} (hc : c.length = 5) :
    ∃ tg u A B C, c = [tg, u, A, B, C] := by
  match c, hc with
  | [tg, u, A, B, C], _ => exact ⟨tg, u, A, B, C, rfl⟩

/-! ### Soundness -/

section Sound

variable {tbl : List Row} {x : List Bool}

theorem dset_eq_of_subEntB {S S' : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w)
    (hS' : ∀ w ∈ S', IsCanon w) (h1 : subEntB (blist S) (blist S') = true)
    (h2 : subEntB (blist S') (blist S) = true) : dset S = dset S' := by
  rw [← List.append_nil (blist S), ← List.append_nil (blist S'), subEntB_iff] at h1 h2
  ext f
  simp only [dset, Set.mem_setOf_eq, mem_decSt_iff hS, mem_decSt_iff hS']
  exact ⟨h1 _, h2 _⟩

/-- **Soundness**: what an accepting configuration of the machine asserts is true. -/
theorem acc_sound {c : Args} (h : altMachine.Acc x (tblAdv true tbl) c) :
    (∀ u S S' C, c = [tE, u, blist S, blist S', C] → WfC x (tblAdv true tbl) (blist S) →
        WfC x (tblAdv true tbl) (blist S') → AReach kPush kRet tbl (dset S) (dset S')) ∧
    (∀ i S₁ T S', c = [tG, idEnt i, blist S₁, blist T, blist S'] →
        WfC x (tblAdv true tbl) (blist S₁) → WfC x (tblAdv true tbl) (blist T) →
        WfC x (tblAdv true tbl) (blist S') → (idEnt i).length ≤ (tblAdv true tbl).length →
        AReach kPush kRet tbl (dset S₁) (dset T) ∧ RowOk (rowOf tbl (i + 1)) (dset T) ∧
          AReach kPush kRet tbl (rowApp (rowOf tbl (i + 1)) (dset T)) (dset S')) ∧
    (∀ i T S' C, c = [tR, idEnt i, blist T, blist S', C] → WfC x (tblAdv true tbl) (blist T) →
        WfC x (tblAdv true tbl) (blist S') →
        RowOk (rowOf tbl (i + 1)) (dset T) ∧
          AReach kPush kRet tbl (rowApp (rowOf tbl (i + 1)) (dset T)) (dset S')) := by
  set a := tblAdv true tbl with ha
  induction h with
  | @acc c hc hacc =>
    refine ⟨?_, ?_, ?_⟩
    · rintro u S S' C rfl hS hS'
      obtain ⟨-, h1, h2⟩ := (acc_test_iff x a _ _ _ _ _).1 hacc
      rw [dset_eq_of_subEntB (canon_of_wfC hS) (canon_of_wfC hS') h1 h2]
      exact AReach.refl _
    · rintro i S₁ T S' rfl
      exact absurd ((acc_test_iff x a _ _ _ _ _).1 hacc).1 (Ne.symm tE_ne_tG)
    · rintro i T S' C rfl
      exact absurd ((acc_test_iff x a _ _ _ _ _).1 hacc).1 (Ne.symm tE_ne_tR)
  | @univ c hc hu hall ih =>
    refine ⟨?_, ?_, ?_⟩
    · rintro u S S' C rfl
      exact absurd ((univ_test_iff x a _ _ _ _ _).1 hu) tE_ne_tG
    · rintro i S₁ T S' rfl hS₁ hT hS' hlen
      have hstep1 : altMachine.stepB (x :: a :: ([tE, [], blist S₁, blist T, []] ++
          [tG, idEnt i, blist S₁, blist T, blist S'])) = true :=
        (step_iff _ _ _ _ _ _ _ _ _ _ _ _).2 (Or.inr (Or.inr (Or.inl
          ⟨rfl, rfl, rfl, rfl, hS₁, hT, rfl, rfl⟩)))
      have hstep2 : altMachine.stepB (x :: a :: ([tR, idEnt i, blist T, blist S', []] ++
          [tG, idEnt i, blist S₁, blist T, blist S'])) = true :=
        (step_iff _ _ _ _ _ _ _ _ _ _ _ _).2 (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, rfl, hlen, rfl, rfl, hT, hS', rfl, rfl⟩))))
      have h1 := (ih _ rfl hstep1).1 [] S₁ T [] rfl hS₁ hT
      have h2 := (ih _ rfl hstep2).2.2 i T S' [] rfl hT hS'
      exact ⟨h1, h2⟩
    · rintro i T S' C rfl
      exact absurd ((univ_test_iff x a _ _ _ _ _).1 hu) (Ne.symm tG_ne_tR)
  | @ex c c' hc hu hc' hs hacc' ih =>
    obtain ⟨tg', u', A', B', C', rfl⟩ := length_five hc'
    refine ⟨?_, ?_, ?_⟩
    · rintro u S S' C rfl hS hS'
      have hSc := canon_of_wfC hS
      rcases (step_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hs with
        ⟨-, rfl, rfl, rfl, hA', hB', rfl, hplain⟩ |
        ⟨-, rfl, hu', hA', hB', hC', rfl, hpush⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · obtain ⟨S₁, rfl, hS₁⟩ := exists_of_wfC hA'
        obtain ⟨i, hi, hp, hr, hok, heq⟩ := (plainStepB_iff hSc hS₁ true).1 hplain
        have := ih.1 [] S₁ S' [] rfl hA' hB'
        rw [heq] at this
        exact AReach.plain hi hp hr hok this
      · obtain ⟨S₁, rfl, hS₁⟩ := exists_of_wfC hA'
        obtain ⟨T, rfl, -⟩ := exists_of_wfC hB'
        obtain ⟨i, hi, rfl, hp, hok, heq⟩ := (pushStepB_iff hSc hS₁ true).1 hpush
        obtain ⟨h1, hok2, h2⟩ := ih.2.1 i S₁ T S' rfl hA' hB' hC' hu'
        rw [heq] at h1
        exact AReach.call hi hp hok h1 hok2 h2
      · exact absurd h tE_ne_tG
      · exact absurd h tE_ne_tG
      · exact absurd h tE_ne_tR
    · rintro i S₁ T S' rfl
      rw [(univ_test_iff x a _ _ _ _ _).2 rfl] at hu
      exact absurd hu (by simp)
    · rintro i T S' C rfl hT hS'
      have hTc := canon_of_wfC hT
      rcases (step_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
          ⟨-, rfl, rfl, rfl, hA', hB', rfl, hret⟩
      · exact absurd h.symm tE_ne_tR
      · exact absurd h.symm tE_ne_tR
      · exact absurd h.symm tG_ne_tR
      · exact absurd h.symm tG_ne_tR
      · obtain ⟨T₂, rfl, hT₂⟩ := exists_of_wfC hA'
        obtain ⟨j, hj, hij, hok, heq⟩ := (retStepB_iff hTc hT₂ true).1 hret
        have hij' := idEnt_injective hij
        subst hij'
        have := ih.1 [] T₂ S' [] rfl hA' hB'
        rw [heq] at this
        exact ⟨hok, this⟩

end Sound

/-! ### Completeness -/

section Complete

variable {tbl : List Row} {x : List Bool} {Bl : List ℕ}

open Classical in
/-- The representative of a state: its facts among `Bl`, without repetition. -/
noncomputable def rep (Bl : List ℕ) (s : Set ℕ) : List (List Bool) :=
  (Bl.dedup.filter fun f => decide (f ∈ s)).map bitsOfNat

theorem canon_rep (s : Set ℕ) : ∀ w ∈ rep Bl s, IsCanon w := canon_map_bitsOfNat _

theorem dset_rep {s : Set ℕ} (hs : s ⊆ {f | f ∈ Bl}) : dset (rep Bl s) = s := by
  ext f
  simp only [dset, rep, decSt_map_bitsOfNat, Set.mem_setOf_eq, List.mem_filter,
    List.mem_dedup, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hs h, h⟩⟩

theorem wfC_rep (hlen : Bl.length ≤ x.length + (tblAdv true tbl).length)
    (hbits : ∀ f ∈ Bl, (bitsOfNat f).length ≤ x.length + (tblAdv true tbl).length)
    (s : Set ℕ) : WfC x (tblAdv true tbl) (blist (rep Bl s)) := by
  classical
  refine wfB_iff.2 ⟨rep Bl s, rfl, canon_rep s, ?_⟩
  rw [length_cubeF]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have hL : (Bl.dedup.filter fun f => decide (f ∈ s)).length ≤
      x.length + (tblAdv true tbl).length :=
    ((List.filter_sublist).length_le.trans (List.dedup_sublist Bl).length_le).trans hlen
  have := length_encState_le_cube hL (fun f hf => hbits f (List.mem_dedup.1
    (List.mem_of_mem_filter hf)))
  simpa [encState, rep] using this

theorem length_entry_le {l : List (List Bool)} {w : List Bool} (hw : w ∈ l) :
    (true :: bstr w).length ≤ (blist l).length := by
  rw [blist_eq_entriesEnc, entriesEnc, List.length_append, List.length_flatMap]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => (true :: bstr x).length) hw)
  beta_reduce at this
  omega

theorem length_idEnt_le {i : ℕ} (hi : i < tbl.length) (b : Bool) :
    (idEnt i).length ≤ (tblAdv b tbl).length := by
  rw [tblAdv_eq, List.length_append]
  have := length_entry_le (mem_idEnts_iff.2 ⟨i, hi, rfl⟩ : rowId i ∈ idEnts tbl)
  simp only [idEnt] at this ⊢
  omega

theorem subEntB_of_dset {S S' : List (List Bool)} (hS : ∀ w ∈ S, IsCanon w)
    (hS' : ∀ w ∈ S', IsCanon w) (h : dset S ⊆ dset S') : subEntB (blist S) (blist S') = true := by
  rw [← List.append_nil (blist S), ← List.append_nil (blist S'), subEntB_iff]
  intro w hw
  have hf : natOfBits w ∈ dset S := by
    show natOfBits w ∈ decSt S
    rw [mem_decSt_iff hS, hS w hw]
    exact hw
  have := h hf
  change natOfBits w ∈ decSt S' at this
  rw [mem_decSt_iff hS', hS w hw] at this
  exact this

/-- **Completeness**: every reachability through states made of facts of `Bl` is accepted. -/
theorem acc_complete (hlen : Bl.length ≤ x.length + (tblAdv true tbl).length)
    (hbits : ∀ f ∈ Bl, (bitsOfNat f).length ≤ x.length + (tblAdv true tbl).length)
    (hadd : ∀ f ∈ addFacts tbl, f ∈ Bl) {s s' : Set ℕ}
    (h : AReach kPush kRet tbl s s') :
    s ⊆ {f | f ∈ Bl} → ∀ S S', WfC x (tblAdv true tbl) (blist S) →
      WfC x (tblAdv true tbl) (blist S') → dset S = s → dset S' = s' →
      altMachine.Acc x (tblAdv true tbl) [tE, [], blist S, blist S', []] := by
  set a := tblAdv true tbl with ha
  have hsubB : ∀ {u v : Set ℕ}, u ⊆ {f | f ∈ Bl} → AReach kPush kRet tbl u v →
      v ⊆ {f | f ∈ Bl} := by
    intro u v hu huv f hf
    rcases huv.subset_union_adds hf with hf | hf
    · exact hu hf
    · exact hadd f hf
  have happB : ∀ {i : ℕ} {u : Set ℕ}, i < tbl.length → u ⊆ {f | f ∈ Bl} →
      rowApp (rowOf tbl i) u ⊆ {f | f ∈ Bl} := by
    intro i u hi hu f hf
    rcases hf with hf | ⟨hf, -⟩
    · exact hadd f (mem_addFacts_of_rowOf hi hf)
    · exact hu hf
  induction h with
  | refl s =>
    intro _ S S' hS hS' h1 h2
    have hSc := canon_of_wfC hS
    have hS'c := canon_of_wfC hS'
    refine AltSpace.Acc.acc rfl ((acc_test_iff _ _ _ _ _ _ _).2 ⟨rfl, ?_, ?_⟩)
    · exact subEntB_of_dset hSc hS'c (by rw [h1, h2])
    · exact subEntB_of_dset hS'c hSc (by rw [h1, h2])
  | @plain i s s' hi hp hr hok hrest ih =>
    intro hs S S' hS hS' h1 h2
    subst h1 h2
    have hs1 := happB hi hs
    have hW := wfC_rep (tbl := tbl) (x := x) hlen hbits (rowApp (rowOf tbl i) (dset S))
    have hnotU : altMachine.univB (x :: a :: [tE, [], blist S, blist S', []]) = false := by
      have := (univ_test_iff x a tE [] (blist S) (blist S') []).not.2 tE_ne_tG
      simpa using this
    refine AltSpace.Acc.ex rfl hnotU (c' := [tE, [], blist (rep Bl (rowApp (rowOf tbl i) (dset S))),
        blist S', []]) rfl ?_ (ih hs1 _ _ hW hS' (dset_rep hs1) rfl)
    refine (step_iff _ _ _ _ _ _ _ _ _ _ _ _).2 (Or.inl ⟨rfl, rfl, rfl, rfl, hW, hS', rfl, ?_⟩)
    exact (plainStepB_iff (canon_of_wfC hS) (canon_rep _) true).2
      ⟨i, hi, hp, hr, hok, dset_rep hs1⟩
  | @call i s t s' hi hp hok1 h1 hok2 h2 ih1 ih2 =>
    intro hs S S' hS hS' he1 he2
    subst he1 he2
    have hi' : i < tbl.length := by omega
    have hs1 := happB hi' hs
    have ht := hsubB hs1 h1
    have hs2 := happB hi ht
    set S₁ := rep Bl (rowApp (rowOf tbl i) (dset S)) with hS₁
    set T := rep Bl t with hT
    set T₂ := rep Bl (rowApp (rowOf tbl (i + 1)) t) with hT₂
    have hW1 : WfC x a (blist S₁) := wfC_rep hlen hbits _
    have hWT : WfC x a (blist T) := wfC_rep hlen hbits _
    have hW2 : WfC x a (blist T₂) := wfC_rep hlen hbits _
    have hdT : dset T = t := dset_rep ht
    have hnotU : altMachine.univB (x :: a :: [tE, [], blist S, blist S', []]) = false := by
      have := (univ_test_iff x a tE [] (blist S) (blist S') []).not.2 tE_ne_tG
      simpa using this
    have hnotR : altMachine.univB (x :: a :: [tR, idEnt i, blist T, blist S', []]) = false := by
      have := (univ_test_iff x a tR (idEnt i) (blist T) (blist S') []).not.2 (Ne.symm tG_ne_tR)
      simpa using this
    have hlenU : (idEnt i).length ≤ a.length := length_idEnt_le hi' true
    -- the continuation configuration accepts
    have hR : altMachine.Acc x a [tR, idEnt i, blist T, blist S', []] := by
      refine AltSpace.Acc.ex rfl hnotR (c' := [tE, [], blist T₂, blist S', []]) rfl ?_
        (ih2 hs2 _ _ hW2 hS' (dset_rep hs2) rfl)
      refine (step_iff _ _ _ _ _ _ _ _ _ _ _ _).2 (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨rfl, rfl, rfl, rfl, hW2, hS', rfl, ?_⟩))))
      refine (retStepB_iff (canon_rep _) (canon_rep _) true).2 ⟨i, hi, rfl, ?_, ?_⟩
      · rw [hdT]; exact hok2
      · rw [hdT, dset_rep hs2]
    -- the call configuration accepts
    have hG : altMachine.Acc x a [tG, idEnt i, blist S₁, blist T, blist S'] := by
      refine AltSpace.Acc.univ rfl ((univ_test_iff _ _ _ _ _ _ _).2 rfl) fun c'' hc'' hs'' => ?_
      obtain ⟨tg, u, A, B, C, rfl⟩ := length_five hc''
      rcases (step_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hs'' with ⟨h, -⟩ | ⟨h, -⟩ |
          ⟨-, rfl, rfl, rfl, -, -, rfl, rfl⟩ | ⟨-, rfl, -, rfl, rfl, -, -, rfl, rfl⟩ | ⟨h, -⟩
      · exact absurd h.symm tE_ne_tG
      · exact absurd h.symm tE_ne_tG
      · exact ih1 hs1 _ _ hW1 hWT (dset_rep hs1) hdT
      · exact hR
      · exact absurd h tG_ne_tR
    refine AltSpace.Acc.ex rfl hnotU rfl ?_ hG
    refine (step_iff _ _ _ _ _ _ _ _ _ _ _ _).2 (Or.inr (Or.inl
      ⟨rfl, rfl, hlenU, hW1, hWT, hS', rfl, ?_⟩))
    exact (pushStepB_iff (canon_of_wfC hS) (canon_rep _) true).2
      ⟨i, hi, rfl, hp, hok1, dset_rep hs1⟩

end Complete

/-! ### The machine decides solvability -/

/-- **The alternating machine accepts exactly the instances whose table problem is solvable.** -/
theorem altMachine_accepts_iff (tbl : List Row) (q : InstDesc) :
    altMachine.Accepts (instSer q) (tblAdv true tbl) ↔
      ASolvable kPush kRet tbl {f | f ∈ regInitR q} {f | f ∈ regGoalR q} := by
  set x := instSer q with hx
  set a := tblAdv true tbl with ha
  set Bl := regInitR q ++ addFacts tbl with hBl
  have hlen : Bl.length ≤ x.length + a.length := by
    have h1 : (regInitR q).length ≤ x.length := length_regInitR_le q
    have h2 : (addFacts tbl).length ≤ a.length := length_addFacts_le_tblAdv
    simp only [hBl, List.length_append]
    omega
  have hbits : ∀ f ∈ Bl, (bitsOfNat f).length ≤ x.length + a.length := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · have h1 : (bitsOfNat f).length ≤ x.length := length_bitsOfNat_le_of_mem_regInitR hf
      omega
    · have h1 : (bitsOfNat f).length ≤ a.length := length_bitsOfNat_le_tblAdv hf
      omega
  have hadd : ∀ f ∈ addFacts tbl, f ∈ Bl := fun f hf => List.mem_append_right _ hf
  constructor
  · rintro ⟨c, hc, hinit, hacc⟩
    obtain ⟨tg, u, A, B, C, rfl⟩ := length_five hc
    obtain ⟨rfl, rfl, rfl, hA, hB, hini, hgoal⟩ := (init_test_iff _ _ _ _ _ _ _).1 hinit
    obtain ⟨S, rfl, hS⟩ := exists_of_wfC hA
    obtain ⟨S', rfl, hS'⟩ := exists_of_wfC hB
    have hreach := (acc_sound hacc).1 [] S S' [] rfl hA hB
    have h0 : dset S = {f | f ∈ regInitR q} := by
      ext f; exact (initCoreR_iff hS q).1 hini f
    obtain ⟨-, hg⟩ := (accCoreR_iff hS' q true tbl).1 hgoal
    rw [h0] at hreach
    exact ⟨dset S', hreach, fun f hf => hg f hf⟩
  · rintro ⟨s', hreach, hgoal⟩
    have hs0 : {f | f ∈ regInitR q} ⊆ {f | f ∈ Bl} := fun f hf => List.mem_append_left _ hf
    have hs' : s' ⊆ {f | f ∈ Bl} := by
      intro f hf
      rcases hreach.subset_union_adds hf with hf | hf
      · exact hs0 hf
      · exact hadd f hf
    have hW0 := wfC_rep (tbl := tbl) (x := x) hlen hbits {f | f ∈ regInitR q}
    have hW' := wfC_rep (tbl := tbl) (x := x) hlen hbits s'
    refine ⟨[tE, [], blist (rep Bl {f | f ∈ regInitR q}), blist (rep Bl s'), []], rfl, ?_,
      acc_complete hlen hbits hadd hreach hs0 _ _ hW0 hW' (dset_rep hs0) (dset_rep hs')⟩
    refine (init_test_iff _ _ _ _ _ _ _).2 ⟨rfl, rfl, rfl, hW0, hW', ?_, ?_⟩
    · refine (initCoreR_iff (canon_rep _) q).2 fun f => ?_
      have := congrArg (f ∈ ·) (dset_rep (Bl := Bl) hs0)
      simpa [dset] using this
    · refine (accCoreR_iff (canon_rep _) q true tbl).2 ⟨rfl, fun f hf => ?_⟩
      have := dset_rep (Bl := Bl) hs'
      have hf' : f ∈ s' := hgoal hf
      rw [← this] at hf'
      exact hf'

end Space

end HTN
