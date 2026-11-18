import ComplexityTheory.UOSpace.Steinitz
import ComplexityTheory.UOSpace.TreeBound
import HtnComplexity.UODecide.Abstract
/-!
# Unordered HTN planning: a single-exponential bound on shortest solutions

`HTN.UOAbs.short_run` (`HtnComplexity/UODecide/Abstract.lean`) bounds the length of a
shortest solution of an abstract unordered problem by `uoBound`, a bound that is *triply*
exponential in the number of facts: it treats the states of the execution as nonterminals of the
grammar of solutions and uses a height bound exponential in the number of nonterminals.

This file proves the bound the polynomial-space algorithm of Lauer, Höller and Bercher needs:

    HTN.UOAbs.short_runP : … → ∃ m ≤ uoBoundP |I| |Comps| (2 ^ |F|) |Acts| (|I| + Mb + 2), …

where the logarithm of `uoBoundP nI nC nS nA Mx` is polynomial in `nI, nC, log nS, nA, Mx`.
The proof keeps the argument of `short_run` but

* decomposes the hierarchy trees and the execution path *separately*: the hierarchy trees only
  carry compound names, so their base trees have height `(|Comps|+1)² - 1`
  (`HTN.CTree.decompP`), and the execution path is a tree of a *linear* grammar, whose size is
  linear in its height (`HTN.CTree.DT.size_le_lin`), so its base has length `O(2^(2|F|))`;
* restores the balance with the Steinitz zero-sum lemma (`HTN.Steinitz.exists_small_zero_sum_mem`),
  whose bound `(2·n·a + 1)^n` is single exponential.
-/

namespace HTN

namespace UOAbs

open CTree

/-- **The single-exponential bound** on the length of a shortest solution: `nI` initial labels,
`nC` compound names, `nS` states, `nA` actions, rule bodies of at most `Mx` symbols. -/
def uoBoundP (nI nC nS nA Mx : ℕ) : ℕ :=
  let bC := (Mx + 1) ^ (nC * nC + 2 * nC + 2)
  let bS := 3 * (nS * nS + 2 * nS + 2)
  let base := 1 + nI * bC + bS
  let ab := base + bC + bS
  base + Steinitz.zsP nA ab * ab

variable {S : Sys} {s₀ : Finset ℕ} {I : Multiset (Bool × ℕ)} {Acts : Finset ℕ}

theorem pH_le {N : Type} [DecidableEq N] {K : Finset N} {n : ℕ} (h : K.card ≤ n) :
    pH K ≤ n * n + 2 * n := by
  unfold pH
  have := Nat.mul_le_mul h h
  omega

/-- **The small-solution theorem, single-exponential form.** -/
theorem short_runP {Comps F : Finset ℕ} {Mb : ℕ} (hC : Closed S Comps Acts F Mb)
    (hs₀ : s₀ ⊆ F) (hI : LabOK Comps Acts I)
    {n : ℕ} {y : Cfg} (h : ReachIn S n (s₀, I) y) (hy : IsGoal S y) :
    ∃ m ≤ uoBoundP (Multiset.card I) Comps.card (2 ^ F.card) Acts.card
        (Multiset.card I + Mb + 2), ∃ y', ReachIn S m (s₀, I) y' ∧ IsGoal S y' := by
  classical
  set Mx := Multiset.card I + Mb + 2 with hMx
  set nC := Comps.card with hnC
  set nS := 2 ^ F.card with hnS
  set bC := (Mx + 1) ^ (nC * nC + 2 * nC + 2) with hbC
  set bS := 3 * (nS * nS + 2 * nS + 2) with hbS
  set base := 1 + Multiset.card I * bC + bS with hbase
  set ab := base + bC + bS with hab
  obtain ⟨Fo, t₂, hFo, hroots, ht₂, hr₂, hvec⟩ :=
    forest_of_reach (s₀ := s₀) (I := I) hC h hy hI
  set KC : Finset NT := Comps.image NT.comp with hKC
  set KS : Finset NT := F.powerset.image NT.st with hKS
  have hKCc : KC.card ≤ nC := Finset.card_image_le
  have hKSc : KS.card ≤ nS := Finset.card_image_le.trans (by rw [Finset.card_powerset])
  -- the rules
  have hMrule : ∀ X β, G S s₀ I Acts X β → Multiset.card β ≤ Mx := by
    intro X β hR
    cases X with
    | top =>
      simp only [G] at hR
      subst hR
      simp only [Multiset.card_add, Multiset.card_map, Multiset.card_singleton]
      omega
    | comp c =>
      obtain ⟨β', hm, rfl⟩ := hR
      have := hC.meth_card c β' hm
      simp only [Multiset.card_map]
      omega
    | st s =>
      rcases hR with ⟨a, -, -, rfl⟩ | ⟨-, rfl⟩
      · simp [hMx]
      · simp
  have hQ : ∀ X β, G S s₀ I Acts X β → ∀ x, Sum.inr x ∈ β → x.name ∈ Acts := by
    intro X β hR x hx
    cases X with
    | top =>
      simp only [G] at hR
      subst hR
      rcases Multiset.mem_add.1 hx with hx | hx
      · obtain ⟨⟨b, a⟩, hba, hsym⟩ := Multiset.mem_map.1 hx
        cases b with
        | true => simp [sym] at hsym
        | false =>
          simp only [sym, Sum.inr.injEq] at hsym
          subst hsym
          exact (hI _ hba).2 rfl
      · simp at hx
    | comp c =>
      obtain ⟨β', hm, rfl⟩ := hR
      obtain ⟨⟨b, a⟩, hba, hsym⟩ := Multiset.mem_map.1 hx
      cases b with
      | true => simp [sym] at hsym
      | false =>
        simp only [sym, Sum.inr.injEq] at hsym
        subst hsym
        exact (hC.meth_lab c β' hm _ hba).2 rfl
    | st s =>
      rcases hR with ⟨a, ha, -, rfl⟩ | ⟨-, rfl⟩
      · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Sum.inr.injEq,
          Multiset.mem_singleton, reduceCtorEq, or_false] at hx
        subst hx
        exact ha
      · simp at hx
  have hclC : ∀ X β, X ∈ KC → G S s₀ I Acts X β → ∀ Y, Sum.inl Y ∈ β → Y ∈ KC := by
    intro X β hX hR Y hY
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨β', hm, rfl⟩ := hR
    obtain ⟨⟨b, c'⟩, hbc, hsym⟩ := Multiset.mem_map.1 hY
    cases b with
    | false => simp [sym] at hsym
    | true =>
      simp only [sym, Sum.inl.injEq] at hsym
      subst hsym
      exact Finset.mem_image_of_mem _ ((hC.meth_lab c β' hm _ hbc).1 rfl)
  have hclS : ∀ X β, X ∈ KS → G S s₀ I Acts X β → ∀ Y, Sum.inl Y ∈ β → Y ∈ KS := by
    intro X β hX hR Y hY
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hX
    rcases hR with ⟨a, -, -, rfl⟩ | ⟨-, rfl⟩
    · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
        reduceCtorEq, false_or, Sum.inl.injEq] at hY
      subst hY
      exact Finset.mem_image_of_mem _
        (Finset.mem_powerset.2 (hC.nxt_sub s a (Finset.mem_powerset.1 hs)))
    · simp at hY
  -- labels of the pieces
  have hlabFo : ∀ u ∈ Fo, u.labels ⊆ KC := by
    intro u hu
    cases u with
    | leaf x => simp
    | node X ts =>
      have hmem : Sum.inl X ∈ I.map sym := by
        rw [← hroots, Multiset.mem_coe]
        exact List.mem_map_of_mem (f := DT.root) hu
      obtain ⟨⟨b, c⟩, hbc, hsym⟩ := Multiset.mem_map.1 hmem
      cases b with
      | false => simp [sym] at hsym
      | true =>
        simp only [sym, Sum.inl.injEq] at hsym
        subst hsym
        exact DT.labels_subset_of_closed hclC (hFo _ hu) _ rfl
          (Finset.mem_image_of_mem _ ((hI _ hbc).1 rfl))
  have hlab₂ : t₂.labels ⊆ KS :=
    DT.labels_subset_of_closed hclS ht₂ _ hr₂
      (Finset.mem_image_of_mem _ (Finset.mem_powerset.2 hs₀))
  -- size bounds in terms of the height
  have hgC : ∀ t : DT NT TT, t.Valid (G S s₀ I Acts) → t.labels ⊆ KC →
      t.size ≤ (fun h => (Mx + 1) ^ (h + 1)) t.height :=
    fun t ht _ => DT.size_le_pow hMrule ht
  have hgS : ∀ t : DT NT TT, t.Valid (G S s₀ I Acts) → t.labels ⊆ KS →
      t.size ≤ (fun h => (2 + 1) * (h + 1)) t.height := by
    intro t ht hK
    refine DT.size_le_lin KS ?_ ?_ ht hK
    · intro X hX β hR
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hX
      rcases hR with ⟨a, -, -, rfl⟩ | ⟨-, rfl⟩ <;> simp
    · intro X hX β hR
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hX
      rcases hR with ⟨a, -, -, rfl⟩ | ⟨-, rfl⟩ <;> simp [Multiset.filter_singleton]
  have hmonoC : Monotone (fun h : ℕ => (Mx + 1) ^ (h + 1)) :=
    fun a b hab => Nat.pow_le_pow_right (by omega) (by omega)
  have hmonoS : Monotone (fun h : ℕ => (2 + 1) * (h + 1)) :=
    fun a b hab => Nat.mul_le_mul_left _ (by omega)
  have hpHC : pH KC ≤ nC * nC + 2 * nC := pH_le hKCc
  have hpHS : pH KS ≤ nS * nS + 2 * nS := pH_le hKSc
  -- decompose the hierarchy trees
  let P : DT NT TT → DT NT TT × List (NT × Ctx NT TT) → Prop := fun u v =>
    v.1.Valid (G S s₀ I Acts) ∧ v.1.root = u.root ∧ v.1.size ≤ bC ∧
    (∀ p ∈ v.2, IsPump (G S s₀ I Acts) p.1 p.2 ∧ p.1 ∈ v.1.labels ∧ p.2.size ≤ bC) ∧
    u.yield = v.1.yield + (v.2.map (fun p => p.2.yieldC)).sum
  obtain ⟨vs, hvs⟩ := exists_forall₂ (P := P) Fo (fun u hu => by
    obtain ⟨u₀, ps, h₀, hr₀, hl₀, hh₀, hps, hy₀⟩ :=
      decompP KC _ hmonoC hgC u.size u rfl (hFo u hu) (hlabFo u hu)
    refine ⟨(u₀, ps), h₀, hr₀, ?_, fun p hp => ?_, hy₀⟩
    · refine (hgC u₀ h₀ (hl₀ ▸ hlabFo u hu)).trans ?_
      exact Nat.pow_le_pow_right (by omega) (by omega)
    · obtain ⟨h1, h2, h3⟩ := hps p hp
      exact ⟨h1, h2, h3.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩)
  -- decompose the execution path
  obtain ⟨t₂₀, ps₂, h₂₀, hr₂₀, hl₂₀, hh₂₀, hps₂, hy₂₀⟩ :=
    decompP KS _ hmonoS hgS t₂.size t₂ rfl ht₂ hlab₂
  have hsz₂₀ : t₂₀.size ≤ bS := by
    refine (hgS t₂₀ h₂₀ (hl₂₀ ▸ hlab₂)).trans ?_
    show 3 * (t₂₀.height + 1) ≤ bS
    rw [hbS]
    omega
  -- the base tree
  let Fo₀ := vs.map Prod.fst
  let t₀ : DT NT TT := DT.node NT.top (Fo₀ ++ [t₂₀])
  have hroots₀ : Fo₀.map DT.root = Fo.map DT.root := by
    simp only [Fo₀, List.map_map]
    exact (forall₂_map_eq (fun u v (h : P u v) => h.2.1.symm) hvs).symm
  have ht₀ : t₀.Valid (G S s₀ I Acts) := by
    refine DT.Valid.node _ _ ?_ ?_
    · show _ = _
      simp only [List.map_append, List.map_cons, List.map_nil, ← Multiset.coe_add, hroots₀,
        hroots, hr₂₀, hr₂]
      rfl
    · intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
        obtain ⟨u, -, huw⟩ := forall₂_mem_right hvs w hw
        exact huw.1
      · rw [List.mem_singleton] at hv
        exact hv ▸ h₂₀
  have hlenFo : Fo.length = Multiset.card I := by
    have := congrArg Multiset.card hroots
    simpa using this
  have hlenvs : vs.length = Fo.length := (List.Forall₂.length_eq hvs).symm
  have hszt₀ : t₀.size ≤ base := by
    have h1 : (Fo₀.map DT.size).sum ≤ Fo₀.length * bC := by
      refine sum_le_length_mul _ _ Fo₀ fun w hw => ?_
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      obtain ⟨u, -, huv⟩ := forall₂_mem_right hvs v hv
      exact huv.2.2.1
    have h2 : Fo₀.length = Multiset.card I := by
      simp only [Fo₀, List.length_map, hlenvs, hlenFo]
    simp only [t₀, DT.size_node, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    rw [h2] at h1
    rw [hbase]
    omega
  -- all pumps
  let ps : List (NT × Ctx NT TT) := vs.flatMap Prod.snd ++ ps₂
  have hps : ∀ p ∈ ps, IsPump (G S s₀ I Acts) p.1 p.2 ∧ p.1 ∈ t₀.labels ∧ p.2.size ≤ ab := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨v, hv, hpv⟩ := List.mem_flatMap.1 hp
      obtain ⟨u, -, huv⟩ := forall₂_mem_right hvs v hv
      obtain ⟨h1, h2, h3⟩ := huv.2.2.2.1 p hpv
      refine ⟨h1, ?_, by rw [hab]; omega⟩
      exact DT.labels_subset_of_mem (X := NT.top)
        (List.mem_append_left _ (List.mem_map_of_mem hv)) h2
    · obtain ⟨h1, h2, h3⟩ := hps₂ p hp
      refine ⟨h1, ?_, ?_⟩
      · exact DT.labels_subset_of_mem (X := NT.top)
          (List.mem_append_right Fo₀ (List.mem_singleton_self t₂₀)) h2
      · refine h3.trans ?_
        show 3 * (pH KS + 1 + 1) ≤ ab
        rw [hab, hbase, hbS]
        omega
  -- the yield of the solution tree is the base yield plus the pump yields
  have hyields : Fo.map DT.yield =
      vs.map (fun v => v.1.yield + (v.2.map (fun p => p.2.yieldC)).sum) :=
    forall₂_map_eq (fun u v (h : P u v) => h.2.2.2.2) hvs
  have hyt : (Fo.map DT.yield).sum + t₂.yield =
      t₀.yield + (ps.map (fun p => p.2.yieldC)).sum := by
    simp only [t₀, ps, DT.yield_node, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, hyields, sum_flatMap_map, Fo₀, List.map_map,
      hy₂₀]
    rw [List.sum_map_add]
    simp only [Function.comp_def, add_zero]
    abel
  have hvt : vec (t₀.yield + (ps.map (fun p => p.2.yieldC)).sum) = 0 := by
    rw [← hyt]
    exact hvec
  have hnames₀ : ∀ x ∈ t₀.yield, x.name ∈ Acts :=
    DT.yield_mem_of_rules hQ ht₀ (fun x hx => by cases hx)
  have hnamesp : ∀ p ∈ ps, ∀ x ∈ p.2.yieldC, x.name ∈ Acts := fun p hp =>
    Ctx.yieldC_mem_of_rules hQ (hps p hp).1.1
  -- select pumps restoring the balance
  let g : Option (NT × Ctx NT TT) → ℕ → ℤ := fun o =>
    match o with
    | none => vec t₀.yield
    | some p => vec p.2.yieldC
  let S0 : Multiset (Option (NT × Ctx NT TT)) := none ::ₘ (↑ps : Multiset _).map some
  have hsum : (S0.map g).sum = 0 := by
    have e : (S0.map g).sum = vec t₀.yield + (ps.map (fun p => vec p.2.yieldC)).sum := by
      simp only [S0, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_coe, Multiset.sum_coe]
      rw [List.map_map]
      rfl
    rw [e, ← vec_list_sum, ← vec_add]
    exact hvt
  have hsupp : ∀ x ∈ S0, ∀ i, i ∉ Acts → g x i = 0 := by
    intro x hx i hi
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact vec_eq_zero_of_names hnames₀ hi
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      exact vec_eq_zero_of_names (hnamesp p (Multiset.mem_coe.1 hp)) hi
  have hbnd : ∀ x ∈ S0, ∀ i, |g x i| ≤ (ab : ℤ) := by
    intro x hx i
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · refine (abs_vec_le _ _).trans ?_
      have := (DT.card_yield_le _ t₀ rfl).trans hszt₀
      have hle : base ≤ ab := by rw [hab]; omega
      exact_mod_cast this.trans hle
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      refine (abs_vec_le _ _).trans ?_
      exact_mod_cast (Ctx.card_yieldC_le p.2).trans (hps p (Multiset.mem_coe.1 hp)).2.2
  obtain ⟨T, hTS, hnone, hcardT, hTsum⟩ := Steinitz.exists_small_zero_sum_mem Acts ab g none _
    S0 rfl (Multiset.mem_cons_self _ _) hsupp hbnd hsum
  have hTe : T.erase none ≤ (↑ps : Multiset _).map some := by
    have := Multiset.erase_le_erase none hTS
    simpa [S0] using this
  obtain ⟨W, hW, hTW⟩ := exists_map_some _ _ hTe
  let qs := W.toList
  have hqs_mem : ∀ q ∈ qs, q ∈ ps := fun q hq =>
    Multiset.mem_coe.1 (Multiset.mem_of_le hW (Multiset.mem_toList.1 hq))
  have hqs_len : qs.length ≤ Steinitz.zsP Acts.card ab := by
    have h1 : qs.length = Multiset.card (T.erase none) := by
      rw [Multiset.length_toList, hTW, Multiset.card_map]
    rw [h1, Multiset.card_erase_of_mem hnone]
    exact (Nat.pred_le _).trans hcardT
  have hqs_sum : vec t₀.yield + (qs.map (fun q => vec q.2.yieldC)).sum = 0 := by
    have e : (T.map g).sum = vec t₀.yield + (qs.map (fun q => vec q.2.yieldC)).sum := by
      rw [← Multiset.cons_erase hnone, Multiset.map_cons, Multiset.sum_cons, hTW,
        Multiset.map_map]
      have : W = (↑qs : Multiset _) := (Multiset.coe_toList W).symm
      rw [this, Multiset.map_coe, Multiset.sum_coe]
      rfl
    rw [← e]
    exact hTsum
  -- insert them
  obtain ⟨t', ht', hr', hy', hs'⟩ := insert_pumps qs ht₀
    (fun q hq => ⟨(hps q (hqs_mem q hq)).1, (hps q (hqs_mem q hq)).2.1⟩)
  have hvt' : vec t'.yield = 0 := by
    rw [hy', vec_add, vec_list_sum]
    exact hqs_sum
  have hst' : t'.size ≤ uoBoundP (Multiset.card I) nC nS Acts.card Mx := by
    rw [hs']
    have h1 : (qs.map (fun p => p.2.size)).sum ≤ qs.length * ab :=
      sum_le_length_mul _ _ qs (fun q hq => (hps q (hqs_mem q hq)).2.2)
    have h2 : qs.length * ab ≤ Steinitz.zsP Acts.card ab * ab := Nat.mul_le_mul_right _ hqs_len
    have e : uoBoundP (Multiset.card I) nC nS Acts.card Mx = base + Steinitz.zsP Acts.card ab * ab :=
      rfl
    rw [e]
    omega
  -- read off a run
  have hrt' : t'.root = Sum.inl NT.top := by rw [hr']; rfl
  cases t' with
  | leaf x => simp at hrt'
  | node X ch =>
  simp only [DT.root_node, Sum.inl.injEq] at hrt'
  subst hrt'
  obtain ⟨hR, hch⟩ := DT.Valid.children ht'
  simp only [G] at hR
  obtain ⟨L₁, L₂, hp, h₁, h₂⟩ := exists_split DT.root ch _ _ hR
  obtain ⟨u₂, rfl, hu₂⟩ := eq_singleton_of_map h₂
  have hmem : ∀ v, v ∈ L₁ ++ [u₂] → v ∈ ch := fun v hv => hp.symm.subset hv
  have hyl : (ch.map DT.yield).sum = (L₁.map DT.yield).sum + u₂.yield := by
    rw [(hp.map DT.yield).sum_eq]
    simp
  have hsz : (ch.map DT.size).sum = (L₁.map DT.size).sum + u₂.size := by
    rw [(hp.map DT.size).sum_eq]
    simp
  obtain ⟨m, hm, y', hy', hg'⟩ := reach_of_forest (S := S) (s₀ := s₀) (I := I) (Acts := Acts) _
    L₁ u₂ s₀ I rfl (fun v hv => hch v (hmem v (List.mem_append_left _ hv))) h₁
    (hch u₂ (hmem u₂ (by simp))) hu₂ (by rw [← hyl]; simpa using hvt')
  refine ⟨m, ?_, y', hy', hg'⟩
  simp only [DT.size_node] at hst'
  omega

end UOAbs

end HTN
