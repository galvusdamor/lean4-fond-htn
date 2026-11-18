import HtnComplexity.UOSpace.ShortRun
/-!
# Unordered HTN planning: shortest solutions are *linear* in the initial task network

`HTN.UOAbs.short_runP` (`HtnComplexity/UOSpace/ShortRun.lean`) bounds the length of a
shortest solution of an abstract unordered problem by `uoBoundP`, which is single exponential but
*polynomial of domain-dependent degree* in the number `|I|` of initial tasks: the base forest is
treated as one vector of size `≈ |I|`, and the Steinitz selection is applied to vectors of that
size.

This file proves the sharper bound

    HTN.UOAbs.short_runL : … → ∃ m ≤ (|I| + 1) * uoKL |Comps| (2 ^ |F|) |Acts| Mb, …

in which the factor `uoKL` depends on the domain data only (compound names, facts, actions,
largest method body).  The proof is that of `short_runP` with two changes:

* the hierarchy trees are bounded with the branching of the *methods* only
  (`HTN.CTree.DT.size_le_pow_of_labels`), not with the `|I| + 1` children of the artificial top
  rule;
* the base forest is split into its `|I| + 1` pieces (one tree per initial task and the base of
  the execution path), each of domain-bounded size, and the Steinitz selection is iterated once
  per piece (`HTN.Steinitz.exists_zero_sum_superset`): at most `(|I| + 1) · zsP` pumps are
  inserted.

This is the bound the acyclic compilation of unordered problems needs
(`HtnCompilability/UOtoAC/`): the number of decompositions of a shortest solution is at most
`|I|` times a single-exponential function of the domain.
-/

namespace HTN

namespace CTree

namespace DT

variable {N T : Type} [DecidableEq N]

/-- Valid trees whose labels lie in `K` are valid trees of the grammar restricted to `K`. -/
theorem valid_restrict {R : N → Multiset (N ⊕ T) → Prop} {K : Finset N} {t : DT N T}
    (ht : Valid R t) : t.labels ⊆ K → Valid (fun X β => X ∈ K ∧ R X β) t := by
  induction ht with
  | leaf t => intro _; exact Valid.leaf t
  | node X ts hR _ ih =>
    intro hK
    exact Valid.node X ts ⟨hK root_mem_labels, hR⟩
      (fun u hu => ih u hu ((labels_subset_of_mem hu).trans hK))

/-- **Size bound with the branching of the labels that occur only.** -/
theorem size_le_pow_of_labels {R : N → Multiset (N ⊕ T) → Prop} {K : Finset N} {M : ℕ}
    (hM : ∀ X ∈ K, ∀ β, R X β → Multiset.card β ≤ M) {t : DT N T} (ht : Valid R t)
    (hK : t.labels ⊆ K) : t.size ≤ (M + 1) ^ (t.height + 1) :=
  size_le_pow (R := fun X β => X ∈ K ∧ R X β) (fun X β h => hM X h.1 β h.2)
    (valid_restrict ht hK)

end DT

end CTree

namespace Steinitz

/-- **Iterated small zero-sum selection.**  In a zero-sum multiset `S` of vectors with entries in
`[-a, a]` (supported on `A`), every sub-multiset `B` extends to a zero-sum sub-multiset of `S` with
at most `|B| · zsP |A| a` elements. -/
theorem exists_zero_sum_superset (A : Finset ℕ) (a : ℕ) {β : Type} [DecidableEq β]
    (g : β → ℕ → ℤ) :
    ∀ (n : ℕ) (B S : Multiset β), Multiset.card B = n → B ≤ S →
      (∀ x ∈ S, ∀ i, i ∉ A → g x i = 0) → (∀ x ∈ S, ∀ i, |g x i| ≤ a) →
      (S.map g).sum = 0 →
      ∃ T, B ≤ T ∧ T ≤ S ∧ Multiset.card T ≤ Multiset.card B * zsP A.card a ∧
        (T.map g).sum = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B S hn hBS hsupp hb hs
    rcases Multiset.empty_or_exists_mem B with rfl | ⟨b, hbB⟩
    · exact ⟨0, le_rfl, Multiset.zero_le _, by simp, by simp⟩
    have hbS : b ∈ S := Multiset.mem_of_le hBS hbB
    obtain ⟨T₁, hT₁S, hbT₁, hcard₁, hsum₁⟩ :=
      exists_small_zero_sum_mem A a g b _ S rfl hbS hsupp hb hs
    have hS' : (S - T₁) + T₁ = S := tsub_add_cancel_of_le hT₁S
    have hsum' : ((S - T₁).map g).sum = 0 := by
      have := congrArg (fun U => (U.map g).sum) hS'
      simp only [Multiset.map_add, Multiset.sum_add, hsum₁, add_zero] at this
      rw [this, hs]
    have hlt : Multiset.card (B - T₁) < n := by
      have h1 : B - T₁ ≤ B.erase b := by
        rw [← Multiset.sub_singleton]
        exact tsub_le_tsub_left (Multiset.singleton_le.2 hbT₁) B
      have h2 := Multiset.card_le_card h1
      rw [Multiset.card_erase_of_mem hbB, Nat.pred_eq_sub_one] at h2
      have : 0 < Multiset.card B := Multiset.card_pos_iff_exists_mem.2 ⟨b, hbB⟩
      omega
    obtain ⟨T₂, hB₂, hT₂, hcard₂, hsum₂⟩ := ih _ hlt (B - T₁) (S - T₁) rfl
      (Multiset.sub_le_sub_right hBS)
      (fun x hx => hsupp x (Multiset.mem_of_le (Multiset.sub_le_self _ _) hx))
      (fun x hx => hb x (Multiset.mem_of_le (Multiset.sub_le_self _ _) hx)) hsum'
    refine ⟨T₁ + T₂, ?_, ?_, ?_, ?_⟩
    · calc B ≤ T₁ + (B - T₁) := le_add_tsub
        _ ≤ T₁ + T₂ := add_le_add le_rfl hB₂
    · calc T₁ + T₂ ≤ T₁ + (S - T₁) := add_le_add le_rfl hT₂
        _ = S := by rw [add_comm]; exact hS'
    · rw [Multiset.card_add]
      have h3 : Multiset.card (B - T₁) + 1 ≤ Multiset.card B := by omega
      have h4 := Nat.mul_le_mul_right (zsP A.card a) h3
      rw [add_mul, one_mul] at h4
      omega
    · rw [Multiset.map_add, Multiset.sum_add, hsum₁, hsum₂, add_zero]

end Steinitz

namespace UOAbs

open CTree

theorem exists_map_inr {α γ : Type*} :
    ∀ (U : Multiset (α ⊕ γ)) (V : Multiset γ), U ≤ V.map Sum.inr →
      ∃ W ≤ V, U = W.map Sum.inr := by
  intro U V hUV
  have hr : ∀ x ∈ U, ∃ c, x = Sum.inr c := by
    intro x hx
    obtain ⟨c, -, hc⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hUV hx)
    exact ⟨c, hc.symm⟩
  have key : ∀ U : Multiset (α ⊕ γ), (∀ x ∈ U, ∃ c, x = Sum.inr c) →
      (U.filterMap Sum.getRight?).map Sum.inr = U := by
    intro U
    induction U using Multiset.induction_on with
    | empty => simp
    | cons x U ih =>
      intro h
      obtain ⟨c, rfl⟩ := h x (Multiset.mem_cons_self _ _)
      rw [Multiset.filterMap_cons_some Sum.getRight? (Sum.inr c) U rfl, Multiset.map_cons,
        ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))]
  refine ⟨U.filterMap Sum.getRight?, ?_, (key U hr).symm⟩
  rw [← Multiset.map_le_map_iff Sum.inr_injective, key U hr]
  exact hUV

/-- **The linear bound**: `nC` compound names, `nS` states, `nA` actions, method bodies of at
most `Mb` labels.  The length of a shortest solution is at most `(|I| + 1) * uoKL nC nS nA Mb`. -/
def uoKL (nC nS nA Mb : ℕ) : ℕ :=
  let bC := (Mb + 2) ^ (nC * nC + 2 * nC + 2)
  let bS := 3 * (nS * nS + 2 * nS + 2)
  let a := bC + bS
  1 + a + Steinitz.zsP nA a * a

variable {S : Sys} {s₀ : Finset ℕ} {I : Multiset (Bool × ℕ)} {Acts : Finset ℕ}

/-- **The small-solution theorem, linear form.**  If a goal configuration can be reached from
`(s₀, I)`, then it can be reached in at most `(|I| + 1) * uoKL |Comps| (2 ^ |F|) |Acts| Mb`
steps; the factor depends on the domain data only. -/
theorem short_runL {Comps F : Finset ℕ} {Mb : ℕ} (hC : Closed S Comps Acts F Mb)
    (hs₀ : s₀ ⊆ F) (hI : LabOK Comps Acts I)
    {n : ℕ} {y : Cfg} (h : ReachIn S n (s₀, I) y) (hy : IsGoal S y) :
    ∃ m ≤ (Multiset.card I + 1) * uoKL Comps.card (2 ^ F.card) Acts.card Mb,
      ∃ y', ReachIn S m (s₀, I) y' ∧ IsGoal S y' := by
  classical
  set nC := Comps.card with hnC
  set nS := 2 ^ F.card with hnS
  set bC := (Mb + 2) ^ (nC * nC + 2 * nC + 2) with hbC
  set bS := 3 * (nS * nS + 2 * nS + 2) with hbS
  set a := bC + bS with ha
  obtain ⟨Fo, t₂, hFo, hroots, ht₂, hr₂, hvec⟩ :=
    forest_of_reach (s₀ := s₀) (I := I) hC h hy hI
  set KC : Finset NT := Comps.image NT.comp with hKC
  set KS : Finset NT := F.powerset.image NT.st with hKS
  have hKCc : KC.card ≤ nC := Finset.card_image_le
  have hKSc : KS.card ≤ nS := Finset.card_image_le.trans (by rw [Finset.card_powerset])
  -- the rules
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
      t.size ≤ (fun h => (Mb + 1 + 1) ^ (h + 1)) t.height := by
    intro t ht hK
    refine DT.size_le_pow_of_labels (K := KC) (fun X hX β hR => ?_) ht hK
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨β', hm, rfl⟩ := hR
    have := hC.meth_card c β' hm
    simp only [Multiset.card_map]
    omega
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
  have hmonoC : Monotone (fun h : ℕ => (Mb + 1 + 1) ^ (h + 1)) :=
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
  have hszt₀ : t₀.size ≤ 1 + Multiset.card I * bC + bS := by
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
    omega
  -- all pumps
  let ps : List (NT × Ctx NT TT) := vs.flatMap Prod.snd ++ ps₂
  have hps : ∀ p ∈ ps, IsPump (G S s₀ I Acts) p.1 p.2 ∧ p.1 ∈ t₀.labels ∧ p.2.size ≤ a := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨v, hv, hpv⟩ := List.mem_flatMap.1 hp
      obtain ⟨u, -, huv⟩ := forall₂_mem_right hvs v hv
      obtain ⟨h1, h2, h3⟩ := huv.2.2.2.1 p hpv
      refine ⟨h1, ?_, by omega⟩
      exact DT.labels_subset_of_mem (X := NT.top)
        (List.mem_append_left _ (List.mem_map_of_mem hv)) h2
    · obtain ⟨h1, h2, h3⟩ := hps₂ p hp
      refine ⟨h1, ?_, ?_⟩
      · exact DT.labels_subset_of_mem (X := NT.top)
          (List.mem_append_right Fo₀ (List.mem_singleton_self t₂₀)) h2
      · refine h3.trans ?_
        show 3 * (pH KS + 1 + 1) ≤ a
        rw [ha, hbS]
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
  -- the pieces of the base tree
  let B : List (DT NT TT) := Fo₀ ++ [t₂₀]
  have hBy : t₀.yield = (B.map DT.yield).sum := by simp only [t₀, DT.yield_node, B]
  have hBv : ∀ u ∈ B, u.Valid (G S s₀ I Acts) ∧ u.size ≤ a := by
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
      obtain ⟨w, -, hwv⟩ := forall₂_mem_right hvs v hv
      exact ⟨hwv.1, by have := hwv.2.2.1; omega⟩
    · rw [List.mem_singleton] at hu
      subst hu
      exact ⟨h₂₀, by omega⟩
  have hBlen : B.length = Multiset.card I + 1 := by
    simp only [B, Fo₀, List.length_append, List.length_map, hlenvs, hlenFo, List.length_singleton]
  have hnamesB : ∀ u ∈ B, ∀ x ∈ u.yield, x.name ∈ Acts := fun u hu x hx =>
    hnames₀ x (hBy ▸ Multiset.mem_of_le (List.le_sum_of_mem (List.mem_map_of_mem hu)) hx)
  -- select pumps restoring the balance, keeping every piece
  let g : DT NT TT ⊕ (NT × Ctx NT TT) → ℕ → ℤ := fun o =>
    match o with
    | Sum.inl u => vec u.yield
    | Sum.inr p => vec p.2.yieldC
  let MB : Multiset (DT NT TT ⊕ (NT × Ctx NT TT)) := (↑B : Multiset _).map Sum.inl
  let S0 : Multiset (DT NT TT ⊕ (NT × Ctx NT TT)) := MB + (↑ps : Multiset _).map Sum.inr
  have hMBg : (MB.map g).sum = vec t₀.yield := by
    rw [hBy, ← Multiset.sum_coe, ← Multiset.map_coe, vec_multiset_sum]
    simp only [MB, Multiset.map_map]
    rfl
  have hsum : (S0.map g).sum = 0 := by
    have e : (S0.map g).sum = vec t₀.yield + (ps.map (fun p => vec p.2.yieldC)).sum := by
      simp only [S0, Multiset.map_add, Multiset.sum_add, hMBg,
        Multiset.map_coe, Multiset.sum_coe, List.map_map]
      rfl
    rw [e, ← vec_list_sum, ← vec_add]
    exact hvt
  have hsupp : ∀ x ∈ S0, ∀ i, i ∉ Acts → g x i = 0 := by
    intro x hx i hi
    rcases Multiset.mem_add.1 hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hx
      exact vec_eq_zero_of_names (hnamesB u (Multiset.mem_coe.1 hu)) hi
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      exact vec_eq_zero_of_names (hnamesp p (Multiset.mem_coe.1 hp)) hi
  have hbnd : ∀ x ∈ S0, ∀ i, |g x i| ≤ (a : ℤ) := by
    intro x hx i
    rcases Multiset.mem_add.1 hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hx
      refine (abs_vec_le _ _).trans ?_
      exact_mod_cast (DT.card_yield_le _ u rfl).trans (hBv u (Multiset.mem_coe.1 hu)).2
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      refine (abs_vec_le _ _).trans ?_
      exact_mod_cast (Ctx.card_yieldC_le p.2).trans (hps p (Multiset.mem_coe.1 hp)).2.2
  obtain ⟨T, hBT, hTS, hcardT, hTsum⟩ := Steinitz.exists_zero_sum_superset Acts a g _ MB S0 rfl
    (Multiset.le_add_right _ _) hsupp hbnd hsum
  have hTe : T - MB ≤ (↑ps : Multiset _).map Sum.inr := by
    rw [tsub_le_iff_left]
    exact hTS
  obtain ⟨W, hW, hTW⟩ := exists_map_inr _ _ hTe
  let qs := W.toList
  have hqs_mem : ∀ q ∈ qs, q ∈ ps := fun q hq =>
    Multiset.mem_coe.1 (Multiset.mem_of_le hW (Multiset.mem_toList.1 hq))
  have hcardMB : Multiset.card MB = Multiset.card I + 1 := by
    simp only [MB, Multiset.card_map, Multiset.coe_card, hBlen]
  have hqs_len : qs.length ≤ (Multiset.card I + 1) * Steinitz.zsP Acts.card a := by
    have h1 : qs.length = Multiset.card (T - MB) := by
      rw [Multiset.length_toList, hTW, Multiset.card_map]
    rw [h1, ← hcardMB]
    exact (Multiset.card_le_card (Multiset.sub_le_self _ _)).trans hcardT
  have hqs_sum : vec t₀.yield + (qs.map (fun q => vec q.2.yieldC)).sum = 0 := by
    have hsplit : T = MB + (T - MB) := (add_tsub_cancel_of_le hBT).symm
    have e : (T.map g).sum = vec t₀.yield + (qs.map (fun q => vec q.2.yieldC)).sum := by
      rw [hsplit, Multiset.map_add, Multiset.sum_add, hMBg, hTW,
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
  have hst' : t'.size ≤ (Multiset.card I + 1) * uoKL nC nS Acts.card Mb := by
    rw [hs']
    have h1 : (qs.map (fun p => p.2.size)).sum ≤ qs.length * a :=
      sum_le_length_mul _ _ qs (fun q hq => (hps q (hqs_mem q hq)).2.2)
    have h2 : qs.length * a ≤ (Multiset.card I + 1) * Steinitz.zsP Acts.card a * a :=
      Nat.mul_le_mul_right _ hqs_len
    have e : uoKL nC nS Acts.card Mb = 1 + a + Steinitz.zsP Acts.card a * a := rfl
    rw [e]
    have h3 : Multiset.card I * bC ≤ Multiset.card I * a := Nat.mul_le_mul_left _ (by omega)
    have e2 : (Multiset.card I + 1) * (1 + a + Steinitz.zsP Acts.card a * a) =
        (Multiset.card I + 1) + (Multiset.card I * a + a) +
          (Multiset.card I + 1) * Steinitz.zsP Acts.card a * a := by ring
    rw [e2]
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
