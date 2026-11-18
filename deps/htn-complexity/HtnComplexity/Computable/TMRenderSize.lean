import HtnComplexity.Computable.TMRender
/-!
# The size of the described family construction

A hardness family bounds the size of the descriptions it produces.  This file bounds the two
descriptions of `HtnComplexity/Computable/TMRender.lean` in the symbol-counting measure of
`HtnPlanning/Computable/Syntax.lean`, through the generic bounds
`HTN.Syn.Rendering.size_domDesc_le` and `HTN.Syn.Rendering.size_instDesc_le`:

* `HTN.TMEnc.Fam.size_famDomDesc_le` — the described family domain has at most
  `HTN.TMEnc.Fam.famDomBound |Q| |Γ| n L l` symbols, a polynomial in the number of states, the
  number of symbols, the input length `n` and the two logarithmic quantities `L` (the bound on
  the counting tasks of the construction, logarithmic in the time bound `K`,
  `HTN.TMEnc.card_countFinset_le`) and `l = 2 log₂ (K - 1) + 2` (the counting tasks of the
  repaired head chain).  The time bound enters **only logarithmically**, as in the size claim of
  Theorem 4.3.7;
* `HTN.TMEnc.Fam.size_famInstDesc_le` — the described instance has at most `|w| + 4` symbols.
-/

namespace HTN

namespace TMEnc

namespace Fam

open scoped Classical

open TM TaskNetwork Syn

variable {Q Γ : Type} [Fintype Q] [Fintype Γ]

/-! ### The actions -/

omit [Fintype Q] [Fintype Γ] in
lemma length_tmPrecL_le (a : TMAct Q Γ) : (tmPrecL a).length ≤ 3 := by
  cases a <;> simp [tmPrecL]

omit [Fintype Q] [Fintype Γ] in
lemma length_tmAddL_le (a : TMAct Q Γ) : (tmAddL a).length ≤ 2 := by
  cases a <;> simp [tmAddL]

omit [Fintype Q] in
lemma length_tmDelL_le (a : TMAct Q Γ) : (tmDelL a).length ≤ Fintype.card Γ + 2 := by
  cases a with
  | assert c =>
      simp only [tmDelL, List.length_map]
      refine le_trans (List.length_filter_le _ _) ?_
      simp [symList]
  | _ => simp [tmDelL]

omit [Fintype Q] in
/-- Every listed action has at most `|Γ| + 8` symbols. -/
lemma act_size_le (o : GAct Q Γ) :
    1 + (gPrecL o).length + (gAddL o).length + (gDelL o).length ≤ Fintype.card Γ + 8 := by
  rcases o with (_ | p) | a
  · simp [gPrecL, gAddL, gDelL]
  · simp [gPrecL, gAddL, gDelL]
  · have h1 := length_tmPrecL_le a
    have h2 := length_tmAddL_le a
    have h3 := length_tmDelL_le a
    simp only [gPrecL, gAddL, gDelL, List.length_map]
    omega

/-- The number of listed actions. -/
lemma length_famActs (n : ℕ) :
    (famActs (Q := Q) (Γ := Γ) n).length =
      1 + n * Fintype.card Γ + (opFinset (Finset.univ : Finset Q) (Finset.univ : Finset Γ)).card := by
  simp only [famActs, List.length_cons, List.length_append, List.length_flatMap, List.length_map,
    Finset.length_toList, Finset.card_univ, List.map_const', List.length_range, List.sum_replicate,
    smul_eq_mul]
  ring

/-! ### The bodies -/

omit [Fintype Q] [Fintype Γ] in
lemma cells_liftBody (ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))) :
    ((liftBody ls).map List.length).sum = (ls.map List.length).sum := by
  simp [liftBody, Function.comp_def]

omit [Fintype Q] [Fintype Γ] in
/-- Every body of the unguarded family domain has at most ten cells. -/
lemma cells_le_of_mem_bodiesAll {N : NTM Q Γ} {n K : ℕ} {t : TMTask Q Γ}
    {ls : List (List (GAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodiesAll N n K t) :
    (ls.map List.length).sum ≤ 10 := by
  by_cases hw : ∃ i, t = TMTask.produceWord i
  · obtain ⟨i, rfl⟩ := hw
    rw [bodiesAll_produceWord] at hls
    have hex : ∃ c', ls = liftBody (bodyWord n i c') := by
      by_cases hlt : i < n
      · rw [if_pos hlt] at hls; exact hls
      · rw [if_neg hlt] at hls; exact ⟨N.blank, hls⟩
    obtain ⟨c', rfl⟩ := hex
    rw [cells_liftBody]
    unfold bodyWord
    split_ifs <;> simp
  · push_neg at hw
    rw [bodiesAll_eq_image hw] at hls
    obtain ⟨ls₀, hls₀, rfl⟩ := hls
    rw [cells_liftBody]
    obtain ⟨h1, h2⟩ := bodiesFix_small hls₀
    have h := List.sum_le_card_nsmul (ls₀.map List.length) 5 (by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact h2 l hl)
    simp only [List.length_map, smul_eq_mul] at h
    omega

/-- Every listed body has at most `34` symbols. -/
lemma body_size_le {N : NTM Q Γ} {n K : ℕ} {p : TMTask Q Γ × Shape (GAct Q Γ) (TMTask Q Γ)}
    (hp : p ∈ famBodies N n K) : 1 + 3 * p.2.cells + p.2.after ≤ 34 := by
  simp only [famBodies, List.mem_append, List.mem_flatMap, List.mem_map, Finset.mem_toList,
    List.mem_singleton] at hp
  rcases hp with ⟨t, -, ls, hls, rfl⟩ | rfl
  · have h := cells_le_of_mem_bodiesAll (N := N) (by rw [← coe_bodyFinsetFam]; exact hls)
    simp only [guardShape, Shape.cells, List.map_append, List.sum_append]
    simp only [List.map_cons, List.length_singleton, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · simp [sIShape, Shape.cells, liftBody, initChainsFix, headChainFix]

/-- A compound task of the unguarded family domain has at most `B + |Γ|` bodies, `B` the bound of
the repaired encoding. -/
lemma card_bodyFinsetFam_le (N : NTM Q Γ) (n K : ℕ) (t : TMTask Q Γ) :
    (bodyFinsetFam N n K t).card ≤
      ((Fintype.card Γ + 1) + Fintype.card Q * (Fintype.card Γ *
        (Fintype.card Q * (Fintype.card Γ * 3))) + Fintype.card Q + 2) + Fintype.card Γ := by
  have hB := card_bodyFinsetFix_le (N := N) (qs := (Finset.univ : Finset Q))
    (gs := (Finset.univ : Finset Γ)) (w := wpad N n) (K := K) t
  simp only [Finset.card_univ] at hB
  by_cases hw : ∃ i, t = TMTask.produceWord i
  · obtain ⟨i, rfl⟩ := hw
    by_cases hi : i < n
    · simp only [bodyFinsetFam, if_pos hi]
      have := Finset.card_image_le (s := (Finset.univ : Finset Γ))
        (f := fun c => liftBody (bodyWord (Q := Q) n i c))
      simp only [Finset.card_univ] at this
      omega
    · simp only [bodyFinsetFam, if_neg hi, Finset.card_singleton]
      omega
  · push_neg at hw
    have h1 : bodyFinsetFam N n K t =
        (bodyFinsetFix N Finset.univ Finset.univ (wpad N n) K t).image liftBody := by
      cases t with
      | produceWord i => exact absurd rfl (hw i)
      | _ => rfl
    rw [h1]
    exact le_trans Finset.card_image_le (by omega)

/-- The number of listed methods. -/
lemma length_famBodies_le (N : NTM Q Γ) (n K : ℕ) :
    (famBodies N n K).length ≤
      (taskFinsetFam N n K).card *
        (((Fintype.card Γ + 1) + Fintype.card Q * (Fintype.card Γ *
          (Fintype.card Q * (Fintype.card Γ * 3))) + Fintype.card Q + 2) + Fintype.card Γ) + 1 := by
  simp only [famBodies, List.length_append, List.length_flatMap, List.length_map,
    Finset.length_toList, List.length_singleton]
  refine Nat.add_le_add_right ?_ _
  have h := List.sum_le_card_nsmul
    ((taskFinsetFam N n K).toList.map fun t => (bodyFinsetFam N n K t).card) _ (by
      intro x hx
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      exact card_bodyFinsetFam_le N n K t)
  simpa [smul_eq_mul] using h

/-! ### The bound -/

/-- **The closed-form size bound of the described family domain**, in the number of states
`nq`, the number of symbols `ng`, the input length `n`, the number `L` of counts of the counting
tasks and the number `l` of counting tasks of the repaired head chain. -/
def famDomBound (nq ng n L l : ℕ) : ℕ :=
  (1 + n * ng + ((ng + 1) + (ng + nq + 9) + 12 + 2 + nq * ((ng + 1) * (nq * (ng + 1))))) *
      (ng + 8) +
    34 * ((25 + 2 * n + 13 * L + L * L + l + ng) *
      (((ng + 1) + nq * (ng * (nq * (ng * 3))) + nq + 2) + ng) + 1)

/-- **The size of the described family domain.**  It is polynomial in the number of states and
symbols of the machine and in the input length `n`, and the time bound `K` enters only through
the logarithmic quantities `L` and `2 log₂ (K - 1) + 2`. -/
theorem size_famDomDesc_le (N : NTM Q Γ) (q : Q → ℕ) (g : Γ → ℕ) (n K : ℕ) :
    (famDomDesc N q g n K).size ≤
      famDomBound (Fintype.card Q) (Fintype.card Γ) n
        ((2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) + (2 * Nat.log 2 (K + 2) + 2) +
          (2 * Nat.log 2 (K - n) + 2))
        (2 * Nat.log 2 (K - 1) + 2) := by
  unfold famDomBound
  -- the size of the described domain, read off the lists
  have hsize : (famDomDesc N q g n K).size ≤
      ((famActs (Q := Q) (Γ := Γ) n).map fun o =>
        1 + (gPrecL o).length + (gAddL o).length + (gDelL o).length).sum +
      ((famBodies N n K).map fun p => 1 + 3 * p.2.cells + p.2.after).sum := by
    refine Nat.add_le_add ?_ ?_
    · show ((((famActs (Q := Q) (Γ := Γ) n).map fun o =>
        (encGAct q g o, ((gPrecL o).map (encGFact q g), (gAddL o).map (encGFact q g),
          (gDelL o).map (encGFact q g))))).map ActionDesc.size).sum ≤ _
      rw [List.map_map]
      refine List.sum_le_sum fun o _ => ?_
      simp [ActionDesc.size]
    · show (((famBodies N n K).map fun p =>
        (encTMTask g p.1, p.2.desc (encGAct q g) (encTMTask g))).map MethodDesc.size).sum ≤ _
      rw [List.map_map]
      refine List.sum_le_sum fun p _ => ?_
      have := Shape.size_desc_le (encGAct q g) (encTMTask g) p.2
      show 1 + (p.2.desc (encGAct q g) (encTMTask g)).size ≤ 1 + 3 * p.2.cells + p.2.after
      omega
  -- the actions
  have hacts : ((famActs (Q := Q) (Γ := Γ) n).map fun o =>
      1 + (gPrecL o).length + (gAddL o).length + (gDelL o).length).sum ≤
      (famActs (Q := Q) (Γ := Γ) n).length * (Fintype.card Γ + 8) := by
    have h := List.sum_le_card_nsmul ((famActs (Q := Q) (Γ := Γ) n).map fun o =>
      1 + (gPrecL o).length + (gAddL o).length + (gDelL o).length) (Fintype.card Γ + 8) (by
        intro x hx
        obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
        exact act_size_le o)
    simpa [smul_eq_mul] using h
  -- the bodies
  have hbodies : ((famBodies N n K).map fun p => 1 + 3 * p.2.cells + p.2.after).sum ≤
      (famBodies N n K).length * 34 := by
    have h := List.sum_le_card_nsmul ((famBodies N n K).map fun p =>
      1 + 3 * p.2.cells + p.2.after) 34 (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        exact body_size_le hp)
    simpa [smul_eq_mul] using h
  -- the counts
  have hops := card_opFinset_le (qs := (Finset.univ : Finset Q)) (gs := (Finset.univ : Finset Γ))
  simp only [Finset.card_univ] at hops
  have hlen := length_famActs (Q := Q) (Γ := Γ) n
  have hbl := length_famBodies_le N n K
  have htf := card_taskFinsetFam_le N n K
  have htfix := card_taskFinsetFix_le N (wpad N n) K
  have htask := card_taskFinset_le (N := N) (w := wpad N n) (K := K)
  have hcnt := card_countFinset_le K n
  rw [length_wpad] at htask
  set L := (2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) + (2 * Nat.log 2 (K + 2) + 2) +
    (2 * Nat.log 2 (K - n) + 2)
  set c := (countFinset K n).card
  set B := ((Fintype.card Γ + 1) + Fintype.card Q * (Fintype.card Γ *
    (Fintype.card Q * (Fintype.card Γ * 3))) + Fintype.card Q + 2) + Fintype.card Γ
  have hcc : 25 + 2 * n + 13 * c + c * c ≤ 25 + 2 * n + 13 * L + L * L := by
    have := Nat.mul_le_mul hcnt hcnt
    omega
  have hT : (taskFinsetFam N n K).card ≤
      25 + 2 * n + 13 * L + L * L + (2 * Nat.log 2 (K - 1) + 2) + Fintype.card Γ := by
    omega
  have h1 : (famActs (Q := Q) (Γ := Γ) n).length * (Fintype.card Γ + 8) ≤
      (1 + n * Fintype.card Γ + ((Fintype.card Γ + 1) + (Fintype.card Γ + Fintype.card Q + 9) +
        12 + 2 + Fintype.card Q * ((Fintype.card Γ + 1) * (Fintype.card Q *
          (Fintype.card Γ + 1))))) * (Fintype.card Γ + 8) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (famBodies N n K).length * 34 ≤
      34 * ((25 + 2 * n + 13 * L + L * L + (2 * Nat.log 2 (K - 1) + 2) + Fintype.card Γ) * B + 1) := by
    rw [Nat.mul_comm]
    refine Nat.mul_le_mul_left _ (le_trans hbl (Nat.add_le_add_right ?_ _))
    exact Nat.mul_le_mul_right _ hT
  omega

/-- **The size of the described family instance**: at most `|w| + 4` symbols. -/
theorem size_famInstDesc_le (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) (w : List Γ) :
    (famInstDesc N q g w).size ≤ w.length + 4 := by
  have h := (famRendering N hq hg w 0).size_instDesc_le
  rw [instDesc_famRendering] at h
  refine le_trans h (le_of_eq ?_)
  simp [famRendering, famInitL, Shape.cells]

end Fam

end TMEnc

end HTN
