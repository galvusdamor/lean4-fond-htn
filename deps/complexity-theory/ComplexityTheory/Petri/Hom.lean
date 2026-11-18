import ComplexityTheory.Petri.Refute
/-!
# Full homogeneous solutions from unbounded variables

If every variable of the characteristic system (edge multiplicities, `ω`-coordinates of inputs
and outputs) is unbounded over its solutions, then the homogeneous system has a **full** solution
(`exists_full`).  This is Dickson's lemma: two solutions `s ≤ s'` with a strictly larger value of
a given variable yield the homogeneous solution `s' - s`, and homogeneous solutions add up.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp Classical

variable {ι : Type*}

/-! ### Arithmetic of candidate solutions -/

/-- The zero candidate solution. -/
def Tri.zero : Tri ι := ⟨0, 0, 0⟩

/-- The sum of candidate solutions. -/
def Tri.add (t t' : Tri ι) : Tri ι := ⟨t.M₁ + t'.M₁, t.ψ + t'.ψ, t.M' + t'.M'⟩

/-- The difference of candidate solutions (truncated on the multiplicities). -/
def Tri.sub (t t' : Tri ι) : Tri ι := ⟨t.M₁ - t'.M₁, t.ψ - t'.ψ, t.M' - t'.M'⟩

theorem outF_zero (E : List (ℕ × ℕ)) (w : ℕ) : outF E 0 w = 0 := by simp [outF]

theorem inF_zero (E : List (ℕ × ℕ)) (w : ℕ) : inF E 0 w = 0 := by simp [inF]

theorem kirch_zero (E : List (ℕ × ℕ)) (s : ℕ) : Kirch E 0 s s := by
  intro w; simp [outF_zero, inF_zero]

theorem kirch_sub {E : List (ℕ × ℕ)} {φ ψ : ℕ → ℕ} {s t : ℕ} (h₁ : Kirch E φ s t)
    (h₂ : Kirch E ψ s t) (hle : ∀ k < E.length, φ k ≤ ψ k) : Kirch E (ψ - φ) s s := by
  have hc : ∀ k < E.length, ψ k = (φ + (ψ - φ)) k := fun k hk => by
    simp only [Pi.add_apply, Pi.sub_apply]; have := hle k hk; omega
  intro w
  have a := h₁ w; have b := h₂ w
  rw [outF_congr E hc, inF_congr E hc, outF_add, inF_add] at b
  omega

theorem psum_zero (C : Comp ι) : psum C 0 = 0 := by simp [psum]

theorem psum_sub (C : Comp ι) {φ ψ : ℕ → ℕ} (hle : ∀ k < C.edges.length, φ k ≤ ψ k) :
    psum C (ψ - φ) = psum C ψ - psum C φ := by
  have hc : ∀ k < C.edges.length, ψ k = (φ + (ψ - φ)) k := fun k hk => by
    simp only [Pi.add_apply, Pi.sub_apply]; have := hle k hk; omega
  rw [psum_congr C hc, psum_add]; abel

theorem homOK_zero (b : Block ι) : HomOK b Tri.zero := by
  refine ⟨fun j => le_rfl, fun j _ => rfl, kirch_zero _ _, ?_, fun j => le_rfl, fun j _ => rfl⟩
  simp [Tri.zero, psum_zero]

theorem homOK_add {b : Block ι} {h h' : Tri ι} (hh : HomOK b h) (hh' : HomOK b h') :
    HomOK b (h.add h') := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hh
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hh'
  refine ⟨fun j => ?_, fun j hj => ?_, kirch_add a3 b3, ?_, fun j => ?_, fun j hj => ?_⟩
  · simp only [Tri.add, Pi.add_apply]; linarith [a1 j, b1 j]
  · simp [Tri.add, a2 j hj, b2 j hj]
  · simp only [Tri.add, psum_add, a4, b4]; abel
  · simp only [Tri.add, Pi.add_apply]; linarith [a5 j, b5 j]
  · simp [Tri.add, a6 j hj, b6 j hj]

/-- Coordinatewise comparison of two candidate solutions of a block. -/
def TriLE (b : Block ι) (t t' : Tri ι) : Prop :=
  (∀ j, t.M₁ j ≤ t'.M₁ j) ∧ (∀ k < b.comp.edges.length, t.ψ k ≤ t'.ψ k) ∧ ∀ j, t.M' j ≤ t'.M' j

theorem homOK_sub {b : Block ι} {t t' : Tri ι} (ht : CharOK b t) (ht' : CharOK b t')
    (hle : TriLE b t t') : HomOK b (t'.sub t) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ht
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := ht'
  obtain ⟨l1, l2, l3⟩ := hle
  refine ⟨fun j => ?_, fun j hj => ?_, ?_, ?_, fun j => ?_, fun j hj => ?_⟩
  · simp only [Tri.sub, Pi.sub_apply]; linarith [l1 j]
  · simp [Tri.sub, a2 j hj, b2 j hj]
  · exact kirch_sub a3 b3 fun k hk => l2 k (by rwa [gr_length] at hk)
  · simp only [Tri.sub, psum_sub _ l2, a4, b4]; abel
  · simp only [Tri.sub, Pi.sub_apply]; linarith [l3 j]
  · simp [Tri.sub, a6 j hj, b6 j hj]

/-! ### Lists -/

theorem linkedBy_iff {f : (ι → ℤ) → (ι → ℤ) → (ι → ℤ)} {bs : List (Block ι)}
    {ts : List (Tri ι)} (hl : bs.length = ts.length) :
    LinkedBy f bs ts ↔ ∀ i (h : i + 1 < ts.length),
      ts[i + 1].M₁ = f ts[i].M' (bs[i + 1]'(by omega)).pre := by
  induction bs generalizing ts with
  | nil =>
    cases ts with
    | nil => simp [LinkedBy]
    | cons => simp at hl
  | cons b bs ih =>
    cases ts with
    | nil => simp at hl
    | cons t ts =>
      cases bs with
      | nil =>
        cases ts with
        | nil => simp [LinkedBy]
        | cons => simp at hl
      | cons b' bs =>
        cases ts with
        | nil => simp at hl
        | cons t' ts =>
          simp only [LinkedBy]
          rw [ih (ts := t' :: ts) (by simpa using hl)]
          constructor
          · rintro ⟨h0, h1⟩ i hi
            rcases i with _ | i
            · simpa using h0
            · simpa using h1 i (by simp at hi ⊢; omega)
          · intro H
            refine ⟨by simpa using H 0 (by simp), fun i hi => ?_⟩
            simpa using H (i + 1) (by simp at hi ⊢; omega)

theorem forall₂_iff_get {α β : Type*} {R : α → β → Prop} {bs : List α} {ts : List β} :
    List.Forall₂ R bs ts ↔ ∃ h : bs.length = ts.length, ∀ i (hi : i < bs.length),
      R bs[i] (ts[i]'(h ▸ hi)) := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨h, H⟩; exact ⟨h, fun i hi => H i hi _⟩
  · rintro ⟨h, H⟩; exact ⟨h, fun i hi _ => H i hi⟩

/-- The sum of two lists of candidate solutions. -/
def addL (hs hs' : List (Tri ι)) : List (Tri ι) := List.zipWith Tri.add hs hs'

/-- The difference of two lists of candidate solutions. -/
def subL (ts' ts : List (Tri ι)) : List (Tri ι) := List.zipWith Tri.sub ts' ts

theorem homSol_zero (bs : List (Block ι)) : HomSol bs (bs.map fun _ => Tri.zero) := by
  refine ⟨?_, ?_⟩
  · rw [forall₂_iff_get]
    exact ⟨by simp, fun i hi => by simpa using homOK_zero _⟩
  · rw [linkedBy_iff (by simp)]
    intro i hi; simp [Tri.zero]

theorem homSol_add {bs : List (Block ι)} {hs hs' : List (Tri ι)} (h : HomSol bs hs)
    (h' : HomSol bs hs') : HomSol bs (addL hs hs') := by
  obtain ⟨⟨hl, H⟩, hL⟩ := And.imp_left forall₂_iff_get.1 h
  obtain ⟨⟨hl', H'⟩, hL'⟩ := And.imp_left forall₂_iff_get.1 h'
  have hlen : bs.length = (addL hs hs').length := by simp [addL, ← hl, ← hl']
  refine ⟨forall₂_iff_get.2 ⟨hlen, fun i hi => ?_⟩, (linkedBy_iff hlen).2 fun i hi => ?_⟩
  · simp only [addL, List.getElem_zipWith]
    exact homOK_add (H i hi) (H' i hi)
  · rw [linkedBy_iff hl] at hL; rw [linkedBy_iff hl'] at hL'
    have hi' : i + 1 < hs.length := by simp [addL] at hi; omega
    have hi'' : i + 1 < hs'.length := by simp [addL] at hi; omega
    simp only [addL, List.getElem_zipWith, Tri.add]
    rw [hL i hi', hL' i hi'']

theorem homSol_sub {bs : List (Block ι)} {ts ts' : List (Tri ι)} (h : CharSol bs ts)
    (h' : CharSol bs ts') (hle : List.Forall₂ (fun b (p : Tri ι × Tri ι) => TriLE b p.1 p.2) bs
      (List.zip ts ts')) : HomSol bs (subL ts' ts) := by
  obtain ⟨⟨hl, H⟩, hL⟩ := And.imp_left forall₂_iff_get.1 h
  obtain ⟨⟨hl', H'⟩, hL'⟩ := And.imp_left forall₂_iff_get.1 h'
  obtain ⟨hlz, Hle⟩ := forall₂_iff_get.1 hle
  have hlen : bs.length = (subL ts' ts).length := by simp [subL, ← hl, ← hl']
  refine ⟨forall₂_iff_get.2 ⟨hlen, fun i hi => ?_⟩, (linkedBy_iff hlen).2 fun i hi => ?_⟩
  · simp only [subL, List.getElem_zipWith]
    have := Hle i hi
    simp only [List.getElem_zip] at this
    exact homOK_sub (H i hi) (H' i hi) this
  · rw [linkedBy_iff hl] at hL; rw [linkedBy_iff hl'] at hL'
    have hi' : i + 1 < ts.length := by simp [subL] at hi; omega
    have hi'' : i + 1 < ts'.length := by simp [subL] at hi; omega
    simp only [subL, List.getElem_zipWith, Tri.sub]
    rw [hL i hi', hL' i hi'']
    abel

/-! ### Coordinates -/

/-- The coordinates of a list of candidate solutions: block index and variable. -/
def crd (ts : List (Tri ι)) : ℕ × (ι ⊕ ℕ ⊕ ι) → ℤ
  | (i, .inl j) => (ts.getD i Tri.zero).M₁ j
  | (i, .inr (.inl k)) => ((ts.getD i Tri.zero).ψ k : ℤ)
  | (i, .inr (.inr j)) => (ts.getD i Tri.zero).M' j

theorem getD_addL {hs hs' : List (Tri ι)} (hl : hs.length = hs'.length) (i : ℕ) :
    (addL hs hs').getD i Tri.zero = (hs.getD i Tri.zero).add (hs'.getD i Tri.zero) := by
  by_cases hi : i < hs.length
  · rw [List.getD_eq_getElem _ _ (by simp [addL]; omega), List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by omega)]
    simp [addL]
  · rw [List.getD_eq_default _ _ (by simp [addL]; omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]
    simp [Tri.add, Tri.zero]

theorem getD_subL {ts ts' : List (Tri ι)} (hl : ts.length = ts'.length) (i : ℕ) :
    (subL ts' ts).getD i Tri.zero = (ts'.getD i Tri.zero).sub (ts.getD i Tri.zero) := by
  by_cases hi : i < ts.length
  · rw [List.getD_eq_getElem _ _ (by simp [subL]; omega), List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by omega)]
    simp [subL]
  · rw [List.getD_eq_default _ _ (by simp [subL]; omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]
    simp [Tri.sub, Tri.zero]

theorem crd_addL {hs hs' : List (Tri ι)} (hl : hs.length = hs'.length) (v : ℕ × (ι ⊕ ℕ ⊕ ι)) :
    crd (addL hs hs') v = crd hs v + crd hs' v := by
  obtain ⟨i, j | k | j⟩ := v <;> simp only [crd] <;> rw [getD_addL hl] <;> simp [Tri.add]

theorem crd_subL {ts ts' : List (Tri ι)} (hl : ts.length = ts'.length) {v : ℕ × (ι ⊕ ℕ ⊕ ι)}
    (hle : crd ts v ≤ crd ts' v) : crd (subL ts' ts) v = crd ts' v - crd ts v := by
  obtain ⟨i, j | k | j⟩ := v
  · simp only [crd]; rw [getD_subL hl]; simp [Tri.sub]
  · simp only [crd] at hle ⊢; rw [getD_subL hl]; simp only [Tri.sub, Pi.sub_apply]
    have : (ts.getD i Tri.zero).ψ k ≤ (ts'.getD i Tri.zero).ψ k := by exact_mod_cast hle
    push_cast [this]; ring
  · simp only [crd]; rw [getD_subL hl]; simp [Tri.sub]

theorem getD_of_forall₂ {R : Block ι → Tri ι → Prop} {P : Tri ι → Prop} {bs : List (Block ι)}
    {ts : List (Tri ι)} (h : List.Forall₂ R bs ts) (hR : ∀ b t, R b t → P t) (hz : P Tri.zero)
    (i : ℕ) : P (ts.getD i Tri.zero) := by
  obtain ⟨hl, H⟩ := forall₂_iff_get.1 h
  by_cases hi : i < bs.length
  · rw [List.getD_eq_getElem _ _ (by omega)]; exact hR _ _ (H i hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hz

theorem crd_nonneg_hom {bs : List (Block ι)} {hs : List (Tri ι)} (h : HomSol bs hs)
    (v : ℕ × (ι ⊕ ℕ ⊕ ι)) : 0 ≤ crd hs v := by
  have hb := getD_of_forall₂ (P := fun t : Tri ι => (∀ j, 0 ≤ t.M₁ j) ∧ ∀ j, 0 ≤ t.M' j) h.1
    (fun _ _ ht => ⟨ht.1, ht.2.2.2.2.1⟩) ⟨fun _ => le_rfl, fun _ => le_rfl⟩ v.1
  obtain ⟨i, j | k | j⟩ := v
  · exact hb.1 j
  · simp [crd]
  · exact hb.2 j

theorem crd_nonneg_char {bs : List (Block ι)} {ts : List (Tri ι)} (h : CharSol bs ts)
    (v : ℕ × (ι ⊕ ℕ ⊕ ι)) : 0 ≤ crd ts v := by
  have hb := getD_of_forall₂ (P := fun t : Tri ι => (∀ j, 0 ≤ t.M₁ j) ∧ ∀ j, 0 ≤ t.M' j) h.1
    (fun _ _ ht => ⟨ht.1, ht.2.2.2.2.1⟩) ⟨fun _ => le_rfl, fun _ => le_rfl⟩ v.1
  obtain ⟨i, j | k | j⟩ := v
  · exact hb.1 j
  · simp [crd]
  · exact hb.2 j

/-! ### Dickson's lemma -/

/-- **An unbounded variable is positive in some homogeneous solution.** -/
theorem exists_hom_pos [Fintype ι] {bs : List (Block ι)} (L : ℕ)
    (hL : ∀ b ∈ bs, b.comp.edges.length ≤ L) (v : ℕ × (ι ⊕ ℕ ⊕ ι)) (hv : v.1 < bs.length)
    (hvk : ∀ k, v.2 = .inr (.inl k) → k < L)
    (hunb : ∀ B : ℤ, ∃ ts, CharSol bs ts ∧ B < crd ts v) :
    ∃ hs, HomSol bs hs ∧ 1 ≤ crd hs v := by
  choose S hS hSv using hunb
  let seq : ℕ → List (Tri ι) := fun n => Nat.rec (S 0) (fun _ ts => S (crd ts v)) n
  have hseq : ∀ n, CharSol bs (seq n) := fun n => by cases n <;> exact hS _
  have hmono : StrictMono fun n => crd (seq n) v :=
    strictMono_nat_of_lt_succ fun n => hSv (crd (seq n) v)
  let W := Fin bs.length × (ι ⊕ Fin L ⊕ ι)
  let emb : W → ℕ × (ι ⊕ ℕ ⊕ ι) := fun w => (w.1, match w.2 with
    | .inl j => .inl j
    | .inr (.inl k) => .inr (.inl k.1)
    | .inr (.inr j) => .inr (.inr j))
  let f : ℕ → W → ℕ := fun n w => (crd (seq n) (emb w)).toNat
  obtain ⟨m, n, hmn, hle⟩ := wellQuasiOrdered_le f
  have hle' : ∀ w, crd (seq m) (emb w) ≤ crd (seq n) (emb w) := fun w => by
    have h1 := hle w
    have h2 := crd_nonneg_char (hseq m) (emb w)
    have h3 := crd_nonneg_char (hseq n) (emb w)
    simp only [f] at h1
    omega
  have hlm := (hseq m).1.length_eq
  have hln := (hseq n).1.length_eq
  have hvW : ∃ w, emb w = v := by
    obtain ⟨i, j | k | j⟩ := v
    · exact ⟨(⟨i, hv⟩, .inl j), rfl⟩
    · exact ⟨(⟨i, hv⟩, .inr (.inl ⟨k, hvk k rfl⟩)), rfl⟩
    · exact ⟨(⟨i, hv⟩, .inr (.inr j)), rfl⟩
  obtain ⟨w₀, rfl⟩ := hvW
  refine ⟨subL (seq n) (seq m), homSol_sub (hseq m) (hseq n) ?_, ?_⟩
  · rw [forall₂_iff_get]
    refine ⟨by simp [← hlm, ← hln], fun i hi => ?_⟩
    simp only [List.getElem_zip]
    have gm : (seq m)[i]'(by omega) = (seq m).getD i Tri.zero :=
      (List.getD_eq_getElem _ _ (by omega)).symm
    have gn : (seq n)[i]'(by omega) = (seq n).getD i Tri.zero :=
      (List.getD_eq_getElem _ _ (by omega)).symm
    rw [gm, gn]
    refine ⟨fun j => hle' (⟨i, hi⟩, .inl j), fun k hk => ?_, fun j => hle' (⟨i, hi⟩, .inr (.inr j))⟩
    have := hle' (⟨i, hi⟩, .inr (.inl ⟨k, (hk.trans_le (hL _ (List.getElem_mem hi)))⟩))
    simp only [emb, crd] at this
    exact_mod_cast this
  · rw [crd_subL (by omega) (hle' w₀)]
    have := hmono hmn
    simp only at this
    omega

/-- Homogeneous solutions positive on finitely many given variables. -/
theorem exists_hom_finset {bs : List (Block ι)} (W : Finset (ℕ × (ι ⊕ ℕ ⊕ ι)))
    (h : ∀ v ∈ W, ∃ hs, HomSol bs hs ∧ 1 ≤ crd hs v) :
    ∃ hs, HomSol bs hs ∧ ∀ v ∈ W, 1 ≤ crd hs v := by
  induction W using Finset.induction_on with
  | empty => exact ⟨_, homSol_zero bs, by simp⟩
  | insert v W hv ih =>
    obtain ⟨hs, hH, hW⟩ := ih fun w hw => h w (Finset.mem_insert_of_mem hw)
    obtain ⟨hs', hH', hv'⟩ := h v (Finset.mem_insert_self _ _)
    have hl : hs'.length = hs.length := by rw [← hH.1.length_eq, ← hH'.1.length_eq]
    refine ⟨addL hs' hs, homSol_add hH' hH, fun w hw => ?_⟩
    rw [crd_addL hl]
    rcases Finset.mem_insert.1 hw with rfl | hw
    · linarith [crd_nonneg_hom hH w]
    · linarith [crd_nonneg_hom hH' w, hW w hw]

/-- The variables that must be positive in a full homogeneous solution. -/
def Req (bs : List (Block ι)) : ℕ × (ι ⊕ ℕ ⊕ ι) → Prop
  | (i, .inl j) => ∃ h : i < bs.length, bs[i].inp j = ⊤
  | (i, .inr (.inl k)) => ∃ h : i < bs.length, k < bs[i].comp.edges.length
  | (i, .inr (.inr j)) => ∃ h : i < bs.length, bs[i].out j = ⊤

/-- **Full homogeneous solutions from unbounded variables.** -/
theorem exists_full [Fintype ι] {bs : List (Block ι)}
    (hunb : ∀ v, Req bs v → ∀ B : ℤ, ∃ ts, CharSol bs ts ∧ B < crd ts v) :
    ∃ hs, HomSol bs hs ∧ List.Forall₂ Full bs hs := by
  let L := (bs.map fun b => b.comp.edges.length).sum
  have hL : ∀ b ∈ bs, b.comp.edges.length ≤ L := fun b hb =>
    List.le_sum_of_mem (List.mem_map_of_mem hb)
  let W : Finset (ℕ × (ι ⊕ ℕ ⊕ ι)) := (Finset.range bs.length ×ˢ
    (Finset.univ.image Sum.inl ∪ ((Finset.range L).image fun k => Sum.inr (Sum.inl k)) ∪
      Finset.univ.image fun j => Sum.inr (Sum.inr j))).filter (Req bs)
  have hW : ∀ v, Req bs v → v ∈ W := by
    rintro ⟨i, j | k | j⟩ hv <;> obtain ⟨hi, hv'⟩ := hv <;>
      simp only [W, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_union,
        Finset.mem_image, Finset.mem_univ, true_and]
    · exact ⟨⟨hi, Or.inl (Or.inl ⟨j, rfl⟩)⟩, hi, hv'⟩
    · exact ⟨⟨hi, Or.inl (Or.inr ⟨k, (hv'.trans_le (hL _ (List.getElem_mem hi))), rfl⟩)⟩, hi, hv'⟩
    · exact ⟨⟨hi, Or.inr ⟨j, rfl⟩⟩, hi, hv'⟩
  obtain ⟨hs, hH, hpos⟩ := exists_hom_finset (bs := bs) W fun v hv => by
    have hR := (Finset.mem_filter.1 hv).2
    refine exists_hom_pos L hL v ?_ ?_ (hunb v hR)
    · obtain ⟨i, j | k | j⟩ := v <;> exact hR.1
    · rintro k hk
      obtain ⟨i, w⟩ := v
      subst hk
      exact hR.2.trans_le (hL _ (List.getElem_mem hR.1))
  refine ⟨hs, hH, ?_⟩
  obtain ⟨hl, -⟩ := forall₂_iff_get.1 hH.1
  rw [forall₂_iff_get]
  refine ⟨hl, fun i hi => ?_⟩
  have g : hs[i]'(hl ▸ hi) = hs.getD i Tri.zero := (List.getD_eq_getElem _ _ _).symm
  rw [g]
  refine ⟨fun k hk => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have := hpos (i, .inr (.inl k)) (hW _ ⟨hi, hk⟩)
    simp only [crd] at this; exact_mod_cast this
  · exact hpos (i, .inl j) (hW _ ⟨hi, hj⟩)
  · exact hpos (i, .inr (.inr j)) (hW _ ⟨hi, hj⟩)

end KLM

end Petri

end HTN
