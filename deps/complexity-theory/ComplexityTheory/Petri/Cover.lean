import ComplexityTheory.Petri.RE
import ComplexityTheory.Petri.Ideal
/-!
# Petri net coverability is decidable

`HTN.Petri.cover_computable`: the predicate "some marking `≥ m₁` is reachable from `m₀` in the
net `N`" is computable on triples `(N, m₀, m₁)`.

Coverability is r.e. (`HTN.Petri.cover_re`).  Non-coverability is r.e. because it has a
**certificate**: a finite list `D` of ω-markings (written `(Ω, f)`: the places in `Ω` are
unbounded, a place `p ∉ Ω` holds at most `count p f` tokens) such that

1. `m₀` lies in the ideal of some member of `D`;
2. `m₁` lies in the ideal of no member of `D`;
3. `D` is **inductive**: firing a transition enabled somewhere in the ideal of a member of `D`
   leads into the ideal of a member of `D` (`HTN.Petri.LeStep`).

Soundness (`HTN.Petri.not_cover_of_covCert`) is an induction along runs.  Completeness
(`HTN.Petri.exists_covCert`) takes for `D` the ideal decomposition of the downward closure of the
reachability set (`HTN.Petri.exists_finset_idl`); inductiveness then comes from irreducibility
of ideals (`HTN.Petri.le_of_idl_subset_biUnion`).  The certificate check is primitive recursive
(`HTN.Petri.primrec_covCert`).
-/

namespace HTN

namespace Petri

open Primrec

/-- **Coverability**: some marking `≥ m₁` is reachable from `m₀`. -/
def Cover (N : List (Trans ℕ)) (m₀ m₁ : Multiset ℕ) : Prop := ∃ m, m₁ ≤ m ∧ Reach N m₀ m

/-! ### Certificates -/

/-- An ω-marking, as lists: the unbounded places and the bounds of the others. -/
abbrev OM : Type := List ℕ × List ℕ

/-- The marking `m` lies in the ideal of `o`. -/
def InIdl (o : OM) (m : List ℕ) : Prop := ∀ p ∈ m, p ∉ o.1 → cnt p m ≤ cnt p o.2

/-- The transition `t` is enabled somewhere in the ideal of `o`. -/
def Enab (t : Trans ℕ) (o : OM) : Prop := ∀ p ∈ t.1, p ∉ o.1 → cnt p t.1 ≤ cnt p o.2

/-- Firing `t` in the ideal of `o` leads into the ideal of `o'`. -/
def LeStep (o : OM) (t : Trans ℕ) (o' : OM) : Prop :=
  (∀ p ∈ o.1, p ∈ o'.1) ∧
    ∀ p ∈ o.2 ++ t.2, p ∉ o'.1 → cnt p o.2 - cnt p t.1 + cnt p t.2 ≤ cnt p o'.2

/-- **A certificate of non-coverability.** -/
def CovCert (N : List (Trans ℕ)) (m₀ m₁ : List ℕ) (D : List OM) : Prop :=
  (∃ o ∈ D, InIdl o m₀) ∧ (∀ o ∈ D, ¬ InIdl o m₁) ∧
    ∀ o ∈ D, ∀ t ∈ N, Enab t o → ∃ o' ∈ D, LeStep o t o'

/-- The ideal of `o`, on multisets. -/
def IdlM (o : OM) (m : Multiset ℕ) : Prop :=
  ∀ p, p ∉ o.1 → m.count p ≤ (o.2 : Multiset ℕ).count p

theorem inIdl_iff {o : OM} {m : List ℕ} : InIdl o m ↔ IdlM o (m : Multiset ℕ) := by
  constructor
  · intro h p hp
    by_cases hm : p ∈ m
    · simpa [cnt_eq] using h p hm hp
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using hm)]; exact Nat.zero_le _
  · intro h p _ hp
    simpa [cnt_eq] using h p hp

/-! ### Soundness -/

theorem idlM_of_reach {N : List (Trans ℕ)} {D : List OM}
    (hD : ∀ o ∈ D, ∀ t ∈ N, Enab t o → ∃ o' ∈ D, LeStep o t o') {m₀ m : Multiset ℕ}
    (h : Reach N m₀ m) (h₀ : ∃ o ∈ D, IdlM o m₀) : ∃ o ∈ D, IdlM o m := by
  induction h with
  | refl => exact h₀
  | @tail m m' _ hstep ih =>
    obtain ⟨o, ho, hm⟩ := ih
    obtain ⟨t, ht, hle, rfl⟩ := hstep
    have hen : Enab t o := by
      intro p _ hp
      have h1 := Multiset.le_iff_count.1 hle p
      have h2 := hm p hp
      simp only [cnt_eq]
      omega
    obtain ⟨o', ho', hsub, hcnt⟩ := hD o ho t ht hen
    refine ⟨o', ho', fun p hp => ?_⟩
    have hpo : p ∉ o.1 := fun h => hp (hsub p h)
    have h1 := Multiset.le_iff_count.1 hle p
    have h2 := hm p hpo
    rw [Multiset.count_add, Multiset.count_sub]
    by_cases hmem : p ∈ o.2 ++ t.2
    · have h3 := hcnt p hmem hp
      simp only [cnt_eq] at h3
      omega
    · simp only [List.mem_append, not_or] at hmem
      have h4 : (o.2 : Multiset ℕ).count p = 0 :=
        Multiset.count_eq_zero_of_notMem (by simpa using hmem.1)
      have h5 : (t.2 : Multiset ℕ).count p = 0 :=
        Multiset.count_eq_zero_of_notMem (by simpa using hmem.2)
      omega

/-- **Soundness of certificates.** -/
theorem not_cover_of_covCert {N : List (Trans ℕ)} {m₀ m₁ : List ℕ} {D : List OM}
    (h : CovCert N m₀ m₁ D) : ¬ Cover N (m₀ : Multiset ℕ) (m₁ : Multiset ℕ) := by
  rintro ⟨m, hle, hr⟩
  obtain ⟨h₀, h₁, hD⟩ := h
  obtain ⟨o, ho, hm⟩ := idlM_of_reach hD hr
    (by obtain ⟨o, ho, h⟩ := h₀; exact ⟨o, ho, inIdl_iff.1 h⟩)
  refine h₁ o ho (inIdl_iff.2 fun p hp => ?_)
  exact (Multiset.le_iff_count.1 hle p).trans (hm p hp)

/-! ### Completeness -/

section Complete

variable (N : List (Trans ℕ)) (m₀ m₁ : List ℕ)

/-- The places mentioned. -/
def places : Finset ℕ := (m₀ ++ m₁ ++ N.flatMap fun t => t.1 ++ t.2).toFinset

variable {N m₀ m₁}

theorem mem_places_of_pre {t : Trans ℕ} (ht : t ∈ N) {p : ℕ} (hp : p ∈ t.1) :
    p ∈ places N m₀ m₁ := by
  simp only [places, List.mem_toFinset, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨t, ht, Or.inl hp⟩

theorem mem_places_of_post {t : Trans ℕ} (ht : t ∈ N) {p : ℕ} (hp : p ∈ t.2) :
    p ∈ places N m₀ m₁ := by
  simp only [places, List.mem_toFinset, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨t, ht, Or.inr hp⟩

theorem mem_places_of_m₀ {p : ℕ} (hp : p ∈ m₀) : p ∈ places N m₀ m₁ := by
  simp [places, hp]

theorem mem_places_of_m₁ {p : ℕ} (hp : p ∈ m₁) : p ∈ places N m₀ m₁ := by
  simp [places, hp]

theorem count_eq_zero_of_reach {m : Multiset ℕ} (h : Reach N (m₀ : Multiset ℕ) m) {p : ℕ}
    (hp : p ∉ places N m₀ m₁) : m.count p = 0 := by
  induction h with
  | refl => exact Multiset.count_eq_zero_of_notMem (by simpa using fun h => hp (mem_places_of_m₀ h))
  | @tail m m' _ hstep ih =>
    obtain ⟨t, ht, -, rfl⟩ := hstep
    rw [Multiset.count_add, Multiset.count_sub, ih,
      Multiset.count_eq_zero_of_notMem (s := (t.2 : Multiset ℕ))
        (by simpa using fun h => hp (mem_places_of_post ht h))]
    simp

/-- The ω-marking of an ω-vector over the places. -/
noncomputable def conv (v : places N m₀ m₁ → ℕ∞) : OM :=
  (((places N m₀ m₁).attach.filter fun i => v i = ⊤).toList.map Subtype.val,
    (∑ i ∈ (places N m₀ m₁).attach, Multiset.replicate (v i).toNat i.1).toList)

theorem mem_conv_fst {v : places N m₀ m₁ → ℕ∞} {p : ℕ} :
    p ∈ (conv v).1 ↔ ∃ h : p ∈ places N m₀ m₁, v ⟨p, h⟩ = ⊤ := by
  simp [conv]

theorem count_conv_snd (v : places N m₀ m₁ → ℕ∞) (p : ℕ) :
    ((conv v).2 : Multiset ℕ).count p =
      if h : p ∈ places N m₀ m₁ then (v ⟨p, h⟩).toNat else 0 := by
  simp only [conv, Multiset.coe_toList, Multiset.count_sum', Multiset.count_replicate]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨p, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro he
      exact hb (Subtype.ext he)
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro he
    exact h (he ▸ i.2)

theorem mem_conv_snd {v : places N m₀ m₁ → ℕ∞} {p : ℕ} (hp : p ∈ (conv v).2) :
    p ∈ places N m₀ m₁ := by
  by_contra h
  have := count_conv_snd v p
  rw [dif_neg h] at this
  exact (Multiset.count_eq_zero.1 this) (by simpa using hp)

/-- The downward closure of the reachability set, on the places. -/
def dset (N : List (Trans ℕ)) (m₀ m₁ : List ℕ) : Set (places N m₀ m₁ → ℕ) :=
  {x | ∃ m, Reach N (m₀ : Multiset ℕ) m ∧ ∀ i, x i ≤ m.count i.1}

theorem dset_down : ∀ x ∈ dset N m₀ m₁, ∀ y ≤ x, y ∈ dset N m₀ m₁ := by
  rintro x ⟨m, hr, hx⟩ y hy
  exact ⟨m, hr, fun i => (hy i).trans (hx i)⟩

/-- The ω-vector after firing `t`. -/
noncomputable def postV (t : Trans ℕ) (v : places N m₀ m₁ → ℕ∞) : places N m₀ m₁ → ℕ∞ :=
  fun i => v i - ((t.1 : Multiset ℕ).count i.1 : ℕ∞) + ((t.2 : Multiset ℕ).count i.1 : ℕ∞)

theorem enab_conv {v : places N m₀ m₁ → ℕ∞} {t : Trans ℕ} (hen : Enab t (conv v))
    (i : places N m₀ m₁) (hv : v i ≠ ⊤) : (t.1 : Multiset ℕ).count i.1 ≤ (v i).toNat := by
  by_cases hp : i.1 ∈ t.1
  · have hni : i.1 ∉ (conv v).1 := by
      rw [mem_conv_fst]
      rintro ⟨h, h'⟩
      exact hv h'
    have := hen i.1 hp hni
    rw [cnt_eq, cnt_eq, count_conv_snd, dif_pos i.2] at this
    exact this
  · rw [Multiset.count_eq_zero_of_notMem (by simpa using hp)]
    exact Nat.zero_le _

theorem postV_of_ne_top {v : places N m₀ m₁ → ℕ∞} {t : Trans ℕ} {i : places N m₀ m₁}
    (hv : v i ≠ ⊤) : postV t v i = (((v i).toNat - (t.1 : Multiset ℕ).count i.1 +
      (t.2 : Multiset ℕ).count i.1 : ℕ) : ℕ∞) := by
  unfold postV
  rw [← ENat.coe_toNat hv]
  push_cast [ENat.coe_sub]
  rfl

theorem postV_of_top {v : places N m₀ m₁ → ℕ∞} {t : Trans ℕ} {i : places N m₀ m₁}
    (hv : v i = ⊤) : postV t v i = ⊤ := by
  simp [postV, hv]

theorem idl_postV_subset {v : places N m₀ m₁ → ℕ∞} (hv : idl v ⊆ dset N m₀ m₁)
    {t : Trans ℕ} (ht : t ∈ N) (hen : Enab t (conv v)) : idl (postV t v) ⊆ dset N m₀ m₁ := by
  intro x hx
  -- a point of the ideal of `v` from which `t` leads above `x`
  let y : places N m₀ m₁ → ℕ := fun i =>
    (t.1 : Multiset ℕ).count i.1 + (x i - (t.2 : Multiset ℕ).count i.1)
  have hy : y ∈ idl v := by
    intro i
    by_cases hvi : v i = ⊤
    · rw [hvi]; exact le_top
    · have h1 := enab_conv hen i hvi
      have h2 := hx i
      rw [postV_of_ne_top hvi, Nat.cast_le] at h2
      rw [← ENat.coe_toNat hvi, Nat.cast_le]
      simp only [y]
      omega
  obtain ⟨m, hr, hm⟩ := hv hy
  have hle : (t.1 : Multiset ℕ) ≤ m := by
    rw [Multiset.le_iff_count]
    intro p
    by_cases hp : p ∈ places N m₀ m₁
    · have := hm ⟨p, hp⟩
      simp only [y] at this
      omega
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using fun h => hp (mem_places_of_pre ht h))]
      exact Nat.zero_le _
  refine ⟨m - t.1 + t.2, hr.tail ⟨t, ht, hle, rfl⟩, fun i => ?_⟩
  have := hm i
  have h1 := Multiset.le_iff_count.1 hle i.1
  simp only [y] at this
  rw [Multiset.count_add, Multiset.count_sub]
  omega

/-- **Completeness of certificates.** -/
theorem exists_covCert (h : ¬ Cover N (m₀ : Multiset ℕ) (m₁ : Multiset ℕ)) :
    ∃ D, CovCert N m₀ m₁ D := by
  classical
  obtain ⟨D₀, hD₀⟩ := exists_finset_idl (dset N m₀ m₁) dset_down
  have hsub : ∀ v ∈ D₀, idl v ⊆ dset N m₀ m₁ := by
    intro v hv x hx
    rw [hD₀]
    exact Set.mem_biUnion hv hx
  refine ⟨D₀.toList.map conv, ⟨?_, ?_, ?_⟩⟩
  · -- the initial marking
    have hx : (fun i : places N m₀ m₁ => (m₀ : Multiset ℕ).count i.1) ∈ dset N m₀ m₁ :=
      ⟨m₀, Relation.ReflTransGen.refl, fun _ => le_rfl⟩
    rw [hD₀] at hx
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.1 hx
    refine ⟨conv v, List.mem_map.2 ⟨v, Finset.mem_toList.2 hv, rfl⟩, inIdl_iff.2 fun p hp => ?_⟩
    rw [count_conv_snd]
    split_ifs with hpl
    · have hvt : v ⟨p, hpl⟩ ≠ ⊤ := fun h' => hp (mem_conv_fst.2 ⟨hpl, h'⟩)
      have := hxv ⟨p, hpl⟩
      rw [← ENat.coe_toNat hvt, Nat.cast_le] at this
      exact this
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using fun h => hpl (mem_places_of_m₀ h))]
  · -- the target is outside
    intro o ho hin
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ho
    rw [Finset.mem_toList] at hv
    have hin' := inIdl_iff.1 hin
    have hx : (fun i : places N m₀ m₁ => (m₁ : Multiset ℕ).count i.1) ∈ idl v := by
      intro i
      by_cases hvi : v i = ⊤
      · rw [hvi]; exact le_top
      · have hni : i.1 ∉ (conv v).1 := fun h' => by
          obtain ⟨_, h''⟩ := mem_conv_fst.1 h'
          exact hvi h''
        have := hin' i.1 hni
        rw [count_conv_snd, dif_pos i.2] at this
        rw [← ENat.coe_toNat hvi, Nat.cast_le]
        exact this
    obtain ⟨m, hr, hm⟩ := hsub v hv hx
    refine h ⟨m, Multiset.le_iff_count.2 fun p => ?_, hr⟩
    by_cases hp : p ∈ places N m₀ m₁
    · exact hm ⟨p, hp⟩
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using fun h => hp (mem_places_of_m₁ h))]
      exact Nat.zero_le _
  · -- inductiveness
    intro o ho t ht hen
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ho
    rw [Finset.mem_toList] at hv
    have hpost := idl_postV_subset (hsub v hv) ht hen
    rw [hD₀] at hpost
    obtain ⟨v', hv', hle⟩ := le_of_idl_subset_biUnion hpost
    refine ⟨conv v', List.mem_map.2 ⟨v', Finset.mem_toList.2 hv', rfl⟩, ?_, ?_⟩
    · intro p hp
      obtain ⟨hpl, hvt⟩ := mem_conv_fst.1 hp
      have := hle ⟨p, hpl⟩
      rw [postV_of_top hvt, top_le_iff] at this
      exact mem_conv_fst.2 ⟨hpl, this⟩
    · intro p hp hp'
      have hpl : p ∈ places N m₀ m₁ := by
        rcases List.mem_append.1 hp with h' | h'
        · exact mem_conv_snd h'
        · exact mem_places_of_post ht h'
      have hv't : v' ⟨p, hpl⟩ ≠ ⊤ := fun h' => hp' (mem_conv_fst.2 ⟨hpl, h'⟩)
      have hvt : v ⟨p, hpl⟩ ≠ ⊤ := by
        intro h'
        have := hle ⟨p, hpl⟩
        rw [postV_of_top h', top_le_iff] at this
        exact hv't this
      have := hle ⟨p, hpl⟩
      rw [postV_of_ne_top hvt, ← ENat.coe_toNat hv't, Nat.cast_le] at this
      simp only [cnt_eq, count_conv_snd, dif_pos hpl]
      exact this

end Complete

/-! ### The check is primitive recursive -/

theorem mem_iff_cnt_pos {p : ℕ} {l : List ℕ} : p ∈ l ↔ 0 < cnt p l := by
  rw [cnt_eq, Multiset.count_pos]; simp

theorem primrecPred_mem :
    PrimrecPred fun w : ℕ × List ℕ => w.1 ∈ w.2 :=
  (PrimrecRel.comp Primrec.nat_lt (Primrec.const 0) primrec_cnt).of_eq fun _ =>
    mem_iff_cnt_pos.symm

theorem primrec_covCert :
    PrimrecPred fun w : (List (Trans ℕ) × List ℕ × List ℕ) × List OM =>
      CovCert w.1.1 w.1.2.1 w.1.2.2 w.2 := by
  -- `InIdl`
  have hIn : PrimrecPred fun w : OM × List ℕ => InIdl w.1 w.2 := by
    refine primrecPred_forall_mem Primrec.snd ?_
    refine (PrimrecPred.or (primrecPred_mem.comp (Primrec.pair Primrec.snd
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) (PrimrecRel.comp Primrec.nat_le
      (primrec_cnt.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (primrec_cnt.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))).of_eq
      fun z => ?_
    simp only [imp_iff_not_or, not_not]
  -- `Enab`
  have hEn : PrimrecPred fun w : Trans ℕ × OM => Enab w.1 w.2 := by
    refine primrecPred_forall_mem (Primrec.fst.comp Primrec.fst) ?_
    refine (PrimrecPred.or (primrecPred_mem.comp (Primrec.pair Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))) (PrimrecRel.comp Primrec.nat_le
      (primrec_cnt.comp Primrec.snd (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (primrec_cnt.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).of_eq
      fun z => ?_
    simp only [imp_iff_not_or, not_not]
  -- `LeStep`
  have hLe : PrimrecPred fun w : (OM × Trans ℕ) × OM => LeStep w.1.1 w.1.2 w.2 := by
    refine PrimrecPred.and ?_ ?_
    · exact primrecPred_forall_mem (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (primrecPred_mem.comp (Primrec.pair Primrec.snd
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
    · refine primrecPred_forall_mem (Primrec.list_append.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) ?_
      have c1 : Primrec fun z : ((OM × Trans ℕ) × OM) × ℕ => cnt z.2 z.1.1.1.2 :=
        primrec_cnt.comp Primrec.snd
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      have c2 : Primrec fun z : ((OM × Trans ℕ) × OM) × ℕ => cnt z.2 z.1.1.2.1 :=
        primrec_cnt.comp Primrec.snd
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      have c3 : Primrec fun z : ((OM × Trans ℕ) × OM) × ℕ => cnt z.2 z.1.1.2.2 :=
        primrec_cnt.comp Primrec.snd
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      have c4 : Primrec fun z : ((OM × Trans ℕ) × OM) × ℕ => cnt z.2 z.1.2.2 :=
        primrec_cnt.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      refine (PrimrecPred.or (primrecPred_mem.comp (Primrec.pair Primrec.snd
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))) (PrimrecRel.comp Primrec.nat_le
        (Primrec.nat_add.comp (Primrec.nat_sub.comp c1 c2) c3) c4)).of_eq fun z => ?_
      simp only [imp_iff_not_or, not_not]
  refine PrimrecPred.and ?_ (PrimrecPred.and ?_ ?_)
  · exact primrecPred_exists_mem Primrec.snd
      (hIn.comp (Primrec.pair Primrec.snd (Primrec.fst.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst)))))
  · exact primrecPred_forall_mem Primrec.snd
      ((hIn.comp (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst)))))).not
  · refine primrecPred_forall_mem Primrec.snd ?_
    refine primrecPred_forall_mem (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) ?_
    refine (PrimrecPred.or (hEn.comp (Primrec.pair Primrec.snd (Primrec.snd.comp
      Primrec.fst))).not (primrecPred_exists_mem (q := fun a o' => LeStep a.1.2 a.2 o')
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (hLe.comp (Primrec.pair (Primrec.pair (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
          Primrec.snd)))).of_eq fun z => ?_
    simp only [imp_iff_not_or]

/-- **Non-coverability is r.e.** -/
theorem cover_compl_re :
    REPred fun x : List (Trans ℕ) × List ℕ × List ℕ =>
      ¬ Cover x.1 (x.2.1 : Multiset ℕ) (x.2.2 : Multiset ℕ) :=
  (rePred_exists (q := fun x D => CovCert x.1 x.2.1 x.2.2 D) primrec_covCert).of_eq fun _ =>
    ⟨fun ⟨_, hD⟩ => not_cover_of_covCert hD, exists_covCert⟩

/-- **Petri net coverability is decidable.** -/
theorem cover_computable :
    ComputablePred fun x : List (Trans ℕ) × List ℕ × List ℕ =>
      Cover x.1 (x.2.1 : Multiset ℕ) (x.2.2 : Multiset ℕ) :=
  ComputablePred.computable_iff_re_compl_re'.2 ⟨cover_re, cover_compl_re⟩

end Petri

end HTN
