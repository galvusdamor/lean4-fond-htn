import HtnComplexity.Space.AltPlanner
import HtnComplexity.Space.SeqSpace
/-!
# Tables with calls: no-op prefixes, renaming, and advice lengths

Auxiliary facts for the alternating planner for totally ordered HTN with an initial task network
(`HtnComplexity/Space/AltSeqPlanner.lean`):

* `HTN.Space.aSolvable_noop_append` — rows with empty add and delete lists put in front of a table
  with calls change nothing (the marker rows of `HTN.Space.SeqM.markRows` and padding rows are of
  this kind);
* `HTN.Space.aSolvable_tblNorm` — the renaming `tblNorm L` of a table with calls preserves
  solvability when the initial state, the goal and the two markers are below `2 ^ L`;
* length bounds on the advice `tblAdv` in terms of its two parts.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### No-op prefixes -/

/-- A row with empty add and delete lists. -/
def NoopRow (r : Row) : Prop := r.2.1 = [] ∧ r.2.2 = []

theorem rowOf_append_right (M T : List Row) (i : ℕ) :
    rowOf (M ++ T) (M.length + i) = rowOf T i := by
  simp [rowOf, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem rowOf_append_left {M T : List Row} {i : ℕ} (hi : i < M.length) :
    rowOf (M ++ T) i = rowOf M i := by
  simp [rowOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem noop_rowOf {M T : List Row} (hM : ∀ r ∈ M, NoopRow r) {i : ℕ} (hi : i < M.length) :
    NoopRow (rowOf (M ++ T) i) := by
  rw [rowOf_append_left hi]
  exact hM _ (rowOf_mem hi)

theorem rowApp_noop {r : Row} (h : NoopRow r) (s : Set ℕ) : rowApp r s = s := by
  ext f
  simp [rowApp, h.1, h.2]

/-- **A prefix of no-op rows changes nothing.** -/
theorem aReach_noop_append {kp kr : ℕ} {M T : List Row} (hM : ∀ r ∈ M, NoopRow r)
    {s s' : Set ℕ} : AReach kp kr (M ++ T) s s' ↔ AReach kp kr T s s' := by
  constructor
  · intro h
    induction h with
    | refl s => exact AReach.refl s
    | @plain i s s' hi hp hr hok _ ih =>
      by_cases hiM : i < M.length
      · rwa [rowApp_noop (noop_rowOf hM hiM)] at ih
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hiM)
        rw [rowOf_append_right] at hp hr hok ih
        simp only [List.length_append] at hi
        exact AReach.plain (by omega) hp hr hok ih
    | @call i s t s' hi hp hok1 _ hok2 _ ih1 ih2 =>
      by_cases hiM : i < M.length
      · have := (noop_rowOf (T := T) hM hiM).2
        rw [this] at hp
        simp at hp
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hiM)
        rw [Nat.add_assoc, rowOf_append_right] at hok2 ih2
        rw [rowOf_append_right] at hp hok1 ih1
        simp only [List.length_append] at hi
        exact AReach.call (by omega) hp hok1 ih1 hok2 ih2
  · intro h
    induction h with
    | refl s => exact AReach.refl s
    | @plain j s s' hj hp hr hok _ ih =>
      rw [← rowOf_append_right M] at hp hr hok ih
      exact AReach.plain (by simp; omega) hp hr hok ih
    | @call j s t s' hj hp hok1 _ hok2 _ ih1 ih2 =>
      rw [← rowOf_append_right M] at hp hok1 ih1 hok2 ih2
      rw [← Nat.add_assoc] at hok2 ih2
      exact AReach.call (by simp; omega) hp hok1 ih1 hok2 ih2

theorem aSolvable_noop_append {kp kr : ℕ} {M T : List Row} (hM : ∀ r ∈ M, NoopRow r)
    {s₀ g : Set ℕ} : ASolvable kp kr (M ++ T) s₀ g ↔ ASolvable kp kr T s₀ g := by
  unfold ASolvable
  exact exists_congr fun s => and_congr_left' (aReach_noop_append hM)

theorem noop_markRows (d : DomDesc) (K : ℕ) : ∀ r ∈ SeqM.markRows d K, NoopRow r := by
  intro r hr
  simp only [SeqM.markRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- A padding of `P` empty rows. -/
def padRows (P : ℕ) : List Row := List.replicate P ([], [], [])

theorem noop_padRows (P : ℕ) : ∀ r ∈ padRows P, NoopRow r := by
  intro r hr
  rw [padRows, List.mem_replicate] at hr
  rw [hr.2]
  exact ⟨rfl, rfl⟩

@[simp] theorem length_padRows (P : ℕ) : (padRows P).length = P := by simp [padRows]

theorem tblSize_padRows (P : ℕ) : tblSize (padRows P) = P := by
  simp [tblSize, padRows]

theorem tblFacts_padRows_append (P : ℕ) (T : List Row) :
    tblFacts (padRows P ++ T) = tblFacts T := by
  simp [tblFacts, padRows, List.flatMap_append]

/-! ### Renaming -/

/-- **The renaming `tblNorm L` preserves solvability of a table with calls** when the initial
state, the goal and the two markers are below `2 ^ L`. -/
theorem aSolvable_tblNorm {L kp kr : ℕ} {T : List Row} {s₀ g : List ℕ}
    (hs : ∀ f ∈ s₀, f < 2 ^ L) (hg : ∀ f ∈ g, f < 2 ^ L) (hkp : kp < 2 ^ L) (hkr : kr < 2 ^ L) :
    ASolvable kp kr (T.map (mapRow (tblNorm L T))) {f | f ∈ s₀} {f | f ∈ g} ↔
      ASolvable kp kr T {f | f ∈ s₀} {f | f ∈ g} := by
  set ρ := tblNorm L T with hρ
  have hs' : ∀ f ∈ s₀ ++ [kp, kr], f < 2 ^ L := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · exact hs f hf
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> assumption
  have hinj := injOnRel_tblNorm (tbl := T) hs' hg
  set X : Set ℕ := {f | f ∈ relFacts T (s₀ ++ [kp, kr]) g} with hX
  have hXt : ∀ f ∈ tblFacts T, f ∈ X := fun f hf => by
    simp only [hX, Set.mem_setOf_eq, relFacts, List.mem_append]
    exact Or.inl (Or.inl hf)
  have hkp' : kp ∈ X := by simp [hX, relFacts]
  have hkr' : kr ∈ X := by simp [hX, relFacts]
  have hs₀ : {f | f ∈ s₀} ⊆ X := fun f hf => by
    simp only [hX, Set.mem_setOf_eq, relFacts, List.mem_append] at hf ⊢
    exact Or.inl (Or.inr (Or.inl hf))
  have hgX : {f | f ∈ g} ⊆ X := fun f hf => by
    simp only [hX, Set.mem_setOf_eq, relFacts, List.mem_append] at hf ⊢
    exact Or.inr hf
  have key := aSolvable_map_iff (ρ := ρ) (X := X) (kp := kp) (kr := kr) (tbl := T)
    (fun a ha b hb hab => hinj a ha b hb hab) hXt hkp' hkr' hs₀ hgX
  have hfix : ∀ f, f < 2 ^ L → ρ f = f := fun f hf => tblNorm_of_lt hf
  have eimg : ∀ l : List ℕ, (∀ f ∈ l, f < 2 ^ L) → ρ '' {f | f ∈ l} = {f | f ∈ l} := by
    intro l hl
    ext f
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hfix a (hl a ha)]
      exact ha
    · intro hf
      exact ⟨f, hf, hfix f (hl f hf)⟩
  rw [hfix _ hkp, hfix _ hkr, eimg _ hs, eimg _ hg] at key
  exact key

/-! ### Lengths in the advice -/

theorem length_addFacts_le_factEnts (tbl : List Row) :
    (addFacts tbl).length ≤ (blist (factEnts tbl)).length := by
  have h1 : (addFacts tbl).length ≤ (factEnts tbl).length := by
    have hA : (addFacts tbl).length
        = ((List.range tbl.length).map fun i => (rowOf tbl i).2.1.length).sum := by
      rw [addFacts, List.length_flatMap]
      conv_lhs => rw [← map_rowOf_range tbl]
      rw [List.map_map]
      rfl
    have hF : (factEnts tbl).length
        = ((List.range tbl.length).map fun i =>
            (rowOf tbl i).1.length + (rowOf tbl i).2.1.length + (rowOf tbl i).2.2.length).sum := by
      rw [factEnts, List.length_flatMap]
      congr 1
      exact List.map_congr_left fun i _ => length_rowEnts _ _
    rw [hA, hF]
    refine List.sum_le_sum ?_
    intro i _
    omega
  exact h1.trans (length_le_length_blist _)

theorem length_bitsOfNat_le_factEnts {tbl : List Row} {f : ℕ} (hf : f ∈ addFacts tbl) :
    (bitsOfNat f).length ≤ (blist (factEnts tbl)).length := by
  obtain ⟨r, hr, hfr⟩ := List.mem_flatMap.1 hf
  obtain ⟨i, hi, rfl⟩ := exists_rowOf hr
  have hmem : factEnt i tagAdd f ∈ factEnts tbl := (mem_factEnts_add hi).2 hfr
  have h1 := le_length_blist_of_mem hmem
  have h2 : (bitsOfNat f).length ≤ (factEnt i tagAdd f).length := by
    simp only [factEnt, List.length_append, length_rowId]
    omega
  omega

theorem length_bitsOfNat_cRoot_le_factEnts (d : DomDesc) (K : ℕ) (T : List Row) :
    (bitsOfNat (SeqM.cRoot d)).length ≤ (blist (factEnts (SeqM.markRows d K ++ T))).length := by
  have hmem : factEnt 0 tagPrec (SeqM.cRoot d) ∈ factEnts (SeqM.markRows d K ++ T) := by
    rw [mem_factEnts_prec (by simp [SeqM.markRows])]
    simp [rowOf, SeqM.markRows]
  have h1 := le_length_blist_of_mem hmem
  have h2 : (bitsOfNat (SeqM.cRoot d)).length ≤ (factEnt 0 tagPrec (SeqM.cRoot d)).length := by
    simp only [factEnt, List.length_append, length_rowId]
    omega
  omega

theorem length_tblAdv_split (b : Bool) (tbl : List Row) :
    (tblAdv b tbl).length = (blist (idEnts tbl)).length + (blist (factEnts tbl)).length + 1 := by
  simp [tblAdv]; omega

theorem length_le_idEnts (tbl : List Row) : tbl.length ≤ (blist (idEnts tbl)).length := by
  have := length_le_length_blist (idEnts tbl)
  rwa [length_idEnts] at this

end Space

end HTN
