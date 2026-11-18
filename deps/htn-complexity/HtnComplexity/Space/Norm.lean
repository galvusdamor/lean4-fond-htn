import HtnComplexity.Space.Canon
import HtnComplexity.Space.Rename
/-!
# Normalising the facts of an action table against a bound

The advice of the target-side machine must be polynomially long in the **number of symbols** of
the action table and in the bound `L` on the facts of the input (see
`HtnComplexity/Space/TblSolver.lean`).  A table of few symbols may mention facts of
astronomical magnitude, whose numerals no such advice could carry — but those facts are facts no
admissible input mentions, so they may be renamed to short fresh names.

`HTN.Space.tblNorm L tbl` is that renaming: it fixes every fact below `2 ^ L` and sends the facts
of the table that are not below `2 ^ L` to the pairwise distinct values `2 ^ L + i`.  It is
injective on the facts that matter as soon as the initial state and the goal are made of facts
below `2 ^ L` (`HTN.Space.injOnRel_tblNorm`), so solvability is unaffected
(`HTN.Space.solvableTbl_tblNorm`), and every fact of the normalised table is below
`2 ^ (L + tblSize tbl)` (`HTN.Space.tblNorm_lt`), hence has a numeral of at most `L + tblSize tbl`
bits.
-/

namespace HTN

namespace Space

open Syn PTime

/-- The facts of the table that are too large for the bound. -/
def bigFacts (L : ℕ) (tbl : List Row) : List ℕ :=
  ((tblFacts tbl).filter fun f => decide (2 ^ L ≤ f)).dedup

theorem mem_bigFacts {L : ℕ} {tbl : List Row} {f : ℕ} :
    f ∈ bigFacts L tbl ↔ f ∈ tblFacts tbl ∧ 2 ^ L ≤ f := by
  simp [bigFacts, List.mem_filter]

theorem length_tblFacts_le (tbl : List Row) : (tblFacts tbl).length ≤ tblSize tbl := by
  rw [tblFacts, List.length_flatMap, tblSize]
  have : (tbl.map fun r => (r.1 ++ r.2.1 ++ r.2.2).length)
      = tbl.map fun r => r.1.length + r.2.1.length + r.2.2.length := by
    refine List.map_congr_left fun r _ => ?_
    simp only [List.length_append]
  rw [this]
  omega

theorem length_bigFacts_le (L : ℕ) (tbl : List Row) : (bigFacts L tbl).length ≤ tblSize tbl := by
  refine le_trans ?_ (length_tblFacts_le tbl)
  refine le_trans (List.Sublist.length_le (List.dedup_sublist _)) ?_
  exact List.filter_sublist.length_le

/-- **The normalisation**: facts below `2 ^ L` are fixed, the remaining facts of the table are
sent to pairwise distinct values just above `2 ^ L`. -/
def tblNorm (L : ℕ) (tbl : List Row) (f : ℕ) : ℕ :=
  if f < 2 ^ L then f else 2 ^ L + (bigFacts L tbl).idxOf f

@[simp] theorem tblNorm_of_lt {L : ℕ} {tbl : List Row} {f : ℕ} (h : f < 2 ^ L) :
    tblNorm L tbl f = f := if_pos h

theorem tblNorm_of_le {L : ℕ} {tbl : List Row} {f : ℕ} (h : 2 ^ L ≤ f) :
    tblNorm L tbl f = 2 ^ L + (bigFacts L tbl).idxOf f := if_neg (by omega)

theorem map_tblNorm_eq_self {L : ℕ} {tbl : List Row} {s : List ℕ} (hs : ∀ f ∈ s, f < 2 ^ L) :
    s.map (tblNorm L tbl) = s := by
  exact (List.map_congr_left fun f hf => tblNorm_of_lt (hs f hf)).trans (List.map_id s)

/-- **The normalisation is injective where it matters.** -/
theorem injOnRel_tblNorm {L : ℕ} {tbl : List Row} {s g : List ℕ} (hs : ∀ f ∈ s, f < 2 ^ L)
    (hg : ∀ f ∈ g, f < 2 ^ L) : InjOnRel (tblNorm L tbl) tbl s g := by
  have hbig : ∀ a ∈ relFacts tbl s g, 2 ^ L ≤ a → a ∈ bigFacts L tbl := by
    intro a ha hle
    refine mem_bigFacts.2 ⟨?_, hle⟩
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact ha
      · exact absurd (hs a ha) (by omega)
    · exact absurd (hg a ha) (by omega)
  intro a ha b hb hab
  rcases lt_or_ge a (2 ^ L) with hA | hA <;> rcases lt_or_ge b (2 ^ L) with hB | hB
  · rwa [tblNorm_of_lt hA, tblNorm_of_lt hB] at hab
  · rw [tblNorm_of_lt hA, tblNorm_of_le hB] at hab
    omega
  · rw [tblNorm_of_le hA, tblNorm_of_lt hB] at hab
    omega
  · rw [tblNorm_of_le hA, tblNorm_of_le hB] at hab
    exact (List.idxOf_inj (hbig a ha hA)).1 (by omega)

/-- **Solvability is unaffected by the normalisation.** -/
theorem solvableTbl_tblNorm {L : ℕ} {tbl : List Row} {s g : List ℕ} (hs : ∀ f ∈ s, f < 2 ^ L)
    (hg : ∀ f ∈ g, f < 2 ^ L) :
    SolvableTbl (tbl.map (mapRow (tblNorm L tbl))) s g ↔ SolvableTbl tbl s g := by
  have h := solvableTbl_map (ρ := tblNorm L tbl) (tbl := tbl) (s₀ := s) (g := g)
    (injOnRel_tblNorm hs hg)
  rwa [map_tblNorm_eq_self hs, map_tblNorm_eq_self hg] at h

/-- **Every fact of the normalised table is small.** -/
theorem tblNorm_lt {L : ℕ} {tbl : List Row} {f : ℕ} (hf : f ∈ tblFacts tbl) :
    tblNorm L tbl f < 2 ^ (L + tblSize tbl) := by
  have hpow : (2 : ℕ) ^ (L + tblSize tbl) = 2 ^ L * 2 ^ tblSize tbl := pow_add 2 L _
  have hT : tblSize tbl + 1 ≤ 2 ^ tblSize tbl := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have hL : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_two_pow
  rcases lt_or_ge f (2 ^ L) with h | h
  · rw [tblNorm_of_lt h]
    calc f < 2 ^ L := h
      _ ≤ 2 ^ L * 2 ^ tblSize tbl := Nat.le_mul_of_pos_right _ (by positivity)
      _ = 2 ^ (L + tblSize tbl) := hpow.symm
  · rw [tblNorm_of_le h, hpow]
    have hidx : (bigFacts L tbl).idxOf f < (bigFacts L tbl).length :=
      List.idxOf_lt_length_of_mem (mem_bigFacts.2 ⟨hf, h⟩)
    have hlen := length_bigFacts_le L tbl
    have : 2 ^ L * (tblSize tbl + 1) ≤ 2 ^ L * 2 ^ tblSize tbl :=
      Nat.mul_le_mul_left _ hT
    nlinarith

theorem mem_tblFacts_of_mem_map {ρ : ℕ → ℕ} {tbl : List Row} {f : ℕ}
    (hf : f ∈ tblFacts (tbl.map (mapRow ρ))) : ∃ a ∈ tblFacts tbl, ρ a = f := by
  obtain ⟨r', hr', hfr⟩ := List.mem_flatMap.1 hf
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
  rw [mapRow] at hfr
  simp only [List.mem_append, List.mem_map] at hfr
  rcases hfr with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
  · exact ⟨a, mem_tblFacts_of_prec hr ha, rfl⟩
  · exact ⟨a, mem_tblFacts_of_add hr ha, rfl⟩
  · exact ⟨a, mem_tblFacts_of_del hr ha, rfl⟩

end Space

end HTN
