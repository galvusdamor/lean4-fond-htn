import HtnComplexity.Computable.RenameA
import HtnComplexity.Computable.CanonNetL
/-!
# Canonical action names for the tasks a domain description does not know

An *action* name a domain description never mentions has empty precondition, add and delete list
(`HTN.Syn.DomDesc.prec` and friends default to the empty list), so a primitive task carrying such
a name is a harmless no-op.  It is harmless, but it is not *canonical*: two such tasks carry two
different numerals, and a description of a bounded initial task network can therefore still
carry an unbounded amount of information in its labels.

This file removes that channel.

* `HTN.Syn.exists_perm_of_lists` — a permutation of `ℕ` fixing a given set pointwise and moving
  one finite list of numbers outside the set onto another;
* `HTN.Syn.DomDesc.fixNames`, `HTN.Syn.DomDesc.freshBase` — the action names a domain
  description must keep (its own, plus the default name `0`), and a numeral above all of them;
* `HTN.Syn.canonActMap d t` — the renaming of action names which keeps the names of `d` and
  sends the other names occurring in `t` to `freshBase d, freshBase d + 1, …` in the order in
  which they occur;
* `HTN.Syn.solvable_canonAct` — **applying it does not change solvability**, and
  `HTN.Syn.lblActNames_renameA_canonActMap_subset` — afterwards every action name of the
  description lies in a list depending only on `d` and on the number of labels.
-/

namespace HTN

namespace Syn

/-! ### A permutation carrying one finite list onto another -/

/-- **A permutation of `ℕ` fixing `X` pointwise and carrying `as` onto `bs`.**  The two lists
have to be repetition-free, of the same length, and disjoint from `X`. -/
theorem exists_perm_of_lists (X : Set ℕ) :
    ∀ (as bs : List ℕ), as.Nodup → bs.Nodup → as.length = bs.length →
      (∀ a ∈ as, a ∉ X) → (∀ b ∈ bs, b ∉ X) →
      ∃ σ : Equiv.Perm ℕ, (∀ x ∈ X, σ x = x) ∧ ∀ p ∈ as.zip bs, σ p.1 = p.2
  | [], [], _, _, _, _, _ => ⟨1, fun _ _ => rfl, by simp⟩
  | [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | a :: as, b :: bs, hna, hnb, hlen, hax, hbx => by
    have hna' : as.Nodup := hna.of_cons
    have hnb' : bs.Nodup := hnb.of_cons
    have hlen' : as.length = bs.length := by simpa using hlen
    obtain ⟨σ₀, hfix, hcorr⟩ := exists_perm_of_lists X as bs hna' hnb' hlen'
      (fun x hx => hax x (List.mem_cons_of_mem _ hx))
      (fun x hx => hbx x (List.mem_cons_of_mem _ hx))
    have hane : a ∉ X := hax a (by simp)
    have hbne : b ∉ X := hbx b (by simp)
    have hσ₀a : σ₀ a ∉ X := by
      intro hc
      have : σ₀ (σ₀ a) = σ₀ a := hfix _ hc
      have ha : σ₀ a = a := σ₀.injective this
      exact hane (ha ▸ hc)
    refine ⟨σ₀.trans (Equiv.swap (σ₀ a) b), ?_, ?_⟩
    · intro x hx
      have hx0 : σ₀ x = x := hfix x hx
      have hxb : x ≠ b := fun hc => hbne (hc ▸ hx)
      have hxa : x ≠ σ₀ a := fun hc => hσ₀a (hc ▸ hx)
      show Equiv.swap (σ₀ a) b (σ₀ x) = x
      rw [hx0, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    · intro p hp
      rw [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · show Equiv.swap (σ₀ a) b (σ₀ a) = b
        exact Equiv.swap_apply_left _ _
      · have hmem := List.of_mem_zip hp
        have h1 : σ₀ p.1 = p.2 := hcorr p hp
        have hp2b : p.2 ≠ b := fun hc => (List.nodup_cons.1 hnb).1 (hc ▸ hmem.2)
        have hp2a : p.2 ≠ σ₀ a := by
          intro hc
          have : σ₀ p.1 = σ₀ a := by rw [h1, hc]
          exact (List.nodup_cons.1 hna).1 (σ₀.injective this ▸ hmem.1)
        show Equiv.swap (σ₀ a) b (σ₀ p.1) = p.2
        rw [h1, Equiv.swap_apply_of_ne_of_ne hp2a hp2b]

/-! ### The action names a domain description must keep -/

namespace DomDesc

/-- The action names a renaming has to fix: the ones the domain description mentions, and the
default name `0` an unlabelled identifier denotes. -/
def fixNames (d : DomDesc) : List ℕ := 0 :: d.allActNames

theorem zero_mem_fixNames (d : DomDesc) : 0 ∈ d.fixNames := by simp [fixNames]

theorem allActNames_subset_fixNames {d : DomDesc} {a : ℕ} (h : a ∈ d.allActNames) :
    a ∈ d.fixNames := List.mem_cons_of_mem _ h

/-- A numeral above every action name the domain description must keep. -/
def freshBase (d : DomDesc) : ℕ := d.fixNames.foldr max 0 + 1

theorem lt_freshBase {d : DomDesc} {x : ℕ} (h : x ∈ d.fixNames) : x < d.freshBase := by
  have key : ∀ l : List ℕ, ∀ y ∈ l, y ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => simp
    | cons z l ih =>
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_max_left _ _
      · exact le_trans (ih y hy) (le_max_right _ _)
  have := key d.fixNames x h
  show x < d.fixNames.foldr max 0 + 1
  omega

theorem notMem_fixNames_add_freshBase (d : DomDesc) (i : ℕ) : d.freshBase + i ∉ d.fixNames := by
  intro hc
  have := lt_freshBase hc
  omega

end DomDesc

/-! ### The canonical renaming -/

namespace TnDesc

/-- The action names of a described network the domain description does not know, listed once
each. -/
def unkActs (d : DomDesc) (t : TnDesc) : List ℕ :=
  (t.lblActNames.filter fun a => !memB d.fixNames a).dedup

theorem nodup_unkActs (d : DomDesc) (t : TnDesc) : (unkActs d t).Nodup := List.nodup_dedup _

theorem mem_unkActs {d : DomDesc} {t : TnDesc} {a : ℕ} :
    a ∈ unkActs d t ↔ a ∈ t.lblActNames ∧ a ∉ d.fixNames := by
  rw [unkActs, List.mem_dedup, List.mem_filter]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h hc
    rw [memB_iff.2 hc] at h
    simp at h
  · intro h
    have hb : memB d.fixNames a = false := by
      rcases hb : memB d.fixNames a with _ | _
      · rfl
      · exact absurd (memB_iff.1 hb) h
    simp [hb]

theorem length_unkActs_le (d : DomDesc) (t : TnDesc) : (unkActs d t).length ≤ t.lbl.length := by
  calc (unkActs d t).length ≤ (t.lblActNames.filter fun a => !memB d.fixNames a).length :=
        (List.dedup_sublist _).length_le
    _ ≤ t.lblActNames.length := List.filter_sublist.length_le
    _ ≤ t.lbl.length := List.length_filterMap_le _ _

end TnDesc

/-- **The canonical renaming of action names for the description `t` at the domain description
`d`**: the names of `d` (and the default `0`) are kept, every other name occurring in `t` is sent
to `freshBase d` plus its position among them. -/
def canonActMap (d : DomDesc) (t : TnDesc) (a : ℕ) : ℕ :=
  if memB d.fixNames a then a else d.freshBase + (TnDesc.unkActs d t).idxOf a

theorem canonActMap_of_mem_fixNames {d : DomDesc} {t : TnDesc} {a : ℕ} (h : a ∈ d.fixNames) :
    canonActMap d t a = a := by simp [canonActMap, memB_iff.2 h]

theorem canonActMap_of_notMem {d : DomDesc} {t : TnDesc} {a : ℕ} (h : a ∉ d.fixNames) :
    canonActMap d t a = d.freshBase + (TnDesc.unkActs d t).idxOf a := by
  have : memB d.fixNames a = false := by
    rcases hb : memB d.fixNames a with _ | _
    · rfl
    · exact absurd (memB_iff.1 hb) h
  simp [canonActMap, this]

/-- Two renamings that agree on the action names a description lists give the same result. -/
theorem renameA_congr {σ τ : ℕ → ℕ} {t : TnDesc} (h : ∀ a ∈ t.lblActNames, σ a = τ a) :
    t.renameA σ = t.renameA τ := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  show t.lbl.map (fun l => (l.1, l.2.1, if l.2.1 then l.2.2 else σ l.2.2)) =
    t.lbl.map fun l => (l.1, l.2.1, if l.2.1 then l.2.2 else τ l.2.2)
  refine List.map_congr_left fun l hl => ?_
  rcases hb : l.2.1 with _ | _
  · have := h l.2.2 (TnDesc.mem_lblActNames.2 ⟨l, hl, hb, rfl⟩)
    simp [this]
  · simp

/-- **Canonicalising the unknown action names does not change solvability.** -/
theorem solvable_canonAct (d : DomDesc) (I G : List ℕ) (t : TnDesc) :
    Solvable d (I, G, t.renameA (canonActMap d t)) ↔ Solvable d (I, G, t) := by
  set as : List ℕ := TnDesc.unkActs d t with has
  set bs : List ℕ := (List.range as.length).map fun i => d.freshBase + i with hbs
  have hlen : as.length = bs.length := by simp [hbs]
  have hna : as.Nodup := TnDesc.nodup_unkActs d t
  have hnb : bs.Nodup := by
    refine List.Nodup.map ?_ List.nodup_range
    intro x y hxy
    exact Nat.add_left_cancel hxy
  have hax : ∀ a ∈ as, a ∉ ({x | x ∈ d.fixNames} : Set ℕ) := by
    intro a ha
    exact (TnDesc.mem_unkActs.1 ha).2
  have hbx : ∀ b ∈ bs, b ∉ ({x | x ∈ d.fixNames} : Set ℕ) := by
    intro b hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    exact DomDesc.notMem_fixNames_add_freshBase d i
  obtain ⟨σ, hfix, hcorr⟩ :=
    exists_perm_of_lists {x | x ∈ d.fixNames} as bs hna hnb hlen hax hbx
  have hzip : ∀ i (h : i < as.length), σ as[i] = d.freshBase + i := by
    intro i hi
    have hib : i < bs.length := by omega
    have hmem : (as[i], bs[i]) ∈ as.zip bs := by
      have hlt : i < (as.zip bs).length := by
        rw [List.length_zip]; omega
      have : (as.zip bs)[i] = (as[i], bs[i]) := by simp
      exact this ▸ List.getElem_mem hlt
    have := hcorr _ hmem
    have hbsi : bs[i] = d.freshBase + i := by
      simp [hbs]
    simpa [hbsi] using this
  have hagree : ∀ a ∈ t.lblActNames, σ a = canonActMap d t a := by
    intro a ha
    by_cases hfx : a ∈ d.fixNames
    · rw [hfix a hfx, canonActMap_of_mem_fixNames hfx]
    · have hmem : a ∈ as := TnDesc.mem_unkActs.2 ⟨ha, hfx⟩
      have hi : as.idxOf a < as.length := List.idxOf_lt_length_iff.2 hmem
      have hget : as[as.idxOf a] = a := List.getElem_idxOf hi
      rw [canonActMap_of_notMem hfx, ← hget, hzip _ hi, hget]
  have heq : t.renameA σ = t.renameA (canonActMap d t) := renameA_congr hagree
  have hσ0 : σ 0 = 0 := hfix 0 (DomDesc.zero_mem_fixNames d)
  have hdfix : ∀ a ∈ d.allActNames, σ a = a := fun a ha =>
    hfix a (DomDesc.allActNames_subset_fixNames ha)
  have := solvable_renameA_congr (σ := σ) σ.injective hσ0 hdfix ((I, G, t) : InstDesc)
  rw [show InstDesc.renameA σ ((I, G, t) : InstDesc) = ((I, G, t.renameA σ) : InstDesc) from rfl]
    at this
  rw [← heq]
  exact this

/-- After the canonical renaming every action name of the description is a name of `d` or one of
the first `t.lbl.length` fresh numerals. -/
theorem mem_lblActNames_canonAct {d : DomDesc} {t : TnDesc} {a : ℕ}
    (ha : a ∈ (t.renameA (canonActMap d t)).lblActNames) :
    a ∈ d.fixNames ∨ ∃ i < t.lbl.length, a = d.freshBase + i := by
  obtain ⟨l, hl, hb, rfl⟩ := TnDesc.mem_lblActNames.1 ha
  rw [TnDesc.renameA_lbl, List.mem_map] at hl
  obtain ⟨l0, hl0, rfl⟩ := hl
  simp only at hb ⊢
  rcases hb0 : l0.2.1 with _ | _
  · have hmem : l0.2.2 ∈ t.lblActNames := TnDesc.mem_lblActNames.2 ⟨l0, hl0, hb0, rfl⟩
    by_cases hfx : l0.2.2 ∈ d.fixNames
    · left
      simpa [hb0, canonActMap_of_mem_fixNames hfx] using hfx
    · right
      have hmemu : l0.2.2 ∈ TnDesc.unkActs d t := TnDesc.mem_unkActs.2 ⟨hmem, hfx⟩
      have hi : (TnDesc.unkActs d t).idxOf l0.2.2 < (TnDesc.unkActs d t).length :=
        List.idxOf_lt_length_iff.2 hmemu
      refine ⟨(TnDesc.unkActs d t).idxOf l0.2.2,
        lt_of_lt_of_le hi (TnDesc.length_unkActs_le d t), ?_⟩
      simp [canonActMap_of_notMem hfx]
  · rw [hb0] at hb
    simp at hb

end Syn

end HTN
