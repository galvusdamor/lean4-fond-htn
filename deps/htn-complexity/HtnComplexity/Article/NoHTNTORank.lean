import HtnComplexity.Article.NoHTNNP
import HtnComplexity.Logspace.Parse
/-!
# Totally ordered non-hierarchical problems: the plan is determined by ranks

For a non-hierarchical problem whose initial task network is totally ordered, the only
linearisation lists the tasks by their **rank**, the number of tasks ordered before them
(`HTN.Article.NoHTNTO.linOf`).  Ranks are counted, so the plan can be followed without storing
it (Thm. 4.2.10).

* `HTN.Article.NoHTNTO.linB_iff_eq_linOf` — the linearisation is unique and is `linOf`;
* **`HTN.Article.NoHTNTO.solvable_iff_execB`** — solvability is the execution check of that
  plan.
-/

namespace HTN

namespace Article

namespace NoHTNTO

open Syn Syn.PolyDom NoHTN Logspace

/-! ### Ranks -/

/-- The number of `j < n` with `P j`. -/
def cnt (n : ℕ) (P : ℕ → Bool) : ℕ := ((List.range n).filter P).length

/-- The rank of a task id: the number of ids ordered before it. -/
def rank (t : TnDesc) (x : ℕ) : ℕ := cnt t.ids.length fun j => decide ((t.ids.getD j 0, x) ∈ t.ordList)

/-- The index (into the ids) of the task of rank `k`. -/
def stepIdx (t : TnDesc) (k : ℕ) : ℕ := firstIdx (fun i => rank t (t.ids.getD i 0) == k) t.ids.length

/-- The task of rank `k`. -/
def stepId (t : TnDesc) (k : ℕ) : ℕ := t.ids.getD (stepIdx t k) 0

/-- **The tasks listed by rank.** -/
def linOf (t : TnDesc) : List ℕ := (List.range t.ids.length).map (stepId t)

theorem cnt_getD (l : List ℕ) (P : ℕ → Bool) :
    cnt l.length (fun j => P (l.getD j 0)) = (l.filter P).length := by
  have hl : (List.range l.length).map (fun j => l.getD j 0) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  unfold cnt
  conv_rhs => rw [← hl]
  rw [List.filter_map, List.length_map]
  rfl

/-- The rank as the number of predecessors. -/
theorem rank_eq_card (t : TnDesc) (hnd : t.ids.Nodup) (x : ℕ) :
    rank t x = (t.ids.toFinset.filter fun y => (y, x) ∈ t.ordList).card := by
  rw [rank, cnt_getD t.ids (fun y => decide ((y, x) ∈ t.ordList)),
    ← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1; ext y; simp

section Total

variable {prim : ℕ → Prop} {t : TnDesc} (hv : TnValid prim t)
  (hto : ∀ a ∈ t.ids, ∀ b ∈ t.ids, a ≠ b → (a, b) ∈ t.ordList ∨ (b, a) ∈ t.ordList)

include hv in
theorem rank_lt_rank {a b : ℕ} (hab : (a, b) ∈ t.ordList) : rank t a < rank t b := by
  rw [rank_eq_card t hv.nodup, rank_eq_card t hv.nodup]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_filter, List.mem_toFinset]; exact ⟨(hv.ord_mem _ hab).1, hab⟩
    · simp only [Finset.mem_filter, not_and]; exact fun _ h => hv.irrefl a h
  · intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hv.trans _ _ _ hy.2 hab⟩

include hv in
theorem rank_lt_length {x : ℕ} (hx : x ∈ t.ids) : rank t x < t.ids.length := by
  rw [rank_eq_card t hv.nodup, ← List.toFinset_card_of_nodup hv.nodup]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨x, List.mem_toFinset.2 hx, by simp only [Finset.mem_filter, not_and]; exact fun _ h => hv.irrefl x h⟩

include hv hto in
theorem rank_inj {a b : ℕ} (ha : a ∈ t.ids) (hb : b ∈ t.ids) (h : rank t a = rank t b) : a = b := by
  by_contra hne
  rcases hto a ha b hb hne with h' | h'
  · have := rank_lt_rank hv h'; omega
  · have := rank_lt_rank hv h'; omega

include hv hto in
theorem exists_rank {k : ℕ} (hk : k < t.ids.length) : ∃ x ∈ t.ids, rank t x = k := by
  have himg : t.ids.toFinset.image (rank t) = Finset.range t.ids.length := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      simp only [Finset.mem_image, List.mem_toFinset] at hr
      obtain ⟨x, hx, rfl⟩ := hr
      exact Finset.mem_range.2 (rank_lt_length hv hx)
    · rw [Finset.card_image_of_injOn (fun a ha b hb h => rank_inj hv hto (List.mem_toFinset.1 ha)
        (List.mem_toFinset.1 hb) h), List.toFinset_card_of_nodup hv.nodup, Finset.card_range]
  have : k ∈ t.ids.toFinset.image (rank t) := by rw [himg]; exact Finset.mem_range.2 hk
  simp only [Finset.mem_image, List.mem_toFinset] at this
  exact this

include hv hto in
theorem stepId_spec {k : ℕ} (hk : k < t.ids.length) :
    stepIdx t k < t.ids.length ∧ stepId t k ∈ t.ids ∧ rank t (stepId t k) = k := by
  obtain ⟨x, hx, hr⟩ := exists_rank hv hto hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hlt : stepIdx t k < t.ids.length := by
    have hle := firstIdx_le (fun i => rank t (t.ids.getD i 0) == k) t.ids.length
    obtain ⟨h1, -⟩ := firstIdx_spec (fun i => rank t (t.ids.getD i 0) == k) t.ids.length
    by_contra hge
    have := h1 i (by unfold stepIdx at hge; omega)
    rw [List.getD_eq_getElem _ _ hi, hr] at this; simp at this
  have hsp := (firstIdx_spec (fun i => rank t (t.ids.getD i 0) == k) t.ids.length).2 hlt
  refine ⟨hlt, ?_, ?_⟩
  · unfold stepId; rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem _
  · simpa [stepId] using hsp

include hv hto in
theorem stepId_eq {k : ℕ} (hk : k < t.ids.length) {x : ℕ} (hx : x ∈ t.ids) (hr : rank t x = k) :
    stepId t k = x := by
  obtain ⟨-, h1, h2⟩ := stepId_spec hv hto hk
  exact rank_inj hv hto h1 hx (by rw [h2, hr])

theorem linB_iff' (t : TnDesc) (l : List ℕ) : linB t l = true ↔ l.Nodup ∧ l.Perm t.ids ∧
    ∀ i (hi : i < l.length) j (hj : j < l.length), i < j → (l[j], l[i]) ∉ t.ordList := by
  simp only [linB, Bool.and_eq_true, nodupB_iff, permB_iff, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  rw [and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h i hi j hj hij => ?_, fun h i hi j hj => ?_⟩)
  · rcases h i hi j hj with h' | h'
    · omega
    · rwa [List.getI_eq_getElem _ hj, List.getI_eq_getElem _ hi] at h'
  · by_cases hij : i < j
    · right; rw [List.getI_eq_getElem _ hj, List.getI_eq_getElem _ hi]; exact h i hi j hj hij
    · left; omega

include hv hto in
/-- **The plan by ranks is a linearisation.** -/
theorem linB_linOf : linB t (linOf t) = true := by
  rw [linB_iff']
  have hlen : (linOf t).length = t.ids.length := by simp [linOf]
  have hget : ∀ k (hk : k < (linOf t).length), (linOf t)[k] = stepId t k := by
    intro k hk; simp [linOf]
  have hnd : (linOf t).Nodup := by
    rw [List.nodup_iff_injective_get]
    intro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [List.get_eq_getElem, hget] at h
    have hi' := stepId_spec hv hto (k := i) (by omega)
    have hj' := stepId_spec hv hto (k := j) (by omega)
    have : i = j := by rw [← hi'.2.2, ← hj'.2.2, h]
    exact Fin.ext this
  refine ⟨hnd, ?_, ?_⟩
  · apply (List.Nodup.subperm hnd fun x hx => ?_).perm_of_length_le (by omega)
    simp only [linOf, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact (stepId_spec hv hto hk).2.1
  · intro i hi j hj hij hc
    rw [hget, hget] at hc
    have := rank_lt_rank hv hc
    rw [(stepId_spec hv hto (k := i) (by omega)).2.2, (stepId_spec hv hto (k := j) (by omega)).2.2] at this
    omega

include hv hto in
/-- **The linearisation is unique.** -/
theorem eq_linOf {l : List ℕ} (hl : linB t l = true) : l = linOf t := by
  obtain ⟨hnd, hp, hord⟩ := (linB_iff' t l).1 hl
  have hlen : l.length = t.ids.length := hp.length_eq
  apply List.ext_getElem (by simp [linOf, hlen])
  intro k hk _
  simp only [linOf, List.getElem_map, List.getElem_range]
  have hmem : l[k] ∈ t.ids := hp.subset (List.getElem_mem _)
  refine (stepId_eq hv hto (by omega) hmem ?_).symm
  rw [rank_eq_card t hv.nodup]
  have : (t.ids.toFinset.filter fun y => (y, l[k]) ∈ t.ordList) = (l.take k).toFinset := by
    ext y
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨hy, hyo⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hp.symm.subset hy)
      rcases lt_trichotomy i k with h | h | h
      · exact List.mem_iff_getElem.2 ⟨i, by simp; omega, by simp⟩
      · subst h; exact absurd hyo (hv.irrefl _)
      · exact absurd hyo (hord k hk i hi h)
    · intro hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      simp only [List.length_take] at hi
      have hik : i < k := by omega
      rw [List.getElem_take]
      refine ⟨hp.subset (List.getElem_mem _), ?_⟩
      have hne : l[i] ≠ l[k] := fun h => by
        have := (List.Nodup.getElem_inj_iff hnd).1 h; omega
      rcases hto _ (hp.subset (List.getElem_mem _)) _ hmem hne with h | h
      · exact h
      · exact absurd h (hord i (by omega) k hk hik)
  rw [this, List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist _ _))]
  simp; omega

end Total

/-! ### Solvability -/

/-- The initial task network is totally ordered, on the listed pairs. -/
def TOL (t : TnDesc) : Prop := ∀ a ∈ t.ids, ∀ b ∈ t.ids, a ≠ b → (a, b) ∈ t.ordList ∨ (b, a) ∈ t.ordList

theorem isTO_tnI_iff {p : ProbDesc} (hv : p.Valid) : p.toProblem.IsTO_tnI ↔ TOL p.tnI := by
  show (∀ a ∈ p.tnI.ids.toFinset, ∀ b ∈ p.tnI.ids.toFinset, a ≠ b → p.tnI.ordOf a b ∨ p.tnI.ordOf b a) ↔ _
  simp only [List.mem_toFinset, hv.tnI.ordOf_iff, TOL]

theorem reachableName_empty {p : ProbDesc} (hn : p.toProblem.IsNoHTN) (c : ℕ) :
    ¬ p.toProblem.toPos.ReachableName c := by
  intro h
  induction h with
  | tnI ht hc =>
    obtain ⟨a, ha⟩ := hn _ ht
    rw [ha] at hc; exact absurd hc (by simp)
  | method _ _ _ _ ih => exact ih

theorem isTO_M_of_noHTN {p : ProbDesc} (hn : p.toProblem.IsNoHTN) : p.toProblem.IsTO_M :=
  fun _ hm => absurd hm.2 (reachableName_empty hn _)

/-- **Solvability of a well-formed, non-hierarchical, totally ordered description is the execution
check of the plan by ranks.** -/
theorem solvable_iff_execB {p : ProbDesc} (hv : p.Valid) (hn : p.toProblem.IsNoHTN) (hto : TOL p.tnI) :
    p.toProblem.Solvable ↔
      execB (toSynDom p) (toSynInst p) (actsOf p.tnI (linOf p.tnI)) = true := by
  have key := iff_exists_cert p
  constructor
  · intro hs
    obtain ⟨l, hl⟩ := key.1 ⟨hv, hn, hs⟩
    simp only [certB, Bool.and_eq_true] at hl
    rw [← eq_linOf hv.tnI hto hl.1.2]
    exact hl.2
  · intro he
    have hc : certB (p, linOf p.tnI) = true := by
      simp only [certB, Bool.and_eq_true, validB_iff, noHTNB_iff]
      exact ⟨⟨⟨hv, hn⟩, linB_linOf hv.tnI hto⟩, he⟩
    exact (key.2 ⟨_, hc⟩).2.2

end NoHTNTO

end Article

end HTN
