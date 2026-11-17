import FondHtn.QBF.SavitchEval
/-!
# Savitch's construction: correctness

`FOND.QBF.Savitch.holds_formula_iff_solvable`: for a well-formed STRIPS description `d`, the
QBF `formula d` is true iff `d` has a plan.  Bit vectors of length `n` are read as states
(`FOND.QBF.Savitch.dec`); reachability on bit vectors within `2 ^ k` steps is plan existence of
length `≤ 2 ^ k` (`FOND.QBF.Savitch.reachV_iff`), and every solvable problem has a plan of length
`< 2 ^ |V| ≤ 2 ^ n` (`HTN.Article.exists_short_plan`).
-/

namespace FOND

namespace QBF

namespace Savitch

open HTN HTN.Article

variable (d : StripsDesc)

/-! ## Facts -/

theorem nodup_allF : (allF d).Nodup := List.nodup_dedup _

theorem fI_mem {i : ℕ} (hi : i < nF d) : fI d i ∈ allF d := by
  rw [fI, List.getI_eq_getElem _ hi]; exact List.getElem_mem hi

theorem exists_idx {f : ℕ} (hf : f ∈ allF d) : ∃ i < nF d, fI d i = f := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hf
  exact ⟨i, hi, List.getI_eq_getElem _ hi⟩

theorem fI_inj {i j : ℕ} (hi : i < nF d) (hj : j < nF d) (h : fI d i = fI d j) : i = j := by
  rw [fI, fI, List.getI_eq_getElem _ hi, List.getI_eq_getElem _ hj] at h
  exact (List.Nodup.getElem_inj_iff (nodup_allF d)).1 h

theorem init_sub {f : ℕ} (h : f ∈ d.init) : f ∈ allF d := by
  simp [allF, h]

theorem goalPos_sub {f : ℕ} (h : f ∈ d.goalPos) : f ∈ allF d := by
  simp [allF, h]

theorem goalNeg_sub {f : ℕ} (h : f ∈ d.goalNeg) : f ∈ allF d := by
  simp [allF, h]

theorem act_sub {a : ActDesc} (ha : a ∈ d.actions) {f : ℕ}
    (h : f ∈ a.2.1 ∨ f ∈ a.2.2.1 ∨ f ∈ a.2.2.2.1 ∨ f ∈ a.2.2.2.2) : f ∈ allF d := by
  simp only [allF, List.mem_dedup, List.mem_append, List.mem_flatMap]
  right
  refine ⟨a, ha, ?_⟩
  tauto

/-- The state of a bit vector. -/
def dec (X : ℕ → Bool) : Set ℕ := {f | ∃ i < nF d, fI d i = f ∧ X i = true}

theorem mem_dec {X : ℕ → Bool} {i : ℕ} (hi : i < nF d) : fI d i ∈ dec d X ↔ X i = true := by
  constructor
  · rintro ⟨j, hj, he, hx⟩
    rwa [fI_inj d hj hi he] at hx
  · intro h; exact ⟨i, hi, rfl, h⟩

theorem dec_sub (X : ℕ → Bool) : dec d X ⊆ {f | f ∈ allF d} := by
  rintro f ⟨i, hi, rfl, -⟩; exact fI_mem d hi

/-- The bit vector of a state. -/
noncomputable def encS (s : Set ℕ) : ℕ → Bool := by
  classical exact fun i => decide (fI d i ∈ s)

theorem dec_encS {s : Set ℕ} (hs : s ⊆ {f | f ∈ allF d}) : dec d (encS d s) = s := by
  ext f
  constructor
  · rintro ⟨i, -, rfl, h⟩; simpa [encS] using h
  · intro hf
    obtain ⟨i, hi, rfl⟩ := exists_idx d (hs hf)
    exact ⟨i, hi, rfl, by simpa [encS] using hf⟩

/-! ## Actions -/

/-- The problem denoted by the description. -/
abbrev P : HTN.Article.Problem ℕ ℕ ℕ ℕ := d.toProbDesc.toProblem

theorem δ_of_mem (hv : d.Valid) {a : ActDesc} (ha : a ∈ d.actions) :
    (P d).δ a.name = a.toAction := by
  show d.toProbDesc.δ a.name = _
  unfold ProbDesc.δ
  obtain ⟨x, hx⟩ : ∃ x, d.toProbDesc.actions.find? (fun x => x.name == a.name) = some x := by
    cases h : d.toProbDesc.actions.find? (fun x => x.name == a.name) with
    | none =>
      exact absurd (List.find?_eq_none.1 h a ha) (by simp)
    | some x => exact ⟨x, rfl⟩
  rw [hx]
  have hxm : x ∈ d.actions := List.mem_of_find?_eq_some hx
  have hxn : x.name = a.name := by simpa using List.find?_some hx
  rw [List.inj_on_of_nodup_map hv hxm ha hxn]

theorem add_sub (nm : ℕ) : ((P d).δ nm).add ⊆ {f | f ∈ allF d} := by
  intro f hf
  change f ∈ (d.toProbDesc.δ nm).add at hf
  unfold ProbDesc.δ at hf
  split at hf
  · rename_i x hx
    have hxm : x ∈ d.actions := List.mem_of_find?_eq_some hx
    exact act_sub d hxm (Or.inr (Or.inr (Or.inl hf)))
  · simp at hf

theorem run_sub : ∀ (π : List ℕ) (s t : Set ℕ), (P d).Run π s t →
    s ⊆ {f | f ∈ allF d} → t ⊆ {f | f ∈ allF d} := by
  intro π
  induction π with
  | nil => intro s t h hs; cases h; exact hs
  | cons a π ih =>
    intro s t h hs
    exact ih _ _ h.2 (Set.union_subset (Set.diff_subset.trans hs) (add_sub d a))

theorem actSem_iff {a : ActDesc} (ha : a ∈ d.actions) (X Y : ℕ → Bool) :
    ActSem d a X Y ↔ a.toAction.Applicable (dec d X) ∧ dec d Y = a.toAction.apply (dec d X) := by
  simp only [ActSem, Action.Applicable, Action.apply, ActDesc.toAction]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun f hf => ?_, Set.disjoint_left.2 fun f hf hfX => ?_⟩, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := exists_idx d (act_sub d ha (Or.inl hf))
      exact (mem_dec d hi).2 (h1 i hi hf)
    · obtain ⟨i, hi, rfl⟩ := exists_idx d (act_sub d ha (Or.inr (Or.inl hf)))
      rw [mem_dec d hi, h2 i hi hf] at hfX
      exact absurd hfX (by simp)
    · ext f
      by_cases hf : f ∈ allF d
      · obtain ⟨i, hi, rfl⟩ := exists_idx d hf
        simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, mem_dec d hi, h3 i hi]
        cases X i <;> by_cases h4 : fI d i ∈ a.2.2.2.1 <;> by_cases h5 : fI d i ∈ a.2.2.2.2 <;>
          simp [h4, h5]
      · have h1 : f ∉ dec d Y := fun h => hf (dec_sub d Y h)
        have h2 : f ∉ dec d X := fun h => hf (dec_sub d X h)
        have h3 : f ∉ a.2.2.2.1 := fun h => hf (act_sub d ha (Or.inr (Or.inr (Or.inl h))))
        simp [h1, h2, h3]
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun i hi hf => (mem_dec d hi).1 (h1 hf), fun i hi hf => ?_, fun i hi => ?_⟩
    · have := Set.disjoint_left.1 h2 hf
      rw [mem_dec d hi] at this
      simpa using this
    · have := congrArg (fun s => fI d i ∈ s) h3
      simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, mem_dec d hi, eq_iff_iff] at this
      rw [Bool.eq_iff_iff, this]
      cases X i <;> by_cases h4 : fI d i ∈ a.2.2.2.1 <;> by_cases h5 : fI d i ∈ a.2.2.2.2 <;>
        simp [h4, h5]

/-! ## Reachability -/

theorem run_nil_iff (s t : Set ℕ) : (P d).Run [] s t ↔ t = s := Iff.rfl

theorem run_cons_iff (a : ℕ) (π : List ℕ) (s t : Set ℕ) :
    (P d).Run (a :: π) s t ↔ ((P d).δ a).Applicable s ∧ (P d).Run π (((P d).δ a).apply s) t :=
  Iff.rfl

theorem dec_eq_iff {X Y : ℕ → Bool} : dec d X = dec d Y ↔ ∀ i < nF d, X i = Y i := by
  constructor
  · intro h i hi
    have := congrArg (fun s => fI d i ∈ s) h
    simp only [mem_dec d hi, eq_iff_iff] at this
    rw [Bool.eq_iff_iff, this]
  · intro h
    ext f
    constructor
    · rintro ⟨i, hi, rfl, hx⟩; exact ⟨i, hi, rfl, (h i hi) ▸ hx⟩
    · rintro ⟨i, hi, rfl, hx⟩; exact ⟨i, hi, rfl, (h i hi).symm ▸ hx⟩

/-- **Bit-vector reachability is plan existence of bounded length.** -/
theorem reachV_iff (hv : d.Valid) : ∀ k (X Y : ℕ → Bool), ReachV d k X Y ↔
    ∃ π : List ℕ, π.length ≤ 2 ^ k ∧ (∀ a ∈ π, d.toProbDesc.Declared a) ∧
      (P d).Run π (dec d X) (dec d Y) := by
  intro k
  induction k with
  | zero =>
    intro X Y
    simp only [ReachV, pow_zero]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨[], by simp, by simp, ((dec_eq_iff d).2 h).symm⟩
      · have ha : d.actions.getI j ∈ d.actions := by
          rw [List.getI_eq_getElem _ hj]; exact List.getElem_mem hj
        obtain ⟨happ, heq⟩ := (actSem_iff d ha X Y).1 h
        refine ⟨[(d.actions.getI j).name], by simp, ?_, ?_⟩
        · intro a ha'
          rw [List.mem_singleton.1 ha']
          exact List.mem_map.2 ⟨_, ha, rfl⟩
        · rw [run_cons_iff, δ_of_mem d hv ha, run_nil_iff]
          exact ⟨happ, heq⟩
    · rintro ⟨π, hlen, hdec, hrun⟩
      match π, hlen, hdec, hrun with
      | [], _, _, hrun => exact Or.inl ((dec_eq_iff d).1 hrun.symm)
      | [nm], _, hdec, hrun =>
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (hdec nm (List.mem_singleton_self _))
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
        rw [run_cons_iff, run_nil_iff, δ_of_mem d hv ha] at hrun
        have hj' : j < d.actions.length := hj
        refine Or.inr ⟨j, hj', ?_⟩
        rw [List.getI_eq_getElem _ hj']
        exact (actSem_iff d ha X Y).2 hrun
      | _ :: _ :: _, hlen, _, _ => simp at hlen
  | succ k ih =>
    intro X Y
    simp only [ReachV]
    constructor
    · rintro ⟨Z, h1, h2⟩
      obtain ⟨π₁, l₁, d₁, r₁⟩ := (ih X Z).1 h1
      obtain ⟨π₂, l₂, d₂, r₂⟩ := (ih Z Y).1 h2
      refine ⟨π₁ ++ π₂, by simp; rw [pow_succ]; omega, fun a ha => ?_,
        (run_append π₁ π₂ _ _).2 ⟨_, r₁, r₂⟩⟩
      rcases List.mem_append.1 ha with ha | ha
      · exact d₁ a ha
      · exact d₂ a ha
    · rintro ⟨π, hlen, hdec, hrun⟩
      rw [← List.take_append_drop (2 ^ k) π, run_append] at hrun
      obtain ⟨m, r₁, r₂⟩ := hrun
      have hm : m ⊆ {f | f ∈ allF d} := run_sub d _ _ _ r₁ (dec_sub d X)
      refine ⟨encS d m, (ih _ _).2 ⟨π.take (2 ^ k), by simp, fun a ha =>
        hdec a (List.mem_of_mem_take ha), by rw [dec_encS d hm]; exact r₁⟩,
        (ih _ _).2 ⟨π.drop (2 ^ k), ?_, fun a ha => hdec a (List.mem_of_mem_drop ha),
          by rw [dec_encS d hm]; exact r₂⟩⟩
      simp only [List.length_drop]
      rw [pow_succ] at hlen; omega

/-! ## Correctness -/

theorem nV_le : d.nV ≤ nF d := by
  unfold StripsDesc.nV StripsDesc.facts
  refine (List.subperm_of_subset (List.nodup_dedup _) fun f hf => ?_).length_le
  simp only [List.mem_dedup, List.mem_append, List.mem_flatMap] at hf
  rcases hf with hf | ⟨a, ha, hf⟩
  · exact init_sub d hf
  · exact act_sub d ha (Or.inr (Or.inr (Or.inl hf)))

theorem init_sub' : {f | f ∈ d.init} ⊆ {f | f ∈ allF d} := fun _ hf => init_sub d hf

/-- **Correctness of Savitch's construction.** -/
theorem holds_formula_iff_solvable (hv : d.Valid) : Holds (formula d) ↔ d.Solvable := by
  rw [holds_formula_iff]
  constructor
  · rintro ⟨X, Y, ⟨h1, h2, h3⟩, hr⟩
    obtain ⟨π, -, hdec, hrun⟩ := (reachV_iff d hv _ X Y).1 hr
    have hX : dec d X = {f | f ∈ d.init} := by
      ext f
      constructor
      · rintro ⟨i, hi, rfl, hx⟩
        rw [h1 i hi] at hx; simpa using hx
      · intro hf
        obtain ⟨i, hi, rfl⟩ := exists_idx d (init_sub d hf)
        exact ⟨i, hi, rfl, by rw [h1 i hi]; simpa using hf⟩
    refine ⟨π, hdec, dec d Y, hX ▸ hrun, fun f hf => ?_, Set.disjoint_left.2 fun f hf hfY => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := exists_idx d (goalPos_sub d hf)
      exact (mem_dec d hi).2 (h2 i hi hf)
    · obtain ⟨i, hi, rfl⟩ := exists_idx d (goalNeg_sub d hf)
      rw [mem_dec d hi, h3 i hi hf] at hfY
      exact absurd hfY (by simp)
  · intro h
    obtain ⟨π, hlen, hdec, s, hrun, hg⟩ := exists_short_plan d h
    have hs : s ⊆ {f | f ∈ allF d} := run_sub d _ _ _ hrun (init_sub' d)
    refine ⟨encS d {f | f ∈ d.init}, encS d s, ⟨fun i _ => by simp [encS], fun i _ hf => ?_,
      fun i _ hf => ?_⟩, (reachV_iff d hv _ _ _).2 ⟨π, ?_, hdec, ?_⟩⟩
    · simpa [encS] using hg.1 hf
    · simpa [encS] using Set.disjoint_left.1 hg.2 hf
    · exact hlen.le.trans (Nat.pow_le_pow_right (by norm_num) (nV_le d))
    · rw [dec_encS d (init_sub' d), dec_encS d hs]; exact hrun

end Savitch

end QBF

end FOND
