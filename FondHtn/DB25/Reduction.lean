import FondHtn.DB25.TMLink
/-!
# The reduction from exponential-space machines to regular strong OD (semantic part)

For a machine `N` with space bound `2 ^ n`, the input `w` is mapped to the regular register
program problem `FOND.DB.tmDesc N n w`:

* initial network: nature chooses a cell `c`; the content register is checked to hold the input
  symbol at `c` (`FOND.DB.preOps`); then the compound task;
* loop methods: one per transition and head update (`FOND.DB.loopOps`), each followed by the
  compound task again;
* final methods: one per accepting state (`FOND.DB.finalOps`).

`FOND.DB.tmDesc_strongOD_iff`: **it is strong OD solvable iff `N` accepts `w` in space `2 ^ n`**,
and it is well formed and regular in the sense of [CB21] (`FClass.REGtn`).
-/

namespace FOND

namespace DB

open TM Problem

variable {k : ℕ} (N : NTM (Fin k) Sym)

/-- **The encoding.** -/
noncomputable def tmDesc (n : ℕ) (w : List Sym) : FProbDesc :=
  opDesc (regs n w) (fun _ => false) N.init.val (preOps n w N.blank)
    ((stepData N n).map (loopOps n)) ((accList N).map finalOps)

/-! ## Well-formed operations -/

theorem mem_regs {n : ℕ} {w : List Sym} {x : ℕ} :
    x ∈ regs n w ↔ (∃ b < n, x = cB b) ∨ (∃ b < n, x = hB b) ∨ x = sB 0 ∨ x = sB 1 ∨
      x = tB 0 ∨ x = tB 1 ∨ (∃ b < n, x = dB b) ∨ ∃ i < w.length, x = gB i := by
  simp only [regs, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro (((((⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩) | h) | ⟨b, hb, rfl⟩) | ⟨i, hi, rfl⟩))
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr (Or.inl ⟨b, hb, rfl⟩)
    · rcases h with h | h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, hb, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩))))))
  · rintro (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ | rfl | rfl | rfl | rfl | ⟨b, hb, rfl⟩ | ⟨i, hi, rfl⟩) <;>
      simp_all

theorem wf_preOps {n : ℕ} {w : List Sym} {blank : Sym} :
    ∀ op ∈ preOps n w blank, OpWF (regs n w) op := by
  intro op hop
  simp only [preOps, initChoices, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hop
  rcases hop with ((⟨b, hb, rfl⟩ | ⟨r, (rfl | rfl) | ⟨i, hi, rfl⟩, rfl⟩) | rfl)
  · exact mem_regs.2 (Or.inl ⟨b, hb, rfl⟩)
  · exact mem_regs.2 (Or.inr (Or.inr (Or.inl rfl)))
  · exact mem_regs.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact mem_regs.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))))))
  · intro C hC l hl
    simp only [phiInit, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map] at hC
    rcases hC with (⟨i, hi, hC⟩ | ⟨i, hi, hC⟩) | ⟨j, hj, rfl⟩
    · split_ifs at hC
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hC
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact mem_regs.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))))))
        · exact mem_regs.2 (Or.inl ⟨b, List.mem_range.1 hb, rfl⟩)
      · simp only [List.mem_singleton] at hC; subst hC
        simp only [List.mem_singleton] at hl; subst hl
        exact mem_regs.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))))))
    · split_ifs at hC
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hC
        simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
        rcases hl with ⟨b, hb, rfl⟩ | rfl
        · exact mem_regs.2 (Or.inl ⟨b, hb, rfl⟩)
        · rcases (by have := List.mem_range.1 hj; omega : j = 0 ∨ j = 1) with rfl | rfl
          · exact mem_regs.2 (Or.inr (Or.inr (Or.inl rfl)))
          · exact mem_regs.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · simp at hC
    · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
      rcases hl with ⟨i, hi, rfl⟩ | rfl
      · exact mem_regs.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))))))
      · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · exact mem_regs.2 (Or.inr (Or.inr (Or.inl rfl)))
        · exact mem_regs.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem wf_loopOps {n : ℕ} {w : List Sym} {d : TrD × HU} (hd : HUok n d)
    (hnd : (d.2.2.map Prod.fst).Nodup) : ∀ op ∈ loopOps n d, OpWF (regs n w) op := by
  intro op hop
  simp only [loopOps, stepChoices, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hop
  rcases hop with ⟨r, (rfl | rfl) | ⟨b, hb, rfl⟩, rfl⟩ | rfl | rfl | rfl | rfl
  · exact mem_regs.2 (by simp)
  · exact mem_regs.2 (by simp)
  · exact mem_regs.2 (by simp [hb])
  · intro C hC l hl
    simp only [phiStep, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with ((⟨b, hb, rfl | rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨b, hb, j, hj, hC⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> exact mem_regs.2 (by simp [hb])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> exact mem_regs.2 (by simp [hb])
    · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
      rcases hl with ⟨b, hb, rfl⟩ | rfl
      · exact mem_regs.2 (by simp [hb])
      · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> exact mem_regs.2 (by simp)
    · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
      rcases hl with ⟨b, hb, rfl⟩ | rfl
      · exact mem_regs.2 (by simp [hb])
      · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> exact mem_regs.2 (by simp)
    · have hj' : j = 0 ∨ j = 1 := by omega
      rcases hC with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl <;>
        exact mem_regs.2 (by simp [hb])
  · exact ⟨mem_regs.2 (by simp), mem_regs.2 (by simp), tB_ne_sB _ _⟩
  · exact ⟨mem_regs.2 (by simp), mem_regs.2 (by simp), tB_ne_sB _ _⟩
  · refine ⟨fun l hl => ?_, fun l hl => ?_, ?_⟩
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      exact mem_regs.2 (Or.inr (Or.inl ⟨l'.1, hd l' (List.mem_append_left _ hl'), rfl⟩))
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      exact mem_regs.2 (Or.inr (Or.inl ⟨l'.1, hd l' (List.mem_append_right _ hl'), rfl⟩))
    · rw [List.map_map]
      have : (Prod.fst ∘ hl) = hB ∘ Prod.fst := rfl
      rw [this, ← List.map_map]
      exact hnd.map fun a b h => hB_inj.1 h

theorem nodup_hus {n : ℕ} {m : Move} {μ : HU} (hμ : μ ∈ hus n m) : (μ.2.map Prod.fst).Nodup := by
  cases m <;> simp only [hus, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hμ
  · rcases hμ with ⟨j, -, rfl⟩ | rfl
    · simp only [decHU, List.map_append, List.map_map, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨?_, List.nodup_singleton _, ?_⟩
      · simpa [Function.comp_def] using List.nodup_range
      · intro a ha b hb; simp at ha hb; omega
    · simp
  · subst hμ; simp
  · obtain ⟨j, -, rfl⟩ := hμ
    simp only [incHU, List.map_append, List.map_map, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨?_, List.nodup_singleton _, ?_⟩
    · simpa [Function.comp_def] using List.nodup_range
    · intro a ha b hb; simp at ha hb; omega

theorem wf_tmDesc (n : ℕ) (w : List Sym) :
    ∀ ops ∈ preOps n w N.blank :: ((stepData N n).map (loopOps n) ++ (accList N).map finalOps),
      ∀ op ∈ ops, OpWF (regs n w) op := by
  intro ops hops
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hops
  rcases hops with rfl | ⟨d, hd, rfl⟩ | ⟨acc, -, rfl⟩
  · exact wf_preOps
  · refine wf_loopOps (huOk_stepData N n d hd) ?_
    simp only [stepData, List.mem_flatMap, List.mem_map] at hd
    obtain ⟨t, -, μ, hμ, rfl⟩ := hd
    exact nodup_hus hμ
  · intro op hop
    simp only [finalOps, List.mem_singleton] at hop; subst hop
    exact ⟨by simp, by simp, by simp⟩

/-- **Correctness of the encoding.** -/
theorem tmDesc_strongOD_iff (n : ℕ) (w : List Sym) :
    (tmDesc N n w).toProblem.StrongODSolvable ↔ N.AcceptsInSpace w (2 ^ n) := by
  rw [tmDesc, opDesc_strongOD_iff (wf_tmDesc N n w), ← runC_iff_accepts N n w]
  simp only [List.length_map]
  constructor
  · rintro ⟨ws, f, hws, hf, h⟩
    have hL : ws.map ((stepData N n).map (loopOps n)).getI ++ [((accList N).map finalOps).getI f] =
        blocksOf n (stepData N n) ((accList N).getI f) ws := by
      simp only [blocksOf]
      congr 1
      · exact List.map_congr_left fun x hx => by
          rw [List.getI_eq_getElem _ (by simpa using hws x hx),
            List.getI_eq_getElem _ (hws x hx)]; simp
      · rw [List.getI_eq_getElem _ (by simpa using hf), List.getI_eq_getElem _ hf]; simp
    rw [hL, chain_iff (huOk_stepData N n)] at h
    refine ⟨ws, hws, (accList N).getI f, ?_, h⟩
    rw [List.getI_eq_getElem _ hf]; exact List.getElem_mem hf
  · rintro ⟨ws, hws, acc, hacc, h⟩
    obtain ⟨f, hf, rfl⟩ := List.getElem_of_mem hacc
    refine ⟨ws, f, hws, hf, ?_⟩
    have hL : ws.map ((stepData N n).map (loopOps n)).getI ++ [((accList N).map finalOps).getI f] =
        blocksOf n (stepData N n) ((accList N).getI f) ws := by
      simp only [blocksOf]
      congr 1
      · exact List.map_congr_left fun x hx => by
          rw [List.getI_eq_getElem _ (by simpa using hws x hx),
            List.getI_eq_getElem _ (hws x hx)]; simp
      · rw [List.getI_eq_getElem _ (by simpa using hf), List.getI_eq_getElem _ hf]; simp
    rw [hL, chain_iff (huOk_stepData N n)]
    rw [List.getI_eq_getElem _ hf]
    exact h

/-! ## The class -/

theorem isRegular_of_loop {tn : HTN.TaskNetwork ℕ ℕ ℕ} {c : ℕ} (h : IsLoop tn c) :
    tn.IsRegular := by
  obtain ⟨-, t₀, ht₀, hα₀, hr⟩ := h
  have hab : ∀ t ∈ tn.T, tn.IsAbstractId t → t = t₀ := by
    rintro t ht ⟨c', hc'⟩
    by_contra hne
    obtain ⟨a, ha⟩ := (hr t ht hne).1
    rw [hc'] at ha; cases ha
  refine ⟨fun t ht t' ht' h1 h2 => (hab t ht h1).trans (hab t' ht' h2).symm,
    fun t ht h1 t' ht' hne => ?_⟩
  obtain rfl := hab t ht h1
  exact (hr t' ht' hne).2

theorem isRegular_of_final {tn : HTN.TaskNetwork ℕ ℕ ℕ} (h : IsFinal tn) : tn.IsRegular := by
  have hab : ∀ t ∈ tn.T, ¬ tn.IsAbstractId t := by
    rintro t ht ⟨c', hc'⟩
    obtain ⟨a, ha⟩ := h.2 t ht
    rw [hc'] at ha; cases ha
  exact ⟨fun t ht _ _ h1 => absurd h1 (hab t ht), fun t ht h1 => absurd h1 (hab t ht)⟩

theorem mkDesc_REGtn {init : List ℕ} {pre : List (List FActDesc)}
    {loops finals : List (List (List FActDesc))} :
    FClass.REGtn (mkDesc init pre loops finals).toProblem := by
  refine ⟨?_, isRegular_of_loop (isLoop_progTn (k := 0) (phs := pre))⟩
  rintro m ⟨hm, -⟩
  rcases method_cases hm with ⟨w, -, rfl⟩ | ⟨f, -, rfl⟩
  · exact isRegular_of_loop isLoop_progTn
  · exact isRegular_of_final isFinal_progTn

theorem tmDesc_valid (n : ℕ) (w : List Sym) : (tmDesc N n w).Valid := opDesc_valid _ _ _ _ _ _

theorem tmDesc_REGtn (n : ℕ) (w : List Sym) : FClass.REGtn (tmDesc N n w).toProblem := mkDesc_REGtn

/-- **The semantic reduction**: `enc (tmDesc N n w)` is in `PlanExFM strongOD REGtn` iff `N`
accepts `w` in space `2 ^ n`. -/
theorem tmDesc_mem_iff (n : ℕ) (w : List Sym) :
    PlanExFM .strongOD FClass.REGtn (HTN.Syn.PolyDom.enc (tmDesc N n w)) ↔
      N.AcceptsInSpace w (2 ^ n) := by
  rw [planExFM_enc_iff]
  exact ⟨fun h => (tmDesc_strongOD_iff N n w).1 h.2.2,
    fun h => ⟨tmDesc_valid N n w, tmDesc_REGtn N n w, (tmDesc_strongOD_iff N n w).2 h⟩⟩

end DB


end FOND
