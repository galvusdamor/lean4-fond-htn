import FondHtn.DB25.MachineChain
import HtnComplexity.Article.StripsHard
/-!
# Cell runs are space-bounded runs of the machine

For a nondeterministic machine `N` (states `Fin k`, symbols `Option Bool`), the **step data**
`FOND.DB.stepData N n` lists, for every transition `(q, a, q', a', m)` and every head update `μ`
realising the move `m` on `n`-bit head registers (`FOND.DB.hus`), the pair
`((q, a, q', a'), μ)`.

`FOND.DB.runC_iff_accepts`: some word of step data and some accepting state make the cell run
succeed for every cell iff `N` accepts in space `2 ^ n`.  (The transitions are fixed per step by
the word — chosen in advance, the fixed methods —, so the run is the same for all cells: this is
why nondeterministic machines can be used directly, without Savitch's theorem.)
-/

namespace FOND

namespace DB

open TM

/-! ## Head updates -/

/-- Increment with carry ending at `j`. -/
def incHU (j : ℕ) : HU := ((List.range j).map (·, true) ++ [(j, false)],
  (List.range j).map (·, false) ++ [(j, true)])

/-- Decrement with borrow ending at `j`. -/
def decHU (j : ℕ) : HU := ((List.range j).map (·, false) ++ [(j, true)],
  (List.range j).map (·, true) ++ [(j, false)])

/-- The head updates realising a move. -/
def hus (n : ℕ) : Move → List HU
  | .stay => [([], [])]
  | .right => (List.range n).map incHU
  | .left => (List.range n).map decHU ++ [((List.range n).map (·, false), [])]

theorem setBits_nil (β : ℕ → Bool) : setBits β [] = β := by funext i; simp [setBits]

theorem setBits_incHU (β : ℕ → Bool) (j : ℕ) : setBits β (incHU j).2 = incSet β j := by
  funext i
  simp only [setBits, incHU, incSet, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton, Prod.mk.injEq]
  by_cases h1 : i < j
  · simp [h1, Nat.ne_of_lt h1]
  · by_cases h2 : i = j
    · subst h2; simp
    · simp [h1, h2]

theorem setBits_decHU (β : ℕ → Bool) (j : ℕ) : setBits β (decHU j).2 = decSet β j := by
  funext i
  simp only [setBits, decHU, decSet, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton, Prod.mk.injEq]
  by_cases h1 : i < j
  · simp [h1]
  · by_cases h2 : i = j
    · subst h2; simp
    · simp [h1, h2]

/-- **Soundness of head updates.** -/
theorem hus_sound {n : ℕ} {m : Move} {μ : HU} (hμ : μ ∈ hus n m) {β : ℕ → Bool}
    (hpre : ∀ l ∈ μ.1, β l.1 = l.2) : bval n (setBits β μ.2) = m.apply (bval n β) := by
  cases m with
  | stay => simp [hus] at hμ; subst hμ; simp [setBits_nil, Move.apply]
  | right =>
    simp only [hus, List.mem_map, List.mem_range] at hμ
    obtain ⟨j, hj, rfl⟩ := hμ
    rw [setBits_incHU, bval_incSet n β j hj (fun i hi => hpre (i, true) (by simp [incHU, hi]))
      (hpre (j, false) (by simp [incHU])), Move.apply]
  | left =>
    simp only [hus, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hμ
    rcases hμ with ⟨j, hj, rfl⟩ | rfl
    · have := bval_decSet n β j hj (fun i hi => hpre (i, false) (by simp [decHU, hi]))
        (hpre (j, true) (by simp [decHU]))
      rw [setBits_decHU, Move.apply]; omega
    · have h0 : bval n β = 0 := (bval_zero_iff n β).2 fun i hi => hpre (i, false) (by simp [hi])
      simp [setBits_nil, Move.apply, h0]

/-- **Completeness of head updates.** -/
theorem hus_complete {n : ℕ} (m : Move) (β : ℕ → Bool) (hm : m.apply (bval n β) < 2 ^ n) :
    ∃ μ ∈ hus n m, ∀ l ∈ μ.1, β l.1 = l.2 := by
  cases m with
  | stay => exact ⟨([], []), by simp [hus], by simp⟩
  | right =>
    obtain ⟨j, hj, h1, h2⟩ := exists_inc n β (by simpa [Move.apply] using hm)
    refine ⟨incHU j, by simp [hus]; exact ⟨j, hj, rfl⟩, ?_⟩
    simp only [incHU, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
    rintro l (⟨i, hi, rfl⟩ | rfl)
    · exact h1 i hi
    · exact h2
  | left =>
    by_cases h0 : bval n β = 0
    · refine ⟨((List.range n).map (·, false), []), by simp [hus], ?_⟩
      simp only [List.mem_map, List.mem_range]
      rintro l ⟨i, hi, rfl⟩
      exact (bval_zero_iff n β).1 h0 i hi
    · obtain ⟨j, hj, h1, h2⟩ := exists_dec n β (by omega)
      refine ⟨decHU j, by simp [hus]; exact Or.inl ⟨j, hj, rfl⟩, ?_⟩
      simp only [decHU, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
      rintro l (⟨i, hi, rfl⟩ | rfl)
      · exact h1 i hi
      · exact h2

theorem hus_ok {n : ℕ} {m : Move} {μ : HU} (hμ : μ ∈ hus n m) : ∀ l ∈ μ.1 ++ μ.2, l.1 < n := by
  cases m <;> simp only [hus, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hμ
  · rcases hμ with ⟨j, hj, rfl⟩ | rfl
    · intro l hl
      simp only [decHU, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
      rcases hl with ((⟨i, hi, rfl⟩ | rfl) | (⟨i, hi, rfl⟩ | rfl)) <;> simp <;> omega
    · intro l hl
      simp only [List.append_nil, List.mem_map, List.mem_range] at hl
      obtain ⟨i, hi, rfl⟩ := hl; exact hi
  · subst hμ; simp
  · obtain ⟨j, hj, rfl⟩ := hμ
    intro l hl
    simp only [incHU, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
    rcases hl with ((⟨i, hi, rfl⟩ | rfl) | (⟨i, hi, rfl⟩ | rfl)) <;> simp <;> omega

/-! ## Step data of a machine -/

variable {k : ℕ} (N : NTM (Fin k) Sym)

/-- The transitions of the machine. -/
noncomputable def trsList : List (Fin k × Sym × Fin k × Sym × Move) := by
  classical
  exact ((Finset.univ : Finset (Fin k × Sym × Fin k × Sym × Move)).filter
    (fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2) ∈ N.step t.1 t.2.1)).toList

theorem mem_trsList {t : Fin k × Sym × Fin k × Sym × Move} :
    t ∈ trsList N ↔ (t.2.2.1, t.2.2.2.1, t.2.2.2.2) ∈ N.step t.1 t.2.1 := by
  classical
  simp [trsList]

/-- **The step data**: transitions with the head updates realising their moves. -/
noncomputable def stepData (n : ℕ) : List (TrD × HU) :=
  (trsList N).flatMap fun t => (hus n t.2.2.2.2).map fun μ =>
    ((t.1.val, t.2.1, t.2.2.1.val, t.2.2.2.1), μ)

/-- The accepting states. -/
noncomputable def accList : List ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin k)).filter (· ∈ N.accept)).toList.map Fin.val

theorem mem_accList {q : ℕ} : q ∈ accList N ↔ ∃ qq : Fin k, qq ∈ N.accept ∧ qq.val = q := by
  classical
  simp [accList]

theorem huOk_stepData (n : ℕ) : ∀ d ∈ stepData N n, HUok n d := by
  intro d hd
  simp only [stepData, List.mem_flatMap, List.mem_map] at hd
  obtain ⟨t, -, μ, hμ, rfl⟩ := hd
  exact hus_ok hμ

theorem reachesSpace_head {S K : ℕ} {c c' : Config (Fin k) Sym} (h : N.ReachesSpace S K c c') :
    c.head < S := by
  cases K with
  | zero => exact h.2
  | succ K => exact h.1

/-- From cell runs to runs of the machine. -/
theorem run_of_runC {n : ℕ} {acc : ℕ} (hacc : acc ∈ accList N) : ∀ (ws : List ℕ) (β : ℕ → Bool)
    (qq : Fin k) (tape : ℕ → Sym), (∀ x ∈ ws, x < (stepData N n).length) →
    (∀ γ, RunC n (stepData N n) acc γ ws β qq.val (tape (bval n γ))) →
    ∃ K c, N.ReachesSpace (2 ^ n) K ⟨qq, bval n β, tape⟩ c ∧ c.state ∈ N.accept
  | [], β, qq, tape, _, h => by
    have hq := h fun _ => false
    simp only [RunC] at hq
    obtain ⟨qa, hqa, hqv⟩ := (mem_accList N).1 hacc
    have : qq = qa := Fin.ext (hq.trans hqv.symm)
    subst this
    exact ⟨0, _, ⟨rfl, bval_lt n β⟩, hqa⟩
  | x :: ws, β, qq, tape, hws, h => by
    have hx := hws x (by simp)
    have hmem : (stepData N n).getI x ∈ stepData N n := by
      rw [List.getI_eq_getElem _ hx]; exact List.getElem_mem hx
    obtain ⟨t, ht, μ, hμ, hd⟩ : ∃ t ∈ trsList N, ∃ μ ∈ hus n t.2.2.2.2,
        (stepData N n).getI x = ((t.1.val, t.2.1, t.2.2.1.val, t.2.2.2.1), μ) := by
      unfold stepData at hmem
      obtain ⟨t, ht, hm2⟩ := List.mem_flatMap.1 hmem
      obtain ⟨μ, hμ, he⟩ := List.mem_map.1 hm2
      exact ⟨t, ht, μ, hμ, he.symm⟩
    have h0 := h β
    simp only [RunC, hd] at h0
    obtain ⟨hq, hpre, hread, -⟩ := h0
    have hqq : qq = t.1 := Fin.ext hq
    subst hqq
    have hrd : tape (bval n β) = t.2.1 := hread fun _ _ => trivial
    have hstep : (t.2.2.1, t.2.2.2.1, t.2.2.2.2) ∈ N.step t.1 (tape (bval n β)) := by
      rw [hrd]; exact (mem_trsList N).1 ht
    obtain ⟨K, c, hc, hacc'⟩ := run_of_runC hacc ws (setBits β μ.2) t.2.2.1
      (Function.update tape (bval n β) t.2.2.2.1) (fun y hy => hws y (by simp [hy])) fun γ => by
        have hγ := h γ
        simp only [RunC, hd] at hγ
        have := hγ.2.2.2
        convert this using 2
        by_cases heq : ∀ b < n, γ b = β b
        · rw [if_pos heq, (bval_eq_iff n).2 heq]; simp
        · rw [if_neg heq, Function.update_of_ne]
          exact fun he => heq ((bval_eq_iff n).1 he)
    refine ⟨K + 1, c, ⟨bval_lt n β, _, ⟨t.2.2.1, t.2.2.2.1, t.2.2.2.2, hstep, rfl⟩, ?_⟩, hacc'⟩
    rw [← hus_sound hμ hpre]
    exact hc

/-- From runs of the machine to cell runs. -/
theorem runC_of_run {n : ℕ} : ∀ (K : ℕ) (cfg c : Config (Fin k) Sym),
    N.ReachesSpace (2 ^ n) K cfg c → c.state ∈ N.accept → ∀ β : ℕ → Bool, bval n β = cfg.head →
    ∃ ws : List ℕ, (∀ x ∈ ws, x < (stepData N n).length) ∧
      ∀ γ, RunC n (stepData N n) c.state.val γ ws β cfg.state.val (cfg.tape (bval n γ))
  | 0, cfg, c, h, _, β, _ => by
    obtain ⟨rfl, -⟩ := h
    exact ⟨[], by simp, fun γ => rfl⟩
  | K + 1, cfg, c, h, hacc, β, hβ => by
    obtain ⟨_, d, ⟨q', γ', m, hmem, rfl⟩, hrest⟩ := h
    have hd := reachesSpace_head N hrest
    obtain ⟨μ, hμ, hpre⟩ := hus_complete (n := n) m β (by rw [hβ]; exact hd)
    have hβ' : bval n (setBits β μ.2) = m.apply cfg.head := by rw [hus_sound hμ hpre, hβ]
    obtain ⟨ws, hws, hrun⟩ := runC_of_run K _ c hrest hacc (setBits β μ.2) hβ'
    have hdat : ((cfg.state.val, cfg.tape cfg.head, q'.val, γ'), μ) ∈ stepData N n := by
      simp only [stepData, List.mem_flatMap, List.mem_map]
      exact ⟨(cfg.state, cfg.tape cfg.head, q', γ', m), (mem_trsList N).2 hmem, μ, hμ, rfl⟩
    obtain ⟨x, hx, hxd⟩ := List.getElem_of_mem hdat
    refine ⟨x :: ws, fun y hy => ?_, fun γ => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hws y hy
    · have hxd' : (stepData N n).getI x = ((cfg.state.val, cfg.tape cfg.head, q'.val, γ'), μ) := by
        rw [List.getI_eq_getElem _ hx, hxd]
      simp only [RunC, hxd']
      have heq : (∀ b < n, γ b = β b) ↔ bval n γ = cfg.head := by rw [← hβ, bval_eq_iff]
      refine ⟨trivial, hpre, fun h => by rw [heq.1 h], ?_⟩
      have e : (if ∀ b < n, γ b = β b then γ' else cfg.tape (bval n γ)) =
          Function.update cfg.tape cfg.head γ' (bval n γ) := by
        by_cases h : ∀ b < n, γ b = β b
        · rw [if_pos h, heq.1 h]; simp
        · rw [if_neg h, Function.update_of_ne (fun he => h (heq.2 he))]
      rw [e]; exact hrun γ

/-- **Theorem B**: some word of step data and some accepting state make the cell run succeed
for every cell iff the machine accepts in space `2 ^ n`. -/
theorem runC_iff_accepts (n : ℕ) (w : List Sym) :
    (∃ ws : List ℕ, (∀ x ∈ ws, x < (stepData N n).length) ∧ ∃ acc ∈ accList N,
      ∀ γ, RunC n (stepData N n) acc γ ws (fun _ => false) N.init.val (inp w N.blank (bval n γ))) ↔
    N.AcceptsInSpace w (2 ^ n) := by
  have h0 : bval n (fun _ => false) = 0 := (bval_zero_iff n _).2 fun _ _ => rfl
  constructor
  · rintro ⟨ws, hws, acc, hacc, h⟩
    obtain ⟨K, c, hc, hca⟩ := run_of_runC N hacc ws (fun _ => false) N.init
      (fun i => w.getD i N.blank) hws h
    rw [h0] at hc
    exact ⟨K, c, hc, hca⟩
  · rintro ⟨K, c, hc, hca⟩
    obtain ⟨ws, hws, h⟩ := runC_of_run N K _ c hc hca (fun _ => false) h0
    exact ⟨ws, hws, c.state.val, (mem_accList N).2 ⟨_, hca, rfl⟩, h⟩

end DB


end FOND
