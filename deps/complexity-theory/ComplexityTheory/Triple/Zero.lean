import ComplexityTheory.Triple.Transfer
/-!
# The zero-test gadget for any number of counters

CJLLO's gadget `Zero(x)` for two counters, generalised: the zero-tested counter `x`, the other
simulated counters `Y`, the triple counters `a`, `b`, `c`, the temporary `t` and one temporary
`u z` for every `z ∈ Z = a :: Y`.  Working counters `L = x, t, Z, u Z` (sum `S`).

* phase 1 (`l1`): for `z ∈ Z`, `loop z → u z, c → t`;
* phase 2 (`l2`): `loop t → a, c → a`, then for `z ∈ Z`, `loop u z → z, c → a`;
* then `b −= 1`.

**`zero_macro`**: every run of the two phases moves exactly `S' − S` units of `c` into the working
counters, `S' ≤ 4 S`, and if `S' = 4 S` the test was honest (`x = 0`) and the simulated counters
are restored.  **`zero_honest`**: an honest run exists if `x = t = u = 0` and `c ≥ 3 S`.
-/

namespace HTN

namespace Triple

variable {ι : Type} [DecidableEq ι]

/-- The data of a zero-test gadget. -/
structure ZD (ι : Type) where
  a : ι
  t : ι
  x : ι
  c : ι
  b : ι
  Y : List ι
  u : ι → ι

namespace ZD

variable (g : ZD ι)

/-- The counters emptied in phase 1. -/
def Z : List ι := g.a :: g.Y

/-- The working counters. -/
def L : List ι := g.x :: g.t :: (g.Z ++ g.Z.map g.u)

/-- The working counters, as a set. -/
def W : Finset ι := g.L.toFinset

/-- Phase 1. -/
def l1 : List (ι × ι × ι) := g.Z.map fun z => (z, g.u z, g.t)

/-- Phase 2. -/
def l2 : List (ι × ι × ι) := (g.t, g.a, g.a) :: g.Z.map fun z => (g.u z, z, g.a)

/-- Well-formedness: all named counters distinct. -/
def WF : Prop := (g.c :: g.b :: g.L).Nodup

variable {g}

theorem sumW_eq (hg : g.WF) (v : ι → ℕ) :
    sumW g.W v = v g.x + v g.t + (g.Z.map v).sum + ((g.Z.map g.u).map v).sum := by
  have hL : g.L.Nodup := by
    have := hg; unfold WF at this; exact (List.nodup_cons.mp (List.nodup_cons.mp this).2).2
  unfold sumW W
  rw [List.sum_toFinset _ hL]
  simp [L, List.map_append, List.sum_append]
  ring

theorem srcSum_l1 (v : ι → ℕ) : srcSum g.l1 v = (g.Z.map v).sum := by
  simp [srcSum, l1, Function.comp_def]

theorem srcSum_l2 (v : ι → ℕ) : srcSum g.l2 v = v g.t + ((g.Z.map g.u).map v).sum := by
  simp [srcSum, l2, Function.comp_def]

omit [DecidableEq ι] in
theorem mem_L {i : ι} : i ∈ g.L ↔ i = g.x ∨ i = g.t ∨ i ∈ g.Z ∨ i ∈ g.Z.map g.u := by
  simp [L]

/-! ### Consequences of well-formedness -/

section facts

variable (hg : g.WF)
include hg

theorem nd_all : (g.c :: g.b :: g.x :: g.t :: (g.Z ++ g.Z.map g.u)).Nodup := hg

theorem c_not_L : g.c ∉ g.L := fun h => (List.nodup_cons.mp hg).1 (List.mem_cons_of_mem _ h)

theorem b_not_L : g.b ∉ g.L := (List.nodup_cons.mp (List.nodup_cons.mp hg).2).1

theorem b_ne_c : g.b ≠ g.c := by
  intro h; have := (List.nodup_cons.mp hg).1; simp [h] at this

theorem L_nodup : g.L.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hg).2).2

theorem x_not : g.x ∉ g.t :: (g.Z ++ g.Z.map g.u) := (List.nodup_cons.mp (L_nodup hg)).1

theorem t_not : g.t ∉ g.Z ++ g.Z.map g.u :=
  (List.nodup_cons.mp (List.nodup_cons.mp (L_nodup hg)).2).1

theorem Zu_nodup : (g.Z ++ g.Z.map g.u).Nodup :=
  (List.nodup_cons.mp (List.nodup_cons.mp (L_nodup hg)).2).2

theorem Z_nodup : g.Z.Nodup := (List.nodup_append.mp (Zu_nodup hg)).1

theorem uZ_nodup : (g.Z.map g.u).Nodup := (List.nodup_append.mp (Zu_nodup hg)).2.1

theorem Z_disj {z z' : ι} (hz : z ∈ g.Z) (hz' : z' ∈ g.Z) : z ≠ g.u z' := by
  have := (List.nodup_append.mp (Zu_nodup hg)).2.2
  intro h
  exact this z hz (g.u z') (List.mem_map_of_mem hz') h

theorem u_inj {z z' : ι} (hz : z ∈ g.Z) (hz' : z' ∈ g.Z) (h : g.u z = g.u z') : z = z' := by
  have := uZ_nodup hg
  exact (List.inj_on_of_nodup_map this) hz hz' h

theorem mem_Z_ne {z : ι} (hz : z ∈ g.Z) :
    z ≠ g.c ∧ z ≠ g.b ∧ z ≠ g.x ∧ z ≠ g.t := by
  have h := nd_all hg
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · exact h.1.2.2.2.1 hz
  · exact h.2.1.2.2.1 hz
  · exact h.2.2.1.2.1 hz
  · exact h.2.2.2.1.1 hz

theorem mem_uZ_ne {z : ι} (hz : z ∈ g.Z) :
    g.u z ≠ g.c ∧ g.u z ≠ g.b ∧ g.u z ≠ g.x ∧ g.u z ≠ g.t := by
  have h := nd_all hg
  have hm : g.u z ∈ g.Z.map g.u := List.mem_map_of_mem hz
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he <;> rw [he] at hm
  · exact h.1.2.2.2.2 hm
  · exact h.2.1.2.2.2 hm
  · exact h.2.2.1.2.2 hm
  · exact h.2.2.2.1.2 hm

theorem a_mem : g.a ∈ g.Z := List.mem_cons_self ..

theorem twf1 : TWF g.c g.W g.l1 := by
  refine ⟨?_, fun h => c_not_L hg (by simpa [W] using h), ?_, ?_⟩
  · intro y hy
    simp only [l1, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [W, List.mem_toFinset, mem_L]
    exact ⟨Or.inr (Or.inr (Or.inl hz)), Or.inr (Or.inr (Or.inr (List.mem_map_of_mem hz))),
      Or.inr (Or.inl trivial)⟩
  · simpa [l1, Function.comp_def] using Z_nodup hg
  · intro y hy y' hy'
    simp only [l1, List.mem_map] at hy hy'
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := hy'
    exact ⟨Z_disj hg hz hz', (mem_Z_ne hg hz).2.2.2⟩

theorem twf2 : TWF g.c g.W g.l2 := by
  refine ⟨?_, fun h => c_not_L hg (by simpa [W] using h), ?_, ?_⟩
  · intro y hy
    simp only [l2, List.mem_cons, List.mem_map] at hy
    simp only [W, List.mem_toFinset, mem_L]
    rcases hy with rfl | ⟨z, hz, rfl⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl (a_mem hg))),
        Or.inr (Or.inr (Or.inl (a_mem hg)))⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (List.mem_map_of_mem hz))), Or.inr (Or.inr (Or.inl hz)),
        Or.inr (Or.inr (Or.inl (a_mem hg)))⟩
  · simp only [l2, List.map_cons, List.map_map, Function.comp_def, List.nodup_cons]
    refine ⟨?_, by simpa [Function.comp_def] using uZ_nodup hg⟩
    simp only [List.mem_map, not_exists, not_and]
    intro z hz h
    exact (mem_uZ_ne hg hz).2.2.2 h
  · intro y hy y' hy'
    simp only [l2, List.mem_cons, List.mem_map] at hy hy'
    have hta : g.t ≠ g.a := fun h => (mem_Z_ne hg (a_mem hg)).2.2.2 h.symm
    rcases hy with rfl | ⟨z, hz, rfl⟩ <;> rcases hy' with rfl | ⟨z', hz', rfl⟩
    · exact ⟨hta, hta⟩
    · exact ⟨fun h => (mem_Z_ne hg hz').2.2.2 h.symm, hta⟩
    · exact ⟨fun h => Z_disj hg (a_mem hg) hz h.symm, fun h => Z_disj hg (a_mem hg) hz h.symm⟩
    · exact ⟨fun h => Z_disj hg hz' hz h.symm, fun h => Z_disj hg (a_mem hg) hz h.symm⟩

theorem a_not_Y : g.a ∉ g.Y := (List.nodup_cons.mp (Z_nodup hg)).1

theorem pair1 {y : ι} (hy : y ∈ g.Z) {v w : ι → ℕ} (h : TSeq g.c g.l1 v w) :
    w y + w (g.u y) = v y + v (g.u y) := by
  have hyu : y ≠ g.u y := Z_disj hg hy hy
  refine tseq_pair h hyu (mem_Z_ne hg hy).1 (mem_uZ_ne hg hy).1 ?_ ?_
  · intro x hx
    simp only [l1, List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact (mem_Z_ne hg hz).1
  · intro x hx _
    simp only [l1, List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have h1 : g.t ≠ y := fun h => (mem_Z_ne hg hy).2.2.2 h.symm
    have h2 : g.t ≠ g.u y := fun h => (mem_uZ_ne hg hy).2.2.2 h.symm
    refine ⟨?_, h1, h2⟩
    by_cases hzy : z = y
    · exact Or.inl ⟨hzy, by rw [hzy]⟩
    · exfalso
      rename_i hinv
      simp only at hinv
      rcases hinv with h | h | h | h | h | h
      · exact hzy h
      · exact Z_disj hg hz hy h
      · exact Z_disj hg hy hz h.symm
      · exact hzy (u_inj hg hz hy h)
      · exact h1 h
      · exact h2 h

theorem pair2 {y : ι} (hy : y ∈ g.Y) {v w : ι → ℕ} (h : TSeq g.c g.l2 v w) :
    w y + w (g.u y) = v y + v (g.u y) := by
  have hyZ : y ∈ g.Z := List.mem_cons_of_mem _ hy
  have hyu : y ≠ g.u y := Z_disj hg hyZ hyZ
  have hay : g.a ≠ y := fun h => a_not_Y hg (h ▸ hy)
  have hau : g.a ≠ g.u y := Z_disj hg (a_mem hg) hyZ
  have hty : g.t ≠ y := fun h => (mem_Z_ne hg hyZ).2.2.2 h.symm
  have htu : g.t ≠ g.u y := fun h => (mem_uZ_ne hg hyZ).2.2.2 h.symm
  refine tseq_pair h hyu (mem_Z_ne hg hyZ).1 (mem_uZ_ne hg hyZ).1 ?_ ?_
  · intro x hx
    simp only [l2, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨z, hz, rfl⟩
    · intro h; simp only at h
      exact c_not_L hg (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact (mem_uZ_ne hg hz).1
  · intro x hx hinv
    simp only [l2, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨z, hz, rfl⟩
    · exfalso
      simp only at hinv
      rcases hinv with h | h | h | h | h | h
      · exact hty h
      · exact htu h
      · exact hay h
      · exact hau h
      · exact hay h
      · exact hau h
    · refine ⟨?_, hay, hau⟩
      simp only at hinv ⊢
      by_cases hzy : z = y
      · exact Or.inr ⟨by rw [hzy], hzy⟩
      · exfalso
        rcases hinv with h | h | h | h | h | h
        · exact Z_disj hg hyZ hz h.symm
        · exact hzy (u_inj hg hz hyZ h)
        · exact hzy h
        · exact Z_disj hg hz hyZ h
        · exact hay h
        · exact hau h

end facts

/-- **The zero-test gadget, soundness.** -/
theorem zero_macro (hg : g.WF) {v w1 w2 : ι → ℕ} (h1 : TSeq g.c g.l1 v w1)
    (h2 : TSeq g.c g.l2 w1 w2) :
    sumW g.W w2 + w2 g.c = sumW g.W v + v g.c ∧ sumW g.W w2 ≤ 4 * sumW g.W v ∧
      (sumW g.W w2 = 4 * sumW g.W v → v g.x = 0 ∧ w2 g.x = v g.x ∧ ∀ y ∈ g.Y, w2 y = v y) := by
  obtain ⟨m1a, m1b, m1c⟩ := tseq_main (twf1 hg) h1
  obtain ⟨m2a, m2b, m2c⟩ := tseq_main (twf2 hg) h2
  rw [srcSum_l1] at m1b m1c
  rw [srcSum_l2] at m2b m2c
  have d0 := sumW_eq hg v
  have d1 := sumW_eq hg w1
  refine ⟨by omega, by omega, fun heq => ?_⟩
  have hvx : v g.x = 0 := by omega
  have hxc : g.x ≠ g.c := by
    intro h; exact c_not_L hg (h ▸ List.mem_cons_self ..)
  have hxo1 : ∀ y ∈ g.l1, g.x ≠ y.1 ∧ g.x ≠ y.2.1 ∧ g.x ≠ y.2.2 := by
    intro y hy
    simp only [l1, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨fun h => (mem_Z_ne hg hz).2.2.1 h.symm, fun h => (mem_uZ_ne hg hz).2.2.1 h.symm,
      fun h => x_not hg (h ▸ List.mem_cons_self ..)⟩
  have hxo2 : ∀ y ∈ g.l2, g.x ≠ y.1 ∧ g.x ≠ y.2.1 ∧ g.x ≠ y.2.2 := by
    intro y hy
    simp only [l2, List.mem_cons, List.mem_map] at hy
    have hxa : g.x ≠ g.a := fun h => (mem_Z_ne hg (a_mem hg)).2.2.1 h.symm
    rcases hy with rfl | ⟨z, hz, rfl⟩
    · exact ⟨fun h => x_not hg (h ▸ List.mem_cons_self ..), hxa, hxa⟩
    · exact ⟨fun h => (mem_uZ_ne hg hz).2.2.1 h.symm, fun h => (mem_Z_ne hg hz).2.2.1 h.symm, hxa⟩
  have ex1 := tseq_other h1 hxc hxo1
  have ex2 := tseq_other h2 hxc hxo2
  refine ⟨hvx, by rw [ex2, ex1], fun y hy => ?_⟩
  have hyZ : y ∈ g.Z := List.mem_cons_of_mem _ hy
  have hu0 : ((g.Z.map g.u).map v).sum = 0 := by omega
  have hvu : v (g.u y) = 0 := by
    rw [List.sum_eq_zero_iff] at hu0
    exact hu0 _ (List.mem_map_of_mem (List.mem_map_of_mem hyZ))
  have hdet : w2 = detRun g.c g.l2 w1 := m2c (by omega)
  have hwu : w2 (g.u y) = 0 := by
    rw [hdet]
    have := detRun_src (v := w1) (twf2 hg) (g.u y, y, g.a)
      (by simp only [l2, List.mem_cons, List.mem_map]; exact Or.inr ⟨y, hyZ, rfl⟩)
    simpa using this
  have p1 := pair1 hg hyZ h1
  have p2 := pair2 hg hy h2
  omega

/-- **The zero-test gadget, completeness**: with `x`, `t` and the temporaries empty and a budget
`c ≥ 3 S`, the honest run exists; it quadruples `S` and empties the temporaries again. -/
theorem zero_honest (hg : g.WF) {v : ι → ℕ} (hx : v g.x = 0) (ht : v g.t = 0)
    (hu : ∀ z ∈ g.Z, v (g.u z) = 0) (hc : 3 * sumW g.W v ≤ v g.c) :
    ∃ w1 w2, TSeq g.c g.l1 v w1 ∧ TSeq g.c g.l2 w1 w2 ∧ sumW g.W w2 = 4 * sumW g.W v ∧
      w2 g.t = 0 ∧ ∀ z ∈ g.Z, w2 (g.u z) = 0 := by
  have d0 := sumW_eq hg v
  have hu0 : ((g.Z.map g.u).map v).sum = 0 := by
    rw [List.sum_eq_zero_iff]
    intro n hn
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hn
    obtain ⟨z, hz, rfl⟩ := hn
    exact hu z hz
  have hb1 : srcSum g.l1 v ≤ v g.c := by rw [srcSum_l1]; omega
  have r1 := tseq_detRun (twf1 hg) hb1
  have s1 := sumW_detRun (twf1 hg) hb1
  rw [srcSum_l1] at s1
  set w1 := detRun g.c g.l1 v
  obtain ⟨m1a, -, -⟩ := tseq_main (twf1 hg) r1
  have d1 := sumW_eq hg w1
  have hb2 : srcSum g.l2 w1 ≤ w1 g.c := by rw [srcSum_l2]; omega
  have r2 := tseq_detRun (twf2 hg) hb2
  have s2 := sumW_detRun (twf2 hg) hb2
  rw [srcSum_l2] at s2
  have hZ0 : (g.Z.map w1).sum = 0 := by
    rw [List.sum_eq_zero_iff]
    intro n hn
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hn
    have := detRun_src (v := v) (twf1 hg) (z, g.u z, g.t)
      (by simp only [l1, List.mem_map]; exact ⟨z, hz, rfl⟩)
    simpa using this
  have hx1 : w1 g.x = 0 := by
    have hxc : g.x ≠ g.c := by
      intro h; exact c_not_L hg (h ▸ List.mem_cons_self ..)
    simp only [w1]; rw [detRun_other hxc, hx]
    intro y hy
    simp only [l1, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨fun h => (mem_Z_ne hg hz).2.2.1 h.symm, fun h => (mem_uZ_ne hg hz).2.2.1 h.symm,
      fun h => x_not hg (h ▸ List.mem_cons_self ..)⟩
  refine ⟨w1, _, r1, r2, by omega, ?_, ?_⟩
  · have := detRun_src (v := w1) (twf2 hg) (g.t, g.a, g.a) (List.mem_cons_self ..)
    simpa using this
  · intro z hz
    have := detRun_src (v := w1) (twf2 hg) (g.u z, z, g.a)
      (by simp only [l2, List.mem_cons, List.mem_map]; exact Or.inr ⟨z, hz, rfl⟩)
    simpa using this

end ZD

end Triple

end HTN
