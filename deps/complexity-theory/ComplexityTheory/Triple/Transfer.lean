import ComplexityTheory.Triple.Defs
/-!
# Sequences of transfer loops

A *transfer loop* `(s, d, e)` moves one unit from `s` to `d` and one unit from the budget `c` to
`e` per iteration.  `TSeq c l v w`: the sequence `l` of transfer loops, each iterated some number
of times, leads from `v` to `w`.  With a set `W` of working counters (`c ∉ W`, all loop counters in
`W`), the sources pairwise distinct and never destinations:

* `tseq_sum` — every iteration moves one unit of budget into `W`: `S w + c w = S v + c v`;
* `tseq_le` — at most the initial content of the sources moves: `S w ≤ S v + Σ_s v s`;
* `tseq_eq` — with equality, every loop was iterated maximally: `w = detRun c l v`;
* `tseq_detRun` — the maximal run exists if the budget suffices.
-/

namespace HTN

namespace Triple

variable {ι : Type} [DecidableEq ι]

/-- The consumed vector of a transfer loop. -/
def tdec (c s : ι) : ι → ℕ := Pi.single s 1 + Pi.single c 1

/-- The produced vector of a transfer loop. -/
def tinc (d e : ι) : ι → ℕ := Pi.single d 1 + Pi.single e 1

/-- **Runs of a sequence of transfer loops.** -/
def TSeq (c : ι) : List (ι × ι × ι) → (ι → ℕ) → (ι → ℕ) → Prop
  | [], v, w => w = v
  | (s, d, e) :: l, v, w => ∃ k, k • tdec c s ≤ v ∧ TSeq c l (itv (tdec c s) (tinc d e) k v) w

/-- **The maximal run.** -/
def detRun (c : ι) : List (ι × ι × ι) → (ι → ℕ) → (ι → ℕ)
  | [], v => v
  | (s, d, e) :: l, v => detRun c l (itv (tdec c s) (tinc d e) (v s) v)

/-- The sum over the working counters. -/
def sumW (W : Finset ι) (v : ι → ℕ) : ℕ := ∑ i ∈ W, v i

/-- Well-formedness of a sequence of transfer loops. -/
structure TWF (c : ι) (W : Finset ι) (l : List (ι × ι × ι)) : Prop where
  mem : ∀ x ∈ l, x.1 ∈ W ∧ x.2.1 ∈ W ∧ x.2.2 ∈ W
  cW : c ∉ W
  nodup : (l.map Prod.fst).Nodup
  src : ∀ x ∈ l, ∀ y ∈ l, x.1 ≠ y.2.1 ∧ x.1 ≠ y.2.2

theorem TWF.tail {c : ι} {W : Finset ι} {x : ι × ι × ι} {l : List (ι × ι × ι)}
    (h : TWF c W (x :: l)) : TWF c W l :=
  ⟨fun y hy => h.mem y (List.mem_cons_of_mem _ hy), h.cW, (List.nodup_cons.mp h.nodup).2,
    fun y hy z hz => h.src y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz)⟩

theorem flat_t {c s d e : ι} (hsd : s ≠ d) (hse : s ≠ e) (hcd : c ≠ d) (hce : c ≠ e) :
    Flat (tdec c s) (tinc d e) := by
  intro i
  by_cases h1 : i = s
  · subst h1; right; simp [tinc, Pi.single_apply, hsd, hse]
  · by_cases h2 : i = c
    · subst h2; right; simp [tinc, Pi.single_apply, hcd, hce]
    · left; simp [tdec, Pi.single_apply, h1, h2]

/-- The additive form of `k` iterations. -/
theorem itv_t_add {c s d e : ι} (hsc : s ≠ c) {k : ℕ} {v : ι → ℕ} (hk : k • tdec c s ≤ v) :
    itv (tdec c s) (tinc d e) k v + k • (Pi.single s 1 + Pi.single c 1) =
      v + k • (Pi.single d 1 + Pi.single e 1) := by
  funext i
  have := hk i
  simp only [itv, tdec, tinc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
  omega

theorem itv_t_apply_s {c s d e : ι} (hsc : s ≠ c) (hsd : s ≠ d) (hse : s ≠ e) {k : ℕ}
    {v : ι → ℕ} : itv (tdec c s) (tinc d e) k v s = v s - k := by
  simp [itv, tdec, tinc, Pi.single_apply, hsc, hsd, hse]

theorem itv_t_apply_other {c s d e i : ι} (his : i ≠ s) (hic : i ≠ c) (hid : i ≠ d) (hie : i ≠ e)
    {k : ℕ} {v : ι → ℕ} : itv (tdec c s) (tinc d e) k v i = v i := by
  simp [itv, tdec, tinc, Pi.single_apply, his, hic, hid, hie]

theorem itv_t_apply_c {c s d e : ι} (hsc : s ≠ c) (hcd : c ≠ d) (hce : c ≠ e) {k : ℕ}
    {v : ι → ℕ} : itv (tdec c s) (tinc d e) k v c = v c - k := by
  simp [itv, tdec, tinc, Pi.single_apply, hsc.symm, hcd, hce]

/-- One transfer loop moves `k` units of budget into the working counters. -/
theorem sumW_itv_t {c s d e : ι} {W : Finset ι} (hs : s ∈ W) (hd : d ∈ W) (he : e ∈ W)
    (hcW : c ∉ W) {k : ℕ} {v : ι → ℕ} (hk : k • tdec c s ≤ v) :
    sumW W (itv (tdec c s) (tinc d e) k v) = sumW W v + k := by
  have hsc : s ≠ c := fun h => hcW (h ▸ hs)
  have h := congrArg (fun f => ∑ i ∈ W, f i) (itv_t_add (d := d) (e := e) hsc hk)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_pi_single', hs, hd, he, hcW, if_true, if_false] at h
  unfold sumW
  omega

/-- The content of the sources. -/
def srcSum (l : List (ι × ι × ι)) (v : ι → ℕ) : ℕ := (l.map fun x => v x.1).sum

/-- **The main lemma on sequences of transfer loops.** -/
theorem tseq_main {c : ι} {W : Finset ι} : ∀ {l : List (ι × ι × ι)} {v w : ι → ℕ},
    TWF c W l → TSeq c l v w →
    sumW W w + w c = sumW W v + v c ∧ sumW W w ≤ sumW W v + srcSum l v ∧
      (sumW W w = sumW W v + srcSum l v → w = detRun c l v)
  | [], v, w, _, h => by
    simp only [TSeq] at h; subst h; simp [srcSum, detRun]
  | (s, d, e) :: l, v, w, hwf, ⟨k, hk, ht⟩ => by
    obtain ⟨hs, hd, he⟩ := hwf.mem (s, d, e) (List.mem_cons_self ..)
    have hcW := hwf.cW
    have hsc : s ≠ c := fun h => hcW (h ▸ hs)
    have hcd : c ≠ d := fun h => hcW (h ▸ hd)
    have hce : c ≠ e := fun h => hcW (h ▸ he)
    obtain ⟨hsd, hse⟩ := hwf.src (s, d, e) (List.mem_cons_self ..) (s, d, e) (List.mem_cons_self ..)
    obtain ⟨ih1, ih2, ih3⟩ := tseq_main hwf.tail ht
    have hS := sumW_itv_t (d := d) (e := e) hs hd he hcW hk
    have hkc : k ≤ v c := by have := hk c; simpa [tdec, Pi.single_apply, hsc.symm] using this
    have hks : k ≤ v s := by have := hk s; simpa [tdec, Pi.single_apply, hsc] using this
    have hc' := itv_t_apply_c (d := d) (e := e) (k := k) (v := v) hsc hcd hce
    have htail : srcSum l (itv (tdec c s) (tinc d e) k v) = srcSum l v := by
      unfold srcSum
      congr 1
      apply List.map_congr_left
      intro x hx
      have h1 : x.1 ≠ s := by
        intro h
        have := hwf.nodup
        simp only [List.map_cons, List.nodup_cons] at this
        exact this.1 (h ▸ List.mem_map_of_mem hx)
      obtain ⟨h2, h3⟩ := hwf.src x (List.mem_cons_of_mem _ hx) (s, d, e) (List.mem_cons_self ..)
      have h4 : x.1 ≠ c := fun h => hcW (h ▸ (hwf.mem x (List.mem_cons_of_mem _ hx)).1)
      exact itv_t_apply_other h1 h4 h2 h3
    have hsrc : srcSum ((s, d, e) :: l) v = v s + srcSum l v := by simp [srcSum]
    rw [htail] at ih2 ih3
    rw [hS] at ih1 ih2 ih3
    rw [hc'] at ih1
    rw [hsrc]
    refine ⟨by omega, by omega, fun heq => ?_⟩
    have hk' : k = v s := by omega
    subst hk'
    exact ih3 (by omega)

/-- **The maximal run exists** if the budget covers the sources. -/
theorem tseq_detRun {c : ι} {W : Finset ι} : ∀ {l : List (ι × ι × ι)} {v : ι → ℕ},
    TWF c W l → srcSum l v ≤ v c → TSeq c l v (detRun c l v)
  | [], v, _, _ => rfl
  | (s, d, e) :: l, v, hwf, hb => by
    obtain ⟨hs, hd, he⟩ := hwf.mem (s, d, e) (List.mem_cons_self ..)
    have hcW := hwf.cW
    have hsc : s ≠ c := fun h => hcW (h ▸ hs)
    have hcd : c ≠ d := fun h => hcW (h ▸ hd)
    have hce : c ≠ e := fun h => hcW (h ▸ he)
    have hsrc : srcSum ((s, d, e) :: l) v = v s + srcSum l v := by simp [srcSum]
    have hk : v s • tdec c s ≤ v := by
      intro i
      by_cases h1 : i = s
      · subst h1; simp [tdec, Pi.single_apply, hsc]
      · by_cases h2 : i = c
        · subst h2; simp [tdec, Pi.single_apply, hsc.symm]; omega
        · simp [tdec, Pi.single_apply, h1, h2]
    refine ⟨v s, hk, ?_⟩
    have htail : srcSum l (itv (tdec c s) (tinc d e) (v s) v) = srcSum l v := by
      unfold srcSum
      congr 1
      apply List.map_congr_left
      intro x hx
      have h1 : x.1 ≠ s := by
        intro h
        have := hwf.nodup
        simp only [List.map_cons, List.nodup_cons] at this
        exact this.1 (h ▸ List.mem_map_of_mem hx)
      obtain ⟨h2, h3⟩ := hwf.src x (List.mem_cons_of_mem _ hx) (s, d, e) (List.mem_cons_self ..)
      have h4 : x.1 ≠ c := fun h => hcW (h ▸ (hwf.mem x (List.mem_cons_of_mem _ hx)).1)
      exact itv_t_apply_other h1 h4 h2 h3
    apply tseq_detRun hwf.tail
    rw [htail, itv_t_apply_c hsc hcd hce]
    omega

/-- The vector consumed by the maximal run. -/
def detDec (c : ι) (l : List (ι × ι × ι)) (v : ι → ℕ) : ι → ℕ :=
  (l.map fun x => v x.1 • (Pi.single x.1 1 + Pi.single c 1)).sum

/-- The vector produced by the maximal run. -/
def detInc (l : List (ι × ι × ι)) (v : ι → ℕ) : ι → ℕ :=
  (l.map fun x => v x.1 • (Pi.single x.2.1 1 + Pi.single x.2.2 1)).sum

/-- **The maximal run in closed form.** -/
theorem detRun_add {c : ι} {W : Finset ι} : ∀ {l : List (ι × ι × ι)} {v : ι → ℕ},
    TWF c W l → srcSum l v ≤ v c → detRun c l v + detDec c l v = v + detInc l v
  | [], v, _, _ => by simp [detRun, detDec, detInc]
  | (s, d, e) :: l, v, hwf, hb => by
    obtain ⟨hs, hd, he⟩ := hwf.mem (s, d, e) (List.mem_cons_self ..)
    have hcW := hwf.cW
    have hsc : s ≠ c := fun h => hcW (h ▸ hs)
    have hcd : c ≠ d := fun h => hcW (h ▸ hd)
    have hce : c ≠ e := fun h => hcW (h ▸ he)
    have hsrc : srcSum ((s, d, e) :: l) v = v s + srcSum l v := by simp [srcSum]
    have hk : v s • tdec c s ≤ v := by
      intro i
      by_cases h1 : i = s
      · subst h1; simp [tdec, Pi.single_apply, hsc]
      · by_cases h2 : i = c
        · subst h2; simp [tdec, Pi.single_apply, hsc.symm]; omega
        · simp [tdec, Pi.single_apply, h1, h2]
    set v' := itv (tdec c s) (tinc d e) (v s) v with hv'
    have hagree : ∀ x ∈ l, v' x.1 = v x.1 := by
      intro x hx
      have h1 : x.1 ≠ s := by
        intro h
        have := hwf.nodup
        simp only [List.map_cons, List.nodup_cons] at this
        exact this.1 (h ▸ List.mem_map_of_mem hx)
      obtain ⟨h2, h3⟩ := hwf.src x (List.mem_cons_of_mem _ hx) (s, d, e) (List.mem_cons_self ..)
      have h4 : x.1 ≠ c := fun h => hcW (h ▸ (hwf.mem x (List.mem_cons_of_mem _ hx)).1)
      exact itv_t_apply_other h1 h4 h2 h3
    have htail : srcSum l v' = srcSum l v := by
      unfold srcSum; congr 1; exact List.map_congr_left hagree
    have hdec : detDec c l v' = detDec c l v := by
      unfold detDec; congr 1; apply List.map_congr_left; intro x hx; rw [hagree x hx]
    have hinc : detInc l v' = detInc l v := by
      unfold detInc; congr 1; apply List.map_congr_left; intro x hx; rw [hagree x hx]
    have ih := detRun_add (v := v') hwf.tail (by rw [htail, hv', itv_t_apply_c hsc hcd hce]; omega)
    rw [hdec, hinc] at ih
    have h0 := itv_t_add (d := d) (e := e) hsc hk
    simp only [detRun, detDec, detInc, List.map_cons, List.sum_cons] at ih ⊢
    rw [← hv'] at h0 ⊢
    funext i
    have := congrFun ih i
    have := congrFun h0 i
    simp only [Pi.add_apply] at *
    omega

/-- Counters that no loop touches keep their value. -/
theorem tseq_other {c : ι} : ∀ {l : List (ι × ι × ι)} {v w : ι → ℕ} {i : ι},
    TSeq c l v w → i ≠ c → (∀ x ∈ l, i ≠ x.1 ∧ i ≠ x.2.1 ∧ i ≠ x.2.2) → w i = v i
  | [], v, w, i, h, _, _ => by simp only [TSeq] at h; subst h; rfl
  | (s, d, e) :: l, v, w, i, ⟨k, _, ht⟩, hic, hi => by
    obtain ⟨h1, h2, h3⟩ := hi (s, d, e) (List.mem_cons_self ..)
    rw [tseq_other ht hic (fun x hx => hi x (List.mem_cons_of_mem _ hx)),
      itv_t_apply_other h1 hic h2 h3]

theorem detRun_other {c : ι} : ∀ {l : List (ι × ι × ι)} {v : ι → ℕ} {i : ι},
    i ≠ c → (∀ x ∈ l, i ≠ x.1 ∧ i ≠ x.2.1 ∧ i ≠ x.2.2) → detRun c l v i = v i
  | [], v, i, _, _ => rfl
  | (s, d, e) :: l, v, i, hic, hi => by
    obtain ⟨h1, h2, h3⟩ := hi (s, d, e) (List.mem_cons_self ..)
    simp only [detRun]
    rw [detRun_other hic (fun x hx => hi x (List.mem_cons_of_mem _ hx)),
      itv_t_apply_other h1 hic h2 h3]

/-- **The maximal run empties every source.** -/
theorem detRun_src {c : ι} {W : Finset ι} : ∀ {l : List (ι × ι × ι)} {v : ι → ℕ},
    TWF c W l → ∀ x ∈ l, detRun c l v x.1 = 0
  | [], _, _, x, hx => by simp at hx
  | (s, d, e) :: l, v, hwf, x, hx => by
    obtain ⟨hs, hd, he⟩ := hwf.mem (s, d, e) (List.mem_cons_self ..)
    have hcW := hwf.cW
    have hsc : s ≠ c := fun h => hcW (h ▸ hs)
    obtain ⟨hsd, hse⟩ := hwf.src (s, d, e) (List.mem_cons_self ..) (s, d, e) (List.mem_cons_self ..)
    simp only [detRun]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [detRun_other hsc]
      · simp [itv_t_apply_s hsc hsd hse]
      · intro y hy
        have h1 : s ≠ y.1 := by
          intro h
          have := hwf.nodup
          simp only [List.map_cons, List.nodup_cons] at this
          exact this.1 (h ▸ List.mem_map_of_mem hy)
        obtain ⟨h2, h3⟩ := hwf.src (s, d, e) (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)
        exact ⟨h1, h2, h3⟩
    · exact detRun_src hwf.tail x hx'

/-- **Pairs that only exchange units with each other keep their sum.** -/
theorem tseq_pair {c : ι} : ∀ {l : List (ι × ι × ι)} {v w : ι → ℕ} {p q : ι},
    TSeq c l v w → p ≠ q → p ≠ c → q ≠ c → (∀ x ∈ l, x.1 ≠ c) →
    (∀ x ∈ l, (x.1 = p ∨ x.1 = q ∨ x.2.1 = p ∨ x.2.1 = q ∨ x.2.2 = p ∨ x.2.2 = q) →
      ((x.1 = p ∧ x.2.1 = q) ∨ (x.1 = q ∧ x.2.1 = p)) ∧ x.2.2 ≠ p ∧ x.2.2 ≠ q) →
    w p + w q = v p + v q
  | [], v, w, p, q, h, _, _, _, _, _ => by simp only [TSeq] at h; subst h; rfl
  | (s, d, e) :: l, v, w, p, q, ⟨k, hk, ht⟩, hpq, hpc, hqc, hsc, hl => by
    rw [tseq_pair ht hpq hpc hqc (fun x hx => hsc x (List.mem_cons_of_mem _ hx))
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
    have hs : s ≠ c := hsc (s, d, e) (List.mem_cons_self ..)
    have h0 := itv_t_add (d := d) (e := e) hs hk
    have hp := congrFun h0 p
    have hq := congrFun h0 q
    have hx := hl (s, d, e) (List.mem_cons_self ..)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hp hq hx
    by_cases hinv : s = p ∨ s = q ∨ d = p ∨ d = q ∨ e = p ∨ e = q
    · obtain ⟨h1 | h1, h2, h3⟩ := hx hinv <;> obtain ⟨rfl, rfl⟩ := h1 <;>
        simp_all [Ne.symm hpq, Ne.symm hpc, Ne.symm hqc, eq_comm] <;> omega
    · push_neg at hinv
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hinv
      simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, hpc,
        hqc] at hp hq
      omega

/-- **The maximal run moves the content of all sources.** -/
theorem sumW_detRun {c : ι} {W : Finset ι} : ∀ {l : List (ι × ι × ι)} {v : ι → ℕ},
    TWF c W l → srcSum l v ≤ v c → sumW W (detRun c l v) = sumW W v + srcSum l v
  | [], v, _, _ => by simp [detRun, srcSum]
  | (s, d, e) :: l, v, hwf, hb => by
    obtain ⟨hs, hd, he⟩ := hwf.mem (s, d, e) (List.mem_cons_self ..)
    have hcW := hwf.cW
    have hsc : s ≠ c := fun h => hcW (h ▸ hs)
    have hcd : c ≠ d := fun h => hcW (h ▸ hd)
    have hce : c ≠ e := fun h => hcW (h ▸ he)
    have hsrc : srcSum ((s, d, e) :: l) v = v s + srcSum l v := by simp [srcSum]
    have hk : v s • tdec c s ≤ v := by
      intro i
      by_cases h1 : i = s
      · subst h1; simp [tdec, Pi.single_apply, hsc]
      · by_cases h2 : i = c
        · subst h2; simp [tdec, Pi.single_apply, hsc.symm]; omega
        · simp [tdec, Pi.single_apply, h1, h2]
    have htail : srcSum l (itv (tdec c s) (tinc d e) (v s) v) = srcSum l v := by
      unfold srcSum
      congr 1
      apply List.map_congr_left
      intro x hx
      have h1 : x.1 ≠ s := by
        intro h
        have := hwf.nodup
        simp only [List.map_cons, List.nodup_cons] at this
        exact this.1 (h ▸ List.mem_map_of_mem hx)
      obtain ⟨h2, h3⟩ := hwf.src x (List.mem_cons_of_mem _ hx) (s, d, e) (List.mem_cons_self ..)
      have h4 : x.1 ≠ c := fun h => hcW (h ▸ (hwf.mem x (List.mem_cons_of_mem _ hx)).1)
      exact itv_t_apply_other h1 h4 h2 h3
    simp only [detRun]
    rw [sumW_detRun hwf.tail (by rw [htail, itv_t_apply_c hsc hcd hce]; omega), htail,
      sumW_itv_t hs hd he hcW hk, hsrc]
    ring

/-- One more iteration of the first loop. -/
theorem tseq_cons_step {c s d e : ι} {l : List (ι × ι × ι)} {w r : ι → ℕ}
    (hf : Flat (tdec c s) (tinc d e)) (hw : tdec c s ≤ w)
    (h : TSeq c ((s, d, e) :: l) (w - tdec c s + tinc d e) r) : TSeq c ((s, d, e) :: l) w r := by
  obtain ⟨k, hk, ht⟩ := h
  have h1 : (1 : ℕ) • tdec c s ≤ w := by simpa using hw
  have e1 : itv (tdec c s) (tinc d e) 1 w = w - tdec c s + tinc d e := by
    have := itv_succ (k := 0) hf (by simpa using hw) (v := w)
    rw [this, itv_zero]
  rw [← e1] at hk ht
  obtain ⟨h2, e2⟩ := itv_add hf h1 hk
  exact ⟨1 + k, h2, by rwa [← e2]⟩

/-- Counters outside the working set (other than the budget) keep their value. -/
theorem tseq_out {c : ι} {W : Finset ι} {l : List (ι × ι × ι)} {v w : ι → ℕ} {p : ι}
    (hwf : TWF c W l) (h : TSeq c l v w) (hp : p ∉ W) (hpc : p ≠ c) : w p = v p := by
  refine tseq_other h hpc fun x hx => ?_
  obtain ⟨h1, h2, h3⟩ := hwf.mem x hx
  exact ⟨fun e => hp (e ▸ h1), fun e => hp (e ▸ h2), fun e => hp (e ▸ h3)⟩

/-- Skipping the first loop. -/
theorem tseq_skip {c : ι} {x : ι × ι × ι} {l : List (ι × ι × ι)} {v w : ι → ℕ}
    (h : TSeq c l v w) : TSeq c (x :: l) v w := by
  obtain ⟨s, d, e⟩ := x
  exact ⟨0, by simp, by rw [itv_zero]; exact h⟩

/-! ### Sequences of transfer loops in a counter system -/

variable {Q : Type}

/-- **The sequence `l` sits at the control states `st 0, st 1, …`**: at `st j` the only rules are
the `j`-th loop and the exit to `st (j+1)`. -/
def Embedded (rs : Set (Rule Q ι)) (c : ι) (st : ℕ → Q) : List (ι × ι × ι) → Prop
  | [] => True
  | (s, d, e) :: l => ⟨st 0, tdec c s, tinc d e, st 0⟩ ∈ rs ∧ ⟨st 0, 0, 0, st 1⟩ ∈ rs ∧
      (∀ ρ ∈ rs, ρ.src = st 0 → ρ = ⟨st 0, tdec c s, tinc d e, st 0⟩ ∨ ρ = ⟨st 0, 0, 0, st 1⟩) ∧
      Embedded rs c (fun j => st (j + 1)) l

/-- Flatness of all loops of a sequence. -/
def AllFlat (c : ι) (l : List (ι × ι × ι)) : Prop :=
  ∀ x ∈ l, x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ c ≠ x.2.1 ∧ c ≠ x.2.2

/-- **Soundness**: a run entering the sequence either is still inside or has left it through the
last state after a run of `TSeq`. -/
theorem embedded_split {rs : Set (Rule Q ι)} {c : ι} : ∀ {st : ℕ → Q} {l : List (ι × ι × ι)},
    Embedded rs c st l → AllFlat c l → ∀ {v : ι → ℕ} {y : Cfg Q ι}, Reach rs (st 0, v) y →
    (∃ i < l.length, y.1 = st i) ∨ ∃ w, TSeq c l v w ∧ Reach rs (st l.length, w) y
  | st, [], _, _, v, y, h => Or.inr ⟨v, rfl, h⟩
  | st, (s, d, e) :: l, ⟨hl, hx, hiso, hemb⟩, hfl, v, y, h => by
    obtain ⟨h1, h2, h3, h4⟩ := hfl (s, d, e) (List.mem_cons_self ..)
    have hf : Flat (tdec c s) (tinc d e) := flat_t h1 h2 h3 h4
    rcases loop_split hf hiso h with ⟨k, -, rfl⟩ | ⟨k, hk, hr⟩
    · exact Or.inl ⟨0, by simp, rfl⟩
    · rcases embedded_split (st := fun j => st (j + 1)) hemb
        (fun x hx => hfl x (List.mem_cons_of_mem _ hx)) hr with ⟨i, hi, hy⟩ | ⟨w, hw, hr'⟩
      · exact Or.inl ⟨i + 1, by simp; omega, hy⟩
      · exact Or.inr ⟨w, ⟨k, hk, hw⟩, by simpa using hr'⟩

/-- **Completeness**: every run of `TSeq` is a run of the counter system. -/
theorem embedded_reach {rs : Set (Rule Q ι)} {c : ι} : ∀ {st : ℕ → Q} {l : List (ι × ι × ι)},
    Embedded rs c st l → AllFlat c l → ∀ {v w : ι → ℕ}, TSeq c l v w →
    Reach rs (st 0, v) (st l.length, w)
  | st, [], _, _, v, w, h => by simp only [TSeq] at h; subst h; exact .refl
  | st, (s, d, e) :: l, ⟨hl, hx, _, hemb⟩, hfl, v, w, ⟨k, hk, ht⟩ => by
    obtain ⟨h1, h2, h3, h4⟩ := hfl (s, d, e) (List.mem_cons_self ..)
    have hf : Flat (tdec c s) (tinc d e) := flat_t h1 h2 h3 h4
    have hstep : Step rs (st 0, itv (tdec c s) (tinc d e) k v)
        (st 1, itv (tdec c s) (tinc d e) k v) := by
      have := Step.mk (rs := rs) _ hx (itv (tdec c s) (tinc d e) k v) (by intro i; simp)
      simpa using this
    refine (iter_reach hl hf v k hk).trans (Relation.ReflTransGen.head hstep ?_)
    simpa using embedded_reach (st := fun j => st (j + 1)) hemb
        (fun x hx => hfl x (List.mem_cons_of_mem _ hx)) ht

end Triple

end HTN
