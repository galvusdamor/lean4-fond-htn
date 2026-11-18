import HtnComplexity.SpaceEnc.CompStep3
/-!
# Completeness of the encoding: acceptance and draining

The phase `CFin` (the accepting configuration has been reached) allows the finish action `fin`;
afterwards the stored tails of the last round are drained (`CD1`, `CD2`) until everything is
consumed.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {N : NTM Q Γ}
  {m n' : ℕ} {ι : Bool → Γ} {w : List Bool}

/-! ### Fact bookkeeping while draining -/

section Facts

omit [Fintype Q] [DecidableEq Q] [DecidableEq Γ]

theorem mem_trans_keep {a : Act Q Γ} {s : Set (Fct Q Γ)} {f : Fct Q Γ} (hf : f ∈ s)
    (hd : f ∉ delL m a) : f ∈ (am m n' ι N).transition a s :=
  mem_transition.2 (Or.inl ⟨hf, hd⟩)

theorem mem_trans_add {a : Act Q Γ} {s : Set (Fct Q Γ)} {f : Fct Q Γ} (hf : f ∈ addL m ι N a) :
    f ∈ (am m n' ι N).transition a s :=
  mem_transition.2 (Or.inr hf)

theorem par_mem_of_drainSt {s : Set (Fct Q Γ)} {pcv : ℕ} (h : DrainSt m s pcv) (q : Bool) :
    Fct.par q ∈ s := by
  cases q
  · exact h.2.2.1
  · exact h.2.1

theorem drain_rv {s : Set (Fct Q Γ)} {q : Bool} {g : Γ} (h : DrainSt m s (m + 1)) :
    (am m n' ι N).Applicable (.rv q g) s ∧
      DrainSt m ((am m n' ι N).transition (.rv q g) s) (m + 2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨applicable_iff.2 ?_, mem_trans_keep h1 (by simp [delL]),
    mem_trans_keep h2 (by simp [delL]), mem_trans_keep h3 (by simp [delL]),
    fun k hk x => mem_trans_keep (h4 k hk x) (by simp [delL]), mem_trans_add (by simp [addL])⟩
  intro f hf
  simp only [precL, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact h5
  · exact par_mem_of_drainSt ⟨h1, h2, h3, h4, h5⟩ _

theorem drain_rb {s : Set (Fct Q Γ)} {q x : Bool} {j : ℕ} (hj : j < m)
    (h : DrainSt m s (m + 2 + j)) :
    (am m n' ι N).Applicable (.rb q (m - (j + 1)) x) s ∧
      DrainSt m ((am m n' ι N).transition (.rb q (m - (j + 1)) x) s) (m + 2 + (j + 1)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e1 : 2 * m + 1 - (m - (j + 1)) = m + 2 + j := by omega
  have e2 : 2 * m + 2 - (m - (j + 1)) = m + 2 + (j + 1) := by omega
  refine ⟨applicable_iff.2 ?_, mem_trans_keep h1 (by simp [delL]),
    mem_trans_keep h2 (by simp [delL]), mem_trans_keep h3 (by simp [delL]),
    fun k hk x => mem_trans_keep (h4 k hk x) (by simp [delL]), mem_trans_add (by simp [addL, e2])⟩
  intro f hf
  simp only [precL, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · rw [e1]; exact h5
  · exact h4 _ (by omega) _

theorem drain_drn {s : Set (Fct Q Γ)} (h : DrainSt m s (m + 2 + m)) :
    (am m n' ι N).Applicable .drn s ∧ DrainSt m ((am m n' ι N).transition .drn s) (m + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨applicable_iff.2 ?_, mem_trans_keep h1 (by simp [delL]),
    mem_trans_keep h2 (by simp [delL]), mem_trans_keep h3 (by simp [delL]),
    fun k hk x => mem_trans_keep (h4 k hk x) (by simp [delL]), mem_trans_add (by simp [addL])⟩
  intro f hf
  simp only [precL, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · rw [show 2 * m + 2 = m + 2 + m by omega]; exact h5
  · exact h1

theorem drain_fin {s : Set (Fct Q Γ)} {q : Q} :
    DrainSt m ((am m n' ι N).transition (.fin q) s) (m + 1) := by
  refine ⟨mem_trans_add (by simp [addL]), mem_trans_add (by simp [addL]),
    mem_trans_add (by simp [addL]), fun k hk x => mem_trans_add ?_, mem_trans_add (by simp [addL])⟩
  cases x <;> simp [addL, hk]

end Facts

/-! ### The steps -/

variable (R : RunSeq N (2 ^ m) (N.initConfig (w.map ι)))

omit [Fintype Q] in
/-- `CFin → CD1`: the finish action `fin`. -/
theorem step_CFin {wd : World (Fct Q Γ) (Act Q Γ)} (h : CFin R m w wd) :
    ∃ wd', WStep (am m n' ι N) wd wd' ∧ ∃ S, CD1 R m S wd' := by
  obtain ⟨fs, hs, hpc, hcnt, hst, hA, h0, h1, hφ⟩ := h
  have happ : (am m n' ι N).Applicable (.fin (R.cf R.r).state) wd.s := by
    rw [hs, app_fin]
    exact ⟨hpc, hst, fun j _ => by rw [hcnt]; simp⟩
  refine ⟨_, wstep_phi (a := .fin (R.cf R.r).state)
    (φ' := List.replicate (if R.r = 0 then 0 else 2 ^ m) .drn) hφ happ, ?_⟩
  by_cases hr : R.r = 0
  · refine ⟨[], ⟨parR R.r, wd.bs (parR R.r), [], by simp, hA, h0 hr, Or.inl ⟨rfl, rfl⟩⟩,
      drain_fin, by simp [hr]⟩
  · obtain ⟨E, cur, hb, hE, hms⟩ := h1 hr
    refine ⟨List.range' 0 (2 ^ m), ⟨!parR R.r, E, [cur], hb, hE, by rw [Bool.not_not]; exact hA,
      Or.inr ⟨cur, rfl, hms⟩⟩, drain_fin, by simp [hr]⟩

omit [Fintype Q] in
/-- `CD1 (c :: S) → CD2 S c 0`: the start `rv` of a stored tail. -/
theorem step_CD1 {c : ℕ} {S : List ℕ} {wd : World (Fct Q Γ) (Act Q Γ)} (h : CD1 R m (c :: S) wd) :
    ∃ wd', WStep (am m n' ι N) wd wd' ∧ CD2 R m S c 0 wd' := by
  obtain ⟨⟨q, E, L, hb, hE, hA, hL⟩, hD, hφ⟩ := h
  rcases hL with ⟨-, h⟩ | ⟨cur, rfl, hms⟩
  · exact absurd h (List.cons_ne_nil _ _)
  have hms' : msOf cur = tails m q (R.cf R.r).tape S +
      {.rv q ((R.cf R.r).tape c) :: rbsL q 0 m (bitsOf c)} := by
    rw [hms, tails, List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]
    rfl
  obtain ⟨happ, hD'⟩ := drain_rv (n' := n') (ι := ι) (N := N) (q := q)
    (g := (R.cf R.r).tape c) hD
  obtain ⟨cur', hcur', hst⟩ := wstep_word hb hE hms' happ
  refine ⟨_, hst, ⟨q, [], cur', by simp, by simp [AllE], ?_, by rw [hcur']; simp⟩,
    Nat.zero_le _, by simpa using hD', by rw [hφ]; simp⟩
  show AllE (Function.update wd.bs q _ (!q))
  rw [update_not]; exact hA

omit [Fintype Q] in
/-- `CD2 S c j → CD2 S c (j + 1)`: an address check of the stored tail. -/
theorem step_CD2_lt {c j : ℕ} {S : List ℕ} {wd : World (Fct Q Γ) (Act Q Γ)}
    (h : CD2 R m S c j wd) (hj : j < m) :
    ∃ wd', WStep (am m n' ι N) wd wd' ∧ CD2 R m S c (j + 1) wd' := by
  obtain ⟨⟨q, E, cur, hb, hE, hA, hms⟩, -, hD, hφ⟩ := h
  have hms' : msOf cur = tails m q (R.cf R.r).tape S +
      {.rb q (m - (j + 1)) (bitsOf c (m - (j + 1))) :: rbsL q 0 (m - (j + 1)) (bitsOf c)} := by
    rw [hms, show m - j = (m - (j + 1)) + 1 by omega, rbsL_zero_succ,
      filter_singleton_of_ne (List.cons_ne_nil _ _)]
  obtain ⟨happ, hD'⟩ := drain_rb (n' := n') (ι := ι) (N := N) (q := q)
    (x := bitsOf c (m - (j + 1))) hj hD
  obtain ⟨cur', hcur', hst⟩ := wstep_word hb hE hms' happ
  refine ⟨_, hst, ⟨q, [], cur', by simp, by simp [AllE], ?_, hcur'⟩, hj, hD', hφ⟩
  show AllE (Function.update wd.bs q _ (!q))
  rw [update_not]; exact hA

omit [Fintype Q] [DecidableEq Q] [DecidableEq Γ] in
/-- `CD2 S c m → CD1 S`: the drain action `drn` after a stored tail has been read. -/
theorem step_CD2_top {c : ℕ} {S : List ℕ} {wd : World (Fct Q Γ) (Act Q Γ)}
    (h : CD2 R m S c m wd) : ∃ wd', WStep (am m n' ι N) wd wd' ∧ CD1 R m S wd' := by
  obtain ⟨⟨q, E, cur, hb, hE, hA, hms⟩, -, hD, hφ⟩ := h
  obtain ⟨happ, hD'⟩ := drain_drn (n' := n') (ι := ι) (N := N) hD
  rw [List.replicate_succ] at hφ
  refine ⟨_, wstep_phi hφ happ, ⟨q, E, [cur], hb, hE, hA, Or.inr ⟨cur, rfl, ?_⟩⟩, hD', rfl⟩
  rw [hms, Nat.sub_self, rbsL_zero_zero, filter_singleton_nil, add_zero]

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] in
/-- `CD1 []`: everything has been consumed. -/
theorem final_CD1 {wd : World (Fct Q Γ) (Act Q Γ)} (h : CD1 R m [] wd) : wd.Final := by
  obtain ⟨⟨q, E, L, hb, hE, hA, hL⟩, -, hφ⟩ := h
  have hq : AllE (wd.bs q) := by
    rcases hL with ⟨rfl, -⟩ | ⟨cur, rfl, hms⟩
    · rw [hb, List.append_nil]; exact hE
    · rw [hb]
      refine allE_append hE fun b hb' => ?_
      rw [List.mem_singleton] at hb'
      subst hb'
      exact allEmpty_iff_msOf.2 (by rw [hms]; rfl)
  refine ⟨fun q' => ?_, by rw [hφ]; rfl⟩
  by_cases h' : q' = q
  · subst h'; exact hq
  · rw [bool_eq_not_of_ne h']; exact hA

end SpaceEnc

end HTN
