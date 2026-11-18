import HtnComplexity.ToHtnAc.ToHtnAcFinset
import HtnPlanning.Binarisation.Binarisation
/-!
# The method bodies of the TO-HTN ⟶ HTN-AC compilation

`HtnComplexity/ToHtnAc/ToHtnAc.lean` builds, from a totally ordered HTN problem, an acyclic one.
This file inverts its method relation: for every compound task of the compiled domain except
the parallel counting task `𝔠^k_t` and the initial task `t_I`, all method bodies are *single
chains*, and `HTN.ToAc.seqBody_iff` together with the `HTN.ToAc.seqBody_*_iff` family says
exactly which chains these are.  It also contains the inversion lemmas for the refinement
relation `HTN.Domain.YieldSeq` itself.  The last section marks the boundary of that inventory:
the parallel counting task `𝔠^k` and the initial task `t_I` have methods with genuinely
parallel bodies, and those methods have no totally ordered body at all
(`HTN.ToAc.not_seqBody_tI`), so a refinement relation admitting arbitrary interleavings is
needed to reach them.

The semantic half of the simulation — what those chains *do* to the state — is in
`HtnComplexity/ToHtnAc/ToHtnAcSim.lean`.
-/

namespace HTN

namespace ToAc

universe u v w x

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

/-! ### Inverting the refinement relation -/

section Inversion

variable {F' : Type u} {A' : Type v} {C' : Type w} {I' : Type x} {E : Domain F' A' C' I'}

@[simp] lemma yieldSeq_nil_iff {as : List A'} : E.YieldSeq [] as ↔ as = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact Domain.YieldSeq.nil

lemma yieldSeq_inl_cons_iff {a : A'} {xs : List (A' ⊕ C')} {as : List A'} :
    E.YieldSeq (Sum.inl a :: xs) as ↔ ∃ as', as = a :: as' ∧ E.YieldSeq xs as' := by
  constructor
  · intro h; cases h with | prim h => exact ⟨_, rfl, h⟩
  · rintro ⟨as', rfl, h⟩; exact Domain.YieldSeq.prim h

lemma yieldSeq_inr_cons_iff {c : C'} {xs : List (A' ⊕ C')} {as : List A'} :
    E.YieldSeq (Sum.inr c :: xs) as ↔ ∃ bs, E.SeqBody c bs ∧ E.YieldSeq (bs ++ xs) as := by
  constructor
  · intro h; cases h with | comp hm h => exact ⟨_, hm, h⟩
  · rintro ⟨bs, hm, h⟩; exact Domain.YieldSeq.comp hm h

end Inversion

/-! ### The bodies of the compiled tasks -/

/-- A method whose subtask network is the empty grid has the empty body. -/
lemma hasSeqBody_grid_nil {c : AcTask F A C} {bs : List (AcAct F A C ⊕ AcTask F A C)} :
    (Method.mk c (TaskNetwork.grid ([] : List (List (AcAct F A C ⊕ AcTask F A C))))).HasSeqBody bs
      ↔ bs = [] := by
  constructor
  · rintro ⟨l, hlin, hmap, -⟩
    have hl : l = [] := by
      rcases l with _ | ⟨x, l⟩
      · rfl
      · exact absurd ((hlin.2.1 x).1 (by simp)) (by simp [TaskNetwork.grid])
    subst hl
    simpa using hmap.symm
  · rintro rfl
    exact ⟨[], ⟨List.nodup_nil, by intro x; simp [TaskNetwork.grid], List.Pairwise.nil⟩, rfl,
      List.Pairwise.nil⟩

/-- The totally ordered bodies of the compiled domain are the single-chain bodies of
`HTN.ToAc.bodies`. -/
lemma seqBody_iff {t : AcTask F A C} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody t xs ↔
      ∃ ls ∈ bodies D vars bound t, (Method.mk t (TaskNetwork.grid ls)).HasSeqBody xs := by
  constructor
  · rintro ⟨⟨c, tn⟩, ⟨ls, hls, hsub⟩, hab, hbody⟩
    simp only at hab hsub hls hbody
    subst hab
    subst hsub
    exact ⟨ls, hls, hbody⟩
  · rintro ⟨ls, hls, hbody⟩
    exact ⟨⟨t, TaskNetwork.grid ls⟩, ⟨ls, hls, rfl⟩, rfl, hbody⟩

lemma seqBody_SEL_iff {i : Fin 5} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.SEL i) xs ↔
      xs = [Sum.inr (AcTask.SELn vars.length i)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact TaskNetwork.hasSeqBody_seq_iff.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩

lemma seqBody_SELn_zero_iff {i : Fin 5} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.SELn 0 i) xs ↔ xs = [] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact hasSeqBody_grid_nil.1 hbody
  · rintro rfl
    exact ⟨[], by simp [bodies], hasSeqBody_grid_nil.2 rfl⟩

lemma seqBody_SELn_succ_iff {n : ℕ} {i : Fin 5} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.SELn (n + 1) i) xs ↔
      ∃ v ∈ vars[n]?, xs = [Sum.inl (AcAct.setV v i), Sum.inr (AcTask.SELn n i)] ∨
        xs = [Sum.inl (AcAct.delV v i), Sum.inr (AcTask.SELn n i)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel] at hls
    obtain ⟨v, hv, rfl | rfl⟩ := hls
    · exact ⟨v, hv, Or.inl (TaskNetwork.hasSeqBody_seq_iff.1 hbody)⟩
    · exact ⟨v, hv, Or.inr (TaskNetwork.hasSeqBody_seq_iff.1 hbody)⟩
  · rintro ⟨v, hv, rfl | rfl⟩
    · refine ⟨[[Sum.inl (AcAct.setV v i), Sum.inr (AcTask.SELn n i)]], ?_,
        TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact ⟨v, hv, Or.inl rfl⟩
    · refine ⟨[[Sum.inl (AcAct.delV v i), Sum.inr (AcTask.SELn n i)]], ?_,
        TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact ⟨v, hv, Or.inr rfl⟩

lemma seqBody_EQ_iff {i j : Fin 5} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.EQ i j) xs ↔
      xs = [Sum.inr (AcTask.EQn vars.length i j)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact TaskNetwork.hasSeqBody_seq_iff.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩

lemma seqBody_EQn_zero_iff {i j : Fin 5} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.EQn 0 i j) xs ↔ xs = [] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact hasSeqBody_grid_nil.1 hbody
  · rintro rfl
    exact ⟨[], by simp [bodies], hasSeqBody_grid_nil.2 rfl⟩

lemma seqBody_EQn_succ_iff {n : ℕ} {i j : Fin 5} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.EQn (n + 1) i j) xs ↔
      ∃ v ∈ vars[n]?, xs = [Sum.inl (AcAct.prePV v i j), Sum.inr (AcTask.EQn n i j)] ∨
        xs = [Sum.inl (AcAct.preNV v i j), Sum.inr (AcTask.EQn n i j)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel] at hls
    obtain ⟨v, hv, rfl | rfl⟩ := hls
    · exact ⟨v, hv, Or.inl (TaskNetwork.hasSeqBody_seq_iff.1 hbody)⟩
    · exact ⟨v, hv, Or.inr (TaskNetwork.hasSeqBody_seq_iff.1 hbody)⟩
  · rintro ⟨v, hv, rfl | rfl⟩
    · refine ⟨[[Sum.inl (AcAct.prePV v i j), Sum.inr (AcTask.EQn n i j)]], ?_,
        TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact ⟨v, hv, Or.inl rfl⟩
    · refine ⟨[[Sum.inl (AcAct.preNV v i j), Sum.inr (AcTask.EQn n i j)]], ?_,
        TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact ⟨v, hv, Or.inr rfl⟩

/-! ### The counting task `𝔠̄^k_t`

`AcTask.cnt t k` is the *sequential* counting task: it is meant to refine into any number
`m ≤ k` of consecutive copies of `t`, using only `O(log k)` methods.  Its methods implement the
usual binary recursion (`k` even: two halves; `k` odd: one copy of `t` followed by `k-1`, or
just `k-1`), and `HTN.ToAc.yieldSeq_cnt_iff` below states that the recursion is correct.
-/

lemma seqBody_cnt_zero_iff {t : AcTask F A C} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.cnt t 0) xs ↔ xs = [] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact hasSeqBody_grid_nil.1 hbody
  · rintro rfl
    exact ⟨[], by simp [bodies], hasSeqBody_grid_nil.2 rfl⟩

lemma seqBody_cnt_one_iff {t : AcTask F A C} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.cnt t 1) xs ↔ xs = [Sum.inr t] ∨ xs = [] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, reduceIte] at hls
    rcases hls with rfl | rfl
    · exact Or.inl (TaskNetwork.hasSeqBody_seq_iff.1 hbody)
    · exact Or.inr (hasSeqBody_grid_nil.1 hbody)
  · rintro (rfl | rfl)
    · exact ⟨[[Sum.inr t]], by simp [bodies], TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
    · exact ⟨[], by simp [bodies], hasSeqBody_grid_nil.2 rfl⟩

lemma seqBody_cnt_even_iff {t : AcTask F A C} {k : ℕ} (hk : 2 ≤ k) (he : k % 2 = 0)
    {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.cnt t k) xs ↔
      xs = [Sum.inr (AcTask.cnt t (k / 2)), Sum.inr (AcTask.cnt t (k / 2))] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg h0, if_neg h1, if_pos he, Set.mem_singleton_iff] at hls
    subst hls
    exact TaskNetwork.hasSeqBody_seq_iff.1 hbody
  · rintro rfl
    refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
    simp only [bodies, if_neg h0, if_neg h1, if_pos he, Set.mem_singleton_iff]

lemma seqBody_cnt_odd_iff {t : AcTask F A C} {k : ℕ} (hk : 2 ≤ k) (ho : k % 2 = 1)
    {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.cnt t k) xs ↔
      xs = [Sum.inr t, Sum.inr (AcTask.cnt t (k - 1))] ∨
        xs = [Sum.inr (AcTask.cnt t (k - 1))] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  have h2 : ¬ (k % 2 = 0) := by omega
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg h0, if_neg h1, if_neg h2, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hls
    rcases hls with rfl | rfl
    · exact Or.inl (TaskNetwork.hasSeqBody_seq_iff.1 hbody)
    · exact Or.inr (TaskNetwork.hasSeqBody_seq_iff.1 hbody)
  · rintro (rfl | rfl)
    · refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg h0, if_neg h1, if_neg h2, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
    · refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg h0, if_neg h1, if_neg h2, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto

/-! ### The bodies of the remaining compiled tasks

For completeness, the same inventory for the tasks `STATE_n^1`, `STATE_n^3`, `MEM`, `WRITE`,
`READ` and `TUPLE`.  All of them have single-chain bodies, so `HTN.Domain.SeqBody` describes
them exactly.
-/

lemma seqBody_STATE1_zero_iff {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.STATE1 0) xs ↔
      xs = [Sum.inr (AcTask.STATE3 vars.length)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact TaskNetwork.hasSeqBody_seq_iff.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩

lemma seqBody_STATE1_succ_iff {n : ℕ} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.STATE1 (n + 1)) xs ↔
      ∃ v ∈ vars[n]?,
        xs = [Sum.inl (AcAct.prePV v 0 0), Sum.inr (AcTask.STATE1 n),
              Sum.inl (AcAct.setV v 3)] ∨
        xs = [Sum.inl (AcAct.preNV v 0 0), Sum.inr (AcTask.STATE1 n),
              Sum.inl (AcAct.delV v 3)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel] at hls
    obtain ⟨v, hv, rfl | rfl⟩ := hls
    · exact ⟨v, hv, Or.inl (TaskNetwork.hasSeqBody_seq_iff.1 hbody)⟩
    · exact ⟨v, hv, Or.inr (TaskNetwork.hasSeqBody_seq_iff.1 hbody)⟩
  · rintro ⟨v, hv, rfl | rfl⟩
    · refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact ⟨v, hv, Or.inl rfl⟩
    · refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact ⟨v, hv, Or.inr rfl⟩

lemma seqBody_STATE3_zero_iff {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.STATE3 0) xs ↔
      ∃ t : A ⊕ C, xs = [Sum.inl (AcAct.preC t), Sum.inl (AcAct.doneA RW.write),
        Sum.inl (AcAct.accept RW.read), Sum.inl (AcAct.setC t)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    obtain ⟨t, rfl⟩ := hls
    exact ⟨t, TaskNetwork.hasSeqBody_seq_iff.1 hbody⟩
  · rintro ⟨t, rfl⟩
    refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
    simp only [bodies]
    exact ⟨t, rfl⟩

lemma seqBody_STATE3_succ_iff {n : ℕ} {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.STATE3 (n + 1)) xs ↔
      ∃ v ∈ vars[n]?,
        xs = [Sum.inl (AcAct.prePV v 2 2), Sum.inr (AcTask.STATE3 n),
              Sum.inl (AcAct.setV v 4)] ∨
        xs = [Sum.inl (AcAct.preNV v 2 2), Sum.inr (AcTask.STATE3 n),
              Sum.inl (AcAct.delV v 4)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel] at hls
    obtain ⟨v, hv, rfl | rfl⟩ := hls
    · exact ⟨v, hv, Or.inl (TaskNetwork.hasSeqBody_seq_iff.1 hbody)⟩
    · exact ⟨v, hv, Or.inr (TaskNetwork.hasSeqBody_seq_iff.1 hbody)⟩
  · rintro ⟨v, hv, rfl | rfl⟩
    · refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact ⟨v, hv, Or.inl rfl⟩
    · refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      exact ⟨v, hv, Or.inr rfl⟩

lemma seqBody_MEM_iff {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody AcTask.MEM xs ↔
      xs = [Sum.inl (AcAct.accept RW.write), Sum.inr (AcTask.STATE1 vars.length),
        Sum.inl (AcAct.doneA RW.read)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact TaskNetwork.hasSeqBody_seq_iff.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩

lemma seqBody_WRITE_iff {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.WRITE : AcTask F A C) xs ↔
      xs = [Sum.inl (AcAct.ask RW.write), Sum.inl (AcAct.waitA RW.write)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact TaskNetwork.hasSeqBody_seq_iff.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩

lemma seqBody_READ_iff {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.READ : AcTask F A C) xs ↔
      xs = [Sum.inl (AcAct.ask RW.read), Sum.inl (AcAct.waitA RW.read)] := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact TaskNetwork.hasSeqBody_seq_iff.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩

lemma seqBody_TUPLE_iff {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody AcTask.TUPLE xs ↔
      (∃ (c : C) (x y : A ⊕ C), D.SeqBody c [x, y] ∧ xs =
        [Sum.inl AcAct.lock, Sum.inr (AcTask.SEL 0), Sum.inr (AcTask.SEL 1),
         Sum.inr (AcTask.SEL 2), Sum.inr AcTask.READ, Sum.inr (AcTask.EQ 0 3),
         Sum.inr (AcTask.EQ 1 4), Sum.inl (AcAct.preC x), Sum.inr AcTask.READ,
         Sum.inr (AcTask.EQ 1 3), Sum.inr (AcTask.EQ 2 4), Sum.inl (AcAct.preC y),
         Sum.inl (AcAct.setC (Sum.inr c)), Sum.inr (AcTask.cnt AcTask.WRITE bound),
         Sum.inl AcAct.unlock]) ∨
      (∃ o : A, xs =
        [Sum.inl AcAct.lock, Sum.inr (AcTask.SEL 0), Sum.inr (AcTask.SEL 1),
         Sum.inr (AcTask.SEL 2), Sum.inr (AcTask.EQ 0 1), Sum.inl (AcAct.op2 o),
         Sum.inr (AcTask.EQ 1 2), Sum.inl (AcAct.setC (Sum.inl o)),
         Sum.inr (AcTask.cnt AcTask.WRITE bound), Sum.inl AcAct.unlock]) := by
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_union, Set.mem_setOf_eq] at hls
    rcases hls with ⟨c, x, y, hD, rfl⟩ | ⟨o, rfl⟩
    · exact Or.inl ⟨c, x, y, hD, TaskNetwork.hasSeqBody_seq_iff.1 hbody⟩
    · exact Or.inr ⟨o, TaskNetwork.hasSeqBody_seq_iff.1 hbody⟩
  · rintro (⟨c, x, y, hD, rfl⟩ | ⟨o, rfl⟩)
    · refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, Set.mem_union, Set.mem_setOf_eq]
      exact Or.inl ⟨c, x, y, hD, rfl⟩
    · refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
      simp only [bodies, Set.mem_union, Set.mem_setOf_eq]
      exact Or.inr ⟨o, rfl⟩

/-! ### The boundary: the parallel tasks have no totally ordered body

The counting task `𝔠^k` and the initial task `t_I` are the two tasks of the construction whose
methods have genuinely *parallel* bodies.  `Method.HasSeqBody` demands a linearization that is
totally ordered, so such a method has no body at all, and consequently `Domain.SeqBody` — and
with it the refinement relation `Domain.YieldSeq` — does not see those methods.  This is why
the simulation lemmas of `HtnComplexity/ToHtnAc/ToHtnAcSim.lean` stop at the memory cells and the
proof steps, and why the global argument needs a refinement relation that admits arbitrary
interleavings.
-/

/-- A method whose subtask network is a grid with two non-empty rows has no totally ordered
body: the first tasks of the two rows are incomparable. -/
lemma not_hasSeqBody_grid_pair {A' C' : Type} [Inhabited A'] {c : C'}
    {l₁ l₂ : List (A' ⊕ C')}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {bs : List (A' ⊕ C')} :
    ¬ (Method.mk c (TaskNetwork.grid [l₁, l₂])).HasSeqBody bs := by
  rintro ⟨l, hlin, -, hpair⟩
  have hm₁ : ((0, 0) : ℕ × ℕ) ∈ (TaskNetwork.grid [l₁, l₂]).T := by
    rw [TaskNetwork.mem_grid_T]
    exact ⟨by simp, by simpa using List.length_pos_of_ne_nil h₁⟩
  have hm₂ : ((1, 0) : ℕ × ℕ) ∈ (TaskNetwork.grid [l₁, l₂]).T := by
    rw [TaskNetwork.mem_grid_T]
    exact ⟨by simp, by simpa using List.length_pos_of_ne_nil h₂⟩
  have hl₁ : ((0, 0) : ℕ × ℕ) ∈ l := (hlin.2.1 _).2 hm₁
  have hl₂ : ((1, 0) : ℕ × ℕ) ∈ l := (hlin.2.1 _).2 hm₂
  have hsym : Symmetric (fun p q : ℕ × ℕ => (TaskNetwork.grid [l₁, l₂]).ord p q ∨
      (TaskNetwork.grid [l₁, l₂]).ord q p) := fun _ _ h => h.symm
  have := (hpair.imp Or.inl).forall hsym hl₁ hl₂ (by simp)
  rcases this with h | h <;> · rw [TaskNetwork.grid_ord] at h; simp at h

lemma not_seqBody_cntPar_even {t : AcTask F A C} {k : ℕ} (hk : 2 ≤ k) (he : k % 2 = 0)
    {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    ¬ (domain D vars bound).SeqBody (AcTask.cntPar t k) xs := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  rw [seqBody_iff]
  rintro ⟨ls, hls, hbody⟩
  simp only [bodies, if_neg h0, if_neg h1, if_pos he, Set.mem_singleton_iff] at hls
  subst hls
  exact not_hasSeqBody_grid_pair (by simp) (by simp) hbody

lemma seqBody_cntPar_odd_iff {t : AcTask F A C} {k : ℕ} (hk : 2 ≤ k) (ho : k % 2 = 1)
    {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    (domain D vars bound).SeqBody (AcTask.cntPar t k) xs ↔
      xs = [Sum.inr (AcTask.cntPar t (k - 1))] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  have h2 : ¬ (k % 2 = 0) := by omega
  rw [seqBody_iff]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg h0, if_neg h1, if_neg h2, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hls
    rcases hls with rfl | rfl
    · exact absurd hbody (not_hasSeqBody_grid_pair (by simp) (by simp))
    · exact TaskNetwork.hasSeqBody_seq_iff.1 hbody
  · rintro rfl
    refine ⟨_, ?_, TaskNetwork.hasSeqBody_seq_iff.2 rfl⟩
    simp only [bodies, if_neg h0, if_neg h1, if_neg h2, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto

/-- The initial task of the compiled problem has no totally ordered body: its unique method
runs the memory cells and the proof steps *in parallel*. -/
lemma not_seqBody_tI {xs : List (AcAct F A C ⊕ AcTask F A C)} :
    ¬ (domain D vars bound).SeqBody (AcTask.tI : AcTask F A C) xs := by
  rw [seqBody_iff]
  rintro ⟨ls, hls, hbody⟩
  simp only [bodies] at hls
  subst hls
  exact not_hasSeqBody_grid_pair (by simp) (by simp) hbody

end ToAc

end HTN
