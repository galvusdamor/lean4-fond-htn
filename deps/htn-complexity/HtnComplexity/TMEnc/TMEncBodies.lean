import HtnComplexity.TMEnc.TMEncoding
import HtnPlanning.Interleave.ChainSeqYield
/-!
# The method bodies of the Turing-machine encoding

`HtnComplexity/TMEnc/TMEncoding.lean` builds, from a nondeterministic Turing machine `N`, an
input `w` and a time bound `K`, an acyclic HTN planning problem with a totally ordered initial
task network.  This file inverts its method relation: for every compound task of the encoded
domain it says exactly which *totally ordered* bodies it has.

Most tasks of the encoding have a single chain as their body; the exceptions are the tasks that
start parallel processes — the cell counters `checkers i` for `i ≥ 2`, the parallel counting
task `C_k^t` for `k ≥ 2` and the initial task `sI` — which have no totally ordered body at all
(`HTN.TMEnc.not_seqBody_sI`, `HTN.TMEnc.not_seqBody_cPar`).  Those are reached with the
interleaving refinement relations of `HtnPlanning/Interleave/NetYield.lean`.

This is the syntactic half of the simulation argument; the semantic half — what the chains do to
the state — is in `HtnComplexity/TMEnc/TMEncSem.lean`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The totally ordered bodies of the encoded domain -/

/-- The methods of the encoded domain that decompose a task other than `sI` are exactly the
grid bodies of `HTN.TMEnc.bodies`. -/
lemma seqBody_iff {t : TMTask Q Γ} (ht : t ≠ TMTask.sI)
    {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody t xs ↔
      ∃ ls ∈ bodies N w K t, (Method.mk t (TaskNetwork.grid ls)).HasSeqBody xs := by
  constructor
  · rintro ⟨⟨c, tn⟩, hm, hab, hbody⟩
    simp only at hab hbody
    subst hab
    rcases hm with ⟨ls, hls, hsub⟩ | hm
    · simp only at hls hsub
      subst hsub
      exact ⟨ls, hls, hbody⟩
    · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
      exact absurd hm.1 ht
  · rintro ⟨ls, hls, hbody⟩
    exact ⟨⟨t, TaskNetwork.grid ls⟩, Or.inl ⟨ls, hls, rfl⟩, rfl, hbody⟩

/-- A method whose subtask network is the empty grid has the empty body. -/
lemma hasSeqBody_grid_nil {c : TMTask Q Γ} {bs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (Method.mk c
        (TaskNetwork.grid ([] : List (List (TMAct Q Γ ⊕ TMTask Q Γ))))).HasSeqBody bs ↔
      bs = [] :=
  Method.hasSeqBody_of_subtasks_grid_nil rfl

/-- A method whose subtask network is a one-chain grid has that chain as its body. -/
lemma hasSeqBody_grid_single {c : TMTask Q Γ} {l bs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (Method.mk c (TaskNetwork.grid [l])).HasSeqBody bs ↔ bs = l :=
  Method.hasSeqBody_of_subtasks_grid_single rfl

/-! ### The tasks with a single chain as their body -/

lemma seqBody_acquire_iff {x : SyncKind} {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.acquire x) xs ↔
      xs = [Sum.inl (TMAct.call x), Sum.inl (TMAct.wait x)] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_release_iff {x : SyncKind} {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.release x) xs ↔
      xs = [Sum.inl (TMAct.start x), Sum.inl (TMAct.respond x)] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

/-- The body of one produced tape cell: write a symbol, then take part in one cycle of the head
counter and in `K + 1` cycles of each of the two phases of the cell counters. -/
def produceChain (c : Option Γ) (K : ℕ) : List (TMAct Q Γ ⊕ TMTask Q Γ) :=
  [Sum.inl (TMAct.assert c), Sum.inr (TMTask.acquire .head),
    Sum.inr (TMTask.cSeq (TMTask.acquire .check) (K + 1)),
    Sum.inr (TMTask.cSeq (TMTask.acquire .sync) (K + 1))]

lemma seqBody_produce_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.produce xs ↔ ∃ c : Option Γ, xs = produceChain c K := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_setOf_eq] at hls
    obtain ⟨c, rfl⟩ := hls
    exact ⟨c, hasSeqBody_grid_single.1 hbody⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_produceSym_iff {c : Option Γ} {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.produceSym c) xs ↔ xs = produceChain c K := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies, produceChain], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_tapeProduce_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.tapeProduce xs ↔
      xs = [Sum.inr (TMTask.produceSym none), Sum.inr (TMTask.cSeq TMTask.produce K)] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_waitCell_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.waitCell xs ↔
      xs = [Sum.inr (TMTask.release .check), Sum.inr (TMTask.release .sync)] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_waitN_iff {i : ℕ} {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.waitN i) xs ↔
      xs = [Sum.inr (TMTask.cSeq TMTask.waitCell i)] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

/-- The body of one checking cycle of a cell counter: the symbol of the cell is checked, the
counter takes part in the two synchronisation phases, and after `K` waiting cycles the symbol is
checked again — this is what forces the cell to be copied from one tape row to the next. -/
def chkChain (c : Option Γ) (K : ℕ) : List (TMAct Q Γ ⊕ TMTask Q Γ) :=
  [Sum.inl (TMAct.check (TMFact.sym c)), Sum.inr (TMTask.release .sync),
    Sum.inr (TMTask.waitN K), Sum.inr (TMTask.release .check),
    Sum.inl (TMAct.check (TMFact.sym c))]

lemma seqBody_chk_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.chk xs ↔ ∃ c : Option Γ, xs = chkChain c K := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_setOf_eq] at hls
    obtain ⟨c, rfl⟩ := hls
    exact ⟨c, hasSeqBody_grid_single.1 hbody⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_headCell_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.headCell xs ↔
      xs = [Sum.inl (TMAct.start .head), Sum.inl TMAct.assertHead,
        Sum.inl (TMAct.respond .head)] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_noHeadCell_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.noHeadCell xs ↔
      xs = [Sum.inl (TMAct.start .head), Sum.inl TMAct.retractHead,
        Sum.inl (TMAct.respond .head)] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_heads_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.heads xs ↔
      xs = [Sum.inr TMTask.noHeadCell, Sum.inr TMTask.headCell,
        Sum.inr (TMTask.cSeq TMTask.noHeadCell K)] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_transition_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.transition xs ↔
      ∃ (q q' : Q) (c c' : Γ) (m : Move), (q', c', m) ∈ N.step q c ∧
        xs = Sum.inl (TMAct.step q (some c) q' (some c')) ::
          List.replicate (moveExtra m) (Sum.inr (TMTask.acquire .head)) := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_setOf_eq] at hls
    obtain ⟨q, q', c, c', m, hstep, rfl⟩ := hls
    exact ⟨q, q', c, c', m, hstep, hasSeqBody_grid_single.1 hbody⟩
  · rintro ⟨q, q', c, c', m, hstep, rfl⟩
    exact ⟨_, ⟨q, q', c, c', m, hstep, rfl⟩, hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_transitionAndCheck_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.transitionAndCheck xs ↔
      xs = [Sum.inr TMTask.transition, Sum.inr TMTask.chk] ∨
      xs = [Sum.inl (TMAct.check TMFact.noHead), Sum.inr TMTask.chk] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
    rcases hls with rfl | rfl
    · exact Or.inl (hasSeqBody_grid_single.1 hbody)
    · exact Or.inr (hasSeqBody_grid_single.1 hbody)
  · rintro (rfl | rfl)
    · exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩
    · exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_checkers_zero_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.checkers 0) xs ↔ xs = [] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact hasSeqBody_grid_nil.1 hbody
  · rintro rfl
    exact ⟨[], by simp [bodies], hasSeqBody_grid_nil.2 rfl⟩

/-- The body of a single cell counter: it releases the first synchronisation phase, checks its
cell, takes part in `K` transitions and releases the second phase. -/
def checkerChain (K : ℕ) : List (TMAct Q Γ ⊕ TMTask Q Γ) :=
  [Sum.inr (TMTask.release .check), Sum.inr TMTask.chk,
    Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K), Sum.inr (TMTask.release .sync)]

lemma seqBody_checkers_one_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.checkers 1) xs ↔ xs = checkerChain K := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies, checkerChain], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_produceInit_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.produceInit xs ↔
      xs = [Sum.inr (TMTask.produceSym none), Sum.inr (TMTask.produceWord 0),
        Sum.inr (TMTask.cSeq (TMTask.produceSym (some N.blank)) (K - w.length))] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_produceWord_iff {i : ℕ} {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.produceWord i) xs ↔
      (if i + 1 < w.length then
        xs = [Sum.inr (TMTask.produceSym (some (w.getD i N.blank))),
          Sum.inr (TMTask.produceWord (i + 1))]
      else xs = [Sum.inr (TMTask.produceSym (some (w.getD i N.blank)))]) := by
  rw [seqBody_iff (by simp)]
  by_cases h : i + 1 < w.length
  · simp only [if_pos h]
    constructor
    · rintro ⟨ls, hls, hbody⟩
      simp only [bodies, if_pos h, Set.mem_singleton_iff] at hls
      subst hls
      exact hasSeqBody_grid_single.1 hbody
    · rintro rfl
      exact ⟨_, by simp only [bodies, if_pos h, Set.mem_singleton_iff],
        hasSeqBody_grid_single.2 rfl⟩
  · simp only [if_neg h]
    constructor
    · rintro ⟨ls, hls, hbody⟩
      simp only [bodies, if_neg h, Set.mem_singleton_iff] at hls
      subst hls
      exact hasSeqBody_grid_single.1 hbody
    · rintro rfl
      exact ⟨_, by simp only [bodies, if_neg h, Set.mem_singleton_iff],
        hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_done_iff {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody TMTask.done xs ↔
      ∃ f ∈ N.accept, xs = [Sum.inl (TMAct.check (TMFact.st f))] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, Set.mem_setOf_eq] at hls
    obtain ⟨f, hf, rfl⟩ := hls
    exact ⟨f, hf, hasSeqBody_grid_single.1 hbody⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, hasSeqBody_grid_single.2 rfl⟩

/-! ### The sequential counting task -/

lemma seqBody_cSeq_zero_iff {t : TMTask Q Γ} {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.cSeq t 0) xs ↔ xs = [] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact hasSeqBody_grid_nil.1 hbody
  · rintro rfl
    exact ⟨[], by simp [bodies], hasSeqBody_grid_nil.2 rfl⟩

lemma seqBody_cSeq_one_iff {t : TMTask Q Γ} {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.cSeq t 1) xs ↔ xs = [Sum.inr t] := by
  rw [seqBody_iff (by simp)]
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    exact ⟨_, by simp [bodies], hasSeqBody_grid_single.2 rfl⟩

lemma seqBody_cSeq_even_iff {t : TMTask Q Γ} {k : ℕ} (hk : 2 ≤ k) (he : k % 2 = 0)
    {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.cSeq t k) xs ↔
      xs = [Sum.inr (TMTask.cSeq t (k / 2)), Sum.inr (TMTask.cSeq t (k / 2))] := by
  rw [seqBody_iff (by simp)]
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg h0, if_neg h1, if_pos he, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    refine ⟨_, ?_, hasSeqBody_grid_single.2 rfl⟩
    simp only [bodies, if_neg h0, if_neg h1, if_pos he, Set.mem_singleton_iff]

lemma seqBody_cSeq_odd_iff {t : TMTask Q Γ} {k : ℕ} (hk : 2 ≤ k) (he : k % 2 ≠ 0)
    {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)} :
    (domain N w K).SeqBody (TMTask.cSeq t k) xs ↔
      xs = [Sum.inr t, Sum.inr (TMTask.cSeq t (k - 1))] := by
  rw [seqBody_iff (by simp)]
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  constructor
  · rintro ⟨ls, hls, hbody⟩
    simp only [bodies, if_neg h0, if_neg h1, if_neg he, Set.mem_singleton_iff] at hls
    subst hls
    exact hasSeqBody_grid_single.1 hbody
  · rintro rfl
    refine ⟨_, ?_, hasSeqBody_grid_single.2 rfl⟩
    simp only [bodies, if_neg h0, if_neg h1, if_neg he, Set.mem_singleton_iff]

/-! ### Inverting the refinement relation -/

section Inversion

variable {F' A' C' I' : Type} {E : Domain F' A' C' I'}

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

/-- A refinement of a single compound task is a refinement of the body of one of its methods. -/
lemma yieldSeq_singleton_inr_iff {c : C'} {as : List A'} :
    E.YieldSeq [Sum.inr c] as ↔ ∃ bs, E.SeqBody c bs ∧ E.YieldSeq bs as := by
  rw [yieldSeq_inr_cons_iff]
  simp

end Inversion

/-! ### The sequential counting task counts

`C^k_t` refines into exactly the concatenations of `k` refinements of `t`. -/

/-- `k` refinements of `t`, concatenated. -/
def IsCount (D : Domain (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)) (t : TMTask Q Γ)
    (k : ℕ) (as : List (TMAct Q Γ)) : Prop :=
  ∃ ass : List (List (TMAct Q Γ)), ass.length = k ∧
    (∀ bs ∈ ass, D.YieldSeq [Sum.inr t] bs) ∧ as = ass.flatten

lemma isCount_zero {D : Domain (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)} {t : TMTask Q Γ}
    {as : List (TMAct Q Γ)} : IsCount D t 0 as ↔ as = [] := by
  constructor
  · rintro ⟨ass, hlen, -, rfl⟩
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    simp
  · rintro rfl
    exact ⟨[], rfl, by simp, by simp⟩

lemma isCount_add {D : Domain (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)} {t : TMTask Q Γ}
    {k l : ℕ} {as bs : List (TMAct Q Γ)} (hk : IsCount D t k as) (hl : IsCount D t l bs) :
    IsCount D t (k + l) (as ++ bs) := by
  obtain ⟨ass, hlen, hall, rfl⟩ := hk
  obtain ⟨bss, hlen', hall', rfl⟩ := hl
  refine ⟨ass ++ bss, by simp [hlen, hlen'], ?_, by simp⟩
  intro cs hcs
  rcases List.mem_append.1 hcs with h | h
  · exact hall cs h
  · exact hall' cs h

lemma isCount_split {D : Domain (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)} {t : TMTask Q Γ}
    {k l : ℕ} {as : List (TMAct Q Γ)} (h : IsCount D t (k + l) as) :
    ∃ as₁ as₂, as = as₁ ++ as₂ ∧ IsCount D t k as₁ ∧ IsCount D t l as₂ := by
  obtain ⟨ass, hlen, hall, rfl⟩ := h
  refine ⟨(ass.take k).flatten, (ass.drop k).flatten, ?_,
    ⟨ass.take k, by simp [hlen], fun bs hbs => hall bs (List.mem_of_mem_take hbs), rfl⟩,
    ⟨ass.drop k, by simp [hlen], fun bs hbs => hall bs (List.mem_of_mem_drop hbs), rfl⟩⟩
  rw [← List.flatten_append, List.take_append_drop]

lemma isCount_one {D : Domain (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)} {t : TMTask Q Γ}
    {as : List (TMAct Q Γ)} : IsCount D t 1 as ↔ D.YieldSeq [Sum.inr t] as := by
  constructor
  · rintro ⟨ass, hlen, hall, rfl⟩
    match ass, hlen with
    | [bs], _ => simpa using hall bs (by simp)
  · intro h
    exact ⟨[as], rfl, by simpa using h, by simp⟩

/-- **The sequential counting task counts.**  A refinement of `C^k_t` is exactly a concatenation
of `k` refinements of `t`. -/
theorem yieldSeq_cSeq_iff (t : TMTask Q Γ) :
    ∀ (k : ℕ) (as : List (TMAct Q Γ)),
      (domain N w K).YieldSeq [Sum.inr (TMTask.cSeq t k)] as ↔ IsCount (domain N w K) t k as := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro as
    match k, ih with
    | 0, _ =>
        rw [yieldSeq_singleton_inr_iff, isCount_zero]
        constructor
        · rintro ⟨bs, hbs, hy⟩
          rw [seqBody_cSeq_zero_iff] at hbs
          subst hbs
          simpa using hy
        · rintro rfl
          exact ⟨[], seqBody_cSeq_zero_iff.2 rfl, Domain.YieldSeq.nil⟩
    | 1, _ =>
        rw [yieldSeq_singleton_inr_iff, isCount_one]
        constructor
        · rintro ⟨bs, hbs, hy⟩
          rw [seqBody_cSeq_one_iff] at hbs
          subst hbs
          exact hy
        · intro hy
          exact ⟨_, seqBody_cSeq_one_iff.2 rfl, hy⟩
    | (n + 2), ih =>
        set k := n + 2 with hk
        have hk2 : 2 ≤ k := by omega
        by_cases he : k % 2 = 0
        · have hhalf : k / 2 < k := by omega
          have hsum : k / 2 + k / 2 = k := by omega
          rw [yieldSeq_singleton_inr_iff]
          constructor
          · rintro ⟨bs, hbs, hy⟩
            rw [seqBody_cSeq_even_iff hk2 he] at hbs
            subst hbs
            obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ :=
              (show (domain N w K).YieldSeq
                ([Sum.inr (TMTask.cSeq t (k / 2))] ++ [Sum.inr (TMTask.cSeq t (k / 2))]) as from
                by simpa using hy).split
            rw [← hsum]
            exact isCount_add ((ih _ hhalf _).1 h₁) ((ih _ hhalf _).1 h₂)
          · intro hc
            rw [← hsum] at hc
            obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := isCount_split hc
            refine ⟨_, (seqBody_cSeq_even_iff hk2 he).2 rfl, ?_⟩
            have := ((ih _ hhalf _).2 h₁).append ((ih _ hhalf _).2 h₂)
            simpa using this
        · have hpred : k - 1 < k := by omega
          have hsum : 1 + (k - 1) = k := by omega
          rw [yieldSeq_singleton_inr_iff]
          constructor
          · rintro ⟨bs, hbs, hy⟩
            rw [seqBody_cSeq_odd_iff hk2 he] at hbs
            subst hbs
            obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ :=
              (show (domain N w K).YieldSeq
                ([Sum.inr t] ++ [Sum.inr (TMTask.cSeq t (k - 1))]) as from by simpa using hy).split
            rw [← hsum]
            exact isCount_add (isCount_one.2 h₁) ((ih _ hpred _).1 h₂)
          · intro hc
            rw [← hsum] at hc
            obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := isCount_split hc
            refine ⟨_, (seqBody_cSeq_odd_iff hk2 he).2 rfl, ?_⟩
            have := (isCount_one.1 h₁).append ((ih _ hpred _).2 h₂)
            simpa using this

end TMEnc

end HTN
