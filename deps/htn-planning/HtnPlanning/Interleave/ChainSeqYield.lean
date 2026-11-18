import HtnPlanning.Interleave.GridYield
import HtnPlanning.Binarisation.Binarisation
/-!
# Chains whose methods are chains: the interleaving and the totally ordered refinement agree

`HtnPlanning/Interleave/GridYield.lean` describes the refinements of a grid by the interleaving
relations `HTN.Domain.ChainYield` / `HTN.Domain.GridYield`, while
`HtnPlanning/Core/TONormalForm.lean` describes the refinements of a *totally ordered* task
sequence by `HTN.Domain.YieldSeq`.  If all the methods that can be applied while refining a
chain have a single chain as their body — which is the case for every compound task of the
HTN-AC compilation except the two parallel counting tasks and the initial task — then the two
relations coincide.

* `HTN.Domain.ChainClosed D S` — every grid body of a compound task in `S` is a single chain (or
  the empty grid), whose compound tasks are again in `S`;
* `HTN.Domain.chainYield_iff_yieldSeq` — for a chain all of whose compound tasks lie in such an
  `S`, `D.ChainYield xs as ↔ D.YieldSeq xs as`.

This makes the gadget-level simulation lemmas of `HtnComplexity/ToHtnAc/ToHtnAcSim.lean`, which are
stated for `YieldSeq`, available for the interleaving refinement relation in which the plans of
the compiled problem are described.
-/

namespace HTN

universe u v w

variable {F : Type u} {A : Type v} {C : Type w} [Inhabited A]

open TaskNetwork

omit [Inhabited A] in
/-- Having a totally ordered body depends only on the subtask network. -/
lemma Method.hasSeqBody_congr {I : Type*} {m m' : Method I A C} (h : m.subtasks = m'.subtasks)
    {bs : List (A ⊕ C)} : m.HasSeqBody bs ↔ m'.HasSeqBody bs := by
  simp only [Method.HasSeqBody, h]

/-- A method whose subtask network is a one-chain grid has that chain as its body. -/
lemma Method.hasSeqBody_of_subtasks_grid_single {m : Method (ℕ × ℕ) A C}
    {l bs : List (A ⊕ C)} (h : m.subtasks = TaskNetwork.grid [l]) :
    m.HasSeqBody bs ↔ bs = l :=
  (Method.hasSeqBody_congr (m' := Method.mk m.abstractTask (TaskNetwork.seq l)) h).trans
    TaskNetwork.hasSeqBody_seq_iff

/-- A method whose subtask network is the empty grid has the empty body. -/
lemma Method.hasSeqBody_of_subtasks_grid_nil {m : Method (ℕ × ℕ) A C} {bs : List (A ⊕ C)}
    (h : m.subtasks = TaskNetwork.grid ([] : List (List (A ⊕ C)))) :
    m.HasSeqBody bs ↔ bs = [] := by
  constructor
  · rintro ⟨l, hlin, hmap, -⟩
    have hl : l = [] := by
      rcases l with _ | ⟨x, l⟩
      · rfl
      · have hx := (hlin.2.1 x).1 (by simp)
        rw [h] at hx
        simp at hx
    subst hl
    simpa using hmap.symm
  · rintro rfl
    refine ⟨[], ⟨List.nodup_nil, ?_, List.Pairwise.nil⟩, rfl, List.Pairwise.nil⟩
    intro x
    rw [h]
    simp

namespace Domain

variable {D : Domain F A C (ℕ × ℕ)}

/-- Every grid body of a compound task in `S` is (the grid of) a single chain, and the compound
tasks occurring in that chain are again in `S`.  Note that the empty grid is the grid of the
empty chain (`HTN.TaskNetwork.grid_nil_eq_grid_cons_nil`), so bodies without subtasks are
covered as well. -/
def ChainClosed (D : Domain F A C (ℕ × ℕ)) (S : Set C) : Prop :=
  ∀ c ∈ S, ∀ ls : List (List (A ⊕ C)), D.GridBody c ls →
    ∃ l, TaskNetwork.grid ls = TaskNetwork.grid [l] ∧ ∀ c' : C, Sum.inr c' ∈ l → c' ∈ S

/-! ### Passing between grid bodies and totally ordered bodies -/

lemma seqBody_of_gridBody {c : C} {ls : List (List (A ⊕ C))} {l : List (A ⊕ C)}
    (h : D.GridBody c ls) (he : TaskNetwork.grid ls = TaskNetwork.grid [l]) : D.SeqBody c l := by
  obtain ⟨m, hm, hmc, hsub⟩ := h
  rw [he] at hsub
  exact ⟨m, hm, hmc, (Method.hasSeqBody_of_subtasks_grid_single hsub).2 rfl⟩

lemma gridBody_single_of_gridBody {c : C} {ls : List (List (A ⊕ C))} {l : List (A ⊕ C)}
    (h : D.GridBody c ls) (he : TaskNetwork.grid ls = TaskNetwork.grid [l]) :
    D.GridBody c [l] := by
  obtain ⟨m, hm, hmc, hsub⟩ := h
  rw [he] at hsub
  exact ⟨m, hm, hmc, hsub⟩

/-- For a domain with grid methods and a chain-closed set of compound tasks, a totally ordered
body comes from a one-chain (or empty) grid body. -/
lemma gridBody_of_seqBody (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {S : Set C} (hcc : ChainClosed D S) {c : C} (hc : c ∈ S) {bs : List (A ⊕ C)}
    (h : D.SeqBody c bs) : D.GridBody c [bs] := by
  obtain ⟨m, hm, hmc, hbody⟩ := h
  obtain ⟨ls, hls⟩ := hgrid m hm
  have hgb : D.GridBody c ls := ⟨m, hm, hmc, hls⟩
  obtain ⟨l, he, -⟩ := hcc c hc ls hgb
  rw [he] at hls
  have : bs = l := (Method.hasSeqBody_of_subtasks_grid_single hls).1 hbody
  subst this
  exact ⟨m, hm, hmc, hls⟩

/-- The compound tasks of a one-chain body of a task in `S` are again in `S`. -/
lemma mem_of_gridBody_single {S : Set C} (hcc : ChainClosed D S) {c : C} (hc : c ∈ S)
    {l : List (A ⊕ C)} (h : D.GridBody c [l]) {c' : C} (hc' : Sum.inr c' ∈ l) : c' ∈ S := by
  obtain ⟨l', he, hmem⟩ := hcc c hc [l] h
  have : l = l' := TaskNetwork.grid_single_inj he
  subst this
  exact hmem c' hc'

/-! ### The two refinement relations agree -/

/-- **Every interleaving refinement of a chain-closed chain is a totally ordered
refinement.** -/
theorem yieldSeq_of_chainYieldN (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {S : Set C} (hcc : ChainClosed D S) :
    ∀ n : ℕ, ∀ n' ≤ n, ∀ (xs : List (A ⊕ C)) (as : List A),
      (∀ c : C, Sum.inr c ∈ xs → c ∈ S) → D.ChainYieldN n' xs as → D.YieldSeq xs as := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro n' hn' xs
    induction xs generalizing n' with
    | nil =>
        intro as _ h
        rw [chainYieldN_nil_iff] at h
        obtain ⟨-, rfl⟩ := h
        exact YieldSeq.nil
    | cons x xs ih =>
        intro as hS h
        cases x with
        | inl a =>
            obtain ⟨as', rfl, h'⟩ := chainYieldN_cons_inl_iff.1 h
            exact YieldSeq.prim (ih n' hn' as' (fun c hc => hS c (by simp [hc])) h')
        | inr c =>
            obtain ⟨k, n₂, ls, bs, as', rfl, hm, hb, ht, rfl⟩ := chainYieldN_cons_inr_iff.1 h
            have hcS : c ∈ S := hS c (by simp)
            have hrest : D.YieldSeq xs as' :=
              ih n₂ (by omega) as' (fun c' hc' => hS c' (by simp [hc'])) ht
            obtain ⟨l, he, hmem⟩ := hcc c hcS ls hm
            rw [gridYieldN_congr hgrid he] at hb
            obtain ⟨k₁, k₂, bs₁, bs₂, rfl, hc₁, hc₂, hint⟩ := gridYieldN_cons_iff.1 hb
            rw [gridYieldN_nil_iff] at hc₂
            obtain ⟨rfl, rfl⟩ := hc₂
            rw [hint.eq_of_nil_right]
            have hbody : D.YieldSeq l bs₁ :=
              IH k₁ (by omega) k₁ le_rfl l bs₁ (fun c' hc' => hmem c' hc') hc₁
            exact YieldSeq.comp (seqBody_of_gridBody hm he) (hbody.append hrest)

/-- **Every totally ordered refinement of a chain-closed chain is an interleaving
refinement.** -/
theorem chainYield_of_yieldSeq (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {S : Set C} (hcc : ChainClosed D S) :
    ∀ {xs : List (A ⊕ C)} {as : List A}, D.YieldSeq xs as →
      (∀ c : C, Sum.inr c ∈ xs → c ∈ S) → D.ChainYield xs as := by
  intro xs as h
  induction h with
  | nil => intro _; simp
  | prim h ih =>
      intro hS
      exact chainYield_cons_inl_iff.2 ⟨_, rfl, ih (fun c hc => hS c (by simp [hc]))⟩
  | @comp c bs xs as hm h ih =>
      intro hS
      have hcS : c ∈ S := hS c (by simp)
      have hgb := gridBody_of_seqBody hgrid hcc hcS hm
      have hmem : ∀ c' : C, Sum.inr c' ∈ bs → c' ∈ S :=
        fun c' hc' => mem_of_gridBody_single hcc hcS hgb hc'
      have hall : ∀ c' : C, Sum.inr c' ∈ bs ++ xs → c' ∈ S := by
        intro c' hc'
        rcases List.mem_append.1 hc' with hc'' | hc''
        · exact hmem c' hc''
        · exact hS c' (by simp [hc''])
      obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := chainYield_append_iff.1 (ih hall)
      exact chainYield_cons_inr_iff.2
        ⟨[bs], as₁, as₂, hgb, gridYield_singleton_iff.2 h₁, h₂, rfl⟩

/-- **The interleaving and the totally ordered refinement relations agree on chain-closed
chains.** -/
theorem chainYield_iff_yieldSeq (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {S : Set C} (hcc : ChainClosed D S) {xs : List (A ⊕ C)} {as : List A}
    (hS : ∀ c : C, Sum.inr c ∈ xs → c ∈ S) : D.ChainYield xs as ↔ D.YieldSeq xs as := by
  constructor
  · rintro ⟨n, h⟩
    exact yieldSeq_of_chainYieldN hgrid hcc n n le_rfl xs as hS h
  · intro h
    exact chainYield_of_yieldSeq hgrid hcc h hS

end Domain

end HTN
