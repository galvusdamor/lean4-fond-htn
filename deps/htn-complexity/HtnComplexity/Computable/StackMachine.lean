import HtnPlanning.Computable.Bodies
/-!
# The bounded stack machine of a totally ordered domain description

Totally ordered HTN planning is derivation in a context-free grammar
(`HTN.Problem.solvable_iff_yieldSeq`): the initial task sequence is refined, leftmost first,
until only actions are left.  A leftmost derivation is the run of a pushdown automaton, and the
stack of that automaton is what a compilation into a *classical* (`STRIPS`) problem has to
encode in the state.  For that to be possible with polynomially many facts the stack has to be
**shallow**, and this is exactly what tail recursion buys — provided the machine performs a
*tail call*: when the compound task that is being refined is the **last** task of the body, the
frame is replaced instead of a new one being pushed.

This file formalises that machine, over the finite data of a domain description:

* a **frame** is a pair `(m, j)`: the method listed at position `m` of the description, with the
  first `j` tasks of its body already dealt with; a **stack** is a list of frames, innermost
  first;
* `HTN.Syn.pending d st` — the task sequence the stack still has to refine;
* `HTN.Syn.Run d D st as` — the stack `st` can be run to the empty stack, emitting the action
  sequence `as`, without ever exceeding the depth `D`;
* `HTN.Syn.yieldSeq_of_run` — **soundness**: a run emits a refinement of `pending d st`;
* `HTN.Syn.run_of_yieldSeq` — **completeness with a depth bound**: for a totally ordered *tail
  recursive* domain description every refinement of `pending d st` is emitted by a run of depth
  at most the number of listed methods, provided the ranks of the stack strictly decrease
  towards its bottom — which they do, because a frame is only ever pushed for a *non-last*
  compound subtask, and such a subtask strictly decreases the rank;
* `HTN.Syn.yieldSeq_singleton_iff_run` — the two statements combined, for the initial task
  sequence of a rooted instance.

The depth bound is `d.methods.length`: the ranks of the tasks on the stack are pairwise
distinct and come from the finitely many listed methods (`HTN.Syn.length_le_of_rankChain`).
-/

namespace HTN

namespace Syn

/-! ### Stacks and the tasks they leave to do -/

/-- The task sequence a stack of frames still has to refine: the unfinished suffixes of the
bodies of its frames, innermost frame first. -/
def pending (d : DomDesc) : List (ℕ × ℕ) → List (ℕ ⊕ ℕ)
  | [] => []
  | (m, j) :: rest => (d.bd m).drop j ++ pending d rest

@[simp] theorem pending_nil (d : DomDesc) : pending d [] = [] := rfl

@[simp] theorem pending_cons (d : DomDesc) (m j : ℕ) (rest : List (ℕ × ℕ)) :
    pending d ((m, j) :: rest) = (d.bd m).drop j ++ pending d rest := rfl

/-- Popping the finished frames from the top of a stack. -/
def dropFin (d : DomDesc) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (m, j) :: rest => if (d.bd m).length ≤ j then dropFin d rest else (m, j) :: rest

theorem dropFin_suffix (d : DomDesc) (st : List (ℕ × ℕ)) : dropFin d st <:+ st := by
  induction st with
  | nil => simp [dropFin]
  | cons p rest ih =>
    obtain ⟨m, j⟩ := p
    by_cases h : (d.bd m).length ≤ j
    · rw [dropFin, if_pos h]
      exact ih.trans (List.suffix_cons _ _)
    · rw [dropFin, if_neg h]

theorem pending_dropFin (d : DomDesc) (st : List (ℕ × ℕ)) :
    pending d (dropFin d st) = pending d st := by
  induction st with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨m, j⟩ := p
    by_cases h : (d.bd m).length ≤ j
    · rw [dropFin, if_pos h, ih, pending_cons, List.drop_eq_nil_of_le h, List.nil_append]
    · rw [dropFin, if_neg h]

/-- The head frame of a popped stack is unfinished. -/
theorem lt_length_of_dropFin {d : DomDesc} {st : List (ℕ × ℕ)} {m j : ℕ}
    {rest : List (ℕ × ℕ)} (h : dropFin d st = (m, j) :: rest) : j < (d.bd m).length := by
  induction st with
  | nil => simp [dropFin] at h
  | cons p rest' ih =>
    obtain ⟨m', j'⟩ := p
    by_cases hfin : (d.bd m').length ≤ j'
    · rw [dropFin, if_pos hfin] at h
      exact ih h
    · rw [dropFin, if_neg hfin] at h
      have h1 : (m', j') = (m, j) := (List.cons_eq_cons.1 h).1
      rw [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      omega

/-! ### Runs -/

/-- **A run of the stack machine.**  `Run d D st as` states that the stack `st` can be emptied,
emitting the action sequence `as`, without the stack ever exceeding the depth `D`.

The rules are: *return* from a finished frame, *execute* a primitive subtask, *push* a frame for
a compound subtask that is not the last task of its body, and *tail call* — replace the frame —
for a compound subtask that is the last one. -/
inductive Run (d : DomDesc) (D : ℕ) : List (ℕ × ℕ) → List ℕ → Prop
  /-- The empty stack is finished. -/
  | nil : Run d D [] []
  /-- A frame whose body is exhausted returns. -/
  | ret {m j : ℕ} {rest : List (ℕ × ℕ)} {as : List ℕ} (hj : (d.bd m).length ≤ j)
      (h : Run d D rest as) : Run d D ((m, j) :: rest) as
  /-- A primitive subtask is executed. -/
  | exec {m j a : ℕ} {rest : List (ℕ × ℕ)} {as : List ℕ}
      (hj : (d.bd m)[j]? = some (Sum.inl a)) (h : Run d D ((m, j + 1) :: rest) as) :
      Run d D ((m, j) :: rest) (a :: as)
  /-- A compound subtask that is not the last one pushes a frame. -/
  | push {m j c m' : ℕ} {rest : List (ℕ × ℕ)} {as : List ℕ}
      (hj : (d.bd m)[j]? = some (Sum.inr c)) (hlast : j + 1 < (d.bd m).length)
      (hm' : m' < d.methods.length) (hc : d.hd m' = c) (hdepth : rest.length + 2 ≤ D)
      (h : Run d D ((m', 0) :: (m, j + 1) :: rest) as) : Run d D ((m, j) :: rest) as
  /-- A compound subtask that is the last one replaces the frame. -/
  | tailCall {m j c m' : ℕ} {rest : List (ℕ × ℕ)} {as : List ℕ}
      (hj : (d.bd m)[j]? = some (Sum.inr c)) (hlast : j + 1 = (d.bd m).length)
      (hm' : m' < d.methods.length) (hc : d.hd m' = c)
      (h : Run d D ((m', 0) :: rest) as) : Run d D ((m, j) :: rest) as

/-- Finished frames on top of the stack may be popped. -/
theorem run_of_run_dropFin {d : DomDesc} {D : ℕ} {st : List (ℕ × ℕ)} {as : List ℕ}
    (h : Run d D (dropFin d st) as) : Run d D st as := by
  induction st with
  | nil => simpa [dropFin] using h
  | cons p rest ih =>
    obtain ⟨m, j⟩ := p
    by_cases hfin : (d.bd m).length ≤ j
    · rw [dropFin, if_pos hfin] at h
      exact Run.ret hfin (ih h)
    · rwa [dropFin, if_neg hfin] at h

/-! ### Soundness of the machine -/

variable {d : DomDesc}

/-- **A run emits a refinement of the pending task sequence.** -/
theorem yieldSeq_of_run (hTO : d.MethodsTO) {D : ℕ} {st : List (ℕ × ℕ)} {as : List ℕ}
    (h : Run d D st as) : d.toDomain.YieldSeq (pending d st) as := by
  induction h with
  | nil => exact Domain.YieldSeq.nil
  | ret hj _ ih =>
    rw [pending_cons, List.drop_eq_nil_of_le hj, List.nil_append]
    exact ih
  | @exec m j a rest as hj _ ih =>
    have hlt : j < (d.bd m).length := by
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hj
      exact absurd hj (by simp)
    rw [pending_cons, List.drop_eq_getElem_cons hlt]
    have hval : (d.bd m)[j] = Sum.inl a := by
      have := List.getElem?_eq_getElem hlt
      rw [hj] at this
      exact (Option.some.inj this).symm
    rw [hval, List.cons_append]
    exact Domain.YieldSeq.prim (by simpa using ih)
  | @push m j c m' rest as hj hlast hm' hc _ _ ih =>
    have hlt : j < (d.bd m).length := by omega
    have hval : (d.bd m)[j] = Sum.inr c := by
      have := List.getElem?_eq_getElem hlt
      rw [hj] at this
      exact (Option.some.inj this).symm
    rw [pending_cons, List.drop_eq_getElem_cons hlt, hval, List.cons_append]
    refine Domain.YieldSeq.comp ((DomDesc.seqBody_iff hTO).2 ⟨m', hm', hc, rfl⟩) ?_
    simpa [List.append_assoc] using ih
  | @tailCall m j c m' rest as hj hlast hm' hc _ ih =>
    have hlt : j < (d.bd m).length := by omega
    have hval : (d.bd m)[j] = Sum.inr c := by
      have := List.getElem?_eq_getElem hlt
      rw [hj] at this
      exact (Option.some.inj this).symm
    rw [pending_cons, List.drop_eq_getElem_cons hlt, hval, List.cons_append]
    refine Domain.YieldSeq.comp ((DomDesc.seqBody_iff hTO).2 ⟨m', hm', hc, rfl⟩) ?_
    have hdrop : (d.bd m).drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simpa [hdrop] using ih

/-! ### The depth bound -/

/-- Every frame of the stack is a listed method. -/
def StackOk (d : DomDesc) (st : List (ℕ × ℕ)) : Prop := ∀ p ∈ st, p.1 < d.methods.length

/-- The ranks of the frames strictly decrease from the bottom of the stack to its top. -/
def RankChain (d : DomDesc) (rk : ℕ → ℕ) (st : List (ℕ × ℕ)) : Prop :=
  List.IsChain (fun p q : ℕ × ℕ => rk (d.hd p.1) < rk (d.hd q.1)) st

/-- In a rank chain the top frame has the strictly smallest rank. -/
theorem rank_lt_of_mem_tail {rk : ℕ → ℕ} :
    ∀ {p : ℕ × ℕ} {st : List (ℕ × ℕ)}, RankChain d rk (p :: st) →
      ∀ q ∈ st, rk (d.hd p.1) < rk (d.hd q.1) := by
  intro p st
  induction st generalizing p with
  | nil => intro _ q hq; simp at hq
  | cons r rest ih =>
    intro hch q hq
    obtain ⟨hhead, htail⟩ := List.isChain_cons.1 hch
    have hpr : rk (d.hd p.1) < rk (d.hd r.1) := hhead r (by simp)
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hpr
    · exact lt_trans hpr (ih htail q hq)

/-- The ranks of a rank chain are pairwise increasing. -/
theorem pairwise_of_rankChain {rk : ℕ → ℕ} :
    ∀ {st : List (ℕ × ℕ)}, RankChain d rk st →
      st.Pairwise (fun p q : ℕ × ℕ => rk (d.hd p.1) < rk (d.hd q.1)) := by
  intro st
  induction st with
  | nil => intro _; exact List.Pairwise.nil
  | cons p rest ih =>
    intro hch
    exact List.Pairwise.cons (rank_lt_of_mem_tail hch) (ih (List.isChain_cons.1 hch).2)

/-- **A stack whose ranks strictly decrease is shallow**: it has at most as many frames as the
description has methods. -/
theorem length_le_of_rankChain {rk : ℕ → ℕ} {st : List (ℕ × ℕ)} (hok : StackOk d st)
    (hch : RankChain d rk st) : st.length ≤ d.methods.length := by
  classical
  have hpair : st.Pairwise (fun p q : ℕ × ℕ => rk (d.hd p.1) < rk (d.hd q.1)) :=
    pairwise_of_rankChain hch
  have hnodup : (st.map fun p => rk (d.hd p.1)).Nodup :=
    List.pairwise_map.2 (hpair.imp fun {_ _} hab => Nat.ne_of_lt hab)
  have hsub : (st.map fun p => rk (d.hd p.1)) ⊆
      (List.range d.methods.length).map fun m => rk (d.hd m) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map.2 ⟨p.1, List.mem_range.2 (hok p hp), rfl⟩
  have := (List.subperm_of_subset hnodup hsub).length_le
  simpa using this

/-! ### Completeness of the machine -/

/-- **Every refinement of the pending task sequence is emitted by a shallow run.**

The hypotheses are those of the class `TO-HTN-TR`: the listed methods are totally ordered, and
`rk` witnesses tail recursion.  The stack is required to consist of listed methods whose ranks
strictly decrease towards the bottom — an invariant the machine maintains, because a frame is
pushed only for a compound subtask that is *not* the last task of its body. -/
theorem run_of_yieldSeq (hTO : d.MethodsTO) {rk : ℕ → ℕ} (hrk : d.TailRecBy rk) :
    ∀ {xs : List (ℕ ⊕ ℕ)} {as : List ℕ}, d.toDomain.YieldSeq xs as →
      ∀ st : List (ℕ × ℕ), pending d st = xs → StackOk d st → RankChain d rk st →
        Run d d.methods.length st as := by
  intro xs as hy
  induction hy with
  | nil =>
    intro st hst hok hch
    refine run_of_run_dropFin ?_
    rcases hdf : dropFin d st with _ | ⟨⟨m, j⟩, rest⟩
    · exact Run.nil
    · exfalso
      have hlt : j < (d.bd m).length := lt_length_of_dropFin hdf
      have hp : pending d (dropFin d st) = pending d st := pending_dropFin d st
      rw [hdf, hst, pending_cons] at hp
      have : ((d.bd m).drop j).length = 0 := by
        have := congrArg List.length hp
        simp only [List.length_append, List.length_nil] at this
        omega
      rw [List.length_drop] at this
      omega
  | @prim a xs' as' _ ih =>
    intro st hst hok hch
    refine run_of_run_dropFin ?_
    have hsuf := dropFin_suffix d st
    have hp : pending d (dropFin d st) = Sum.inl a :: xs' := by
      rw [pending_dropFin d st, hst]
    rcases hdf : dropFin d st with _ | ⟨⟨m, j⟩, rest⟩
    · rw [hdf] at hp; simp at hp
    · have hlt : j < (d.bd m).length := lt_length_of_dropFin hdf
      rw [hdf, pending_cons, List.drop_eq_getElem_cons hlt, List.cons_append] at hp
      have hhead : (d.bd m)[j] = Sum.inl a := by
        have := (List.cons.injEq _ _ _ _ ▸ hp).1
        exact this
      have htail : (d.bd m).drop (j + 1) ++ pending d rest = xs' :=
        (List.cons.injEq _ _ _ _ ▸ hp).2
      have hok' : StackOk d ((m, j + 1) :: rest) := by
        intro p hp'
        rcases List.mem_cons.1 hp' with rfl | hp'
        · exact hok (m, j) (hsuf.mem (by rw [hdf]; simp))
        · exact hok p (hsuf.mem (by rw [hdf]; exact List.mem_cons_of_mem _ hp'))
      have hch' : RankChain d rk ((m, j + 1) :: rest) := by
        have hchd : RankChain d rk ((m, j) :: rest) :=
          List.IsChain.suffix hch (hdf ▸ hsuf)
        exact List.isChain_cons.2 ⟨(List.isChain_cons.1 hchd).1, (List.isChain_cons.1 hchd).2⟩
      refine Run.exec (a := a) ?_ (ih ((m, j + 1) :: rest) (by rw [pending_cons, htail]) hok' hch')
      rw [List.getElem?_eq_getElem hlt, hhead]
  | @comp c bs xs' as hm _ ih =>
    intro st hst hok hch
    refine run_of_run_dropFin ?_
    have hsuf := dropFin_suffix d st
    have hp : pending d (dropFin d st) = Sum.inr c :: xs' := by
      rw [pending_dropFin d st, hst]
    rcases hdf : dropFin d st with _ | ⟨⟨m, j⟩, rest⟩
    · rw [hdf] at hp; simp at hp
    · have hlt : j < (d.bd m).length := lt_length_of_dropFin hdf
      rw [hdf, pending_cons, List.drop_eq_getElem_cons hlt, List.cons_append] at hp
      have hhead : (d.bd m)[j] = Sum.inr c := (List.cons.injEq _ _ _ _ ▸ hp).1
      have htail : (d.bd m).drop (j + 1) ++ pending d rest = xs' :=
        (List.cons.injEq _ _ _ _ ▸ hp).2
      have hchd : RankChain d rk ((m, j) :: rest) :=
        List.IsChain.suffix hch (hdf ▸ hsuf)
      have hokd : StackOk d ((m, j) :: rest) := by
        intro p hp'
        exact hok p (hsuf.mem (by rw [hdf]; exact hp'))
      have hmlt : m < d.methods.length := hokd (m, j) (by simp)
      obtain ⟨m', hm', hc', hbs⟩ := (DomDesc.seqBody_iff hTO).1 hm
      have hgetj : (d.bd m)[j]? = some (Sum.inr c) := by
        rw [List.getElem?_eq_getElem hlt, hhead]
      by_cases hlast : j + 1 < (d.bd m).length
      · -- push
        have hrank : rk c < rk (d.hd m) :=
          DomDesc.rank_lt_of_bd_getElem hTO hrk hmlt hlt hlast hhead
        have hok' : StackOk d ((m', 0) :: (m, j + 1) :: rest) := by
          intro p hp'
          rcases List.mem_cons.1 hp' with rfl | hp'
          · exact hm'
          · rcases List.mem_cons.1 hp' with rfl | hp'
            · exact hmlt
            · exact hokd p (List.mem_cons_of_mem _ hp')
        have hch' : RankChain d rk ((m', 0) :: (m, j + 1) :: rest) := by
          refine List.isChain_cons.2 ⟨fun y hy => ?_, ?_⟩
          · have hy' : (m, j + 1) = y := by simpa using hy
            subst hy'
            show rk (d.hd m') < rk (d.hd m)
            rw [hc']
            exact hrank
          · exact List.isChain_cons.2
              ⟨(List.isChain_cons.1 hchd).1, (List.isChain_cons.1 hchd).2⟩
        have hdepth : rest.length + 2 ≤ d.methods.length := by
          have := length_le_of_rankChain hok' hch'
          simpa using this
        refine Run.push hgetj hlast hm' hc' hdepth (ih ((m', 0) :: (m, j + 1) :: rest) ?_ hok' hch')
        rw [pending_cons, pending_cons, List.drop_zero, hbs, htail]
      · -- tail call
        have hlasteq : j + 1 = (d.bd m).length := by omega
        have hrank : rk c ≤ rk (d.hd m) :=
          DomDesc.rank_le_of_bd_getElem_last hTO hrk hmlt hlt hhead
        have hok' : StackOk d ((m', 0) :: rest) := by
          intro p hp'
          rcases List.mem_cons.1 hp' with rfl | hp'
          · exact hm'
          · exact hokd p (List.mem_cons_of_mem _ hp')
        have hch' : RankChain d rk ((m', 0) :: rest) := by
          refine List.isChain_cons.2 ⟨fun y hy => ?_, (List.isChain_cons.1 hchd).2⟩
          have hlt' : rk (d.hd m) < rk (d.hd y.1) := (List.isChain_cons.1 hchd).1 y hy
          show rk (d.hd m') < rk (d.hd y.1)
          rw [hc']
          omega
        refine Run.tailCall hgetj hlasteq hm' hc' (ih ((m', 0) :: rest) ?_ hok' hch')
        have hdrop : (d.bd m).drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
        rw [pending_cons, List.drop_zero, hbs, ← htail, hdrop, List.nil_append]

/-! ### The initial task sequence of a rooted instance -/

/-- **The refinements of a single compound task are the runs of the machine** that start from a
method for it. -/
theorem yieldSeq_singleton_iff_run (hTO : d.MethodsTO) {rk : ℕ → ℕ} (hrk : d.TailRecBy rk)
    {c : ℕ} {as : List ℕ} :
    d.toDomain.YieldSeq [Sum.inr c] as ↔
      ∃ m, m < d.methods.length ∧ d.hd m = c ∧ Run d d.methods.length [(m, 0)] as := by
  constructor
  · intro hy
    cases hy with
    | comp hm h =>
      obtain ⟨m, hm', hc, hbs⟩ := (DomDesc.seqBody_iff hTO).1 hm
      refine ⟨m, hm', hc, ?_⟩
      refine run_of_yieldSeq hTO hrk (by simpa using h) [(m, 0)] ?_ ?_ ?_
      · rw [pending_cons, List.drop_zero, pending_nil, List.append_nil, hbs]
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hm'
        · simp at hp
      · exact List.isChain_singleton _
  · rintro ⟨m, hm, hc, hrun⟩
    have h := yieldSeq_of_run hTO hrun
    rw [pending_cons, List.drop_zero, pending_nil, List.append_nil] at h
    exact Domain.YieldSeq.comp ((DomDesc.seqBody_iff hTO).2 ⟨m, hm, hc, rfl⟩) (by simpa using h)

end Syn

end HTN
