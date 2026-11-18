import HtnComplexity.Computable.AcBodies
/-!
# The compound tasks a description of the compiled acyclic domain has to list

The compiled domain of `HtnComplexity/ToHtnAc/ToHtnAc.lean` has **infinitely many** methods: the
counting tasks `𝔠̄^k_T` and `𝔠^k_T` exist for every task name `T` and every `k`, and each of
them carries a method.  A finite description can only list finitely many, and by
`HTN.Problem.solvable_withMethods_iff` it is enough to list the *reachable* ones.

This file delimits a finite set of compiled compound task names that contains every reachable
one:

* `HTN.Syn.Ac.cntKs bound` — the `k` that the counting tasks can reach from `bound`, obtained
  by repeated halving (`HTN.Syn.Ac.halvChild`).  Only logarithmically many, which is what keeps
  the description polynomial;
* `HTN.Syn.Ac.InTaskSet n bound` — the predicate on `HTN.ToAc.AcTask` that describes the set,
  proved closed under the method bodies (`HTN.Syn.Ac.inTaskSet_of_mem_bodies`);
* `HTN.Syn.Ac.taskListNum n bound` — the same set as a list of numbers, with the two
  transfer lemmas `HTN.Syn.Ac.mem_taskListNum_of_inTaskSet` and
  `HTN.Syn.Ac.exists_encTask_of_mem_taskListNum`.
-/

namespace HTN

namespace Syn

namespace Ac

/-! ### The halving closure, as a list -/

/-- The successor of `k` in the halving chain of the counting tasks. -/
def halvChild (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 else k - 1

/-- The halving chain starting at `k`, with a fuel bound. -/
def halvList : ℕ → ℕ → List ℕ
  | 0, k => [k]
  | fuel + 1, k => if k ≤ 1 then [k] else k :: halvList fuel (halvChild k)

/-- **The values a counting task can take**, starting from `bound`. -/
def cntKs (bound : ℕ) : List ℕ := halvList bound bound

lemma self_mem_halvList (fuel k : ℕ) : k ∈ halvList fuel k := by
  cases fuel with
  | zero => simp [halvList]
  | succ n =>
    by_cases h : k ≤ 1 <;> simp [halvList, h]

lemma halvChild_lt {k : ℕ} (h : 2 ≤ k) : halvChild k < k := by
  rw [halvChild]
  split_ifs with he
  · omega
  · omega

lemma halvList_closed : ∀ fuel k, k ≤ fuel → ∀ j ∈ halvList fuel k, 2 ≤ j →
    halvChild j ∈ halvList fuel k := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk j hj h2
    simp only [halvList, List.mem_singleton] at hj
    omega
  | succ n ih =>
    intro k hk j hj h2
    by_cases h1 : k ≤ 1
    · simp only [halvList, if_pos h1, List.mem_singleton] at hj
      omega
    · rw [halvList, if_neg h1] at hj ⊢
      have hkc : halvChild k ≤ n := by
        have := halvChild_lt (k := k) (by omega)
        omega
      rcases List.mem_cons.1 hj with rfl | hj'
      · exact List.mem_cons_of_mem _ (self_mem_halvList _ _)
      · exact List.mem_cons_of_mem _ (ih _ hkc j hj' h2)

lemma self_mem_cntKs (bound : ℕ) : bound ∈ cntKs bound := self_mem_halvList _ _

lemma halvChild_mem_cntKs {bound j : ℕ} (hj : j ∈ cntKs bound) (h2 : 2 ≤ j) :
    halvChild j ∈ cntKs bound := halvList_closed bound bound (le_refl _) j hj h2

/-! ### The set of compiled task names -/

section Set

variable {F A C : Type}

open ToAc

/-- The compiled compound task names a description has to list. -/
def InTaskSet (n bound : ℕ) : AcTask F A C → Prop
  | .SEL _ => True
  | .SELn m _ => m ≤ n
  | .EQ _ _ => True
  | .EQn m _ _ => m ≤ n
  | .STATE1 m => m ≤ n
  | .STATE3 m => m ≤ n
  | .MEM => True
  | .WRITE => True
  | .READ => True
  | .TUPLE => True
  | .cnt t k => t = AcTask.WRITE ∧ k ∈ cntKs bound
  | .cntPar t k => (t = AcTask.MEM ∨ t = AcTask.TUPLE) ∧ k ∈ cntKs bound
  | .tI => True

lemma inTaskSet_tI (n bound : ℕ) : InTaskSet n bound (AcTask.tI : AcTask F A C) := trivial

variable {I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

local macro "flatten_task" h:ident : tactic =>
  `(tactic| (simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false, false_or, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at $h:ident <;>
      (try casesm* _ ∧ _, _ ∨ _) <;> subst_vars <;>
      simp only [InTaskSet, true_and, and_true] <;>
      first | trivial | omega | tauto))

/-- **The set of listed compound tasks is closed under the method bodies.** -/
lemma inTaskSet_of_mem_bodies {t : AcTask F A C} (ht : InTaskSet vars.length bound t)
    {ls : List (List (AcAct F A C ⊕ AcTask F A C))} (hls : ls ∈ bodies D vars bound t)
    {c' : AcTask F A C} (hc : Sum.inr c' ∈ ls.flatten) : InTaskSet vars.length bound c' := by
  cases t with
  | SEL i => simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; flatten_task hc
  | SELn k i =>
      simp only [bodies] at hls
      split_ifs at hls with hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls; simp at hc
      · obtain ⟨v, -, rfl | rfl⟩ := hls <;>
          (have hle : k ≤ vars.length := ht) <;> flatten_task hc
  | EQ i j => simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; flatten_task hc
  | EQn k i j =>
      simp only [bodies] at hls
      split_ifs at hls with hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls; simp at hc
      · obtain ⟨v, -, rfl | rfl⟩ := hls <;>
          (have hle : k ≤ vars.length := ht) <;> flatten_task hc
  | STATE1 k =>
      simp only [bodies] at hls
      split_ifs at hls with hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls; flatten_task hc
      · obtain ⟨v, -, rfl | rfl⟩ := hls <;>
          (have hle : k ≤ vars.length := ht) <;> flatten_task hc
  | STATE3 k =>
      simp only [bodies] at hls
      split_ifs at hls with hk
      · obtain ⟨t', rfl⟩ := hls; simp at hc
      · obtain ⟨v, -, rfl | rfl⟩ := hls <;>
          (have hle : k ≤ vars.length := ht) <;> flatten_task hc
  | MEM => simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; flatten_task hc
  | WRITE => simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; simp at hc
  | READ => simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; simp at hc
  | TUPLE =>
      have hb : bound ∈ cntKs bound := self_mem_cntKs bound
      rcases hls with ⟨c₀, x, y, -, rfl⟩ | ⟨o, rfl⟩ <;> flatten_task hc
  | cnt t' k =>
      obtain ⟨rfl, hk⟩ := ht
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst hls; simp at hc
      · subst h1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hls
        rcases hls with rfl | rfl
        · flatten_task hc
        · simp at hc
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hch : halvChild k ∈ cntKs bound := halvChild_mem_cntKs hk (by omega)
        rw [halvChild, if_pos he] at hch
        flatten_task hc
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hls
        have hch : halvChild k ∈ cntKs bound := halvChild_mem_cntKs hk (by omega)
        rw [halvChild, if_neg he] at hch
        rcases hls with rfl | rfl <;> flatten_task hc
  | cntPar t' k =>
      obtain ⟨htt, hk⟩ := ht
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst hls; simp at hc
      · subst h1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hls
        rcases hls with rfl | rfl
        · flatten_task hc
        · simp at hc
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hch : halvChild k ∈ cntKs bound := halvChild_mem_cntKs hk (by omega)
        rw [halvChild, if_pos he] at hch
        flatten_task hc
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hls
        have hch : halvChild k ∈ cntKs bound := halvChild_mem_cntKs hk (by omega)
        rw [halvChild, if_neg he] at hch
        rcases hls with rfl | rfl <;> flatten_task hc
  | tI =>
      have hb : bound ∈ cntKs bound := self_mem_cntKs bound
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; flatten_task hc

end Set

/-! ### The set as a list of numbers -/

/-- **The compiled compound task names a description lists**, numbered. -/
def taskListNum (n bound : ℕ) : List ℕ :=
  (List.range 5).map tSEL ++
  ((List.range (n + 1)).flatMap fun m => (List.range 5).map (tSELn m)) ++
  ((List.range 5).flatMap fun i => (List.range 5).map (tEQ i)) ++
  ((List.range (n + 1)).flatMap fun m =>
    (List.range 5).flatMap fun i => (List.range 5).map (tEQn m i)) ++
  ((List.range (n + 1)).map tSTATE1) ++
  ((List.range (n + 1)).map tSTATE3) ++
  [tMEM, tWRITE, tREAD, tTUPLE, tTI] ++
  ((cntKs bound).map fun k => tCnt tWRITE k) ++
  ((cntKs bound).map fun k => tCntPar tMEM k) ++
  ((cntKs bound).map fun k => tCntPar tTUPLE k)

section Transfer

variable {F A C : Type} {f : F → ℕ} {a : A → ℕ} {c : C → ℕ}

open ToAc

/-- Every listed compiled task name is in the list of numbers. -/
lemma mem_taskListNum_of_inTaskSet {n bound : ℕ} {t : AcTask F A C}
    (ht : InTaskSet n bound t) : encTask f a c t ∈ taskListNum n bound := by
  cases t with
  | SEL i =>
      simp only [taskListNum, List.mem_append, List.mem_map, List.mem_range, enc_tSEL]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        ⟨i, i.isLt, rfl⟩))))))))
  | SELn m i =>
      have hm : m ≤ n := ht
      simp only [taskListNum, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
        enc_tSELn]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        ⟨m, by omega, i, i.isLt, rfl⟩))))))))
  | EQ i j =>
      simp only [taskListNum, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
        enc_tEQ]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        ⟨i, i.isLt, j, j.isLt, rfl⟩)))))))
  | EQn m i j =>
      have hm : m ≤ n := ht
      simp only [taskListNum, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
        enc_tEQn]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        ⟨m, by omega, i, i.isLt, j, j.isLt, rfl⟩))))))
  | STATE1 m =>
      have hm : m ≤ n := ht
      simp only [taskListNum, List.mem_append, List.mem_map, List.mem_range, enc_tSTATE1]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, by omega, rfl⟩)))))
  | STATE3 m =>
      have hm : m ≤ n := ht
      simp only [taskListNum, List.mem_append, List.mem_map, List.mem_range, enc_tSTATE3]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨m, by omega, rfl⟩))))
  | MEM => simp [taskListNum]
  | WRITE => simp [taskListNum]
  | READ => simp [taskListNum]
  | TUPLE => simp [taskListNum]
  | cnt t' k =>
      obtain ⟨rfl, hk⟩ := ht
      simp only [taskListNum, List.mem_append, List.mem_map, enc_tCnt, enc_tWRITE]
      exact Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))
  | cntPar t' k =>
      obtain ⟨htt, hk⟩ := ht
      rcases htt with rfl | rfl
      · simp only [taskListNum, List.mem_append, List.mem_map, enc_tCntPar, enc_tMEM]
        exact Or.inl (Or.inr ⟨k, hk, rfl⟩)
      · simp only [taskListNum, List.mem_append, List.mem_map, enc_tCntPar, enc_tTUPLE]
        exact Or.inr ⟨k, hk, rfl⟩
  | tI => simp [taskListNum]

/-- Every number in the list is the number of a listed compiled task name. -/
lemma exists_encTask_of_mem_taskListNum {n bound : ℕ} {x : ℕ}
    (hx : x ∈ taskListNum n bound) :
    ∃ t : AcTask F A C, encTask f a c t = x ∧ InTaskSet n bound t := by
  simp only [taskListNum, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with
      ((((((((⟨i, hi, rfl⟩ | ⟨m, hm, i, hi, rfl⟩) | ⟨i, hi, j, hj, rfl⟩) |
        ⟨m, hm, i, hi, j, hj, rfl⟩) | ⟨m, hm, rfl⟩) | ⟨m, hm, rfl⟩) |
        (rfl | rfl | rfl | rfl | rfl)) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
  · exact ⟨AcTask.SEL ⟨i, hi⟩, rfl, trivial⟩
  · exact ⟨AcTask.SELn m ⟨i, hi⟩, rfl, by simpa [InTaskSet] using Nat.lt_succ_iff.1 ‹m < n + 1›⟩
  · exact ⟨AcTask.EQ ⟨i, hi⟩ ⟨j, hj⟩, rfl, trivial⟩
  · exact ⟨AcTask.EQn m ⟨i, hi⟩ ⟨j, hj⟩, rfl,
      by simpa [InTaskSet] using Nat.lt_succ_iff.1 ‹m < n + 1›⟩
  · exact ⟨AcTask.STATE1 m, rfl, by simpa [InTaskSet] using Nat.lt_succ_iff.1 ‹m < n + 1›⟩
  · exact ⟨AcTask.STATE3 m, rfl, by simpa [InTaskSet] using Nat.lt_succ_iff.1 ‹m < n + 1›⟩
  · exact ⟨AcTask.MEM, rfl, trivial⟩
  · exact ⟨AcTask.WRITE, rfl, trivial⟩
  · exact ⟨AcTask.READ, rfl, trivial⟩
  · exact ⟨AcTask.TUPLE, rfl, trivial⟩
  · exact ⟨AcTask.tI, rfl, trivial⟩
  · exact ⟨AcTask.cnt AcTask.WRITE k, rfl, ⟨rfl, ‹k ∈ cntKs bound›⟩⟩
  · exact ⟨AcTask.cntPar AcTask.MEM k, rfl, ⟨Or.inl rfl, ‹k ∈ cntKs bound›⟩⟩
  · exact ⟨AcTask.cntPar AcTask.TUPLE k, rfl, ⟨Or.inr rfl, ‹k ∈ cntKs bound›⟩⟩

end Transfer

end Ac

end Syn

end HTN
