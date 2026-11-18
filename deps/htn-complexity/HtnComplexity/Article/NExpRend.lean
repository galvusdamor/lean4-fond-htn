import HtnComplexity.Article.HalvingL
import HtnComplexity.Computable.TMLists
import HtnComplexity.Computable.RenderClass
import HtnComplexity.TMEnc.TMHoming
/-!
# The acyclic encoding of Thm. 4.3.7 with an explicit list of methods

`HTN.TMEnc.problemFix N w K` — the repaired encoding of a machine run (word in the domain) — has
infinitely many methods; a description lists those it can reach.  `HTN.TMEnc.U.methodsL` is an
explicit list of methods of it (`HTN.TMEnc.U.mem_bodiesFix_of_mem_methodsL`) containing every method
of every task it can reach (`HTN.TMEnc.U.mem_methodsL_of_mem_taskFinsetFix`): the counting tasks
are listed for all counts in the list `countsL` of halving closures, which is computed in
polynomial time from `K` in binary.

`HTN.TMEnc.U.rendU` is the rendering of the problem with these methods and the numberings of
`HtnComplexity/Computable/TMNum.lean`; its domain is acyclic and its instance rooted.
-/

namespace HTN

namespace TMEnc

namespace U

open scoped Classical

open TM TaskNetwork Syn Article

variable {Q Γ : Type} [Fintype Q] [Fintype Γ]

/-- A method body. -/
abbrev Body (Q Γ : Type) := List (List (TMAct Q Γ ⊕ TMTask Q Γ))

section Lists

variable (N : NTM Q Γ) (w : List Γ) (K : ℕ)

/-- The three channels. -/
def syncAll : List SyncKind := [.head, .check, .sync]

theorem mem_syncAll (x : SyncKind) : x ∈ syncAll := by cases x <;> simp [syncAll]

/-- The transitions of the machine. -/
noncomputable def transAll : List (Q × Γ × Q × Γ × Move) :=
  ((Finset.univ : Finset (Q × Γ × Q × Γ × Move)).filter
    fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2) ∈ N.step t.1 t.2.1).toList

/-- The accepting states. -/
noncomputable def accAll : List Q := ((Finset.univ : Finset Q).filter (· ∈ N.accept)).toList

/-- The counts of the counting tasks: the halving closures of `K`, `K + 1`, `K + 2`, `K - n`,
`K - 1`, and `0`, `1`, `K`. -/
def countsL (n : ℕ) : List ℕ :=
  hcL K ++ hcL (K + 1) ++ hcL (K + 2) ++ hcL (K - n) ++ hcL (K - 1) ++ [0, 1, K]

/-- The tasks that are counted. -/
def baseAll : List (TMTask Q Γ) :=
  [.acquire .check, .acquire .sync, .produce, .waitCell, .noHeadCell, .heads, .transitionAndCheck,
    .tapeProduce, .produceSym (some N.blank)]

def produceBody (c : Option Γ) : Body Q Γ :=
  [[Sum.inl (.assert c), Sum.inr (.acquire .head), Sum.inr (.cSeq (.acquire .check) (K + 1)),
    Sum.inr (.cSeq (.acquire .sync) (K + 1))]]

def chkBody (c : Option Γ) : Body Q Γ :=
  [[Sum.inl (.check (.sym c)), Sum.inr (.release .sync), Sum.inr (.waitN K),
    Sum.inr (.release .check), Sum.inl (.check (.sym c))]]

def transBody (t : Q × Γ × Q × Γ × Move) : Body Q Γ :=
  [Sum.inl (.step t.1 (some t.2.1) t.2.2.1 (some t.2.2.2.1)) ::
    List.replicate (moveExtra t.2.2.2.2) (Sum.inr (.acquire .head))]

def checkersBody (i : ℕ) : Body Q Γ :=
  if i = 0 then []
  else if i = 1 then checkerBodyFix K
  else if i % 2 = 0 then
    [[Sum.inr (.cPar (.waitN (i / 2)) (i / 2)), Sum.inr (.checkers (i / 2))],
      [Sum.inr (.checkers (i / 2)), Sum.inr (.cPar (.waitN (i / 2)) (i / 2))]]
  else
    [[Sum.inr (.cPar (.waitN 1) (i - 1)), Sum.inr (.checkers (i - 1))],
      [Sum.inr (.checkers 1), Sum.inr (.waitN (i - 1))]]

def wordBody (i : ℕ) : Body Q Γ :=
  if i + 1 < w.length then
    [[Sum.inr (.produceSym (some (w.getD i N.blank))), Sum.inr (.produceWord (i + 1))]]
  else [[Sum.inr (.produceSym (some (w.getD i N.blank)))]]

def seqBody (t : TMTask Q Γ) (k : ℕ) : Body Q Γ :=
  if k = 0 then []
  else if k = 1 then [[Sum.inr t]]
  else if k % 2 = 0 then [[Sum.inr (.cSeq t (k / 2)), Sum.inr (.cSeq t (k / 2))]]
  else [[Sum.inr t, Sum.inr (.cSeq t (k - 1))]]

def parBody (t : TMTask Q Γ) (k : ℕ) : Body Q Γ :=
  if k = 0 then []
  else if k = 1 then [[Sum.inr t]]
  else if k % 2 = 0 then [[Sum.inr (.cPar t (k / 2))], [Sum.inr (.cPar t (k / 2))]]
  else [[Sum.inr t], [Sum.inr (.cPar t (k - 1))]]

/-- **The methods of the encoding that the description lists.** -/
noncomputable def methodsL : List (TMTask Q Γ × Body Q Γ) :=
  syncAll.map (fun x => (.acquire x, [[Sum.inl (.call x), Sum.inl (.wait x)]])) ++
  syncAll.map (fun x => (.release x, [[Sum.inl (.start x), Sum.inl (.respond x)]])) ++
  symList.map (fun c => (.produce, produceBody K c)) ++
  symList.map (fun c => (.produceSym c, produceBody K c)) ++
  [(.tapeProduce, [[Sum.inr (.produceSym none), Sum.inr (.cSeq .produce K)]]),
    (.waitCell, [[Sum.inr (.release .check), Sum.inr (.release .sync)]])] ++
  (countsL K w.length).map (fun i => (.waitN i, [[Sum.inr (.cSeq .waitCell i)]])) ++
  symList.map (fun c => (.chk, chkBody K c)) ++
  [(.headCell, [[Sum.inl (.start .head), Sum.inl .assertHead, Sum.inl (.respond .head)]]),
    (.noHeadCell, [[Sum.inl (.start .head), Sum.inl .retractHead, Sum.inl (.respond .head)]]),
    (.heads, [[Sum.inr .noHeadCell, Sum.inr .headCell, Sum.inr (.cSeq .noHeadCell K)]])] ++
  (transAll N).map (fun t => (.transition, transBody t)) ++
  [(.transitionAndCheck, [[Sum.inr .transition, Sum.inr .chk]]),
    (.transitionAndCheck, [[Sum.inl (.check .noHead), Sum.inr .chk]])] ++
  (countsL K w.length).map (fun i => (.checkers i, checkersBody K i)) ++
  [(.produceInit, [[Sum.inr (.produceSym none), Sum.inr (.produceWord 0),
    Sum.inr (.cSeq (.produceSym (some N.blank)) (K - w.length))]])] ++
  (List.range (w.length + 1)).map (fun i => (.produceWord i, wordBody N w i)) ++
  (accAll N).map (fun f => (.done, [[Sum.inl (.check (.st f))]])) ++
  ((baseAll N).flatMap fun t => (countsL K w.length).map fun k => (.cSeq t k, seqBody t k)) ++
  ((countsL K w.length).flatMap fun j => (countsL K w.length).map fun k =>
    (.cPar (.waitN j) k, parBody (.waitN j) k))

end Lists

/-! ### The listed methods are methods -/

section Sub

variable {N : NTM Q Γ} {w : List Γ} {K : ℕ}

theorem seqBody_mem (t : TMTask Q Γ) (k : ℕ) : seqBody t k ∈ bodiesFix N w K (.cSeq t k) := by
  simp only [bodiesFix, bodies, seqBody]
  split_ifs <;> simp

theorem parBody_mem (t : TMTask Q Γ) (k : ℕ) : parBody t k ∈ bodiesFix N w K (.cPar t k) := by
  simp only [bodiesFix, bodies, parBody]
  split_ifs <;> simp

theorem checkersBody_mem (i : ℕ) : checkersBody K i ∈ bodiesFix N w K (.checkers i) := by
  simp only [bodiesFix, bodies, checkersBody]
  split_ifs <;> simp_all

theorem wordBody_mem (i : ℕ) : wordBody N w i ∈ bodiesFix N w K (.produceWord i) := by
  simp only [bodiesFix, bodies, wordBody]
  split_ifs <;> simp

/-- **Every listed method is a method of the encoding.** -/
theorem mem_bodiesFix_of_mem_methodsL {p : TMTask Q Γ × Body Q Γ} (hp : p ∈ methodsL N w K) :
    p.2 ∈ bodiesFix N w K p.1 := by
  simp only [methodsL, List.mem_append, List.mem_map, List.mem_cons, List.mem_flatMap,
    List.mem_nil_iff, or_false, or_assoc] at hp
  rcases hp with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩ | rfl | rfl | ⟨i, -, rfl⟩ |
    ⟨c, -, rfl⟩ | rfl | rfl | rfl | ⟨t, ht, rfl⟩ | rfl | rfl | ⟨i, -, rfl⟩ | rfl | ⟨i, -, rfl⟩ |
    ⟨f, hf, rfl⟩ | ⟨t, -, k, -, rfl⟩ | ⟨j, -, k, -, rfl⟩
  all_goals first
    | exact seqBody_mem _ _
    | exact parBody_mem _ _
    | exact checkersBody_mem _
    | exact wordBody_mem _
    | skip
  all_goals simp only [bodiesFix, bodies, produceBody, chkBody]
  all_goals try simp
  all_goals first
    | exact ⟨_, rfl⟩
    | simpa [transAll] using ht
    | simpa [accAll] using hf
    | (simp only [transAll, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at ht
       exact ⟨t.1, t.2.2.1, t.2.1, t.2.2.2.1, t.2.2.2.2, ht, rfl⟩)
    | (simp only [accAll, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hf
       exact ⟨f, hf, rfl⟩)

end Sub

/-! ### Every method of a reachable task is listed -/

section All

variable {N : NTM Q Γ} {w : List Γ} {K : ℕ}

theorem mem_countsL_of_countFinset {k : ℕ} (h : k ∈ countFinset K w.length) :
    k ∈ countsL K w.length := by
  simp only [countFinset, Finset.mem_union] at h
  simp only [countsL, List.mem_append]
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (mem_hcL_of_mem h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mem_hcL_of_mem h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_hcL_of_mem h))))
  · exact Or.inl (Or.inl (Or.inr (mem_hcL_of_mem h)))

theorem mem_countsL_of_hc1 {k : ℕ} (h : k ∈ halvingClosure (K + 1)) :
    k ∈ countsL K w.length := by
  simp only [countsL, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mem_hcL_of_mem h)))))

theorem mem_countsL_of_hcm1 {k : ℕ} (h : k ∈ halvingClosure (K - 1)) :
    k ∈ countsL K w.length := by
  simp only [countsL, List.mem_append]
  exact Or.inl (Or.inr (mem_hcL_of_mem h))

theorem zero_mem_countsL : 0 ∈ countsL K w.length := by simp [countsL]
theorem one_mem_countsL : 1 ∈ countsL K w.length := by simp [countsL]
theorem K_mem_countsL : K ∈ countsL K w.length := by simp [countsL]

theorem mem_countsL_of_waitN {k : ℕ} (h : k ∈ waitNFinset K) : k ∈ countsL K w.length := by
  simp only [waitNFinset, Finset.mem_insert] at h
  rcases h with rfl | rfl | h
  · exact K_mem_countsL
  · exact one_mem_countsL
  · exact mem_countsL_of_hc1 h

theorem mem_countsL_of_checker {k : ℕ} (h : k ∈ checkerFinset K) : k ∈ countsL K w.length := by
  simp only [checkerFinset, Finset.mem_insert] at h
  rcases h with rfl | rfl | h
  · exact zero_mem_countsL
  · exact one_mem_countsL
  · exact mem_countsL_of_hc1 h

theorem mem_baseAll {t : TMTask Q Γ} (h : t ∈ cSeqBase N) : t ∈ baseAll N := by
  simp only [cSeqBase, Finset.mem_insert, Finset.mem_singleton] at h
  simp only [baseAll, List.mem_cons, List.mem_nil_iff, or_false]
  exact h

theorem bodiesFix_cSeq (t : TMTask Q Γ) (k : ℕ) : bodiesFix N w K (.cSeq t k) = {seqBody t k} := by
  simp only [bodiesFix, bodies, seqBody]; split_ifs <;> rfl

theorem bodiesFix_cPar (t : TMTask Q Γ) (k : ℕ) : bodiesFix N w K (.cPar t k) = {parBody t k} := by
  simp only [bodiesFix, bodies, parBody]; split_ifs <;> rfl

theorem bodiesFix_checkers (i : ℕ) : bodiesFix N w K (.checkers i) = {checkersBody K i} := by
  simp only [bodiesFix, bodies, checkersBody]; split_ifs <;> simp_all

theorem bodiesFix_produceWord (i : ℕ) :
    bodiesFix N w K (.produceWord i) = {wordBody N w i} := by
  simp only [bodiesFix, bodies, wordBody]; split_ifs <;> rfl

/-- The position of a group in `methodsL`: `methodsL = g₁ ++ ⋯ ++ g₁₆`. -/
macro "nav " n:num : tactic =>
  `(tactic| (unfold methodsL; iterate $n apply List.mem_append_left))

theorem mem_m_acquire (x : SyncKind) :
    (TMTask.acquire x, ([[Sum.inl (.call x), Sum.inl (.wait x)]] : Body Q Γ)) ∈ methodsL N w K := by
  nav 15; exact List.mem_map.2 ⟨x, mem_syncAll x, rfl⟩

theorem mem_m_release (x : SyncKind) :
    (TMTask.release x, ([[Sum.inl (.start x), Sum.inl (.respond x)]] : Body Q Γ)) ∈ methodsL N w K := by
  nav 14; apply List.mem_append_right; exact List.mem_map.2 ⟨x, mem_syncAll x, rfl⟩

theorem mem_m_produce (c : Option Γ) : (TMTask.produce, produceBody K c) ∈ methodsL N w K := by
  nav 13; apply List.mem_append_right; exact List.mem_map.2 ⟨c, mem_symList c, rfl⟩

theorem mem_m_produceSym (c : Option Γ) :
    (TMTask.produceSym c, produceBody K c) ∈ methodsL N w K := by
  nav 12; apply List.mem_append_right; exact List.mem_map.2 ⟨c, mem_symList c, rfl⟩

theorem mem_m_g5 {p : TMTask Q Γ × Body Q Γ}
    (h : p = (.tapeProduce, [[Sum.inr (.produceSym none), Sum.inr (.cSeq .produce K)]]) ∨
      p = (.waitCell, [[Sum.inr (.release .check), Sum.inr (.release .sync)]])) :
    p ∈ methodsL N w K := by
  nav 11; apply List.mem_append_right; rcases h with rfl | rfl <;> simp

theorem mem_m_waitN {i : ℕ} (hi : i ∈ countsL K w.length) :
    (TMTask.waitN i, ([[Sum.inr (.cSeq .waitCell i)]] : Body Q Γ)) ∈ methodsL N w K := by
  nav 10; apply List.mem_append_right; exact List.mem_map.2 ⟨i, hi, rfl⟩

theorem mem_m_chk (c : Option Γ) : (TMTask.chk, chkBody K c) ∈ methodsL N w K := by
  nav 9; apply List.mem_append_right; exact List.mem_map.2 ⟨c, mem_symList c, rfl⟩

theorem mem_m_g8 {p : TMTask Q Γ × Body Q Γ}
    (h : p = (.headCell, [[Sum.inl (.start .head), Sum.inl .assertHead, Sum.inl (.respond .head)]]) ∨
      p = (.noHeadCell, [[Sum.inl (.start .head), Sum.inl .retractHead, Sum.inl (.respond .head)]]) ∨
      p = (.heads, [[Sum.inr .noHeadCell, Sum.inr .headCell, Sum.inr (.cSeq .noHeadCell K)]])) :
    p ∈ methodsL N w K := by
  nav 8; apply List.mem_append_right; rcases h with rfl | rfl | rfl <;> simp

theorem mem_m_transition {t : Q × Γ × Q × Γ × Move} (ht : t ∈ transAll N) :
    (TMTask.transition, transBody t) ∈ methodsL N w K := by
  nav 7; apply List.mem_append_right; exact List.mem_map.2 ⟨t, ht, rfl⟩

theorem mem_m_g10 {p : TMTask Q Γ × Body Q Γ}
    (h : p = (.transitionAndCheck, [[Sum.inr .transition, Sum.inr .chk]]) ∨
      p = (.transitionAndCheck, [[Sum.inl (.check .noHead), Sum.inr .chk]])) :
    p ∈ methodsL N w K := by
  nav 6; apply List.mem_append_right; rcases h with rfl | rfl <;> simp

theorem mem_m_checkers {i : ℕ} (hi : i ∈ countsL K w.length) :
    (TMTask.checkers i, checkersBody K i) ∈ methodsL N w K := by
  nav 5; apply List.mem_append_right; exact List.mem_map.2 ⟨i, hi, rfl⟩

theorem mem_m_produceInit :
    (TMTask.produceInit, ([[Sum.inr (.produceSym none), Sum.inr (.produceWord 0),
      Sum.inr (.cSeq (.produceSym (some N.blank)) (K - w.length))]] : Body Q Γ)) ∈ methodsL N w K := by
  nav 4; apply List.mem_append_right; simp

theorem mem_m_produceWord {i : ℕ} (hi : i < w.length + 1) :
    (TMTask.produceWord i, wordBody N w i) ∈ methodsL N w K := by
  nav 3; apply List.mem_append_right; exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

theorem mem_m_done {f : Q} (hf : f ∈ accAll N) :
    ((TMTask.done : TMTask Q Γ), [[Sum.inl (TMAct.check (TMFact.st f))]]) ∈ methodsL N w K := by
  nav 2; apply List.mem_append_right; exact List.mem_map.2 ⟨f, hf, rfl⟩

theorem mem_m_cSeq {t : TMTask Q Γ} {k : ℕ} (ht : t ∈ baseAll N) (hk : k ∈ countsL K w.length) :
    (TMTask.cSeq t k, seqBody t k) ∈ methodsL N w K := by
  nav 1; apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨k, hk, rfl⟩⟩

theorem mem_m_cPar {j k : ℕ} (hj : j ∈ countsL K w.length) (hk : k ∈ countsL K w.length) :
    (TMTask.cPar (.waitN j) k, parBody (Q := Q) (Γ := Γ) (.waitN j) k) ∈ methodsL N w K := by
  unfold methodsL; apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨j, hj, List.mem_map.2 ⟨k, hk, rfl⟩⟩

/-- **Every method of a task of `taskFinsetFix` is listed.** -/
theorem mem_methodsL_of_mem_taskFinsetFix {t : TMTask Q Γ} (ht : t ∈ taskFinsetFix N w K)
    {ls : Body Q Γ} (hls : ls ∈ bodiesFix N w K t) : (t, ls) ∈ methodsL N w K := by
  simp only [taskFinsetFix, taskFinset, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_product, Finset.mem_range, Prod.exists] at ht
  rcases ht with ((((((((⟨x, -, rfl⟩ | ⟨x, -, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl)) | ⟨c, -, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) |
      ⟨b, k, ⟨hb, hk⟩, rfl⟩) | ⟨j, k, ⟨hj, hk⟩, rfl⟩) | ⟨k, hk, rfl⟩
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls; exact mem_m_acquire x
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls; exact mem_m_release x
  · simp only [bodiesFix, bodies, Set.mem_setOf_eq] at hls
    obtain ⟨c, rfl⟩ := hls; exact mem_m_produce c
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_g5 (Or.inl rfl)
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_g5 (Or.inr rfl)
  · simp only [bodiesFix, bodies, Set.mem_setOf_eq] at hls
    obtain ⟨c, rfl⟩ := hls; exact mem_m_chk c
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_g8 (Or.inl rfl)
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_g8 (Or.inr (Or.inl rfl))
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_g8 (Or.inr (Or.inr rfl))
  · simp only [bodiesFix, bodies, Set.mem_setOf_eq] at hls
    obtain ⟨q, q', c, c', m, hmem, rfl⟩ := hls
    exact mem_m_transition (t := (q, c, q', c', m)) (by simp [transAll, hmem])
  · simp only [bodiesFix, bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
    rcases hls with rfl | rfl
    · exact mem_m_g10 (Or.inl rfl)
    · exact mem_m_g10 (Or.inr rfl)
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_produceInit
  · simp only [bodiesFix, bodies, Set.mem_setOf_eq] at hls
    obtain ⟨f, hf, rfl⟩ := hls
    exact mem_m_done (by simp [accAll, hf])
  · simp [bodiesFix, bodies] at hls
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_produceSym c
  · simp only [bodiesFix, bodies, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_waitN (mem_countsL_of_waitN hi)
  · rw [bodiesFix_checkers, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_checkers (mem_countsL_of_checker hi)
  · rw [bodiesFix_produceWord, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_produceWord hi
  · rw [bodiesFix_cSeq, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_cSeq (mem_baseAll hb) (mem_countsL_of_countFinset hk)
  · rw [bodiesFix_cPar, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_cPar (mem_countsL_of_waitN hj) (mem_countsL_of_countFinset hk)
  · rw [bodiesFix_cSeq, Set.mem_singleton_iff] at hls; subst hls
    exact mem_m_cSeq (by simp [baseAll]) (mem_countsL_of_hcm1 hk)

end All

end U

end TMEnc

end HTN
