import HtnComplexity.TMEnc.TMEncBodies
/-!
# The semantics of the Turing-machine encoding: the synchronisation channels

`HtnComplexity/TMEnc/TMEncoding.lean` synchronises the parallel processes of the encoding — the
head counter, the `K + 1` cell counters and the production of the tape — through three
*channels* (`HTN.TMEnc.SyncKind`), each of which is a pair of semaphore facts `x_step` and
`x_stepped` operated by the four actions

| action | precondition | adds | deletes |
| --- | --- | --- | --- |
| `call x` | | `x_step` | |
| `start x` | `x_step` | | `x_step` |
| `respond x` | | `x_stepped` | |
| `wait x` | `x_stepped` | | `x_stepped` |

so that a process asking for a step (`acquire x = call x ; wait x`) is blocked until another
process answers it (`release x = start x ; respond x`).

This file proves the *semantic* half of that protocol: along any executable action sequence
each of the two semaphores behaves like a binary credit, so that

* `HTN.TMEnc.countP_start_le_countP_call` — no more `start x` than `call x` actions occur, and
* `HTN.TMEnc.countP_wait_le_countP_respond` — no more `wait x` than `respond x` actions occur.

Both are instances of one abstract statement about a semaphore fact
(`HTN.TMEnc.countP_down_le_countP_up`).

Together with the *syntactic* half — every `acquire x` task contributes one `call x` and one
`wait x` action and every `release x` task one `start x` and one `respond x` action — this is
the counting argument by which a plan of the encoded problem has to run the parallel processes
in lock-step, which is the first ingredient of the simulation argument of Theorem 4.3.7.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type}

/-! ### The four actions of a channel -/

/-- The action `call x`. -/
def isCall (x : SyncKind) : TMAct Q Γ → Bool
  | .call y => decide (y = x)
  | _ => false

/-- The action `start x`. -/
def isStart (x : SyncKind) : TMAct Q Γ → Bool
  | .start y => decide (y = x)
  | _ => false

/-- The action `respond x`. -/
def isRespond (x : SyncKind) : TMAct Q Γ → Bool
  | .respond y => decide (y = x)
  | _ => false

/-- The action `wait x`. -/
def isWait (x : SyncKind) : TMAct Q Γ → Bool
  | .wait y => decide (y = x)
  | _ => false

open scoped Classical in
/-- The credit of a semaphore fact in a state: `1` if it is up, `0` if it is down. -/
noncomputable def credit (f : TMFact Q Γ) (s : Set (TMFact Q Γ)) : ℕ := if f ∈ s then 1 else 0

open scoped Classical in
@[simp] lemma credit_pos {f : TMFact Q Γ} {s : Set (TMFact Q Γ)} (h : f ∈ s) :
    credit f s = 1 := if_pos h

open scoped Classical in
@[simp] lemma credit_neg {f : TMFact Q Γ} {s : Set (TMFact Q Γ)} (h : f ∉ s) :
    credit f s = 0 := if_neg h

/-! ### A semaphore fact is a credit -/

/-- **The abstract counting lemma.**  If a fact `f` is raised exactly by the actions satisfying
`up`, lowered exactly by those satisfying `down`, and every `down` action needs it, then along
an executable action sequence the `down` actions never outnumber the `up` actions (up to the
credit stored in the state). -/
theorem countP_down_add_credit_le (f : TMFact Q Γ) (up down : TMAct Q Γ → Bool)
    (hmem : ∀ (a : TMAct Q Γ) (s : Set (TMFact Q Γ)),
      f ∈ (actionModel (Q := Q) (Γ := Γ)).transition a s ↔
        (up a = true ∨ (f ∈ s ∧ down a = false)))
    (hneed : ∀ (a : TMAct Q Γ) (s : Set (TMFact Q Γ)),
      (actionModel (Q := Q) (Γ := Γ)).Applicable a s → down a = true → f ∈ s) :
    ∀ (as : List (TMAct Q Γ)) (s : Set (TMFact Q Γ)),
      (actionModel (Q := Q) (Γ := Γ)).SeqApplicable as s →
        as.countP down + credit f ((actionModel (Q := Q) (Γ := Γ)).transitionSeq as s) ≤
          as.countP up + credit f s := by
  intro as
  induction as with
  | nil => intro s _; simp
  | cons a as ih =>
      intro s happ
      obtain ⟨ha, hrest⟩ := happ
      have hIH := ih _ hrest
      have hstep : credit f ((actionModel (Q := Q) (Γ := Γ)).transition a s) +
          (if down a = true then 1 else 0) ≤ (if up a = true then 1 else 0) + credit f s := by
        by_cases hu : up a = true
        · have hin : f ∈ (actionModel (Q := Q) (Γ := Γ)).transition a s :=
            (hmem a s).2 (Or.inl hu)
          by_cases hd : down a = true
          · have hfs : f ∈ s := hneed a s ha hd
            simp [hu, hd, hin, hfs]
          · simp [hu, hd, hin]
        · by_cases hd : down a = true
          · have hfs : f ∈ s := hneed a s ha hd
            have hout : f ∉ (actionModel (Q := Q) (Γ := Γ)).transition a s := by
              intro hcon
              rcases (hmem a s).1 hcon with h | ⟨-, h⟩
              · exact hu h
              · rw [hd] at h; exact Bool.noConfusion h
            simp [hu, hd, hout, hfs]
          · have hd' : down a = false := by simpa using hd
            by_cases hfs : f ∈ s
            · have hin : f ∈ (actionModel (Q := Q) (Γ := Γ)).transition a s :=
                (hmem a s).2 (Or.inr ⟨hfs, hd'⟩)
              simp [hu, hd, hin, hfs]
            · have hout : f ∉ (actionModel (Q := Q) (Γ := Γ)).transition a s := by
                intro hcon
                rcases (hmem a s).1 hcon with h | ⟨h, -⟩
                · exact hu h
                · exact hfs h
              simp [hu, hd, hout, hfs]
      rw [ActionModel.transitionSeq_cons, List.countP_cons, List.countP_cons]
      omega

/-- **The abstract counting lemma**, for a state in which the semaphore is down. -/
theorem countP_down_le_countP_up (f : TMFact Q Γ) (up down : TMAct Q Γ → Bool)
    (hmem : ∀ (a : TMAct Q Γ) (s : Set (TMFact Q Γ)),
      f ∈ (actionModel (Q := Q) (Γ := Γ)).transition a s ↔
        (up a = true ∨ (f ∈ s ∧ down a = false)))
    (hneed : ∀ (a : TMAct Q Γ) (s : Set (TMFact Q Γ)),
      (actionModel (Q := Q) (Γ := Γ)).Applicable a s → down a = true → f ∈ s)
    {as : List (TMAct Q Γ)} {s : Set (TMFact Q Γ)} (hs : f ∉ s)
    (happ : (actionModel (Q := Q) (Γ := Γ)).SeqApplicable as s) :
    as.countP down ≤ as.countP up := by
  have h := countP_down_add_credit_le f up down hmem hneed as s happ
  rw [credit_neg hs] at h
  omega

/-! ### The two semaphores of a channel -/

lemma mem_stepF_transition (x : SyncKind) (a : TMAct Q Γ) (s : Set (TMFact Q Γ)) :
    TMFact.stepF x ∈ (actionModel (Q := Q) (Γ := Γ)).transition a s ↔
      (isCall x a = true ∨ (TMFact.stepF x ∈ s ∧ isStart x a = false)) := by
  cases a <;>
    simp [ActionModel.transition, actionModel, TMEnc.add, TMEnc.del, isCall, isStart,
      Set.mem_setOf_eq, eq_comm]

lemma stepF_mem_of_start (x : SyncKind) (a : TMAct Q Γ) (s : Set (TMFact Q Γ))
    (ha : (actionModel (Q := Q) (Γ := Γ)).Applicable a s) (h : isStart x a = true) :
    TMFact.stepF x ∈ s := by
  cases a with
  | start y =>
      have hy : y = x := by simpa [isStart] using h
      subst hy
      exact ha (by simp [actionModel, TMEnc.prec])
  | _ => simp [isStart] at h

lemma mem_steppedF_transition (x : SyncKind) (a : TMAct Q Γ) (s : Set (TMFact Q Γ)) :
    TMFact.steppedF x ∈ (actionModel (Q := Q) (Γ := Γ)).transition a s ↔
      (isRespond x a = true ∨ (TMFact.steppedF x ∈ s ∧ isWait x a = false)) := by
  cases a <;>
    simp [ActionModel.transition, actionModel, TMEnc.add, TMEnc.del, isRespond, isWait,
      Set.mem_setOf_eq, eq_comm]

lemma steppedF_mem_of_wait (x : SyncKind) (a : TMAct Q Γ) (s : Set (TMFact Q Γ))
    (ha : (actionModel (Q := Q) (Γ := Γ)).Applicable a s) (h : isWait x a = true) :
    TMFact.steppedF x ∈ s := by
  cases a with
  | wait y =>
      have hy : y = x := by simpa [isWait] using h
      subst hy
      exact ha (by simp [actionModel, TMEnc.prec])
  | _ => simp [isWait] at h

/-- **A `start x` action consumes a `call x` action.**  Along an executable action sequence
starting with the semaphore `x_step` down, there are never more `start x` than `call x`
actions. -/
theorem countP_start_le_countP_call (x : SyncKind) {as : List (TMAct Q Γ)}
    {s : Set (TMFact Q Γ)} (hs : TMFact.stepF x ∉ s)
    (happ : (actionModel (Q := Q) (Γ := Γ)).SeqApplicable as s) :
    as.countP (isStart x) ≤ as.countP (isCall x) :=
  countP_down_le_countP_up _ _ _ (mem_stepF_transition x) (stepF_mem_of_start x) hs happ

/-- **A `wait x` action consumes a `respond x` action.**  Along an executable action sequence
starting with the semaphore `x_stepped` down, there are never more `wait x` than `respond x`
actions. -/
theorem countP_wait_le_countP_respond (x : SyncKind) {as : List (TMAct Q Γ)}
    {s : Set (TMFact Q Γ)} (hs : TMFact.steppedF x ∉ s)
    (happ : (actionModel (Q := Q) (Γ := Γ)).SeqApplicable as s) :
    as.countP (isWait x) ≤ as.countP (isRespond x) :=
  countP_down_le_countP_up _ _ _ (mem_steppedF_transition x) (steppedF_mem_of_wait x) hs happ

end TMEnc

end HTN
