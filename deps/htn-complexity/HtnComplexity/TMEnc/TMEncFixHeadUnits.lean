import HtnComplexity.TMEnc.TMEncFixHeadRead
/-!
# How far the head counter can have got: toggles against handshakes

The stream of the repaired head counter is `K² + 3K + 1` **units**, each of which is
`start_head, toggle, respond_head` (`HTN.TMEnc.headUnitActs`).  Consequently, at any point of the stream the number of toggles
performed is squeezed between the number of answers already given and the number of requests
already consumed:

`HTN.TMEnc.headStream_prefix_toggle_bounds` —
`#respond_head ≤ #toggles ≤ #start_head` for every prefix of `HTN.TMEnc.headStream`.

Together with the two semaphores of the channel `head` this is what pins down *exactly* which
mark of the head counter a cell of the tape reads.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {K : ℕ}

/-! ### A stream of units -/

/-- The stream of units whose toggles are the actions `ts`. -/
def unitList (ts : List (TMAct Q Γ)) : List (TMAct Q Γ) :=
  (ts.map fun t => [TMAct.start SyncKind.head, t, TMAct.respond SyncKind.head]).flatten

@[simp] lemma unitList_nil : unitList ([] : List (TMAct Q Γ)) = [] := rfl

lemma unitList_cons (t : TMAct Q Γ) (ts : List (TMAct Q Γ)) :
    unitList (t :: ts) =
      TMAct.start SyncKind.head :: t :: TMAct.respond SyncKind.head :: unitList ts := rfl

lemma headUnitActs_eq (b : Bool) :
    headUnitActs Q Γ b =
      [TMAct.start SyncKind.head, togAct Q Γ b, TMAct.respond SyncKind.head] := rfl

/-! ### The three head actions, evaluated -/

lemma isStart_start_head : isStart SyncKind.head (TMAct.start SyncKind.head : TMAct Q Γ) = true :=
  rfl

lemma headTog_start_head : headTog (TMAct.start SyncKind.head : TMAct Q Γ) = false := rfl

lemma isRespond_start_head :
    isRespond SyncKind.head (TMAct.start SyncKind.head : TMAct Q Γ) = false := rfl

lemma isStart_respond_head :
    isStart SyncKind.head (TMAct.respond SyncKind.head : TMAct Q Γ) = false := rfl

lemma headTog_respond_head : headTog (TMAct.respond SyncKind.head : TMAct Q Γ) = false := rfl

lemma isRespond_respond_head :
    isRespond SyncKind.head (TMAct.respond SyncKind.head : TMAct Q Γ) = true := rfl

lemma isStart_retractHead : isStart SyncKind.head (TMAct.retractHead : TMAct Q Γ) = false := rfl

lemma headTog_retractHead : headTog (TMAct.retractHead : TMAct Q Γ) = true := rfl

lemma isRespond_retractHead :
    isRespond SyncKind.head (TMAct.retractHead : TMAct Q Γ) = false := rfl

/-- The stream of the units of the head counter is a `HTN.TMEnc.unitList`. -/
lemma roundStream_headUnitActs (s : ℕ → Bool) : ∀ R : ℕ,
    (roundStream R fun u => headUnitActs Q Γ (s u)) =
      unitList (((List.range R).map s).map (togAct Q Γ)) := by
  intro R
  induction R with
  | zero => rfl
  | succ R ih =>
      rw [roundStream_succ, ih, List.range_succ, List.map_append, List.map_append]
      simp [unitList, headUnitActs_eq]

/-! ### The counting invariant of a stream of units -/

/-- **In a prefix of a stream of units, the answers given are at most the toggles performed, and
those are at most the requests consumed.** -/
lemma prefix_unitList_counts : ∀ ts : List (TMAct Q Γ),
    (∀ t ∈ ts, headTog t = true ∧ isStart SyncKind.head t = false ∧
      isRespond SyncKind.head t = false) →
    ∀ P : List (TMAct Q Γ), P <+: unitList ts →
      P.countP (isRespond SyncKind.head) ≤ P.countP headTog ∧
        P.countP headTog ≤ P.countP (isStart SyncKind.head) := by
  intro ts
  induction ts with
  | nil =>
      intro _ P hP
      have hP0 : P = [] := List.prefix_nil.1 (by simpa [unitList] using hP)
      subst hP0
      simp
  | cons t ts ih =>
      intro hall P hP
      obtain ⟨htog, hst, hre⟩ := hall t (by simp)
      rw [unitList_cons] at hP
      cases P with
      | nil => simp
      | cons a₁ P₁ =>
          obtain ⟨rfl, hP₁⟩ := List.cons_prefix_cons.1 hP
          cases P₁ with
          | nil =>
              simp only [List.countP_cons, List.countP_nil, isStart_start_head,
                headTog_start_head, isRespond_start_head, if_true, if_false,
                Bool.false_eq_true, zero_add]
              omega
          | cons a₂ P₂ =>
              obtain ⟨rfl, hP₂⟩ := List.cons_prefix_cons.1 hP₁
              cases P₂ with
              | nil =>
                  simp only [List.countP_cons, List.countP_nil, isStart_start_head,
                    headTog_start_head, isRespond_start_head, htog, hst, hre, if_true, if_false,
                    Bool.false_eq_true, zero_add]
                  omega
              | cons a₃ P₃ =>
                  obtain ⟨rfl, hP₃⟩ := List.cons_prefix_cons.1 hP₂
                  have hrec := ih (fun u hu => hall u (by simp [hu])) P₃ hP₃
                  simp only [List.countP_cons, isStart_start_head, headTog_start_head,
                    isRespond_start_head, isStart_respond_head, headTog_respond_head,
                    isRespond_respond_head, htog, hst, hre, if_true, if_false,
                    Bool.false_eq_true]
                  omega

/-! ### The invariant for the head counter -/

/-- **At any point of the stream of the repaired head counter, the number of toggles is at least
the number of answers it has given and at most the number of requests it has consumed.**

For the head counter as printed the second inequality holds only up to the initial retraction,
which toggles the head facts without consuming a request of its own; that one unit of slack is
exactly what makes the printed construction unsound (see `NOTES.md`).  The repaired counter of
`HTN.TMEnc.headChainFix` is a plain stream of units, so it has none. -/
theorem headStream_prefix_toggle_bounds {H : List (TMAct Q Γ)} (hH : H <+: headStream Q Γ K) :
    H.countP (isRespond SyncKind.head) ≤ H.countP headTog ∧
      H.countP headTog ≤ H.countP (isStart SyncKind.head) := by
  rw [show (headStream Q Γ K) =
    roundStream (K * K + 3 * K + 1) (fun u => headUnitActs Q Γ (headMarkStd K u)) from rfl,
    roundStream_headUnitActs] at hH
  refine prefix_unitList_counts _ ?_ H hH
  intro t ht
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ht
  cases b <;> exact ⟨rfl, rfl, rfl⟩

end TMEnc

end HTN
