import ComplexityTheory.Computable.CounterState
import HtnComplexity.Computable.StepChain
/-!
# The counting family: a small domain that reads one letter of a long instance

This file writes down the family of source problems the impossibility argument of
`HtnCompilability/Computable/NoVocCompilation.lean` runs on.

For a number `r` of counter bits and an index `i` there is a domain description
`HTN.Syn.cntDom r i` of size `O(r ^ 2)`, over the `2 * r + 1` facts of
`ComplexityTheory/Computable/CounterState.lean`, and for every bit list `w` an instance
description `HTN.Syn.wordInst r w` whose initial task network is the **chain** of one compound
task per letter of `w`:

* the compound name of a letter is `HTN.Syn.cA` for `false` and `HTN.Syn.cB` for `true`;
* every task decomposes into one increment of the counter, so after `t` tasks the counter holds
  the value `t`;
* a `true` letter may instead decompose into the *marking* action of `cntDom r i`, whose
  precondition is the full bit pattern of the value `i` and which adds the goal fact.

Hence `HTN.Syn.solvable_wordInst_iff`:

    Solvable (cntDom r i) (wordInst r w) ↔ w.getI i = true

— the `2 ^ r` domains of the family read the `2 ^ r` letters of a single instance, each with a
description of size polynomial in `r`.  The family lies in every structural class: its methods
are totally ordered, regular, acyclic and tail recursive (`HTN.Syn.cntDom_methodsTO` and
friends), and its instances are totally ordered.
-/

namespace HTN

namespace Syn

open Bits

/-! ### The domain and the instances -/

/-- The compound name of a `false` letter. -/
def cA : ℕ := 1

/-- The compound name of a `true` letter. -/
def cB : ℕ := 2

theorem cA_ne_cB : cA ≠ cB := by decide

/-- The name of a letter. -/
def letterName (b : Bool) : ℕ := if b then cB else cA

@[simp] theorem letterName_false : letterName false = cA := rfl

@[simp] theorem letterName_true : letterName true = cB := rfl

theorem letterName_eq_cA {b : Bool} (h : letterName b = cA) : b = false := by
  cases b
  · rfl
  · exact absurd h.symm cA_ne_cB

theorem letterName_eq_cB {b : Bool} (h : letterName b = cB) : b = true := by
  cases b
  · exact absurd h cA_ne_cB
  · rfl

/-- The `m`-th named step of the counting domain: an increment under a `false` letter
(`m < r`), an increment under a `true` letter (`r ≤ m < 2 * r`), and the marking step under a
`true` letter (`m = 2 * r`). -/
def cntEntry (r i m : ℕ) : StepEntry :=
  if m < r then (cA, incPrec m, incAdd m, incPrec m)
  else if m < 2 * r then (cB, incPrec (m - r), incAdd (m - r), incPrec (m - r))
  else (cB, stList (cnt r i), gF r :: stList (cnt r (i + 1)), stList (cnt r i))

/-- The named steps of the counting domain. -/
def cntP (r i : ℕ) : List StepEntry := (List.range (2 * r + 1)).map (cntEntry r i)

/-- **The counting domain** of `r` bits and index `i`. -/
def cntDom (r i : ℕ) : DomDesc := stepDom (cntP r i)

/-- **The instance of a bit list**: the counter starts at zero, the goal is the goal fact, and
the initial task network is the chain of the letters of `w`. -/
def wordInst (r : ℕ) (w : List Bool) : InstDesc :=
  stepInst (w.map letterName) (stList (zeros r)) [gF r]

variable {r i : ℕ}

@[simp] theorem length_cntP : (cntP r i).length = 2 * r + 1 := by simp [cntP]

theorem getI_cntP {m : ℕ} (h : m < 2 * r + 1) : (cntP r i).getI m = cntEntry r i m :=
  getI_range_map _ h

theorem cntEntry_inc_lt {m : ℕ} (h : m < r) :
    cntEntry r i m = (cA, incPrec m, incAdd m, incPrec m) := by
  rw [cntEntry, if_pos h]

theorem cntEntry_inc_ge {m : ℕ} (h1 : r ≤ m) (h2 : m < 2 * r) :
    cntEntry r i m = (cB, incPrec (m - r), incAdd (m - r), incPrec (m - r)) := by
  rw [cntEntry, if_neg (by omega), if_pos h2]

theorem cntEntry_mark :
    cntEntry r i (2 * r) =
      (cB, stList (cnt r i), gF r :: stList (cnt r (i + 1)), stList (cnt r i)) := by
  rw [cntEntry, if_neg (by omega), if_neg (by omega)]

/-! ### The family lies in the classes -/

theorem cntDom_methodsTO : (cntDom r i).MethodsTO := stepDom_methodsTO

theorem cntDom_methodsReg : (cntDom r i).MethodsReg := stepDom_methodsReg

theorem cntDom_isAcyclic : (cntDom r i).IsAcyclic := stepDom_isAcyclic

theorem cntDom_isTailRec : (cntDom r i).IsTailRec := stepDom_isTailRec

theorem wordInst_isTO {w : List Bool} : (wordInst r w).IsTO := stepInst_isTO

/-! ### The action model of the counting domain -/

theorem applicable_cntDom {m : ℕ} (hm : m < 2 * r + 1) {s : Set ℕ} :
    (cntDom r i).toDomain.Applicable m s ↔ {f | f ∈ (cntEntry r i m).2.1} ⊆ s := by
  show (cntDom r i).prec m ⊆ s ↔ _
  rw [cntDom, prec_stepDom (by rw [length_cntP]; exact hm), getI_cntP hm]

theorem transition_cntDom {m : ℕ} (hm : m < 2 * r + 1) {s : Set ℕ} :
    (cntDom r i).toDomain.transition m s =
      (s \ {f | f ∈ (cntEntry r i m).2.2.2}) ∪ {f | f ∈ (cntEntry r i m).2.2.1} := by
  show (s \ (cntDom r i).del m) ∪ (cntDom r i).add m = _
  rw [cntDom, del_stepDom (by rw [length_cntP]; exact hm),
    add_stepDom (by rw [length_cntP]; exact hm), getI_cntP hm]

/-! ### The steps of the family -/

/-- The relation "the step `m` serves a task named `c`". -/
def cntStep (r i c m : ℕ) : Prop := m < 2 * r + 1 ∧ (cntEntry r i m).1 = c

/-- **An increment step** is available under either letter as long as the counter is not at its
maximum. -/
theorem exists_inc_step (t : ℕ) (b mk : Bool) (ht : t + 1 < 2 ^ r) :
    ∃ m, cntStep r i (letterName b) m ∧
      (cntDom r i).toDomain.Applicable m (stateAt r t mk) ∧
      (cntDom r i).toDomain.transition m (stateAt r t mk) = stateAt r (t + 1) mk := by
  obtain ⟨j, hj, hlow, hzero⟩ := exists_low_zero (false_mem_cnt ht)
  rw [length_cnt] at hj
  refine ⟨if b then j + r else j, ?_, ?_, ?_⟩
  · cases b with
    | false => exact ⟨by simp; omega, by simp [cntEntry_inc_lt hj, letterName]⟩
    | true => exact ⟨by simp; omega, by simp [cntEntry_inc_ge (show r ≤ j + r by omega) (show j + r < 2 * r by omega), letterName]⟩
  · cases b with
    | false =>
      rw [if_neg (by simp), applicable_cntDom (by omega), cntEntry_inc_lt hj]
      exact (incPrec_subset_iff hj).2 ⟨hlow, hzero⟩
    | true =>
      rw [if_pos rfl, applicable_cntDom (by omega), cntEntry_inc_ge (by omega) (by omega)]
      have hjj : j + r - r = j := by omega
      rw [hjj]
      exact (incPrec_subset_iff hj).2 ⟨hlow, hzero⟩
  · cases b with
    | false =>
      rw [if_neg (by simp), transition_cntDom (by omega), cntEntry_inc_lt hj]
      exact inc_state hj hlow hzero
    | true =>
      rw [if_pos rfl, transition_cntDom (by omega), cntEntry_inc_ge (by omega) (by omega)]
      have hjj : j + r - r = j := by omega
      rw [hjj]
      exact inc_state hj hlow hzero

/-- **The marking step** is available under a `true` letter, and exactly at time `i`. -/
theorem mark_step (t : ℕ) (mk : Bool) (hti : cnt r i = cnt r t) :
    cntStep r i (letterName true) (2 * r) ∧
      (cntDom r i).toDomain.Applicable (2 * r) (stateAt r t mk) ∧
      (cntDom r i).toDomain.transition (2 * r) (stateAt r t mk) = stateAt r (t + 1) true := by
  refine ⟨⟨by omega, by simp [cntEntry_mark, letterName]⟩, ?_, ?_⟩
  · rw [applicable_cntDom (by omega), cntEntry_mark]
    exact markPrec_subset_iff.2 hti
  · rw [transition_cntDom (by omega), cntEntry_mark]
    exact mark_state hti

/-! ### Running the chain -/

/-- **The chain can always be run**: choosing an increment for every letter takes the counter
from `t` to `t + |w|` and changes nothing else. -/
theorem exists_cnt_plan :
    ∀ (w : List Bool) (t : ℕ) (mk : Bool), t + w.length + 1 ≤ 2 ^ r →
      ∃ as, List.Forall₂ (cntStep r i) (w.map letterName) as ∧
        (cntDom r i).toDomain.SeqApplicable as (stateAt r t mk) ∧
        (cntDom r i).toDomain.transitionSeq as (stateAt r t mk) = stateAt r (t + w.length) mk := by
  intro w
  induction w with
  | nil => intro t mk _; exact ⟨[], List.Forall₂.nil, trivial, by simp⟩
  | cons b w' ih =>
    intro t mk h
    simp only [List.length_cons] at h
    obtain ⟨m, hstep, happ, htrans⟩ := exists_inc_step (r := r) (i := i) t b mk (by omega)
    obtain ⟨as', hplan', happ', hstate'⟩ := ih (t + 1) mk (by omega)
    refine ⟨m :: as', ?_, ?_, ?_⟩
    · rw [List.map_cons]
      exact List.Forall₂.cons hstep hplan'
    · rw [ActionModel.seqApplicable_cons, htrans]
      exact ⟨happ, happ'⟩
    · rw [ActionModel.transitionSeq_cons, htrans, hstate']
      congr 1
      simp only [List.length_cons]
      omega

/-- **What a run of the chain can achieve**: the goal fact is reached exactly when the letter at
the position the domain counts to is a `true`. -/
theorem cnt_run_iff (hi : i < 2 ^ r) :
    ∀ (w : List Bool) (t : ℕ) (mk : Bool), t + w.length + 1 ≤ 2 ^ r →
      ((∃ as, List.Forall₂ (cntStep r i) (w.map letterName) as ∧
          (cntDom r i).toDomain.SeqApplicable as (stateAt r t mk) ∧
          gF r ∈ (cntDom r i).toDomain.transitionSeq as (stateAt r t mk))
        ↔ (mk = true ∨ ∃ u, u < w.length ∧ w.getI u = true ∧ t + u = i)) := by
  intro w
  induction w with
  | nil =>
    intro t mk _
    constructor
    · rintro ⟨as, hplan, -, hgoal⟩
      cases hplan
      rw [ActionModel.transitionSeq_nil] at hgoal
      exact Or.inl (gF_mem_stateAt.1 hgoal)
    · rintro (rfl | ⟨u, hu, -, -⟩)
      · exact ⟨[], List.Forall₂.nil, trivial, gF_mem_stateAt.2 rfl⟩
      · simp at hu
  | cons b w' ih =>
    intro t mk h
    simp only [List.length_cons] at h
    have htr : t < 2 ^ r := by omega
    constructor
    · rintro ⟨as, hplan, happ, hgoal⟩
      rw [List.map_cons] at hplan
      obtain ⟨m, as', hhead, htail, rfl⟩ :
          ∃ m as', cntStep r i (letterName b) m ∧
            List.Forall₂ (cntStep r i) (w'.map letterName) as' ∧ as = m :: as' := by
        cases hplan with
        | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
      obtain ⟨hm, hname⟩ := hhead
      rw [ActionModel.seqApplicable_cons] at happ
      rw [ActionModel.transitionSeq_cons] at hgoal
      by_cases hlt : m < r
      · -- an increment under a `false` letter
        rw [cntEntry_inc_lt hlt] at hname
        have hb : b = false := letterName_eq_cA hname.symm
        rw [applicable_cntDom hm, cntEntry_inc_lt hlt] at happ
        obtain ⟨hlow, hzero⟩ := (incPrec_subset_iff hlt).1 happ.1
        have htrans : (cntDom r i).toDomain.transition m (stateAt r t mk) =
            stateAt r (t + 1) mk := by
          rw [transition_cntDom hm, cntEntry_inc_lt hlt]
          exact inc_state hlt hlow hzero
        rw [htrans] at happ hgoal
        rcases (ih (t + 1) mk (by omega)).1 ⟨as', htail, happ.2, hgoal⟩ with hmk | ⟨u, hu, hval, hsum⟩
        · exact Or.inl hmk
        · refine Or.inr ⟨u + 1, by simp; omega, ?_, by omega⟩
          rw [show (b :: w').getI (u + 1) = w'.getI u from rfl]
          exact hval
      · by_cases hmid : m < 2 * r
        · -- an increment under a `true` letter
          rw [cntEntry_inc_ge (by omega) hmid] at hname
          have hj : m - r < r := by omega
          rw [applicable_cntDom hm, cntEntry_inc_ge (by omega) hmid] at happ
          obtain ⟨hlow, hzero⟩ := (incPrec_subset_iff hj).1 happ.1
          have htrans : (cntDom r i).toDomain.transition m (stateAt r t mk) =
              stateAt r (t + 1) mk := by
            rw [transition_cntDom hm, cntEntry_inc_ge (by omega) hmid]
            exact inc_state hj hlow hzero
          rw [htrans] at happ hgoal
          rcases (ih (t + 1) mk (by omega)).1 ⟨as', htail, happ.2, hgoal⟩ with
            hmk | ⟨u, hu, hval, hsum⟩
          · exact Or.inl hmk
          · refine Or.inr ⟨u + 1, by simp; omega, ?_, by omega⟩
            rw [show (b :: w').getI (u + 1) = w'.getI u from rfl]
            exact hval
        · -- the marking step
          have hm2 : m = 2 * r := by omega
          subst hm2
          rw [cntEntry_mark] at hname
          have hb : b = true := letterName_eq_cB hname.symm
          rw [applicable_cntDom hm, cntEntry_mark] at happ
          have hti : i = t := cnt_inj hi htr (by simpa using markPrec_subset_iff.1 happ.1)
          exact Or.inr ⟨0, by simp, by rw [show (b :: w').getI 0 = b from rfl, hb], by omega⟩
    · rintro (rfl | ⟨u, hu, hval, hsum⟩)
      · obtain ⟨as, hplan, happ, hstate⟩ :=
          exists_cnt_plan (r := r) (i := i) (b :: w') t true (by simp only [List.length_cons]; omega)
        exact ⟨as, hplan, happ, by rw [hstate]; exact gF_mem_stateAt.2 rfl⟩
      · cases u with
        | zero =>
          have hb : b = true := by rw [show (b :: w').getI 0 = b from rfl] at hval; exact hval
          have hti : cnt r i = cnt r t := by rw [show i = t by omega]
          obtain ⟨hstep, happ, htrans⟩ := mark_step (r := r) (i := i) t mk hti
          obtain ⟨as', hplan', happ', hstate'⟩ :=
            exists_cnt_plan (r := r) (i := i) w' (t + 1) true (by omega)
          refine ⟨2 * r :: as', ?_, ?_, ?_⟩
          · rw [List.map_cons, hb]
            exact List.Forall₂.cons hstep hplan'
          · rw [ActionModel.seqApplicable_cons, htrans]
            exact ⟨happ, happ'⟩
          · rw [ActionModel.transitionSeq_cons, htrans, hstate']
            exact gF_mem_stateAt.2 rfl
        | succ u' =>
          obtain ⟨m, hstep, happ, htrans⟩ := exists_inc_step (r := r) (i := i) t b mk (by omega)
          have hrest : ∃ as', List.Forall₂ (cntStep r i) (w'.map letterName) as' ∧
              (cntDom r i).toDomain.SeqApplicable as' (stateAt r (t + 1) mk) ∧
              gF r ∈ (cntDom r i).toDomain.transitionSeq as' (stateAt r (t + 1) mk) := by
            refine (ih (t + 1) mk (by omega)).2 (Or.inr ⟨u', ?_, ?_, by omega⟩)
            · simp only [List.length_cons] at hu; omega
            · rw [show (b :: w').getI (u' + 1) = w'.getI u' from rfl] at hval; exact hval
          obtain ⟨as', hplan', happ', hgoal'⟩ := hrest
          refine ⟨m :: as', ?_, ?_, ?_⟩
          · rw [List.map_cons]
            exact List.Forall₂.cons hstep hplan'
          · rw [ActionModel.seqApplicable_cons, htrans]
            exact ⟨happ, happ'⟩
          · rw [ActionModel.transitionSeq_cons, htrans]
            exact hgoal'

/-! ### Correctness of the family -/

/-- **The counting family reads one letter of the instance**: the problem of the domain of index
`i` and the instance of the bit list `w` is solvable exactly when the `i`-th letter of `w` is a
`true`. -/
theorem solvable_wordInst_iff {w : List Bool} (hw : w.length + 1 ≤ 2 ^ r) (hi : i < w.length) :
    Solvable (cntDom r i) (wordInst r w) ↔ w.getI i = true := by
  have hinit : {f | f ∈ stList (zeros r)} = stateAt r 0 false := by
    simp [stateAt, cnt_zero]
  have hplan : ∀ (c m : ℕ), (m < (cntP r i).length ∧ ((cntP r i).getI m).1 = c) ↔
      cntStep r i c m := by
    intro c m
    constructor
    · rintro ⟨h1, h2⟩
      rw [length_cntP] at h1
      rw [getI_cntP h1] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [length_cntP]; exact h1, by rw [getI_cntP h1]; exact h2⟩
  rw [cntDom, wordInst, solvable_step_iff]
  rw [← cntDom]
  constructor
  · rintro ⟨as, hf, happ, hgoal⟩
    have hf' : List.Forall₂ (cntStep r i) (w.map letterName) as :=
      hf.imp (fun {c m} hcm => (hplan c m).1 hcm)
    rw [hinit] at happ hgoal
    have hgoal' : gF r ∈ (cntDom r i).toDomain.transitionSeq as (stateAt r 0 false) :=
      hgoal (gF r) (by simp)
    rcases (cnt_run_iff (r := r) (i := i) (by omega) w 0 false (by omega)).1 ⟨as, hf', happ, hgoal'⟩ with
      hmk | ⟨u, hu, hval, hsum⟩
    · exact absurd hmk (by simp)
    · rw [show i = u by omega]; exact hval
  · intro hval
    obtain ⟨as, hf', happ, hgoal'⟩ :=
      (cnt_run_iff (r := r) (i := i) (by omega) w 0 false (by omega)).2 (Or.inr ⟨i, hi, hval, by omega⟩)
    refine ⟨as, hf'.imp (fun {c m} hcm => (hplan c m).2 hcm), ?_, ?_⟩
    · rw [hinit]; exact happ
    · intro f hf
      rw [List.mem_singleton] at hf
      subst hf
      rw [hinit]
      exact hgoal'

end Syn

end HTN
