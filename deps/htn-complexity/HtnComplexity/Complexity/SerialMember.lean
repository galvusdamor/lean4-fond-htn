import HtnComplexity.Complexity.SerialRead
/-!
# Membership of a fixed fact, read off the serialisation in polynomial time

Two of the four families of bits that make up the bounded profile a fixed domain description sees
(`HTN.Syn.profB`) are of the form

    does the fixed fact `f` occur in the initial state / in the goal of the instance?

This file shows that both are **decided in polynomial time** from the serialisation of the
instance description, by exhibiting the finite-state scan that answers them and feeding it to
`HTN.Syn.polyTimePred_of_dfaList` (`HtnComplexity/Complexity/SerialRead.lean`), which rests
on "a finite-state scan is a function of Cobham's class"
(`ComplexityTheory/Complexity/CobhamDFA.lean`).

## The scan

A serialised description is five self-delimiting lists in a row — the initial state, the goal,
and the three components of the initial task network — each of them a `HTN.Syn.blist`, that is
a sequence of entries `true, bstr x` closed by a `false`, where `bstr x` writes the bits of `x`
as pairs `true, b` and closes with a `false`.  The scan `HTN.Syn.PatScan.step P n` walks the
string from the left carrying

* the number of complete lists seen so far (capped, so that the state space is finite),
* whether a match has already been found in the list number `n`,
* where in the current entry it is (at list level, expecting an entry marker, expecting a bit),
* how far the current entry agrees with the fixed pattern `P`, and whether it still agrees.

`HTN.Syn.PatScan.foldl_blist` is the key lemma: reading a whole list transports the state to the
next list and records whether the pattern occurs among its entries.  Applied five times it gives
`HTN.Syn.PatScan.scan_instSer_zero` and `HTN.Syn.PatScan.scan_instSer_one`, and hence

* `HTN.Syn.polyTimePred_memB_initList` — `fun q => memB q.initList f` is polynomial time;
* `HTN.Syn.polyTimePred_memB_goalList` — `fun q => memB q.goalList f` is polynomial time.

What is still missing for `HTN.Syn.ProfileReadable` is the head bit family (the root name against
a fixed method head — again a finite-state property) and the last bit, whether every goal fact
outside the domain's vocabulary already holds, which is *not* a finite-state property: it
compares two unbounded parts of the input and needs a genuine two-pointer algorithm.  See §23 of
`NOTES.md`.
-/

namespace HTN

namespace Syn

namespace PatScan

open PTime

/-- The state of the scan: the number of complete lists read, whether a match has been found,
the position inside the current entry (`0` at list level, `1` expecting an entry marker, `2`
expecting a bit), how far the entry agrees with the pattern, and whether it still agrees. -/
abbrev St : Type := ℕ × Bool × ℕ × ℕ × Bool

/-- Comparing the next bit of an entry with the pattern. -/
def cmpStep (P : List Bool) (j : ℕ) (ok : Bool) (b : Bool) : ℕ × Bool :=
  if j < P.length ∧ P.getD j false = b then (j + 1, ok) else (j, false)

theorem cmpStep_le {P : List Bool} {j : ℕ} {ok b : Bool} (h : j ≤ P.length) :
    (cmpStep P j ok b).1 ≤ P.length := by
  rw [cmpStep]
  split
  · next h' => simpa using h'.1
  · simpa using h

/-- The transition of the scan. -/
def step (P : List Bool) (n : ℕ) (s : St) (b : Bool) : St :=
  if s.2.2.1 = 0 then
    (if b then (s.1, s.2.1, 1, 0, true) else (min (s.1 + 1) (n + 1), s.2.1, 0, 0, true))
  else if s.2.2.1 = 1 then
    (if b then (s.1, s.2.1, 2, s.2.2.2.1, s.2.2.2.2)
      else (s.1, s.2.1 ||
        (decide (s.1 = n) && s.2.2.2.2 && decide (s.2.2.2.1 = P.length)), 0, 0, true))
  else
    (s.1, s.2.1, 1, (cmpStep P s.2.2.2.1 s.2.2.2.2 b).1, (cmpStep P s.2.2.2.1 s.2.2.2.2 b).2)

/-- The states the scan uses: the counter of complete lists is capped at `n + 1`, the mode is one
of three, and the position in the pattern never exceeds its length. -/
def states (P : List Bool) (n : ℕ) : List St :=
  (List.range (n + 2)).flatMap fun i =>
    [false, true].flatMap fun found =>
      (List.range 3).flatMap fun m =>
        (List.range (P.length + 1)).flatMap fun j =>
          [false, true].map fun ok => (i, found, m, j, ok)

theorem mem_states_iff (P : List Bool) (n : ℕ) (s : St) :
    s ∈ states P n ↔ s.1 ≤ n + 1 ∧ s.2.2.1 ≤ 2 ∧ s.2.2.2.1 ≤ P.length := by
  obtain ⟨i, found, m, j, ok⟩ := s
  simp only [states, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', found', hf', m', hm', j', hj', ok', hok', h1, h2, h3, h4, h5⟩
    subst h1; subst h3; subst h4
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨i, by omega, found, by cases found <;> simp, m, by omega, j, by omega, ok,
      by cases ok <;> simp, rfl, rfl, rfl, rfl, rfl⟩

theorem init_mem_states (P : List Bool) (n : ℕ) :
    ((0, false, 0, 0, true) : St) ∈ states P n :=
  (mem_states_iff P n _).2 ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem step_mem (P : List Bool) (n : ℕ) {s : St} (hs : s ∈ states P n) (b : Bool) :
    step P n s b ∈ states P n := by
  rw [mem_states_iff] at hs ⊢
  obtain ⟨h1, h2, h3⟩ := hs
  rw [step]
  split
  · split
    all_goals simp
    all_goals omega
  · split
    · split
      all_goals simp
      all_goals omega
    · refine ⟨by simpa using h1, by simp, ?_⟩
      simpa using cmpStep_le (P := P) (ok := s.2.2.2.2) (b := b) h3

/-! ### Reading one entry -/

/-- **Reading an entry.**  From the state just after the entry marker, the self-delimiting bits
of `x` are consumed and the scan returns to list level, recording a match when the entry agrees
with the pattern from position `j` on and the list is the one being watched. -/
theorem foldl_bstr (P : List Bool) (n : ℕ) : ∀ (x : List Bool) (i : ℕ) (found : Bool) (j : ℕ)
    (ok : Bool), j ≤ P.length →
    (bstr x).foldl (step P n) (i, found, 1, j, ok)
      = (i, found || (decide (i = n) && ok && decide (P.drop j = x)), 0, 0, true) := by
  intro x
  induction x with
  | nil =>
    intro i found j ok hj
    simp only [bstr_nil, List.foldl_cons, List.foldl_nil, step]
    simp [List.drop_eq_nil_iff, show (j = P.length) ↔ (P.length ≤ j) from by omega]
  | cons b x ih =>
    intro i found j ok hj
    have h1 : step P n (i, found, 1, j, ok) true = (i, found, 2, j, ok) := by simp [step]
    by_cases hc : j < P.length ∧ P.getD j false = b
    · have hstep : cmpStep P j ok b = (j + 1, ok) := by rw [cmpStep, if_pos hc]
      have h2 : step P n (i, found, 2, j, ok) b = (i, found, 1, j + 1, ok) := by
        simp [step, hstep]
      have hdrop : P.drop j = b :: P.drop (j + 1) := by
        rw [← hc.2, List.getD_eq_getElem _ _ hc.1]
        exact List.drop_eq_getElem_cons hc.1
      have hih := ih i found (j + 1) ok (by omega)
      simp only [bstr_cons, List.foldl_cons, h1, h2, hih, hdrop]
      simp
    · have hstep : cmpStep P j ok b = (j, false) := by rw [cmpStep, if_neg hc]
      have h2 : step P n (i, found, 2, j, ok) b = (i, found, 1, j, false) := by
        simp [step, hstep]
      have hne : P.drop j ≠ b :: x := by
        intro hdrop
        rcases lt_or_ge j P.length with hlt | hge
        · rw [List.drop_eq_getElem_cons hlt] at hdrop
          refine hc ⟨hlt, ?_⟩
          rw [List.getD_eq_getElem _ _ hlt]
          exact (List.cons_eq_cons.1 hdrop).1
        · rw [List.drop_eq_nil_of_le hge] at hdrop
          simp at hdrop
      have hih := ih i found j false (by omega)
      simp only [bstr_cons, List.foldl_cons, h1, h2, hih]
      simp [hne]

/-! ### Reading one list -/

/-- **Reading a list.**  The scan moves on to the next list, and records whether the pattern
occurs among the entries of the list it has just read — if that was the list it watches. -/
theorem foldl_blist (P : List Bool) (n : ℕ) : ∀ (l : List (List Bool)) (i : ℕ) (found : Bool)
    (j : ℕ) (ok : Bool),
    (blist l).foldl (step P n) (i, found, 0, j, ok)
      = (min (i + 1) (n + 1), found || (decide (i = n) && decide (P ∈ l)), 0, 0, true) := by
  intro l
  induction l with
  | nil =>
    intro i found j ok
    simp [blist, step]
  | cons x l ih =>
    intro i found j ok
    have hmark : step P n (i, found, 0, j, ok) true = (i, found, 1, 0, true) := by simp [step]
    have hbs := foldl_bstr P n x i found 0 true (by omega)
    simp only [blist_cons, List.foldl_cons, List.foldl_append, hmark, hbs, List.drop_zero]
    rw [ih]
    have hmem : (decide (P ∈ x :: l)) = (decide (P = x) || decide (P ∈ l)) := by
      by_cases h1 : P = x <;> by_cases h2 : P ∈ l <;> simp [List.mem_cons, h1, h2]
    rw [hmem]
    cases found <;> cases hin : decide (i = n) <;> cases hx : decide (P = x) <;>
      cases hl : decide (P ∈ l) <;> simp

end PatScan

/-! ### The two profile bit families -/

open PTime PatScan

/-- The five self-delimiting lists a serialised description consists of. -/
theorem instSer_eq_blists (q : InstDesc) :
    instSer q = blist (q.initList.map bitsOfNat) ++ (blist (q.goalList.map bitsOfNat) ++
      (blist (q.tnI.ids.map bitsOfNat) ++ (blist (q.tnI.ordList.map serPair) ++
        blist (q.tnI.lbl.map serLbl)))) := by
  simp [instSer, serNatList, tnSer, serPairList, serLblList, List.append_assoc]

/-- The scan watching the **first** list answers, after the whole serialisation, whether the
pattern occurs in the initial state. -/
theorem scan_instSer_zero (P : List Bool) (q : InstDesc) :
    ((instSer q).foldl (step P 0) (0, false, 0, 0, true)).2.1
      = decide (P ∈ q.initList.map bitsOfNat) := by
  rw [instSer_eq_blists]
  simp only [List.foldl_append]
  rw [foldl_blist, foldl_blist, foldl_blist, foldl_blist, foldl_blist]
  simp

/-- The scan watching the **second** list answers, after the whole serialisation, whether the
pattern occurs in the goal. -/
theorem scan_instSer_one (P : List Bool) (q : InstDesc) :
    ((instSer q).foldl (step P 1) (0, false, 0, 0, true)).2.1
      = decide (P ∈ q.goalList.map bitsOfNat) := by
  rw [instSer_eq_blists]
  simp only [List.foldl_append]
  rw [foldl_blist, foldl_blist, foldl_blist, foldl_blist, foldl_blist]
  simp

theorem mem_map_bitsOfNat_iff {l : List ℕ} {f : ℕ} :
    bitsOfNat f ∈ l.map bitsOfNat ↔ f ∈ l := by
  constructor
  · intro h
    obtain ⟨a, ha, hab⟩ := List.mem_map.1 h
    rwa [bitsOfNat_injective hab] at ha
  · intro h
    exact List.mem_map.2 ⟨f, h, rfl⟩

/-- **Whether a fixed fact holds initially is decided in polynomial time.** -/
theorem polyTimePred_memB_initList (f : ℕ) :
    PolyTimePred codingSer (fun q => memB q.initList f) := by
  refine polyTimePred_of_dfaList (states (bitsOfNat f) 0) (0, false, 0, 0, true)
    (step (bitsOfNat f) 0) (fun s => s.2.1)
    (init_mem_states _ _) (fun s b hs => step_mem _ _ hs b) ?_
  intro q
  show memB q.initList f
      = ((instSer q).foldl (step (bitsOfNat f) 0) (0, false, 0, 0, true)).2.1
  rw [scan_instSer_zero]
  simp [mem_map_bitsOfNat_iff, ← memB_iff]

/-- **Whether a fixed fact is a goal is decided in polynomial time.** -/
theorem polyTimePred_memB_goalList (f : ℕ) :
    PolyTimePred codingSer (fun q => memB q.goalList f) := by
  refine polyTimePred_of_dfaList (states (bitsOfNat f) 1) (0, false, 0, 0, true)
    (step (bitsOfNat f) 1) (fun s => s.2.1)
    (init_mem_states _ _) (fun s b hs => step_mem _ _ hs b) ?_
  intro q
  show memB q.goalList f
      = ((instSer q).foldl (step (bitsOfNat f) 1) (0, false, 0, 0, true)).2.1
  rw [scan_instSer_one]
  simp [mem_map_bitsOfNat_iff, ← memB_iff]

end Syn

end HTN
