import ComplexityTheory.Savitch.Rec
import ComplexityTheory.Collapse.Code
/-!
# The depth-first search that evaluates Savitch's recursion

`ComplexityTheory/Savitch/Rec.lean` states the halving recursion; a *deterministic
polynomial-space* machine evaluates it by a depth-first search of the recursion tree, keeping one
frame per level of the recursion — that is what makes the space polynomial, the recursion being
only `K` deep while the number of steps is exponential.

This file writes that search down as a function on bit strings, so that it can later be shown to
be a function of the polynomial-time class and iterated exponentially often inside the
polynomial-space class.

## The state

    state  =  ret (2 bits)  ++  frame ++ frame ++ … ++ frame

with the *top* frame first, and

    frame  =  ph (2 bits)  ++  u (E bits)  ++  v (E bits)  ++  m (E bits).

`ret` is `00` while a call is being made and `1b` while the value `b` is being returned to the
caller.  `ph` is `00` in a frame that has just been pushed, `10` while the frame waits for the
value of its first child `(u, m)`, and `01` while it waits for the value of its second child
`(m, v)`.  The field `m` is the midpoint currently being tried, enumerated from `0…0` upwards.

## The guard

A frame is pushed only if there is **room** for it: the stack below the current frame must be no
taller than `KF - (2 + 3E)`, where `KF` is the height at which the recursion bottoms out.  At the
bottom of the recursion there is no room, and the frame returns the one-step test `stp u v`
instead of expanding; the guard is what keeps the state polynomially long whatever string the
machine is started on, which is what the iteration scheme of the polynomial-space class asks
for.
-/

namespace HTN

namespace Savitch

open PTime PSpace

/-! ### Frames -/

/-- The width of a frame: two phase bits and three nodes. -/
def frW (E : ℕ) : ℕ := 2 + 3 * E

theorem frW_pos (E : ℕ) : 0 < frW E := by simp only [frW]; omega

/-- A frame: the phase, the two endpoints and the current midpoint. -/
def frame (ph u v m : List Bool) : List Bool := ph ++ u ++ v ++ m

/-- A freshly pushed frame: phase `00`, and the midpoint enumeration at its start. -/
def fresh (E : ℕ) (u v : List Bool) : List Bool := frame [false, false] u v (zeros E)

theorem length_frame {ph u v m : List Bool} {E : ℕ} (hph : ph.length = 2) (hu : u.length = E)
    (hv : v.length = E) (hm : m.length = E) : (frame ph u v m).length = frW E := by
  simp [frame, frW, hph, hu, hv, hm]; ring

theorem length_fresh {E : ℕ} {u v : List Bool} (hu : u.length = E) (hv : v.length = E) :
    (fresh E u v).length = frW E :=
  length_frame rfl hu hv (by simp [zeros])

/-! ### Cutting a string at a known length -/

theorem take_app {a b : List Bool} {n : ℕ} (h : a.length = n) : (a ++ b).take n = a := by
  subst h; simp

theorem drop_app {a b : List Bool} {n : ℕ} (h : a.length = n) : (a ++ b).drop n = b := by
  subst h; simp

/-! ### The step -/

/-- **One step of the depth-first search.**  `E` is the width of a node, `KF` the height of the
stack at which the recursion bottoms out, and `stp` the one-step test. -/
def step (E KF : ℕ) (stp : List Bool → List Bool → Bool) (s : List Bool) : List Bool :=
  let ret := s.take 2
  let rest := s.drop 2
  let fr := rest.take (frW E)
  let st := rest.drop (frW E)
  let ph := fr.take 2
  let u := ((fr.drop 2).take E)
  let v := (((fr.drop 2).drop E).take E)
  let m := (((fr.drop 2).drop E).drop E)
  let adv := if m = ones E then [true, false] ++ st
    else if st.length + frW E ≤ KF then
        [false, false] ++ (fresh E u (succB m) ++ (frame [true, false] u v (succB m) ++ st))
      else [true, false] ++ st
  if rest.length < frW E then s
  else if ret.headD false = false then
    (if st.length + frW E ≤ KF then
        [false, false] ++ (fresh E u m ++ (frame [true, false] u v m ++ st))
      else [true, stp u v] ++ st)
  else if ph = [true, false] then
    (if (ret.drop 1).headD false = true then
        (if st.length + frW E ≤ KF then
            [false, false] ++ (fresh E m v ++ (frame [false, true] u v m ++ st))
          else [true, false] ++ st)
      else adv)
  else if ph = [false, true] then
    (if (ret.drop 1).headD false = true then [true, true] ++ st else adv)
  else s

/-- The machine has halted: the stack is empty. -/
theorem step_halted (E KF : ℕ) (stp : List Bool → List Bool → Bool) {r : List Bool}
    (hr : r.length = 2) : step E KF stp r = r := by
  have hdrop : r.drop 2 = [] := by
    rw [List.drop_eq_nil_iff]; omega
  have hlt : ([] : List Bool).length < frW E := by
    simp only [List.length_nil]; exact frW_pos E
  simp only [step, hdrop]
  rw [if_pos hlt]

/-- Iterating the step. -/
def run (E KF : ℕ) (stp : List Bool → List Bool → Bool) : ℕ → List Bool → List Bool
  | 0, s => s
  | n + 1, s => step E KF stp (run E KF stp n s)

@[simp] theorem run_zero (E KF : ℕ) (stp : List Bool → List Bool → Bool) (s : List Bool) :
    run E KF stp 0 s = s := rfl

theorem run_succ (E KF : ℕ) (stp : List Bool → List Bool → Bool) (n : ℕ) (s : List Bool) :
    run E KF stp (n + 1) s = step E KF stp (run E KF stp n s) := rfl

theorem run_add (E KF : ℕ) (stp : List Bool → List Bool → Bool) (m n : ℕ) (s : List Bool) :
    run E KF stp (m + n) s = run E KF stp n (run E KF stp m s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show m + (n + 1) = (m + n) + 1 by omega, run_succ, ih, run_succ]

/-- Once the stack is empty nothing changes. -/
theorem run_halted (E KF : ℕ) (stp : List Bool → List Bool → Bool) {r : List Bool}
    (hr : r.length = 2) (n : ℕ) : run E KF stp n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, step_halted E KF stp hr]

/-! ### The state stays short -/

/-- **The guard keeps the state short**: a step never makes the state longer than it was, or
longer than the size of a full stack. -/
theorem length_step_le (E KF : ℕ) (stp : List Bool → List Bool → Bool) (s : List Bool) :
    (step E KF stp s).length ≤ max s.length (2 + KF + frW E) := by
  rcases Nat.lt_or_ge (s.drop 2).length (frW E) with hlt | hge
  · simp only [step, if_pos hlt]
    exact le_max_left _ _
  · have hfrW : frW E = 2 + 3 * E := rfl
    have hpos := frW_pos E
    have hdrop2 : (s.drop 2).length = s.length - 2 := by simp
    have hsl2 : 2 ≤ s.length := by omega
    set fr := (s.drop 2).take (frW E) with hfrdef
    set st := (s.drop 2).drop (frW E) with hstdef
    have hfrl : fr.length = frW E := by
      rw [hfrdef, List.length_take]; omega
    have hstl : st.length = s.length - 2 - frW E := by
      rw [hstdef, List.length_drop]; omega
    have hsl : s.length = 2 + frW E + st.length := by omega
    have hul : ((fr.drop 2).take E).length ≤ E := by simp
    have hvl : (((fr.drop 2).drop E).take E).length ≤ E := by simp
    have hml : ((((fr.drop 2).drop E).drop E)).length ≤ E := by
      simp only [List.length_drop, hfrl, hfrW]
      omega
    set u := ((fr.drop 2).take E) with hudef
    set v := (((fr.drop 2).drop E).take E) with hvdef
    set m := ((((fr.drop 2).drop E).drop E)) with hmdef
    have hpop : ∀ b : Bool, (([true, b] : List Bool) ++ st).length ≤ s.length := by
      intro b
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hpush' : ∀ a b c d e : List Bool, a.length ≤ E → b.length ≤ E → c.length ≤ E →
        d.length ≤ E → e.length ≤ E → st.length + frW E ≤ KF →
        (([false, false] : List Bool) ++ (frame [false, false] a b (zeros E) ++
          (frame [true, false] c d e ++ st))).length ≤ 2 + KF + frW E := by
      intro a b c d e ha hb hc hd he hroom
      simp only [List.length_append, frame, List.length_cons, List.length_nil, length_zeros]
      omega
    have hpush'' : ∀ a b c d e : List Bool, a.length ≤ E → b.length ≤ E → c.length ≤ E →
        d.length ≤ E → e.length ≤ E → st.length + frW E ≤ KF →
        (([false, false] : List Bool) ++ (frame [false, false] a b (zeros E) ++
          (frame [false, true] c d e ++ st))).length ≤ 2 + KF + frW E := by
      intro a b c d e ha hb hc hd he hroom
      simp only [List.length_append, frame, List.length_cons, List.length_nil, length_zeros]
      omega
    have hsucc : (succB m).length ≤ E := by rw [length_succB]; exact hml
    simp only [step, if_neg (by omega : ¬ (s.drop 2).length < frW E), ← hfrdef, ← hstdef,
      ← hudef, ← hvdef, ← hmdef]
    have hadv : (if m = ones E then ([true, false] : List Bool) ++ st
        else if st.length + frW E ≤ KF then
            [false, false] ++ (fresh E u (succB m) ++
              (frame [true, false] u v (succB m) ++ st))
          else [true, false] ++ st).length ≤ max s.length (2 + KF + frW E) := by
      by_cases h1 : m = ones E
      · rw [if_pos h1]
        exact le_trans (hpop false) (le_max_left _ _)
      · rw [if_neg h1]
        by_cases hroom : st.length + frW E ≤ KF
        · rw [if_pos hroom, fresh]
          exact le_trans (hpush' u (succB m) u v (succB m) hul hsucc hul hvl hsucc hroom)
            (le_max_right _ _)
        · rw [if_neg hroom]
          exact le_trans (hpop false) (le_max_left _ _)
    by_cases hret : (s.take 2).headD false = false
    · rw [if_pos hret]
      by_cases hroom : st.length + frW E ≤ KF
      · rw [if_pos hroom, fresh]
        exact le_trans (hpush' u m u v m hul hml hul hvl hml hroom) (le_max_right _ _)
      · rw [if_neg hroom]
        exact le_trans (hpop (stp u v)) (le_max_left _ _)
    · rw [if_neg hret]
      by_cases hph1 : fr.take 2 = [true, false]
      · rw [if_pos hph1]
        by_cases hb : ((s.take 2).drop 1).headD false = true
        · rw [if_pos hb]
          by_cases hroom : st.length + frW E ≤ KF
          · rw [if_pos hroom, fresh]
            exact le_trans (hpush'' m v u v m hml hvl hul hvl hml hroom) (le_max_right _ _)
          · rw [if_neg hroom]
            exact le_trans (hpop false) (le_max_left _ _)
        · rw [if_neg hb]; exact hadv
      · rw [if_neg hph1]
        by_cases hph2 : fr.take 2 = [false, true]
        · rw [if_pos hph2]
          by_cases hb : ((s.take 2).drop 1).headD false = true
          · rw [if_pos hb]
            exact le_trans (hpop true) (le_max_left _ _)
          · rw [if_neg hb]; exact hadv
        · rw [if_neg hph2]
          exact le_max_left _ _

/-- **The state of a run stays short.** -/
theorem length_run_le (E KF : ℕ) (stp : List Bool → List Bool → Bool) (n : ℕ) (s : List Bool) :
    (run E KF stp n s).length ≤ max s.length (2 + KF + frW E) := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    rw [run_succ]
    exact le_trans (length_step_le E KF stp _) (max_le (le_trans ih le_rfl) (le_max_right _ _))

/-! ### What the step does on a well-formed state -/

/-- The state that calls the recursion on the pair `(u, v)`, with the stack `st` below. -/
def callSt (E : ℕ) (u v st : List Bool) : List Bool := [false, false] ++ (fresh E u v ++ st)

/-- The state that returns the value `b` to the stack `st`. -/
def retSt (b : Bool) (st : List Bool) : List Bool := [true, b] ++ st

section Compute

variable {E KF : ℕ} {stp : List Bool → List Bool → Bool} {ph u v m st : List Bool}

/-- The step on a state whose top frame is explicit. -/
theorem step_eq (hph : ph.length = 2) (hu : u.length = E) (hv : v.length = E)
    (hm : m.length = E) (r : List Bool) (hr : r.length = 2) :
    step E KF stp (r ++ (frame ph u v m ++ st)) =
      (if r.headD false = false then
          (if st.length + frW E ≤ KF then
              [false, false] ++ (fresh E u m ++ (frame [true, false] u v m ++ st))
            else [true, stp u v] ++ st)
        else if ph = [true, false] then
          (if (r.drop 1).headD false = true then
              (if st.length + frW E ≤ KF then
                  [false, false] ++ (fresh E m v ++ (frame [false, true] u v m ++ st))
                else [true, false] ++ st)
            else if m = ones E then [true, false] ++ st
              else if st.length + frW E ≤ KF then
                  [false, false] ++ (fresh E u (succB m) ++
                    (frame [true, false] u v (succB m) ++ st))
                else [true, false] ++ st)
        else if ph = [false, true] then
          (if (r.drop 1).headD false = true then [true, true] ++ st
            else if m = ones E then [true, false] ++ st
              else if st.length + frW E ≤ KF then
                  [false, false] ++ (fresh E u (succB m) ++
                    (frame [true, false] u v (succB m) ++ st))
                else [true, false] ++ st)
        else r ++ (frame ph u v m ++ st)) := by
  have hfrl : (frame ph u v m).length = frW E := length_frame hph hu hv hm
  have h1 : (r ++ (frame ph u v m ++ st)).take 2 = r := take_app hr
  have h2 : (r ++ (frame ph u v m ++ st)).drop 2 = frame ph u v m ++ st := drop_app hr
  have h3 : (frame ph u v m ++ st).take (frW E) = frame ph u v m := take_app hfrl
  have h4 : (frame ph u v m ++ st).drop (frW E) = st := drop_app hfrl
  have h5 : (frame ph u v m).take 2 = ph := by
    rw [frame]
    have hassoc : ph ++ u ++ v ++ m = ph ++ (u ++ v ++ m) := by simp
    rw [hassoc, take_app hph]
  have h6 : ((frame ph u v m).drop 2).take E = u := by
    rw [frame]
    have hassoc : ph ++ u ++ v ++ m = ph ++ (u ++ (v ++ m)) := by simp
    rw [hassoc, drop_app hph, take_app hu]
  have h7 : (((frame ph u v m).drop 2).drop E).take E = v := by
    rw [frame]
    have hassoc : ph ++ u ++ v ++ m = ph ++ (u ++ (v ++ m)) := by simp
    rw [hassoc, drop_app hph, drop_app hu, take_app hv]
  have h8 : (((frame ph u v m).drop 2).drop E).drop E = m := by
    rw [frame]
    have hassoc : ph ++ u ++ v ++ m = ph ++ (u ++ (v ++ m)) := by simp
    rw [hassoc, drop_app hph, drop_app hu, drop_app hv]
  have hnot : ¬ ((frame ph u v m ++ st).length < frW E) := by
    rw [List.length_append, hfrl]; omega
  simp only [step, h1, h2, h3, h4, h5, h6, h7, h8, if_neg hnot]

/-! ### The six moves of the search -/

/-- **A call with no room below** returns the one-step test. -/
theorem step_call_base (hu : u.length = E) (hv : v.length = E)
    (hst : ¬ (st.length + frW E ≤ KF)) :
    step E KF stp (callSt E u v st) = retSt (stp u v) st := by
  have h := step_eq (E := E) (KF := KF) (stp := stp) (ph := [false, false]) (u := u) (v := v)
    (m := zeros E) (st := st) rfl hu hv (by simp) [false, false] rfl
  rw [callSt, fresh, h, if_pos (by decide), if_neg hst, retSt]

/-- **A call with room below** pushes the first child. -/
theorem step_call_push (hu : u.length = E) (hv : v.length = E)
    (hst : st.length + frW E ≤ KF) :
    step E KF stp (callSt E u v st)
      = callSt E u (zeros E) (frame [true, false] u v (zeros E) ++ st) := by
  have h := step_eq (E := E) (KF := KF) (stp := stp) (ph := [false, false]) (u := u) (v := v)
    (m := zeros E) (st := st) rfl hu hv (by simp) [false, false] rfl
  rw [callSt, fresh, h, if_pos (by decide), if_pos hst, callSt]

/-- **The first child returned `true`**: call the second one. -/
theorem step_ret_first_true (hu : u.length = E) (hv : v.length = E) (hm : m.length = E)
    (hst : st.length + frW E ≤ KF) :
    step E KF stp (retSt true (frame [true, false] u v m ++ st))
      = callSt E m v (frame [false, true] u v m ++ st) := by
  have h := step_eq (E := E) (KF := KF) (stp := stp) (ph := [true, false]) (u := u) (v := v)
    (m := m) (st := st) rfl hu hv hm [true, true] rfl
  rw [retSt, h, if_neg (by decide), if_pos rfl, if_pos (by decide), if_pos hst, callSt]

/-- **The first child returned `false`**: try the next midpoint, or give up. -/
theorem step_ret_first_false (hu : u.length = E) (hv : v.length = E) (hm : m.length = E)
    (hst : st.length + frW E ≤ KF) :
    step E KF stp (retSt false (frame [true, false] u v m ++ st))
      = (if m = ones E then retSt false st
          else callSt E u (succB m) (frame [true, false] u v (succB m) ++ st)) := by
  have h := step_eq (E := E) (KF := KF) (stp := stp) (ph := [true, false]) (u := u) (v := v)
    (m := m) (st := st) rfl hu hv hm [true, false] rfl
  rw [retSt, h, if_neg (by decide), if_pos rfl, if_neg (by decide)]
  by_cases hones : m = ones E
  · rw [if_pos hones, if_pos hones, retSt]
  · rw [if_neg hones, if_neg hones, if_pos hst, callSt]

/-- **The second child returned `true`**: the frame succeeds. -/
theorem step_ret_second_true (hu : u.length = E) (hv : v.length = E) (hm : m.length = E) :
    step E KF stp (retSt true (frame [false, true] u v m ++ st)) = retSt true st := by
  have h := step_eq (E := E) (KF := KF) (stp := stp) (ph := [false, true]) (u := u) (v := v)
    (m := m) (st := st) rfl hu hv hm [true, true] rfl
  rw [retSt, h, if_neg (by decide), if_neg (by decide), if_pos rfl, if_pos (by decide), retSt]

/-- **The second child returned `false`**: try the next midpoint, or give up. -/
theorem step_ret_second_false (hu : u.length = E) (hv : v.length = E) (hm : m.length = E)
    (hst : st.length + frW E ≤ KF) :
    step E KF stp (retSt false (frame [false, true] u v m ++ st))
      = (if m = ones E then retSt false st
          else callSt E u (succB m) (frame [true, false] u v (succB m) ++ st)) := by
  have h := step_eq (E := E) (KF := KF) (stp := stp) (ph := [false, true]) (u := u) (v := v)
    (m := m) (st := st) rfl hu hv hm [true, false] rfl
  rw [retSt, h, if_neg (by decide), if_neg (by decide), if_pos rfl, if_neg (by decide)]
  by_cases hones : m = ones E
  · rw [if_pos hones, if_pos hones, retSt]
  · rw [if_neg hones, if_neg hones, if_pos hst, callSt]

end Compute

end Savitch

end HTN
