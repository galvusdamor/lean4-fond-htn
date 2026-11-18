import ComplexityTheory.Savitch.Cobham
import ComplexityTheory.Savitch.Run
/-!
# Iterating the search inside the polynomial-space class

`ComplexityTheory/Savitch/Cobham.lean` writes the step of the depth-first search as a function
`HTN.Savitch.svStepFn` of Cobham's class.  The iteration scheme of
`ComplexityTheory/Collapse/Fun.lean` may be applied to it once the state is known to stay short
*whatever* the arguments are — the scheme asks for a bound that holds at every argument list, not
only at the well-formed ones — and that is `HTN.Savitch.length_svStepFn_le`: a step either leaves
the state alone, or pops a frame, or pushes one, and a push happens only when the guard says there
is room.

`HTN.Savitch.psSvLoop` is the conclusion: the iteration of the step belongs to the
polynomial-space class.  `HTN.Savitch.loopAux_eq_run` identifies the iteration with the run of
`ComplexityTheory/Savitch/State.lean`, and `HTN.Savitch.cost_le_val_ones` says that a counter of
polynomially many ones is long enough to let the search finish.
-/

namespace HTN

namespace Savitch

open PTime PSpace Space

/-! ### The state of the search stays short -/

theorem length_svStepFn_le (M : NSpace) (args : Args) :
    (svStepFn M args).length ≤ max (args.getD 0 []).length
      (6 + 5 * (args.getD 2 []).length + 2 * (args.getD 3 []).length +
        (args.getD 4 []).length) := by
  set s := args.getD 0 [] with hs
  set E := (args.getD 2 []).length with hE
  set F := (args.getD 3 []).length with hF
  set KF := (args.getD 4 []).length with hKF
  set C := 6 + 5 * E + 2 * F + KF with hC
  have hfr : (sFr args).length ≤ F := by
    simp only [sFr, sRest, sS, List.length_take]
    omega
  have hu : (sU args).length ≤ E := by
    simp only [sU, List.length_take]
    omega
  have hv : (sV args).length ≤ E := by
    simp only [sV, List.length_take]
    omega
  have hm : (sMid args).length ≤ F := by
    simp only [sMid, List.length_drop]
    have := hfr
    omega
  have hsucc : (succB (sMid args)).length ≤ F := by
    rw [length_succB]; exact hm
  have hst : (sSt args).length = s.length - 2 - F := by
    simp only [sSt, sRest, sS, List.length_drop, ← hs, ← hF]
  have hpop : ∀ b : Bool, (svPop b args).length ≤ max s.length C := by
    intro b
    simp only [svPop, List.length_append, List.length_cons, List.length_nil, hst]
    rcases le_or_gt 2 s.length with h | h
    · exact le_trans (by omega) (le_max_left _ _)
    · exact le_trans (by omega) (le_max_right _ _)
  have hpopstp : (svPopStp M args).length ≤ max s.length C := by
    have h := hpop (sStp M args)
    simpa only [svPop, svPopStp] using h
  have hroom : (sSt args).length + F ≤ KF → (svPush1 args).length ≤ max s.length C := by
    intro hg
    have h : (svPush1 args).length = 2 + (2 + (sU args).length + (sMid args).length + E) +
        (2 + (sU args).length + (sV args).length + (sMid args).length) + (sSt args).length := by
      simp only [svPush1, fresh, frame, List.length_append, List.length_cons, List.length_nil,
        length_zeros, ← hE]
      ring
    rw [h]
    exact le_trans (by omega) (le_max_right _ _)
  have hroom2 : (sSt args).length + F ≤ KF → (svPush2 args).length ≤ max s.length C := by
    intro hg
    have h : (svPush2 args).length = 2 + (2 + (sMid args).length + (sV args).length + E) +
        (2 + (sU args).length + (sV args).length + (sMid args).length) + (sSt args).length := by
      simp only [svPush2, fresh, frame, List.length_append, List.length_cons, List.length_nil,
        length_zeros, ← hE]
      ring
    rw [h]
    exact le_trans (by omega) (le_max_right _ _)
  have hroom3 : (sSt args).length + F ≤ KF → (svPush3 args).length ≤ max s.length C := by
    intro hg
    have h : (svPush3 args).length = 2 + (2 + (sU args).length + (succB (sMid args)).length + E) +
        (2 + (sU args).length + (sV args).length + (succB (sMid args)).length) +
        (sSt args).length := by
      simp only [svPush3, fresh, frame, List.length_append, List.length_cons, List.length_nil,
        length_zeros, ← hE]
      ring
    rw [h]
    exact le_trans (by omega) (le_max_right _ _)
  have hadv : (svAdv args).length ≤ max s.length C := by
    simp only [svAdv]
    by_cases h1 : sMid args = ones E
    · rw [if_pos h1]; exact hpop false
    · rw [if_neg h1]
      by_cases h2 : (sSt args).length + F ≤ KF
      · rw [if_pos h2]; exact hroom3 h2
      · rw [if_neg h2]; exact hpop false
  simp only [svStepFn]
  by_cases h0 : (sRest args).length < F
  · rw [if_pos h0]; exact le_max_left _ _
  · rw [if_neg h0]
    by_cases h1 : (sRet args).headD false = false
    · rw [if_pos h1]
      by_cases h2 : (sSt args).length + F ≤ KF
      · rw [if_pos h2]; exact hroom h2
      · rw [if_neg h2]; exact hpopstp
    · rw [if_neg h1]
      by_cases h3 : sPh args = [true, false]
      · rw [if_pos h3]
        by_cases h4 : ((sRet args).drop 1).headD false = true
        · rw [if_pos h4]
          by_cases h2 : (sSt args).length + F ≤ KF
          · rw [if_pos h2]; exact hroom2 h2
          · rw [if_neg h2]; exact hpop false
        · rw [if_neg h4]; exact hadv
      · rw [if_neg h3]
        by_cases h5 : sPh args = [false, true]
        · rw [if_pos h5]
          by_cases h4 : ((sRet args).drop 1).headD false = true
          · rw [if_pos h4]; exact hpop true
          · rw [if_neg h4]; exact hadv
        · rw [if_neg h5]; exact le_max_left _ _

/-! ### The bounding function of the iteration -/

/-- A function whose value is long enough to bound every state the iteration can reach. -/
def bdFn : Fn := fun args =>
  args.getD 1 [] ++ (args.getD 3 [] ++ args.getD 3 [] ++ args.getD 3 [] ++ args.getD 3 [] ++
    args.getD 3 [] ++ args.getD 4 [] ++ args.getD 4 [] ++ args.getD 5 [] ++
    [false, false, false, false, false, false])

theorem length_bdFn (args : Args) :
    (bdFn args).length = (args.getD 1 []).length + (5 * (args.getD 3 []).length +
      2 * (args.getD 4 []).length + (args.getD 5 []).length + 6) := by
  simp only [bdFn, List.length_append, List.length_cons, List.length_nil]
  ring

theorem cobham_bdFn : Cobham bdFn := by
  have h3 : Cobham (fun args : Args => args.getD 3 []) := Cobham.proj 3
  have h4 : Cobham (fun args : Args => args.getD 4 []) := Cobham.proj 4
  have h5 : Cobham (fun args : Args => args.getD 5 []) := Cobham.proj 5
  exact cobham_app2 (Cobham.proj 1)
    (cobham_app2 (cobham_app2 (cobham_app2 (cobham_app2 (cobham_app2 (cobham_app2
      (cobham_app2 (cobham_app2 h3 h3) h3) h3) h3) h4) h4) h5)
      (cobham_const [false, false, false, false, false, false]))

/-! ### The iteration -/

theorem getD_tail_two (args : Args) (i : ℕ) :
    (args.tail.tail).getD i [] = args.getD (i + 2) [] := by
  cases args with
  | nil => simp
  | cons b rest =>
    cases rest with
    | nil => simp
    | cons c rest => simp [show i + 2 = i + 1 + 1 from rfl]

theorem length_loopAux_le (M : NSpace) (rest : Args) (n : ℕ) (st : List Bool) :
    (loopAux (svStepFn M) rest n st).length ≤ max st.length
      (6 + 5 * (rest.getD 1 []).length + 2 * (rest.getD 2 []).length +
        (rest.getD 3 []).length) := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    rw [loopAux_succ]
    have h := length_svStepFn_le M (loopAux (svStepFn M) rest n st :: rest)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h
    exact le_trans h (max_le ih (le_max_right _ _))

/-- **The iteration of the step belongs to the polynomial-space class.** -/
theorem psSvLoop (M : NSpace) : PSpaceF (loopFn (svStepFn M)) := by
  refine PSpaceF.loop (PSpaceF.cobham (cobham_svStepFn M)) (PSpaceF.cobham cobham_bdFn)
    fun args => ?_
  rw [loopFn, length_bdFn]
  have h := length_loopAux_le M args.tail.tail (val (args.getD 0 [])) (args.getD 1 [])
  norm_num only [getD_tail_two] at h
  exact le_trans h (max_le (by omega) (by omega))

/-- **The iteration is the run of the search**, once the templates have the intended lengths. -/
theorem loopAux_eq_run (M : NSpace) (rest : Args)
    (hF : (rest.getD 2 []).length = frW (rest.getD 1 []).length) (n : ℕ) (st : List Bool) :
    loopAux (svStepFn M) rest n st =
      run (rest.getD 1 []).length (rest.getD 3 []).length
        (stpM M (rest.getD 4 []) (rest.getD 5 []) (rest.getD 0 []).length) n st := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loopAux_succ, ih, run_succ]
    have h := svStepFn_apply M (run (rest.getD 1 []).length (rest.getD 3 []).length
      (stpM M (rest.getD 4 []) (rest.getD 5 []) (rest.getD 0 []).length) n st :: rest) (by
        simpa using hF)
    simpa using h

/-! ### A counter of polynomially many ones is long enough -/

theorem cost_eq (E : ℕ) : ∀ k : ℕ, cost E k = 2 ^ ((E + 3) * (k + 1))
  | 0 => by simp [cost]
  | k + 1 => by
    rw [cost, cost_eq E k, ← pow_add]
    congr 1
    ring

/-- The search at level `K` finishes within the number of steps a counter of
`(E + 3) * (K + 1) + 1` ones counts. -/
theorem cost_le_val_ones (E K : ℕ) :
    cost E K ≤ val (ones ((E + 3) * (K + 1) + 1)) := by
  rw [val_ones, cost_eq]
  have h : (2 : ℕ) ^ ((E + 3) * (K + 1) + 1) = 2 ^ ((E + 3) * (K + 1)) * 2 := by ring
  have h2 : 1 ≤ (2 : ℕ) ^ ((E + 3) * (K + 1)) := Nat.one_le_two_pow
  omega

end Savitch

end HTN
