import ComplexityTheory.Machine.Seg
import ComplexityTheory.Machine.NSM
/-!
# A single-tape Turing machine simulating a stack machine: the machine

The stack machine `C` (`ComplexityTheory/Machine/NSM.lean`) with stacks `0, …, K - 1` is simulated
by a single-tape machine `HTN.Mach.simM C K kin` of `ComplexityTheory/TM/Basic.lean` over the
alphabet `Option Bool` (`none` is the blank).

**The tape.** On input `x` of length `n` the cells `0, …, n` are blank once the input has been
read, and from cell `n + 1` on the tape is cut into blocks of `K + 1` cells: cell `r < K` of block
`j` holds the `j`-th bit (from the bottom) of stack `r`, or a blank above its top, and cell `K` of
block `0` holds the **marker** `some true`; cell `K` of the other blocks stays blank
(`HTN.Mach.lay`).  The head rests on the marker ("home") between two simulated instructions.

**The control.** The states are `HTN.Mach.QS`: either a *phase* (`HTN.Mach.Phase`) or "move `r`
more cells in a fixed direction, then enter a phase" (`QS.mv`, `HTN.Mach.mvTo`).  The phases:

* `exec pc` — at home, about to simulate instruction `pc`;
* `p0`, `pEnd`, `pMark`, `pre`, `pChk`, `pSeek`, `pTake`, `pRet` — the **preamble**, which moves
  the input onto stack `kin` (reversed, the first bit at the bottom): the first input bit is
  remembered and erased, the marker is written behind the input, and then the leftmost
  remaining input bit is fetched, erased and pushed, until no input bit is left;
* `scan act k cont first` — walking up stack `k`, block by block, to the first blank cell of
  its track; there the action `act` (push, guess, pop, branch) is performed, on the blank cell
  (push, guess) or on the top cell one block below (`top`, for pop and branch); `first` records
  whether the walk is still in block `0`, i.e. whether the stack is empty;
* `rScan cont` — walking back to the marker, block by block, then continuing with `exec pc`
  (`cont = some pc`) or with the preamble (`cont = none`).

All transitions are deterministic, except for `guess` (two bits to write) and `choose` (two
jump targets).
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM

/-- What to do at the top of a stack. -/
inductive Act where
  | push (b : Bool)
  | guess
  | pop
  | br (a₀ aF aT : ℕ)
  deriving DecidableEq

/-- The phases of the simulating machine. -/
inductive Phase where
  | exec (pc : ℕ)
  | p0
  | pEnd (b : Bool)
  | pMark (ob : Option Bool)
  | pre
  | pChk
  | pSeek
  | pTake
  | pRet (b : Bool)
  | scan (act : Act) (k : ℕ) (cont : Option ℕ) (first : Bool)
  | top (act : Act) (k : ℕ) (cont : Option ℕ)
  | rScan (cont : Option ℕ)
  deriving DecidableEq

/-- The states of the simulating machine. -/
inductive QS where
  | base (ph : Phase)
  | mv (right : Bool) (r : ℕ) (tgt : Phase)
  deriving DecidableEq

/-- The state that moves `r` cells (to the right iff `right`), then enters the phase `tgt`. -/
def mvTo (right : Bool) : ℕ → Phase → QS
  | 0, tgt => .base tgt
  | r + 1, tgt => .mv right r tgt

/-- The tape symbols. -/
abbrev Sym : Type := Option Bool

/-- A transition: the next state, the symbol written, the move. -/
abbrev Tr : Type := QS × Sym × Move

/-- The move in a direction. -/
def dir (right : Bool) : Move := if right then .right else .left

/-- The phase to continue with after returning home. -/
def contPh : Option ℕ → Phase
  | some pc => .exec pc
  | none => .pre

variable (C : List Ins) (K kin : ℕ)

/-- Starting the action `act` on stack `k`, from home. -/
def startTr (act : Act) (k : ℕ) (cont : Option ℕ) (γ : Sym) : List Tr :=
  [(mvTo false (K - k - 1) (.scan act k cont true), γ, .left)]

/-- The transitions out of `exec pc`. -/
def execTr (pc : ℕ) (γ : Sym) : List Tr :=
  match C[pc]? with
  | some (.push k b) => startTr K (.push b) k (some (pc + 1)) γ
  | some (.pop k) => startTr K .pop k (some (pc + 1)) γ
  | some (.br k a₀ aF aT) => startTr K (.br a₀ aF aT) k none γ
  | some (.jmp a) => [(.base (.exec a), γ, .stay)]
  | some (.guess k) => startTr K .guess k (some (pc + 1)) γ
  | some (.choose a₁ a₂) => [(.base (.exec a₁), γ, .stay), (.base (.exec a₂), γ, .stay)]
  | some .accept => []
  | none => []

/-- The transitions at the first blank cell of the track of stack `k`. -/
def scanBlankTr (act : Act) (k : ℕ) (cont : Option ℕ) (first : Bool) : List Tr :=
  match act with
  | .push b => [(mvTo true (K - k) (.rScan cont), some b, .stay)]
  | .guess => [(mvTo true (K - k) (.rScan cont), some false, .stay),
      (mvTo true (K - k) (.rScan cont), some true, .stay)]
  | .pop => if first then [(mvTo true (K - k) (.rScan cont), none, .stay)]
      else [(mvTo false K (.top .pop k cont), none, .left)]
  | .br a₀ aF aT => if first then [(mvTo true (K - k) (.rScan (some a₀)), none, .stay)]
      else [(mvTo false K (.top (.br a₀ aF aT) k cont), none, .left)]

/-- The transitions at the top cell of the track of stack `k`. -/
def topTr (act : Act) (k : ℕ) (cont : Option ℕ) (γ : Sym) : List Tr :=
  match act, γ with
  | .pop, _ => [(mvTo true (K - k) (.rScan cont), none, .stay)]
  | .br _ aF aT, some b => [(mvTo true (K - k) (.rScan (some (if b then aT else aF))), some b, .stay)]
  | _, _ => []

/-- The transitions of a phase. -/
def phaseTr : Phase → Sym → List Tr
  | .exec pc, γ => execTr C K pc γ
  | .p0, none => [(mvTo true K (.pMark none), none, .right)]
  | .p0, some b => [(.base (.pEnd b), none, .right)]
  | .pEnd b, some c => [(.base (.pEnd b), some c, .right)]
  | .pEnd b, none => [(mvTo true K (.pMark (some b)), none, .right)]
  | .pMark none, _ => [(.base (.exec 0), some true, .stay)]
  | .pMark (some b), _ => [(mvTo false (K - kin - 1) (.scan (.push b) kin none true), some true, .left)]
  | .pre, γ => [(mvTo false (K + 1) .pChk, γ, .left)]
  | .pChk, none => [(mvTo true (K + 1) (.exec 0), none, .right)]
  | .pChk, some c => [(.base .pSeek, some c, .left)]
  | .pSeek, some c => [(.base .pSeek, some c, .left)]
  | .pSeek, none => [(.base .pTake, none, .right)]
  | .pTake, some b => [(.base (.pRet b), none, .right)]
  | .pTake, none => []
  | .pRet b, some c => [(.base (.pRet b), some c, .right)]
  | .pRet b, none => [(mvTo true kin (.scan (.push b) kin none true), none, .right)]
  | .scan act k cont _, some c => [(mvTo true K (.scan act k cont false), some c, .right)]
  | .scan act k cont first, none => scanBlankTr K act k cont first
  | .top act k cont, γ => topTr K act k cont γ
  | .rScan cont, some true => [(.base (contPh cont), some true, .stay)]
  | .rScan cont, γ => [(mvTo false K (.rScan cont), γ, .left)]

/-- The transitions of a state. -/
def δ : QS → Sym → List Tr
  | .mv right r tgt, γ => [(mvTo right r tgt, γ, dir right)]
  | .base ph, γ => phaseTr C K kin ph γ

/-- **The simulating machine.** -/
def simM : NTM QS Sym where
  step q γ := {t | t ∈ δ C K kin q γ}
  init := .base .p0
  accept := {q | ∃ pc, q = .base (.exec pc) ∧ C[pc]? = some .accept}
  blank := none

/-! ### The layout of the tape -/

/-- **The tape for the stacks `S`** behind an input of length `n`. -/
def lay (n : ℕ) (S : Store) (i : ℕ) : Sym :=
  if i < n + 1 then none
  else if (i - (n + 1)) % (K + 1) < K then
    (S ((i - (n + 1)) % (K + 1))).reverse[(i - (n + 1)) / (K + 1)]?
  else if (i - (n + 1)) / (K + 1) = 0 then some true else none

/-- The cell `r` of block `j`. -/
def cell (n j r : ℕ) : ℕ := n + 1 + j * (K + 1) + r

/-- Home: the marker cell. -/
def home (n : ℕ) : ℕ := n + 1 + K

/-- The configuration simulating `⟨pc, S⟩`. -/
def good (n : ℕ) (σ : SCfg) : Config QS Sym := ⟨.base (.exec σ.pc), home K n, lay K n σ.S⟩

variable {K}

theorem cell_div {n j r : ℕ} (hr : r < K + 1) : (cell K n j r - (n + 1)) / (K + 1) = j := by
  unfold cell
  rw [show n + 1 + j * (K + 1) + r - (n + 1) = r + j * (K + 1) by omega,
    Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, zero_add]

theorem cell_mod {n j r : ℕ} (hr : r < K + 1) : (cell K n j r - (n + 1)) % (K + 1) = r := by
  unfold cell
  rw [show n + 1 + j * (K + 1) + r - (n + 1) = r + j * (K + 1) by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem lay_track {n : ℕ} (S : Store) {j r : ℕ} (hr : r < K) :
    lay K n S (cell K n j r) = (S r).reverse[j]? := by
  unfold lay
  rw [if_neg (by unfold cell; omega), cell_mod (by omega), if_pos hr, cell_div (by omega)]

theorem lay_marker {n : ℕ} (S : Store) (j : ℕ) :
    lay K n S (cell K n j K) = if j = 0 then some true else none := by
  unfold lay
  rw [if_neg (by unfold cell; omega), cell_mod (by omega), if_neg (lt_irrefl _), cell_div (by omega)]

theorem lay_low {n : ℕ} (S : Store) {i : ℕ} (hi : i ≤ n) : lay K n S i = none := by
  unfold lay; rw [if_pos (by omega)]

/-- Every cell behind the input is a cell of some block. -/
theorem eq_cell {n i : ℕ} (hi : n + 1 ≤ i) :
    i = cell K n ((i - (n + 1)) / (K + 1)) ((i - (n + 1)) % (K + 1)) := by
  unfold cell
  have := Nat.div_add_mod (i - (n + 1)) (K + 1)
  rw [mul_comm] at this
  omega

theorem home_eq (n : ℕ) : home K n = cell K n 0 K := by unfold home cell; ring

/-- The layout only depends on the stacks below `K`. -/
theorem lay_congr {n : ℕ} {S S' : Store} (h : ∀ r < K, S r = S' r) : lay K n S = lay K n S' := by
  funext i
  unfold lay
  split_ifs with h1 h2 <;> try rfl
  rw [h _ h2]

/-- **Pushing** writes the new bit into the first blank cell of the track. -/
theorem lay_push {n : ℕ} (S : Store) {k : ℕ} (hk : k < K) (b : Bool) :
    Function.update (lay K n S) (cell K n (S k).length k) (some b) =
      lay K n (Function.update S k (b :: S k)) := by
  funext i
  by_cases hi : i ≤ n
  · rw [Function.update_of_ne (by unfold cell; omega), lay_low _ hi, lay_low _ hi]
  rw [eq_cell (K := K) (n := n) (by omega : n + 1 ≤ i)]
  set j := (i - (n + 1)) / (K + 1)
  set r := (i - (n + 1)) % (K + 1)
  have hr : r < K + 1 := Nat.mod_lt _ (by omega)
  by_cases hrK : r < K
  · rw [lay_track _ hrK]
    by_cases hrk : r = k
    · subst hrk
      by_cases hj : j = (S r).length
      · rw [hj, Function.update_self]; simp
      · rw [Function.update_of_ne (fun h => hj ?_), lay_track _ hrK]
        · simp only [Function.update_self, List.reverse_cons]
          rcases Nat.lt_or_gt_of_ne hj with hj' | hj'
          · rw [List.getElem?_append_left (by simpa using hj')]
          · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
        · unfold cell at h
          have := congrArg (fun x => (x - (n + 1)) / (K + 1)) h
          simp only at this
          rwa [show n + 1 + j * (K + 1) + r - (n + 1) = r + j * (K + 1) by omega,
            show n + 1 + (S r).length * (K + 1) + r - (n + 1) = r + (S r).length * (K + 1) by omega,
            Nat.add_mul_div_right _ _ (by omega), Nat.add_mul_div_right _ _ (by omega),
            Nat.div_eq_of_lt hr, zero_add, zero_add] at this
    · rw [Function.update_of_ne, lay_track _ hrK, Function.update_of_ne hrk]
      intro h
      have := congrArg (fun x => (x - (n + 1)) % (K + 1)) h
      simp only at this
      rw [cell_mod hr, cell_mod (by omega)] at this
      exact hrk this
  · have hrK' : r = K := by omega
    rw [hrK', Function.update_of_ne, lay_marker, lay_marker]
    intro h
    have := congrArg (fun x => (x - (n + 1)) % (K + 1)) h
    simp only at this
    rw [cell_mod (by omega), cell_mod (by omega)] at this
    omega

/-- **Popping** blanks the top cell of the track. -/
theorem lay_pop {n : ℕ} (S : Store) {k : ℕ} (hk : k < K) {c : Bool} {rest : List Bool}
    (hS : S k = c :: rest) :
    Function.update (lay K n S) (cell K n rest.length k) none =
      lay K n (Function.update S k rest) := by
  have h := lay_push (n := n) (Function.update S k rest) hk c
  simp only [Function.update_self, Function.update_idem] at h
  rw [← hS, Function.update_eq_self] at h
  rw [← h, Function.update_idem]
  conv_rhs => rw [← Function.update_eq_self (cell K n rest.length k) (lay K n (Function.update S k rest))]
  rw [lay_track _ hk]
  simp

end Mach

end HTN
