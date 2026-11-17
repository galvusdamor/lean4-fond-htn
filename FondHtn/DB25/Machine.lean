import FondHtn.DB25.OpProg
import FondHtn.DB25.Bits
/-!
# The register programs simulating a space-bounded Turing machine

Registers (`n` = number of address bits):

* `cB b` — the cell `c` checked in this branch (chosen by nature at the start);
* `hB b` — the head position;
* `sB 0, sB 1` — the content of cell `c` (a symbol `γ : Option Bool` as `(isSome, getD false)`);
* `tB 0, tB 1` — the next content, `dB b` — mismatch witnesses, `gB i` — input helpers (chosen by
  the policy, checked by CNFs).

The machine state is the state fact `qF q`.

* The **initial block** (`FOND.DB.preOps`): nature chooses `c`; the policy chooses the content and
  helpers; a CNF checks that the content is the input symbol at `c`.
* A **loop block** (`FOND.DB.loopOps`) for a transition `(q, a, q', a')` and a head update `μ`
  (literals on the head bits that must hold, and that are set): the policy chooses the next
  content and witnesses; a CNF checks "if `c` = head then content = `a` and next = `a'`, else next =
  content"; the next content is copied; the update requires state `q` and the literals of `μ` and
  moves to `q'`, setting the head bits.
* A **final block** (`FOND.DB.finalOps`): requires an accepting state.

The abstract meaning of a chain of blocks is `FOND.DB.RunC`: for every cell `c`, the run of the
blocks tracks the content of `c`.
-/

namespace FOND

namespace DB

/-! ## Registers and symbols -/

/-- The cell bits. -/
def cB (b : ℕ) : ℕ := Nat.pair 0 b
/-- The head bits. -/
def hB (b : ℕ) : ℕ := Nat.pair 1 b
/-- The content bits. -/
def sB (j : ℕ) : ℕ := Nat.pair 2 j
/-- The next content bits. -/
def tB (j : ℕ) : ℕ := Nat.pair 3 j
/-- The mismatch witnesses. -/
def dB (b : ℕ) : ℕ := Nat.pair 4 b
/-- The input helpers. -/
def gB (i : ℕ) : ℕ := Nat.pair 5 i

/-- Tape symbols. -/
abbrev Sym : Type := Option Bool

/-- The bits of a symbol. -/
def ebit (γ : Sym) (j : ℕ) : Bool := if j = 0 then γ.isSome else γ.getD false

theorem ebit_inj {γ γ' : Sym} (h0 : ebit γ 0 = ebit γ' 0) (h1 : ebit γ 1 = ebit γ' 1) : γ = γ' := by
  rcases γ with _ | _ | _ <;> rcases γ' with _ | _ | _ <;> simp_all [ebit]

/-- A transition `(q, a, q', a')` (the move is given by the head update). -/
abbrev TrD : Type := ℕ × Sym × ℕ × Sym

/-- A head update: literals on head bits that must hold, and literals that are set. -/
abbrev HU : Type := List (ℕ × Bool) × List (ℕ × Bool)

/-- Head-bit literals as register literals. -/
def hl (l : ℕ × Bool) : ℕ × Bool := (hB l.1, l.2)

/-! ## The blocks -/

/-- The CNF of a step: `d_b → c_b ≠ h_b`; `(∃ b, d_b) ∨ content = a`; `(∃ b, d_b) ∨ next = a'`;
`c_b ≠ h_b → next = content`. -/
def phiStep (n : ℕ) (τ : TrD) : List Clause :=
  ((List.range n).flatMap fun b =>
    [[(dB b, false), (cB b, true), (hB b, true)], [(dB b, false), (cB b, false), (hB b, false)]]) ++
  ((List.range 2).map fun j => (List.range n).map (fun b => (dB b, true)) ++ [(sB j, ebit τ.2.1 j)]) ++
  ((List.range 2).map fun j => (List.range n).map (fun b => (dB b, true)) ++
    [(tB j, ebit τ.2.2.2 j)]) ++
  ((List.range n).flatMap fun b => (List.range 2).flatMap fun j =>
    [[(cB b, true), (hB b, false), (tB j, false), (sB j, true)],
     [(cB b, true), (hB b, false), (tB j, true), (sB j, false)],
     [(cB b, false), (hB b, true), (tB j, false), (sB j, true)],
     [(cB b, false), (hB b, true), (tB j, true), (sB j, false)]])

/-- The registers chosen in a step. -/
def stepChoices (n : ℕ) : List ℕ := [tB 0, tB 1] ++ (List.range n).map dB

/-- **A loop block.** -/
def loopOps (n : ℕ) (d : TrD × HU) : List Op :=
  (stepChoices n).map Op.choice ++
    [.check (phiStep n d.1), .copy (tB 0) (sB 0), .copy (tB 1) (sB 1),
     .upd d.1.1 (d.2.1.map hl) d.1.2.2.1 (d.2.2.map hl)]

/-- **A final block.** -/
def finalOps (acc : ℕ) : List Op := [.upd acc [] acc []]

/-- The CNF of the initial content: `g_i → c = i`; `c = i → content = w_i`;
`(∀ i, ¬g_i) → content = blank`. -/
def phiInit (n : ℕ) (w : List Sym) (blank : Sym) : List Clause :=
  ((List.range w.length).flatMap fun i =>
    if i < 2 ^ n then (List.range n).map fun b => [(gB i, false), (cB b, i.testBit b)]
    else [[(gB i, false)]]) ++
  ((List.range w.length).flatMap fun i =>
    if i < 2 ^ n then (List.range 2).map fun j =>
      (List.range n).map (fun b => (cB b, !i.testBit b)) ++ [(sB j, ebit (w.getI i) j)]
    else []) ++
  ((List.range 2).map fun j =>
    (List.range w.length).map (fun i => (gB i, true)) ++ [(sB j, ebit blank j)])

/-- The registers chosen initially. -/
def initChoices (w : List Sym) : List ℕ := [sB 0, sB 1] ++ (List.range w.length).map gB

/-- **The initial block.** -/
def preOps (n : ℕ) (w : List Sym) (blank : Sym) : List Op :=
  (List.range n).map (fun b => Op.nature (cB b)) ++ (initChoices w).map Op.choice ++
    [.check (phiInit n w blank)]

/-- All registers. -/
def regs (n : ℕ) (w : List Sym) : List ℕ :=
  (List.range n).map cB ++ (List.range n).map hB ++ [sB 0, sB 1, tB 0, tB 1] ++
    (List.range n).map dB ++ (List.range w.length).map gB

end DB

end FOND
