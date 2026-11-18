import HtnComplexity.TMEnc.TMEncWitness
/-!
# Cell runs: space–time diagrams with an arbitrary set of transition cells

`HTN.TMEnc.IsWitness` (`HtnComplexity/TMEnc/TMEncWitness.lean`) is the space–time diagram of a
run of **exactly `K` steps**: one transition per block, at the marked cell.  The analysis of a
solution plan of the repaired encoding does *not* deliver that much — the head counter pins the
cells that may carry a transition only up to one unit, so a plan may take fewer than `K`
transitions, and possibly two of them inside one block (see `NOTES.md`).  What the analysis
*does* deliver is a diagram read **cell by cell**: for every cell of the `(K+1) × (K+1)` array,
either the cell is copied into the next block and the state does not change, or a transition of
the machine is applied there.

This file proves that such a diagram is still an accepting run — of as many steps as it has
transition cells:

* `HTN.TMEnc.IsCellRun` — the diagram, indexed by the cell number `n = i(K+1) + p` (`p = 0` is
  the separator of the block `i`, `p = j + 1` is the tape cell `j`);
* `HTN.TMEnc.cellTape` — **the tape of the machine at the cell `n`**: the cells of the block of
  `n` that the diagram has already passed are read in the *next* block, the others in the block
  of `n` itself.  This is the definition that makes several transitions per block work;
* `HTN.TMEnc.reaches_cellConfig` — after the first `n` cells the machine has made exactly as
  many steps as there are transition cells below `n`;
* `HTN.TMEnc.acceptsWithin_of_isCellRun` — **a cell run is an accepting run**, of length the
  number of its transition cells.

`HTN.TMEnc.isCellRun_of_isWitness` connects the two notions: a witness in the sense of
`IsWitness` is a cell run whose transition cells are the marked ones.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **A space–time diagram read cell by cell.**

`sym n` is the symbol of the cell `n` of the array (`n = i(K+1) + p`, the cell `p` of the block
`i`; `p = 0` is the separator and `p = j + 1` is the tape cell `j`), `st n` is the state of the
machine and `hd n` its head position *before* the cell `n` is treated, and `tr n` says whether
the cell `n` carries a transition.

A cell that carries no transition is copied into the next block and changes neither the state
nor the head; a cell that carries one applies a transition of the machine, which requires the
head to be on that cell. -/
structure IsCellRun (N : NTM Q Γ) (w : List Γ) (K : ℕ) (sym : ℕ → Option Γ) (st : ℕ → Q)
    (hd : ℕ → ℕ) (tr : ℕ → Bool) : Prop where
  /-- The first block holds the input, padded with blanks. -/
  initTape : ∀ j < K, sym (j + 1) = some (w.getD j N.blank)
  /-- The run starts in the initial state. -/
  initState : st 0 = N.init
  /-- The head starts on the first tape cell. -/
  headInit : hd 0 = 0
  /-- A cell without a transition is copied, and neither the state nor the head changes. -/
  copy : ∀ n < K * (K + 1), tr n = false →
    sym (n + (K + 1)) = sym n ∧ st (n + 1) = st n ∧ hd (n + 1) = hd n
  /-- At a transition cell a transition of the machine is applied; the head is on that cell and
  moves as the transition prescribes. -/
  step : ∀ n < K * (K + 1), tr n = true →
    ∃ (a b : Γ) (mv : Move), (st (n + 1), b, mv) ∈ N.step (st n) a ∧
      sym n = some a ∧ sym (n + (K + 1)) = some b ∧
      n % (K + 1) = hd n + 1 ∧ hd n < K ∧ hd (n + 1) = mv.apply (hd n)
  /-- The last block is accepting. -/
  accept : st (K * (K + 1)) ∈ N.accept

/-! ### The tape at a cell -/

private lemma mod_succ_of_lt {n K : ℕ} (h : n % (K + 1) + 1 < K + 1) :
    (n + 1) % (K + 1) = n % (K + 1) + 1 := by
  conv_lhs => rw [← Nat.div_add_mod n (K + 1)]
  rw [show (K + 1) * (n / (K + 1)) + n % (K + 1) + 1
      = (n % (K + 1) + 1) + (K + 1) * (n / (K + 1)) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

private lemma mod_succ_of_eq {n K : ℕ} (h : n % (K + 1) = K) : (n + 1) % (K + 1) = 0 := by
  conv_lhs => rw [← Nat.div_add_mod n (K + 1)]
  rw [show (K + 1) * (n / (K + 1)) + n % (K + 1) + 1
      = (n % (K + 1) + 1) + (K + 1) * (n / (K + 1)) by ring,
    Nat.add_mul_mod_self_left, h, Nat.mod_self]

/-- **The tape of the machine when the cell `n` is reached.**  The tape cell `j` is read in the
block of `n` if the diagram has not passed it yet (`j + 1 ≥ n % (K+1)`), and in the *next*
block if it has (`j + 1 < n % (K+1)`) — the transitions of the current block have already
written their result there. -/
def cellTape (N : NTM Q Γ) (K : ℕ) (sym : ℕ → Option Γ) (n : ℕ) : ℕ → Γ := fun j =>
  if j < K then
    (sym ((if j + 1 < n % (K + 1) then K + 1 else 0) + (n - n % (K + 1)) + (j + 1))).getD N.blank
  else N.blank

/-- The configuration of the machine when the cell `n` is reached. -/
def cellConfig (N : NTM Q Γ) (K : ℕ) (sym : ℕ → Option Γ) (st : ℕ → Q) (hd : ℕ → ℕ) (n : ℕ) :
    Config Q Γ := ⟨st n, hd n, cellTape N K sym n⟩

/-- The tape cell the diagram is about to treat is read in the block of `n`. -/
lemma cellTape_current {sym : ℕ → Option Γ} {n j : ℕ} (hj : j < K) (hp : j + 1 = n % (K + 1)) :
    cellTape N K sym n j = (sym n).getD N.blank := by
  have hlt : ¬ j + 1 < n % (K + 1) := by omega
  have hn : n - n % (K + 1) + (j + 1) = n := by
    have := Nat.mod_le n (K + 1)
    omega
  simp only [cellTape, if_pos hj, if_neg hlt, Nat.zero_add, hn]

/-- **How the tape changes from one cell to the next**: only the tape cell the diagram has just
treated can change, and it takes the value written in the next block. -/
lemma cellTape_succ {sym : ℕ → Option Γ} (n j : ℕ) (hj : j < K) :
    cellTape N K sym (n + 1) j =
      if j + 1 = n % (K + 1) then (sym (n + (K + 1))).getD N.blank
      else cellTape N K sym n j := by
  have hK1 : 0 < K + 1 := Nat.succ_pos _
  have hmod : n % (K + 1) < K + 1 := Nat.mod_lt _ hK1
  have hle : n % (K + 1) ≤ n := Nat.mod_le n (K + 1)
  rcases Nat.lt_or_ge (n % (K + 1) + 1) (K + 1) with hlt | hge
  · -- the next cell is in the same block
    have hmod' : (n + 1) % (K + 1) = n % (K + 1) + 1 := mod_succ_of_lt hlt
    have hbase : n + 1 - (n + 1) % (K + 1) = n - n % (K + 1) := by
      rw [hmod']
      omega
    by_cases hcur : j + 1 = n % (K + 1)
    · have h1 : j + 1 < (n + 1) % (K + 1) := by omega
      have h2 : ¬ j + 1 < n % (K + 1) := by omega
      have hn : K + 1 + (n - n % (K + 1)) + (j + 1) = n + (K + 1) := by omega
      simp only [cellTape, if_pos hj, if_pos h1, if_neg h2, hbase, if_pos hcur, hn]
    · have h1 : (j + 1 < (n + 1) % (K + 1)) ↔ (j + 1 < n % (K + 1)) := by omega
      simp only [cellTape, if_pos hj, hbase, if_neg hcur]
      rw [show (if j + 1 < (n + 1) % (K + 1) then K + 1 else 0)
            = (if j + 1 < n % (K + 1) then K + 1 else 0) by
        by_cases h : j + 1 < n % (K + 1)
        · rw [if_pos (h1.2 h), if_pos h]
        · rw [if_neg (fun hc => h (h1.1 hc)), if_neg h]]
  · -- the next cell starts a new block
    have hmodK : n % (K + 1) = K := by omega
    have hmod' : (n + 1) % (K + 1) = 0 := mod_succ_of_eq hmodK
    have hbase : n + 1 - (n + 1) % (K + 1) = n - n % (K + 1) + (K + 1) := by
      rw [hmod']
      omega
    have h1 : ¬ j + 1 < (n + 1) % (K + 1) := by omega
    by_cases hcur : j + 1 = n % (K + 1)
    · have h2 : ¬ j + 1 < n % (K + 1) := by omega
      have hn : n - n % (K + 1) + (K + 1) + (j + 1) = n + (K + 1) := by omega
      simp only [cellTape, if_pos hj, if_neg h1, if_neg h2, hbase, if_pos hcur, Nat.zero_add, hn]
    · have h2 : j + 1 < n % (K + 1) := by omega
      have hn : n - n % (K + 1) + (K + 1) + (j + 1)
          = K + 1 + (n - n % (K + 1)) + (j + 1) := by omega
      simp only [cellTape, if_pos hj, if_neg h1, if_pos h2, hbase, if_neg hcur, Nat.zero_add, hn]

/-! ### A cell run is a run of the machine -/

variable {sym : ℕ → Option Γ} {st : ℕ → Q} {hd : ℕ → ℕ} {tr : ℕ → Bool}

/-- A cell without a transition does not change the configuration. -/
lemma cellConfig_succ_of_copy (h : IsCellRun N w K sym st hd tr) {n : ℕ} (hn : n < K * (K + 1))
    (htr : tr n = false) :
    cellConfig N K sym st hd (n + 1) = cellConfig N K sym st hd n := by
  obtain ⟨hsym, hst, hhd⟩ := h.copy n hn htr
  simp only [cellConfig, Config.mk.injEq]
  refine ⟨hst, hhd, ?_⟩
  funext j
  by_cases hj : j < K
  · rw [cellTape_succ (N := N) n j hj]
    by_cases hcur : j + 1 = n % (K + 1)
    · rw [if_pos hcur, hsym, cellTape_current (N := N) hj hcur]
    · rw [if_neg hcur]
  · simp [cellTape, hj]

/-- A cell with a transition performs one step of the machine. -/
lemma step_cellConfig_of_step (h : IsCellRun N w K sym st hd tr) {n : ℕ} (hn : n < K * (K + 1))
    (htr : tr n = true) :
    N.Step (cellConfig N K sym st hd n) (cellConfig N K sym st hd (n + 1)) := by
  obtain ⟨a, b, mv, hmem, hsa, hsb, hpos, hhdK, hmove⟩ := h.step n hn htr
  have hread : cellTape N K sym n (hd n) = a := by
    rw [cellTape_current (N := N) hhdK hpos.symm, hsa]
    rfl
  have htape : cellTape N K sym (n + 1) = Function.update (cellTape N K sym n) (hd n) b := by
    funext j
    by_cases hj : j < K
    · rw [cellTape_succ (N := N) n j hj]
      by_cases hcur : j + 1 = n % (K + 1)
      · have hjhd : j = hd n := by omega
        subst hjhd
        rw [if_pos hcur, hsb, Function.update_self]
        rfl
      · have hjhd : j ≠ hd n := by omega
        rw [if_neg hcur, Function.update_of_ne hjhd]
    · have hjhd : j ≠ hd n := by omega
      rw [Function.update_of_ne hjhd]
      simp [cellTape, hj]
  refine ⟨st (n + 1), b, mv, ?_, ?_⟩
  · simp only [cellConfig, hread]
    exact hmem
  · simp only [cellConfig, htape, hmove]

/-- **After the first `n` cells the machine has made exactly as many steps as there are
transition cells below `n`.** -/
theorem reaches_cellConfig (h : IsCellRun N w K sym st hd tr) :
    ∀ n ≤ K * (K + 1), N.Reaches ((List.range n).countP tr) (cellConfig N K sym st hd 0)
      (cellConfig N K sym st hd n) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hn' : n < K * (K + 1) := by omega
      have hrec := ih (by omega)
      rw [List.range_succ, List.countP_append]
      by_cases htr : tr n = true
      · have hstep := step_cellConfig_of_step h hn' htr
        have hone : N.Reaches 1 (cellConfig N K sym st hd n) (cellConfig N K sym st hd (n + 1)) :=
          ⟨_, hstep, rfl⟩
        have h2 : N.Reaches ((List.range n).countP tr + 1) (cellConfig N K sym st hd 0)
            (cellConfig N K sym st hd (n + 1)) := NTM.Reaches.trans N hrec hone
        simpa [htr] using h2
      · have hfalse : tr n = false := by simpa using htr
        rw [cellConfig_succ_of_copy h hn' hfalse]
        simpa [hfalse] using hrec

/-- The first configuration of a cell run is the initial configuration of the machine. -/
lemma cellConfig_zero (h : IsCellRun N w K sym st hd tr) (hwK : w.length ≤ K) :
    cellConfig N K sym st hd 0 = N.initConfig w := by
  simp only [cellConfig, NTM.initConfig, Config.mk.injEq]
  refine ⟨h.initState, h.headInit, ?_⟩
  funext j
  by_cases hj : j < K
  · have := h.initTape j hj
    simp only [cellTape, if_pos hj, Nat.zero_mod, Nat.sub_zero, Nat.zero_add,
      if_neg (by omega : ¬ j + 1 < 0)]
    rw [this]
    rfl
  · have hnone : w[j]? = none := List.getElem?_eq_none (by omega)
    simp only [cellTape, if_neg hj, List.getD, hnone]
    rfl

/-- **A cell run is an accepting run**: the machine accepts the input within as many steps as
the diagram has transition cells. -/
theorem acceptsWithin_of_isCellRun (h : IsCellRun N w K sym st hd tr) (hwK : w.length ≤ K) :
    N.AcceptsWithin w ((List.range (K * (K + 1))).countP tr) := by
  refine ⟨(List.range (K * (K + 1))).countP tr, le_rfl, cellConfig N K sym st hd (K * (K + 1)),
    ?_, h.accept⟩
  have := reaches_cellConfig h (K * (K + 1)) le_rfl
  rwa [cellConfig_zero h hwK] at this

/-- **A cell run with at most `T` transition cells is an accepting run of at most `T` steps.** -/
theorem acceptsWithin_of_isCellRun_le (h : IsCellRun N w K sym st hd tr) (hwK : w.length ≤ K)
    {T : ℕ} (hT : (List.range (K * (K + 1))).countP tr ≤ T) : N.AcceptsWithin w T := by
  obtain ⟨n, hn, c, hc, hacc⟩ := acceptsWithin_of_isCellRun h hwK
  exact ⟨n, le_trans hn hT, c, hc, hacc⟩

end TMEnc

end HTN
