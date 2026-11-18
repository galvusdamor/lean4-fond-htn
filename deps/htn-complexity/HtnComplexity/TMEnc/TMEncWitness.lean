import HtnComplexity.TMEnc.TMEncFixRight
/-!
# Witnesses: the space–time diagram a plan of the encoding writes out

A plan of the encoded problem of Theorem 4.3.7 writes out the word

`W = # w⁰ # w¹ # … # w^K`

of `K + 1` blocks of `K + 1` cells each: block `i` is the separator `#` followed by the `K`
tape cells of the machine at time `i`.  The hierarchy of the construction enforces that `W` is
the space–time diagram of an accepting run: the cell counters compare each cell with the cell
`K + 1` positions later (the same cell of the next tape), the head counter marks one cell per
block, and the marked cell is where a transition of the machine is applied.

This file introduces that combinatorial object — `HTN.TMEnc.IsWitness` — and proves the
**mathematical core of the simulation argument**, namely that witnesses and accepting runs are
the same thing:

* `HTN.TMEnc.homingRun_of_isWitness` — a witness yields a homing accepting run of exactly `K`
  steps (`HTN.TMEnc.HomingRun`);
* `HTN.TMEnc.isWitness_of_homingRun` — a homing accepting run yields a witness;
* `HTN.TMEnc.homingRun_iff_exists_witness` — the two are equivalent.

What is left of simulation correctness after this file is *purely* the plan-level half — that a
solution plan of the repaired problem writes out a witness, and that every witness can be
scheduled into a solution plan.  These two statements are the definitions
`HTN.TMEnc.SolutionYieldsWitnessFix` and `HTN.TMEnc.WitnessYieldsSolutionFix`, and
`HTN.TMEnc.encodingSoundFix_of_solutionYieldsWitness`,
`HTN.TMEnc.encodingCompleteFixHoming_of_witnessYieldsSolution` reduce soundness and
completeness of the repaired encoding to them.  See `NOTES.md`.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Witnesses -/

/-- **The space–time diagram of a run**, in the shape the encoding writes it out.

`sym i j` is the symbol in cell `j` of block `i` — cell `0` is the separator `#`, and cell
`j + 1` holds the tape cell `j` of the machine — `st i` is the state and `hd i` the head
position (as a machine tape cell, i.e. cell `hd i + 1` of the block) at time `i`.

The conditions are the ones the construction enforces: the blocks are separated by `#`, block
`0` holds the input, consecutive blocks differ only at the marked cell, where a transition of
the machine is applied, the head stays inside the `K` cells of a block, the run has exactly `K`
steps, it ends in an accepting state and — the assumption the source makes w.l.o.g. — with the
head back on the first cell. -/
structure IsWitness (N : NTM Q Γ) (w : List Γ) (K : ℕ)
    (sym : ℕ → ℕ → Option Γ) (st : ℕ → Q) (hd : ℕ → ℕ) : Prop where
  /-- Cell `0` of every block is the separator `#`. -/
  sep : ∀ i ≤ K, sym i 0 = none
  /-- Block `0` holds the input, padded with blanks. -/
  initTape : ∀ j, 1 ≤ j → j ≤ K → sym 0 j = some (w.getD (j - 1) N.blank)
  /-- The run starts in the initial state. -/
  initState : st 0 = N.init
  /-- The head is on one of the `K` tape cells of a block. -/
  headLt : ∀ i ≤ K, hd i < K
  /-- The head starts on the first cell. -/
  headInit : hd 0 = 0
  /-- The head returns to the first cell. -/
  headHome : hd K = 0
  /-- At the marked cell a transition of the machine is applied. -/
  step : ∀ i < K, ∃ c c' : Γ, ∃ m : Move,
    sym i (hd i + 1) = some c ∧ sym (i + 1) (hd i + 1) = some c' ∧
      (st (i + 1), c', m) ∈ N.step (st i) c ∧ hd (i + 1) = m.apply (hd i)
  /-- Every other cell is copied. -/
  copy : ∀ i < K, ∀ j, 1 ≤ j → j ≤ K → j ≠ hd i + 1 → sym (i + 1) j = sym i j
  /-- The last block is accepting. -/
  accept : st K ∈ N.accept

/-! ### From a witness to a run -/

/-- The tape of the machine at time `i`, read off a witness. -/
def witnessTape (N : NTM Q Γ) (K : ℕ) (sym : ℕ → ℕ → Option Γ) (i : ℕ) : ℕ → Γ :=
  fun t => if t < K then (sym i (t + 1)).getD N.blank else N.blank

/-- The configuration of the machine at time `i`, read off a witness. -/
def witnessConfig (N : NTM Q Γ) (K : ℕ) (sym : ℕ → ℕ → Option Γ) (st : ℕ → Q) (hd : ℕ → ℕ)
    (i : ℕ) : Config Q Γ :=
  ⟨st i, hd i, witnessTape N K sym i⟩

lemma witnessTape_of_lt {sym : ℕ → ℕ → Option Γ} {i t : ℕ} (ht : t < K) {c : Γ}
    (h : sym i (t + 1) = some c) : witnessTape N K sym i t = c := by
  simp [witnessTape, ht, h]

/-- **A witness is an accepting run of exactly `K` steps ending with the head at home.** -/
theorem homingRun_of_isWitness (hwK : w.length ≤ K) {sym : ℕ → ℕ → Option Γ} {st : ℕ → Q}
    {hd : ℕ → ℕ} (h : IsWitness N w K sym st hd) : HomingRun N w K := by
  refine ⟨witnessConfig N K sym st hd, ⟨?_, ?_, ?_⟩, h.headHome⟩
  · -- the initial configuration
    have htape : witnessTape N K sym 0 = fun t => w.getD t N.blank := by
      funext t
      by_cases ht : t < K
      · have h1 : sym 0 (t + 1) = some (w.getD t N.blank) := by
          have := h.initTape (t + 1) (by omega) (by omega)
          simpa using this
        simp [witnessTape, ht, h1]
      · have hnone : w[t]? = none := List.getElem?_eq_none (by omega)
        simp [witnessTape, ht, hnone]
    simp [witnessConfig, NTM.initConfig, h.initState, h.headInit, htape]
  · -- the transitions
    intro i hi
    obtain ⟨c, c', m, hc, hc', hmem, hmove⟩ := h.step i hi
    have hhd : hd i < K := h.headLt i (by omega)
    refine ⟨st (i + 1), c', m, ?_, ?_⟩
    · have : witnessTape N K sym i (hd i) = c := witnessTape_of_lt hhd hc
      simpa [witnessConfig, this] using hmem
    · have htape : witnessTape N K sym (i + 1) =
          Function.update (witnessTape N K sym i) (hd i) c' := by
        funext t
        by_cases ht : t = hd i
        · subst ht
          rw [Function.update_self]
          exact witnessTape_of_lt hhd hc'
        · rw [Function.update_of_ne ht]
          by_cases htK : t < K
          · have hne : t + 1 ≠ hd i + 1 := by omega
            have := h.copy i hi (t + 1) (by omega) (by omega) hne
            simp [witnessTape, htK, this]
          · simp [witnessTape, htK]
      simp [witnessConfig, htape, hmove]
  · exact h.accept

/-! ### From a run to a witness -/

/-- The space–time diagram of a run. -/
def runSym (K : ℕ) (hist : ℕ → Config Q Γ) (i j : ℕ) : Option Γ :=
  if j = 0 then none else if j ≤ K then some ((hist i).tape (j - 1)) else none

/-- **A homing accepting run of exactly `K` steps is a witness.** -/
theorem isWitness_of_homingRun (hK : 1 ≤ K) {hist : ℕ → Config Q Γ}
    (hh : IsHistory N w K hist) (hhome : (hist K).head = 0) :
    IsWitness N w K (runSym K hist) (fun i => (hist i).state) (fun i => (hist i).head) := by
  have hhead : ∀ i ≤ K, (hist i).head ≤ i := N.isHistory_head_le hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _; simp [runSym]
  · intro j hj1 hjK
    have h0 : hist 0 = N.initConfig w := hh.init
    have hj0 : ¬ j = 0 := by omega
    simp [runSym, h0, NTM.initConfig, hj0, hjK]
  · rw [hh.init]; rfl
  · intro i hi
    rcases eq_or_lt_of_le hi with rfl | hlt
    · omega
    · have := hhead i hi; omega
  · rw [hh.init]; rfl
  · exact hhome
  · intro i hi
    obtain ⟨q', γ', m, hmem, heq⟩ := hh.step i hi
    have hhd : (hist i).head < K := by have := hhead i (by omega); omega
    refine ⟨(hist i).tape ((hist i).head), γ', m, ?_, ?_, ?_, ?_⟩
    · have hle : (hist i).head + 1 ≤ K := by omega
      simp [runSym, hle]
    · have hup : (hist (i + 1)).tape ((hist i).head) = γ' := by
        rw [heq]; simp
      have hle : (hist i).head + 1 ≤ K := by omega
      simp [runSym, hle, hup]
    · rw [heq]; exact hmem
    · rw [heq]
  · intro i hi j hj1 hjK hjne
    have hne : j - 1 ≠ (hist i).head := by omega
    have hcopy := NTM.Step.tape_eq_of_ne N (hh.step i hi) hne
    have hj0 : ¬ j = 0 := by omega
    simp [runSym, hj0, hjK, hcopy]
  · exact hh.accept

/-- **Homing accepting runs and witnesses are the same thing.** -/
theorem homingRun_iff_exists_witness (hK : 1 ≤ K) (hwK : w.length ≤ K) :
    HomingRun N w K ↔
      ∃ (sym : ℕ → ℕ → Option Γ) (st : ℕ → Q) (hd : ℕ → ℕ), IsWitness N w K sym st hd := by
  constructor
  · rintro ⟨hist, hh, hhome⟩
    exact ⟨_, _, _, isWitness_of_homingRun hK hh hhome⟩
  · rintro ⟨sym, st, hd, h⟩
    exact homingRun_of_isWitness hwK h

/-! ### What is left of simulation correctness

The two statements below are the plan-level halves of the simulation argument; they are the
only part of the correctness of the repaired encoding that is not proved in this development,
and they are carried as explicit hypotheses. -/

/-- **The soundness half at the plan level**: every solution plan of the repaired problem writes
out a witness. -/
def SolutionYieldsWitnessFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  ∀ as : List (TMAct Q Γ), (problemFix N w K).IsSolutionPlan as →
    ∃ (sym : ℕ → ℕ → Option Γ) (st : ℕ → Q) (hd : ℕ → ℕ), IsWitness N w K sym st hd

/-- **The completeness half at the plan level**: every witness can be scheduled into a solution
plan of the repaired problem. -/
def WitnessYieldsSolutionFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  ∀ (sym : ℕ → ℕ → Option Γ) (st : ℕ → Q) (hd : ℕ → ℕ), IsWitness N w K sym st hd →
    (problemFix N w K).Solvable

/-- **Soundness of the repaired encoding reduces to the plan-level half.** -/
theorem encodingSoundFix_of_solutionYieldsWitness (hwK : w.length ≤ K)
    (h : SolutionYieldsWitnessFix N w K) : EncodingSoundFix N w K := by
  intro hsolv
  obtain ⟨as, hplan⟩ := Problem.solvable_iff_exists_solutionPlan.1 hsolv
  obtain ⟨sym, st, hd, hwit⟩ := h as hplan
  exact acceptsWithin_of_homingRun (homingRun_of_isWitness hwK hwit)

/-- **Completeness of the repaired encoding for homing runs reduces to the plan-level half.** -/
theorem encodingCompleteFixHoming_of_witnessYieldsSolution (hK : 1 ≤ K) (hwK : w.length ≤ K)
    (h : WitnessYieldsSolutionFix N w K) : EncodingCompleteFixHoming N w K := by
  intro hrun
  obtain ⟨sym, st, hd, hwit⟩ := (homingRun_iff_exists_witness hK hwK).1 hrun
  exact h sym st hd hwit

end TMEnc

end HTN
