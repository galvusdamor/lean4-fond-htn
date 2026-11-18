import HtnPlanning.Basic
import HtnPlanning.Classes.Basic
import HtnComplexity.Complexity.BitCoding
import ComplexityTheory.Complexity.Hypotheses
/-!
# The equal-sum partition problem in a fixed merge domain

**Definitions only.**  Grid descriptions of task networks, the merge domain and its instances
`HTN.Merge.mergeInst`, the equal-sum partition problem `HTN.Merge.EqualSumPartition` and its
instances `HTN.Merge.partInst` in the merge domain, and the statement
`HTN.Syn.ThreePartitionNPHard` that every `NP` language reduces in polynomial time to it (proved
in `HtnComplexity/NPHard/ThreePartition.lean`).
-/

/-! ## Grid descriptions (for the partition instances) -/

namespace HTN

namespace Syn

open TaskNetwork

/-- The `i`-th row of a described grid. -/
def gridRow (ls : List (List (Bool × ℕ))) (i : ℕ) : List (Bool × ℕ) := ls.getD i []

/-- The identifiers of a described grid. -/
def cellIds (ls : List (List (Bool × ℕ))) : List ℕ :=
  (List.range ls.length).flatMap fun i =>
    (List.range (gridRow ls i).length).map fun j => Nat.pair i j

/-- The ordering pairs of a described grid: the consecutive pairs of each row. -/
def cellOrd (ls : List (List (Bool × ℕ))) : List (ℕ × ℕ) :=
  (List.range ls.length).flatMap fun i =>
    (List.range ((gridRow ls i).length - 1)).map fun j => (Nat.pair i j, Nat.pair i (j + 1))

/-- The labels of a described grid. -/
def cellLbl (ls : List (List (Bool × ℕ))) : List (ℕ × Bool × ℕ) :=
  (List.range ls.length).flatMap fun i =>
    (List.range (gridRow ls i).length).map fun j =>
      (Nat.pair i j, (gridRow ls i).getD j (false, 0))

/-- **The description of a grid of tasks.** -/
def gridDesc (ls : List (List (Bool × ℕ))) : TnDesc := (cellIds ls, cellOrd ls, cellLbl ls)

variable {ls : List (List (Bool × ℕ))}

section Denotes

variable {A C : Type} [Inhabited A]

/-- A task name, as a described label. -/
def encLabel (eA : A → ℕ) (eC : C → ℕ) : A ⊕ C → Bool × ℕ
  | Sum.inl a => (false, eA a)
  | Sum.inr c => (true, eC c)

/-- **The description of the grid `ls`**, with the names numbered by `eA` and `eC`. -/
def gridDescOf (eA : A → ℕ) (eC : C → ℕ) (ls : List (List (A ⊕ C))) : TnDesc :=
  gridDesc (ls.map fun row => row.map (encLabel eA eC))

end Denotes

end Syn

end HTN

/-! ## The merge domain (for the partition instances) -/

namespace HTN

namespace Merge

open Syn TaskNetwork Domain

/-- The *write* action for a bit. -/
def aName (b : Bool) : ℕ := cond b 1 0

/-- The *read* action for a bit. -/
def bName (b : Bool) : ℕ := cond b 3 2

/-- The word `w` as the list of its write actions. -/
def aWord (w : List Bool) : List ℕ := w.map aName

/-- The word `z` as the list of its read actions. -/
def bWord (z : List Bool) : List ℕ := z.map bName

/-- The action lists of the branches of the initial task network: one per word of `ws`, plus the
branch that reads `z`. -/
def letters (ws : List (List Bool)) (z : List Bool) : List (List ℕ) :=
  ws.map aWord ++ [bWord z]

/-- A list of action names, as a chain of primitive tasks. -/
def primChain (l : List ℕ) : List (ℕ ⊕ ℕ) := l.map Sum.inl

/-- The branches of the initial task network of an instance. -/
def chains (ws : List (List Bool)) (z : List Bool) : List (List (ℕ ⊕ ℕ)) :=
  (letters ws z).map primChain

/-- **The instance description** for the words `ws` and the word `z`. -/
def mergeInst (ws : List (List Bool)) (z : List Bool) : InstDesc :=
  ([0], [0], gridDescOf id id (chains ws z))

end Merge

end HTN

/-! ## Equal-sum partition -/

namespace HTN

namespace Merge

/-- The word `0^a 1^a`. -/
def zoWord (a : ℕ) : List Bool :=
  List.replicate a false ++ List.replicate a true

/-- The word `(0^B 1^B)^m`: `m` blocks, each `B` zeros followed by `B` ones. -/
def zoBlocks (B : ℕ) : ℕ → List Bool
  | 0 => []
  | m + 1 => zoWord B ++ zoBlocks B m

/-- `as` can be split into `m` groups, each of sum `B`. -/
def EqualSumPartition (as : List ℕ) (B m : ℕ) : Prop :=
  ∃ gs : List (List ℕ), gs.length = m ∧ gs.flatten.Perm as ∧ ∀ g ∈ gs, g.sum = B

end Merge

end HTN

/-! ## Partition instances as descriptions -/

namespace HTN

namespace Merge

open Syn Table

/-- The instance of the fixed domain description `mergeDom` that asks for an equal-sum
partition: one chain of writes `0^a 1^a` per item `a ∈ as`, unordered against the chain of reads
`(0^B 1^B)^m`. -/
def partInst (as : List ℕ) (B m : ℕ) : InstDesc :=
  mergeInst (as.map zoWord) (zoBlocks B m)

end Merge

end HTN

/-! ## `P ≠ NP` and the NP-hardness of 3-Partition -/

namespace HTN

namespace Syn

open PTime Merge

/-- **A polynomial-time many-one reduction of `L` to the equal-sum partition problem**, in the
concrete form this development uses: the reduction (a function computed in polynomial time by a Turing machine (`HTN.PTime.PolyTimeFun`, i.e. Mathlib's
`Turing.TM2ComputableInPolyTime` on bit strings)) writes, for every input `x`, the serialisation
of an instance description `partInst as B m` with positive items, and `x ∈ L` exactly when `as`
splits into `m` groups of sum `B`.

Since the instances `partInst as B m` spell the numbers out in unary — the chain of an item `a`
has `2a` tasks — a reduction of this shape is exactly a reduction to 3-Partition *in the strong
sense*, which is the classical statement. -/
def ReducesToPartition (L : List Bool → Prop) : Prop :=
  ∃ r : List Bool → List Bool, PolyTimeFun r ∧
    ∀ x, ∃ (as : List ℕ) (B m : ℕ), (∀ a ∈ as, 0 < a) ∧
      r x = codingSer.code (partInst as B m) ∧ (L x ↔ EqualSumPartition as B m)

/-- **The NP-hardness of 3-Partition**: every language of `NP` reduces in polynomial time to the
equal-sum partition problem written in unary.  It is *proved* in
`HtnComplexity/NPHard/ThreePartition.lean` (`HTN.NPHard.threePartitionNPHard`, by Cook–Levin
and the Garey–Johnson reduction), so no theorem of the project carries it as a hypothesis. -/
def ThreePartitionNPHard : Prop := ∀ L : List Bool → Prop, InNP L → ReducesToPartition L

end Syn

end HTN

