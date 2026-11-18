import HtnComplexity.Computable.StripsDecide
import HtnComplexity.Computable.RegInv
import HtnPlanning.Progression.ProgressionSound
import HtnComplexity.SynClasses.UOHD
/-!
# One-hole-digging HTN planning: the bidirectional search on pieces

Dekker and Behnke (*Barely Decidable Fragments of Planning*, Lemma 6 and Proposition 7) decide
plan existence for one-hole-digging problems by a **bidirectional** search in which a compound
task is only decomposed when it is *isolated*.  Under that discipline the task network is always
a disjoint union of *pieces*, each piece being what is left of one copy of a task network of the
problem (the initial one or a method's), without ordering constraints between different pieces.
A search configuration is therefore described by

* the state of the forward search, the state of the backward search, and
* the multiset of pieces, a piece being a pair `(k, S)`: the index `k` of a task network of the
  description (`0` for the initial one, `j + 1` for the `j`-th method) and the set `S` of its
  identifiers that are still present.

This file defines that search (`HTN.HD.HStep`) and the representation relation `HTN.HD.RepW`
between semantic task networks and multisets of pieces, with the operations the two simulation
proofs need.
-/

namespace HTN

namespace HD

open Syn

/-! ### The search on pieces -/

/-- The task networks of a description: `0` is the initial one, `j + 1` the `j`-th method's. -/
def net (d : DomDesc) (q : InstDesc) : ℕ → TnDesc
  | 0 => q.tnI
  | j + 1 => (d.methods.getD j default).2

/-- A piece: the index of a task network and the identifiers of it that are still present. -/
abbrev Piece : Type := ℕ × Finset ℕ

/-- The multiset with the single piece `(k, S)`, or nothing if `S` is empty. -/
def piece (k : ℕ) (S : Finset ℕ) : Multiset Piece := if S = ∅ then 0 else {(k, S)}

/-- A configuration: the forward state, the backward state and the pieces. -/
abbrev HCfg : Type := Finset ℕ × Finset ℕ × Multiset Piece

/-- Applicability of an action, on finite states. -/
def appF (d : DomDesc) (s : Finset ℕ) (a : ℕ) : Prop := ∀ f ∈ (actOf d a).1, f ∈ s

/-- The transition of an action, on finite states. -/
def nxtF (d : DomDesc) (s : Finset ℕ) (a : ℕ) : Finset ℕ :=
  s.filter (fun f => f ∉ (actOf d a).2.2) ∪ (actOf d a).2.1.toFinset

/-- The facts a state of the search may contain. -/
def facts (d : DomDesc) (q : InstDesc) : Finset ℕ := (allFacts d q).toFinset

/-- The ordering of the task network with index `k`. -/
def ordK (d : DomDesc) (q : InstDesc) (k : ℕ) (a b : ℕ) : Prop := (net d q k).toTaskNetwork.ord a b

/-- **One step of the bidirectional search on pieces**: progressing a minimal primitive task,
regressing a maximal primitive task, or decomposing an isolated compound task. -/
inductive HStep (d : DomDesc) (q : InstDesc) : HCfg → HCfg → Prop
  | prog (sf sb : Finset ℕ) (M : Multiset Piece) (k : ℕ) (S : Finset ℕ) (x a : ℕ) :
      (k, S) ∈ M → x ∈ S → (∀ y ∈ S, ¬ ordK d q k y x) → (net d q k).label x = Sum.inl a →
      appF d sf a →
      HStep d q (sf, sb, M) (nxtF d sf a, sb, M.erase (k, S) + piece k (S.erase x))
  | regr (sf sb s : Finset ℕ) (M : Multiset Piece) (k : ℕ) (S : Finset ℕ) (x a : ℕ) :
      (k, S) ∈ M → x ∈ S → (∀ y ∈ S, ¬ ordK d q k x y) → (net d q k).label x = Sum.inl a →
      s ⊆ facts d q → appF d s a → nxtF d s a = sb →
      HStep d q (sf, sb, M) (sf, s, M.erase (k, S) + piece k (S.erase x))
  | dec (sf sb : Finset ℕ) (M : Multiset Piece) (k : ℕ) (S : Finset ℕ) (x c j : ℕ) :
      (k, S) ∈ M → x ∈ S → (∀ y ∈ S, ¬ ordK d q k y x ∧ ¬ ordK d q k x y) →
      (net d q k).label x = Sum.inr c → j < d.methods.length → (d.methods.getD j default).1 = c →
      HStep d q (sf, sb, M) (sf, sb, M.erase (k, S) + piece k (S.erase x) +
        piece (j + 1) (net d q (j + 1)).ids.toFinset)

/-- Reachability in the search on pieces. -/
def HReach (d : DomDesc) (q : InstDesc) : HCfg → HCfg → Prop := Relation.ReflTransGen (HStep d q)

/-- The initial pieces: the whole initial task network. -/
def initPieces (q : InstDesc) : Multiset Piece := piece 0 q.tnI.ids.toFinset

/-- **The pieces criterion**: from the initial state and a guessed goal state, the search on
pieces reaches a configuration without pieces in which the two states agree. -/
def PiecesSolvable (d : DomDesc) (q : InstDesc) : Prop :=
  ∃ sω s : Finset ℕ, sω ⊆ facts d q ∧ (∀ f ∈ q.goalList, f ∈ sω) ∧
    HReach d q (q.initList.toFinset, sω, initPieces q) (s, s, 0)

/-! ### Finite states and the semantic action model -/

theorem coe_nxtF (d : DomDesc) (s : Finset ℕ) (a : ℕ) :
    ({f | f ∈ nxtF d s a} : Set ℕ) = (d.toDomain.toActionModel).transition a {f | f ∈ s} := by
  ext f
  have h1 : (d.toDomain.toActionModel).del a = {f | f ∈ (actOf d a).2.2} := del_eq_actOf d a
  have h2 : (d.toDomain.toActionModel).add a = {f | f ∈ (actOf d a).2.1} := add_eq_actOf d a
  simp [nxtF, ActionModel.transition, h1, h2]

theorem appF_iff (d : DomDesc) (s : Finset ℕ) (a : ℕ) :
    appF d s a ↔ (d.toDomain.toActionModel).Applicable a {f | f ∈ s} := by
  simp only [appF, ActionModel.Applicable, DomDesc.toDomain]
  rw [prec_eq_actOf]
  exact Iff.rfl

end HD

end HTN
