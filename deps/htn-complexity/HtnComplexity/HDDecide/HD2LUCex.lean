import HtnComplexity.HDDecide.NetMain
import HtnComplexity.Computable.PoSearch
import HtnComplexity.SynClasses.HD2
import HtnPlanning.Classes.LU
/-!
# Lemma 6 of Dekker and Behnke fails for two-hole-digging, loop-unrolling problems

Dekker and Behnke decide plan existence for `1-HD-HTN` by a bidirectional search that decomposes
a compound task only when it is isolated (*Barely Decidable Fragments of Planning*, Lemma 6 and
Prop. 7; here `HTN.HD.HStep`, `HTN.HD.PiecesSolvable`).  The search is sound for every
description (`HTN.HD.solvable_of_piecesSolvable`), and it is a Petri net for every description
(`HTN.HD.piecesSolvable_iff_reach`); only completeness (Lemma 6,
`HTN.HD.piecesSolvable_of_solvable`) uses the one-hole restriction.

This file shows that completeness fails already for two-hole-digging, loop-unrolling problems
(`2-HD-HTN ∩ L`), so the Petri net of Prop. 7 does not decide that class
(`HTN.HD.Cex.exists_hd2LU_solvable_not_piecesSolvable`, `HTN.HD.Cex.not_solvable_iff_reach`).

## The instance

One compound name `c`, two methods, and an initial network with two compound tasks:

* `cont : c ↦ b ≺ h ≺ a` (`h` a copy of `c`), `stop : c ↦ t`;
* `t₀ = {c₁, c₂, p₁ ≺ p₂ ≺ p₃}`, the chain unordered with `c₁` and `c₂`.

The chain splits a plan into four phases `0 | 1 | 2 | 3`.  Fluents restrict `b` to phases
`0, 1`, `a` to phases `2, 3` and `t` to phases `0, 3`; moreover `p₂` needs a `b` in phase `1`
and `p₃` needs an `a` in phase `2`.  The problem is solvable: `b t p₁ b p₂ a p₃ t a`, the first
hole `b ≺ t ≺ a` and the second `b ≺ t ≺ a` crossing it (`cx_solvable`).

## Why the search fails

In a `cont` piece `b ≺ h ≺ a`, so the search can only *progress* `b` and only *regress* `a`.  Let
`i` be the number of chain tasks progressed and `3 - j` the number regressed, so the forward
search is in phase `i`, the backward search in phase `j`, and `i ≤ j`; `i` only grows and `j` only
shrinks.

* `p₃` cannot be progressed (no `a` is ever progressed), so `p₃` is regressed and some `a` is
  regressed in phase `2`, while its hole is still present.  Some hole is therefore closed (by
  `stop`) later, when `j ≤ 2`; its `t` must then run in phase `0`, so the closing happens with
  `i = 0`.
* `p₂` needs some `b` progressed in phase `1`, while its hole is still present.  Some hole is
  closed later, when `i ≥ 1`; its `t` must run in phase `3`, so the closing happens with `j = 3`.

The two closings are incompatible: whichever comes first, the frontiers have already moved too
far for the other.  The proof is an invariant of the search (`Good`), with ghost phases `i`, `j`,
the four events above as ghost propositions, and a monotone predicate `Bad` for the
configurations that can no longer finish.
-/

namespace HTN

namespace HD

namespace Cex

open Syn

/-! ### The instance

Facts: `0` = `bOK`, `1` = `aOK`, `2` = `tOK`, `3` = `bDone`, `4` = `aDone`.
Actions: `1` = `b`, `2` = `a`, `3` = `t`, `4` = `p₁`, `5` = `p₂`, `6` = `p₃`. -/

/-- `cont`: `b ≺ h ≺ a`, with identifiers `0 = b`, `1 = h`, `2 = a`. -/
def contTn : TnDesc := ([0, 1, 2], [(0, 1), (1, 2)], [(0, false, 1), (1, true, 0), (2, false, 2)])

/-- `stop`: the single task `t` (identifier `0`). -/
def stopTn : TnDesc := ([0], [], [(0, false, 3)])

/-- The initial network: `c₁ = 0`, `c₂ = 1`, and the chain `p₁ = 2 ≺ p₂ = 3 ≺ p₃ = 4`. -/
def tnI0 : TnDesc := ([0, 1, 2, 3, 4], [(2, 3), (3, 4)],
  [(0, true, 0), (1, true, 0), (2, false, 4), (3, false, 5), (4, false, 6)])

/-- The domain: the six actions and the two methods `cont` and `stop` of the compound name `0`. -/
def cxD : DomDesc :=
  ([(1, [0], [3], []), (2, [1], [4], []), (3, [2], [], []),
    (4, [], [], [2, 3]), (5, [3], [1], [0, 4]), (6, [4], [2], [])],
   [(0, contTn), (0, stopTn)])

/-- The instance: initially `bOK` and `tOK`, no goal. -/
def cxQ : InstDesc := ([0, 2], [], tnI0)

/-! ### The instance is solvable

The progression search on descriptions (`HTN.Syn.PReach`) is followed along a path given by
the indices of the chosen successors; the kernel checks the path. -/

/-- Follow the successors with the given indices. -/
def pick (d : DomDesc) : PConfig → List ℕ → PConfig
  | c, [] => c
  | c, i :: is => pick d ((succsOf d c).getD i c) is

/-- All indices of the path exist. -/
def pickOk (d : DomDesc) : PConfig → List ℕ → Bool
  | _, [] => true
  | c, i :: is => decide (i < (succsOf d c).length) && pickOk d ((succsOf d c).getD i c) is

theorem pReach_pick (d : DomDesc) : ∀ (is : List ℕ) (c : PConfig), pickOk d c is = true →
    PReach d c (pick d c is)
  | [], _, _ => Relation.ReflTransGen.refl
  | i :: is, c, h => by
    simp only [pickOk, Bool.and_eq_true, decide_eq_true_eq] at h
    refine Relation.ReflTransGen.head ?_ (pReach_pick d is _ h.2)
    show _ ∈ succsOf d c
    rw [List.getD_eq_getElem _ _ h.1]
    exact List.getElem_mem h.1

/-- The path `c₁ ↦ cont, b, h ↦ stop, t, p₁, c₂ ↦ cont, b, p₂, …`. -/
def cxPath : List ℕ := [0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 1, 0, 0]

/-- **The instance is solvable.** -/
theorem cx_solvable : Solvable cxD cxQ :=
  solvable_of_pReach (pReach_pick cxD cxPath _ (by decide)) (by decide)

/-! ### The instance is two-hole-digging and loop-unrolling -/

theorem isAbstractId_iff {t : TnDesc} {x : ℕ} :
    t.toTaskNetwork.IsAbstractId x ↔ (t.label x).isRight = true := by
  unfold TaskNetwork.IsAbstractId
  change (∃ c, t.label x = Sum.inr c) ↔ _
  cases t.label x <;> simp

theorem methodsHD1 : cxD.MethodsHD1 := by
  intro e he
  simp only [cxD, DomDesc.methods, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> intro x hx y hy hxa hya <;>
    simp only [TnDesc.toTaskNetwork, contTn, stopTn, TnDesc.ids, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert, Finset.mem_singleton, insert_empty_eq] at hx hy <;>
    rw [isAbstractId_iff] at hxa hya <;>
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | rfl | exact absurd hxa (by decide) | exact absurd hya (by decide)

/-- The compound tasks of the initial network are `c₁` and `c₂`. -/
theorem tnI0_abstract {x : ℕ} (hx : x ∈ tnI0.toTaskNetwork.T)
    (ha : tnI0.toTaskNetwork.IsAbstractId x) : x = 0 ∨ x = 1 := by
  rw [isAbstractId_iff] at ha
  simp only [TnDesc.toTaskNetwork, tnI0, TnDesc.ids, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_insert, Finset.mem_singleton, insert_empty_eq] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact absurd ha (by decide)

theorem isHD2 : cxQ.IsHD2 := by
  intro s hs habs
  have hsub : s ⊆ {0, 1} := fun x hx => by
    rcases tnI0_abstract (hs hx) (habs x hx) with rfl | rfl <;> simp
  exact (Finset.card_le_card hsub).trans (by decide)

/-- Every compound task name of the problem is `0`. -/
theorem eq_zero_of_label {t : TnDesc} (ht : t = tnI0 ∨ t = contTn ∨ t = stopTn) {x c : ℕ}
    (hx : x ∈ t.toTaskNetwork.T) (hc : t.toTaskNetwork.α x = Sum.inr c) : c = 0 := by
  change t.label x = Sum.inr c at hc
  have hx' : x ∈ t.ids := List.mem_toFinset.1 hx
  have hr : (t.label x).isRight = true := by rw [hc]; rfl
  have key : t.label x = Sum.inr 0 := by
    rcases ht with rfl | rfl | rfl
    · exact (by decide : ∀ y ∈ tnI0.ids, (tnI0.label y).isRight = true →
        tnI0.label y = Sum.inr 0) x hx' hr
    · exact (by decide : ∀ y ∈ contTn.ids, (contTn.label y).isRight = true →
        contTn.label y = Sum.inr 0) x hx' hr
    · exact (by decide : ∀ y ∈ stopTn.ids, (stopTn.label y).isRight = true →
        stopTn.label y = Sum.inr 0) x hx' hr
  exact (Sum.inr.inj (key.symm.trans hc)).symm

theorem isLU : (problem cxD cxQ).IsLU := by
  have hmeth : ∀ m : Method ℕ ℕ ℕ, m ∈ (problem cxD cxQ).methods →
      m = MethodDesc.toMethod (0, contTn) ∨ m = MethodDesc.toMethod (0, stopTn) := by
    rintro m ⟨e, he, rfl⟩
    simp only [cxD, DomDesc.methods, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨fun c hc c' hc' => ?_, ?_⟩
  · have key : ∀ c, (problem cxD cxQ).ReachableName c → c = 0 := by
      intro c h
      induction h with
      | tnI ht hc => exact eq_zero_of_label (Or.inl rfl) ht hc
      | method hm _ ht hc =>
        rcases hmeth _ hm with rfl | rfl
        · exact eq_zero_of_label (Or.inr (Or.inl rfl)) ht hc
        · exact eq_zero_of_label (Or.inr (Or.inr rfl)) ht hc
    exact (key c hc).trans (key c' hc').symm
  · calc {m | (problem cxD cxQ).ReachableMethod m}.encard
        ≤ ({MethodDesc.toMethod (0, contTn), MethodDesc.toMethod (0, stopTn)} :
            Set (Method ℕ ℕ ℕ)).encard :=
          Set.encard_le_encard fun m hm => by
            rcases hmeth m hm.1 with rfl | rfl <;> simp
      _ ≤ 2 := by
          refine (Set.encard_insert_le _ _).trans ?_
          rw [Set.encard_singleton]
          rfl

/-! ### Facts about the instance used by the search -/

@[simp] theorem net_zero : net cxD cxQ 0 = tnI0 := rfl
@[simp] theorem net_one : net cxD cxQ 1 = contTn := rfl
@[simp] theorem net_two : net cxD cxQ 2 = stopTn := rfl

theorem ordK_iff {k a b : ℕ} : ordK cxD cxQ k a b ↔ (net cxD cxQ k).ordB a b = true :=
  TnDesc.ordB_iff.symm

@[simp] theorem actOf_b : actOf cxD 1 = ([0], [3], []) := rfl
@[simp] theorem actOf_a : actOf cxD 2 = ([1], [4], []) := rfl
@[simp] theorem actOf_t : actOf cxD 3 = ([2], [], []) := rfl
@[simp] theorem actOf_p₁ : actOf cxD 4 = ([], [], [2, 3]) := rfl
@[simp] theorem actOf_p₂ : actOf cxD 5 = ([3], [1], [0, 4]) := rfl
@[simp] theorem actOf_p₃ : actOf cxD 6 = ([4], [2], []) := rfl

theorem mem_nxtF {s : Finset ℕ} {a f : ℕ} :
    f ∈ nxtF cxD s a ↔ (f ∈ s ∧ f ∉ (actOf cxD a).2.2) ∨ f ∈ (actOf cxD a).2.1 := by
  simp [nxtF]

theorem nxtF_t (s : Finset ℕ) : nxtF cxD s 3 = s := by
  ext f
  simp [mem_nxtF]

/-- The labels of the initial network: `c₁`, `c₂` compound, `pₖ` the action `k + 3`. -/
theorem tnI0_label_lo {x : ℕ} (hx : x ≤ 1) : tnI0.label x = Sum.inr 0 := by
  interval_cases x <;> rfl

theorem tnI0_label_hi {x : ℕ} (h₁ : 2 ≤ x) (h₂ : x ≤ 4) : tnI0.label x = Sum.inl (x + 2) := by
  interval_cases x <;> rfl

theorem tnI0_ord {x y : ℕ} (hy : 2 ≤ y) (hyx : y < x) (hx : x ≤ 4) : ordK cxD cxQ 0 y x := by
  rw [ordK_iff]
  interval_cases x <;> interval_cases y <;> decide

/-! ### The invariant -/

/-- The shapes of a `cont` piece during the search: `b ≺ h ≺ a` with `b` and `a` possibly gone;
the hole `h` is only removed together with the piece. -/
def contShapes : Finset (Finset ℕ) := {{0, 1, 2}, {1, 2}, {0, 1}, {1}}

/-- The pieces other than the remainder of the initial network. -/
def RestOk (R : Multiset Piece) : Prop :=
  ∀ p ∈ R, (p.1 = 1 ∧ p.2 ∈ contShapes) ∨ p = (2, {0})

/-- The number of compound tasks: `c₁`, `c₂` still in the initial network, and the holes. -/
def ncomp (C : Finset ℕ) (R : Multiset Piece) : ℕ := C.card + R.countP (fun p => p.1 = 1)

/-- **Dead ends**: a `stop` piece whose `t` can no longer run (the forward search is past phase
`0`, the backward search before phase `3`, and the backward state lacks `tOK`), or a backward
state with `tOK` in phases `1, 2`, which can never meet a forward state. -/
def Bad (sb : Finset ℕ) (R : Multiset Piece) (i j : ℕ) : Prop :=
  ((2, {0}) ∈ R ∧ 1 ≤ i ∧ j ≤ 2 ∧ 2 ∉ sb) ∨ (2 ∈ sb ∧ j ≤ 2)

/-- **The invariant**, with the ghost phases `i`, `j`, the compound tasks `C` left in the initial
network, the other pieces `R`, and the events `Pa` (an `a` was regressed in phase `2`), `Pb` (a
`b` was progressed in phase `1`), `A₁` (a hole was closed with `i = 0`, `j ≤ 2`) and `A₂` (a hole
was closed with `i ≥ 1`, `j = 3`). -/
structure Good (sf sb : Finset ℕ) (M : Multiset Piece) (i j : ℕ) (C : Finset ℕ)
    (R : Multiset Piece) (Pa Pb A₁ A₂ : Prop) : Prop where
  hM : M = piece 0 (C ∪ Finset.Ico (i + 2) (j + 2)) + R
  hC : C ⊆ {0, 1}
  hR : RestOk R
  hij : i ≤ j
  hi : i ≤ 2
  hj : 1 ≤ j
  hj3 : j ≤ 3
  tOK_sf : 2 ∈ sf ↔ i = 0
  aDone_sf : 4 ∉ sf
  bDone_sf : i = 1 → 3 ∈ sf → Pb
  pb_of_i : 2 ≤ i → Pb
  bDone_sb : j = 1 → 3 ∈ sb
  pa_of_aDone : j = 2 → 4 ∉ sb → Pa
  pa_of_j : j ≤ 1 → Pa
  pa_j : Pa → j ≤ 2
  pb_i : Pb → 1 ≤ i
  a₁_j : A₁ → j ≤ 2
  a₂_i : A₂ → 1 ≤ i
  not_both : ¬ (A₁ ∧ A₂)
  comp_a : Pa → ¬ A₁ → ¬ Bad sb R i j → 1 ≤ ncomp C R
  comp_b : Pb → ¬ A₂ → ¬ Bad sb R i j → 1 ≤ ncomp C R

/-- The invariant, with the ghost data quantified. -/
def Inv (c : HCfg) : Prop :=
  ∃ i j C R, ∃ Pa Pb A₁ A₂ : Prop, Good c.1 c.2.1 c.2.2 i j C R Pa Pb A₁ A₂

/-! ### Lemmas for the invariant -/

theorem bad_mono {sb sb' : Finset ℕ} {R R' : Multiset Piece} {i i' j j' : ℕ} (hi : i ≤ i')
    (hj : j' ≤ j) (hR : (2, {0}) ∈ R → 1 ≤ i → j ≤ 2 → 2 ∉ sb → (2, {0}) ∈ R')
    (hs : j ≤ 2 → (2 ∈ sb' ↔ 2 ∈ sb)) : Bad sb R i j → Bad sb' R' i' j' := by
  rintro (⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂⟩)
  · exact Or.inl ⟨hR h₁ h₂ h₃ h₄, h₂.trans hi, hj.trans h₃, fun h => h₄ ((hs h₃).1 h)⟩
  · exact Or.inr ⟨(hs h₂).2 h₁, hj.trans h₂⟩

theorem mem_split {X : Finset ℕ} {R : Multiset Piece} {k : ℕ} {S : Finset ℕ}
    (h : (k, S) ∈ piece 0 X + R) : (k = 0 ∧ S = X ∧ X ≠ ∅) ∨ (k, S) ∈ R := by
  rcases Multiset.mem_add.1 h with h | h
  · obtain ⟨hX, he⟩ := mem_piece.1 h
    simp only [Prod.mk.injEq] at he
    exact Or.inl ⟨he.1, he.2, hX⟩
  · exact Or.inr h

theorem erase_zero {X : Finset ℕ} (R : Multiset Piece) (hX : X ≠ ∅) :
    (piece 0 X + R).erase (0, X) = R := by
  rw [piece_eq_singleton (Finset.nonempty_iff_ne_empty.2 hX), Multiset.singleton_add,
    Multiset.erase_cons_head]

theorem erase_rest {X : Finset ℕ} {R : Multiset Piece} {p : Piece} (h : p ∈ R) :
    (piece 0 X + R).erase p = piece 0 X + R.erase p :=
  Multiset.erase_add_right_pos _ h

theorem restOk_erase {R : Multiset Piece} (h : RestOk R) (p : Piece) : RestOk (R.erase p) :=
  fun q hq => h q (Multiset.mem_of_mem_erase hq)

theorem restOk_add {R R' : Multiset Piece} (h : RestOk R) (h' : RestOk R') : RestOk (R + R') :=
  fun q hq => (Multiset.mem_add.1 hq).elim (h q) (h' q)

theorem restOk_cont {S : Finset ℕ} (hS : S ∈ contShapes) : RestOk (piece 1 S) := by
  intro q hq
  obtain ⟨-, rfl⟩ := mem_piece.1 hq
  exact Or.inl ⟨rfl, hS⟩

theorem restOk_stop : RestOk (piece 2 {0}) := by
  intro q hq
  obtain ⟨-, rfl⟩ := mem_piece.1 hq
  exact Or.inr rfl

theorem countP_eq_erase {R : Multiset Piece} {q : Piece} (h : q ∈ R) :
    R.countP (fun p => p.1 = 1) = (R.erase q).countP (fun p => p.1 = 1) +
      if q.1 = 1 then 1 else 0 := by
  conv_lhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

theorem one_le_ncomp {C : Finset ℕ} {R : Multiset Piece} {S : Finset ℕ} (h : (1, S) ∈ R) :
    1 ≤ ncomp C R := by
  have : 0 < R.countP (fun p => p.1 = 1) := Multiset.countP_pos.2 ⟨_, h, rfl⟩
  unfold ncomp
  omega

theorem le_one_of_mem {C : Finset ℕ} (hC : C ⊆ {0, 1}) {y : ℕ} (hy : y ∈ C) : y ≤ 1 := by
  have := hC hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem mem_X {C : Finset ℕ} {i j y : ℕ} :
    y ∈ C ∪ Finset.Ico (i + 2) (j + 2) ↔ y ∈ C ∨ (i + 2 ≤ y ∧ y < j + 2) := by
  simp [Finset.mem_Ico]

/-- Removing a chain task from the remainder of the initial network. -/
theorem erase_X {C : Finset ℕ} (hC : C ⊆ {0, 1}) {a b a' b' x : ℕ} (hx : 2 ≤ x)
    (h : ∀ y, (y ≠ x ∧ a ≤ y ∧ y < b) ↔ (a' ≤ y ∧ y < b')) :
    (C ∪ Finset.Ico a b).erase x = C ∪ Finset.Ico a' b' := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_Ico]
  by_cases hy : y ∈ C
  · have := le_one_of_mem hC hy
    exact ⟨fun _ => Or.inl hy, fun _ => ⟨by omega, Or.inl hy⟩⟩
  · simp only [hy, false_or]
    exact h y

/-- Removing `c₁` or `c₂` from the remainder of the initial network. -/
theorem erase_X_comp {C : Finset ℕ} {i j x : ℕ} (hx : x ≤ 1) :
    (C ∪ Finset.Ico (i + 2) (j + 2)).erase x = C.erase x ∪ Finset.Ico (i + 2) (j + 2) := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_Ico]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact Or.inl ⟨hne, h⟩
    · exact Or.inr h
  · rintro (⟨hne, h⟩ | h)
    · exact ⟨hne, Or.inl h⟩
    · exact ⟨by omega, Or.inr h⟩

theorem shape_basic : ∀ S ∈ contShapes, 1 ∈ S ∧ S ⊆ {0, 1, 2} := by decide

theorem shape_erase_b : ∀ S ∈ contShapes, 0 ∈ S → S.erase 0 ∈ contShapes ∧ S.erase 0 ≠ ∅ := by
  decide

theorem shape_erase_a : ∀ S ∈ contShapes, 2 ∈ S → S.erase 2 ∈ contShapes ∧ S.erase 2 ≠ ∅ := by
  decide

/-- A hole can only be decomposed once `b` and `a` are gone. -/
theorem shape_iso : ∀ S ∈ contShapes, 0 ∉ S → 2 ∉ S → S = {1} := by decide

theorem mem_contShapes {S : Finset ℕ} :
    S ∈ contShapes ↔ S = {0, 1, 2} ∨ S = {1, 2} ∨ S = {0, 1} ∨ S = {1} := by
  simp [contShapes]

theorem bad_new_stop {sb : Finset ℕ} {R : Multiset Piece} {i j : ℕ} (hR : (2, {0}) ∈ R)
    (hi : 1 ≤ i) (hj : j ≤ 2) : Bad sb R i j := by
  by_cases h : 2 ∈ sb
  · exact Or.inr ⟨h, hj⟩
  · exact Or.inl ⟨hR, hi, hj, h⟩

theorem not_bad_three {sb : Finset ℕ} {R : Multiset Piece} {i : ℕ} : ¬ Bad sb R i 3 := by
  rintro (⟨-, -, h, -⟩ | ⟨-, h⟩) <;> omega

section Steps

variable {sf sb : Finset ℕ} {M : Multiset Piece} {i j : ℕ} {C : Finset ℕ} {R : Multiset Piece}
  {Pa Pb A₁ A₂ : Prop}

/-- A step that adds a hole (`cont`) and changes nothing else. -/
theorem good_cont (g : Good sf sb M i j C R Pa Pb A₁ A₂) {M' : Multiset Piece} {C' : Finset ℕ}
    {R' : Multiset Piece} {S' : Finset ℕ} (hM : M' = piece 0 (C' ∪ Finset.Ico (i + 2) (j + 2)) + R')
    (hC : C' ⊆ {0, 1}) (hR : RestOk R') (h₁ : (1, S') ∈ R') :
    Good sf sb M' i j C' R' Pa Pb A₁ A₂ :=
  { g with hM := hM, hC := hC, hR := hR
           comp_a := fun _ _ _ => one_le_ncomp h₁
           comp_b := fun _ _ _ => one_le_ncomp h₁ }

/-- A step that closes a hole (`stop`): the events `A₁` and `A₂` are recorded. -/
theorem good_stop (g : Good sf sb M i j C R Pa Pb A₁ A₂) {M' : Multiset Piece} {C' : Finset ℕ}
    {R' : Multiset Piece} (hM : M' = piece 0 (C' ∪ Finset.Ico (i + 2) (j + 2)) + R')
    (hC : C' ⊆ {0, 1}) (hR : RestOk R') (h₂ : (2, {0}) ∈ R') :
    Good sf sb M' i j C' R' Pa Pb (A₁ ∨ (i = 0 ∧ j ≤ 2)) (A₂ ∨ (1 ≤ i ∧ j = 3)) :=
  { g with hM := hM, hC := hC, hR := hR
           a₁_j := by rintro (h | ⟨-, h⟩); exacts [g.a₁_j h, h]
           a₂_i := by rintro (h | ⟨h, -⟩); exacts [g.a₂_i h, h]
           not_both := by
             rintro ⟨h₁ | ⟨h₁, h₁'⟩, h₂ | ⟨h₂, h₂'⟩⟩
             · exact g.not_both ⟨h₁, h₂⟩
             · have := g.a₁_j h₁; omega
             · have := g.a₂_i h₂; omega
             · omega
           comp_a := by
             intro hPa hA hB
             have hj := g.pa_j hPa
             have hi : 1 ≤ i := by
               by_contra h
               exact hA (Or.inr ⟨by omega, hj⟩)
             exact absurd (bad_new_stop h₂ hi hj) hB
           comp_b := by
             intro hPb hA hB
             have hi := g.pb_i hPb
             have hj : j ≤ 2 := by
               by_contra h
               have := g.hj3
               exact hA (Or.inr ⟨hi, by omega⟩)
             exact absurd (bad_new_stop h₂ hi hj) hB }

/-- **Progression preserves the invariant.** -/
theorem inv_prog (g : Good sf sb M i j C R Pa Pb A₁ A₂) {k : ℕ} {S : Finset ℕ} {x a : ℕ}
    (hmem : (k, S) ∈ M) (hx : x ∈ S) (hmin : ∀ y ∈ S, ¬ ordK cxD cxQ k y x)
    (hlab : (net cxD cxQ k).label x = Sum.inl a) (happ : appF cxD sf a) :
    Inv (nxtF cxD sf a, sb, M.erase (k, S) + piece k (S.erase x)) := by
  rw [g.hM] at hmem ⊢
  rcases mem_split hmem with ⟨rfl, rfl, hX⟩ | hR'
  · -- a task of the initial network: the next task of the chain
    rw [erase_zero R hX]
    rcases mem_X.1 hx with hxC | ⟨hx₁, hx₂⟩
    · rw [net_zero, tnI0_label_lo (le_one_of_mem g.hC hxC)] at hlab
      exact absurd hlab (by simp)
    have hj3 := g.hj3
    have hi2 := g.hi
    obtain rfl : x = i + 2 := by
      by_contra hne
      exact hmin (i + 2) (mem_X.2 (Or.inr ⟨le_rfl, by omega⟩)) (tnI0_ord (by omega) (by omega)
        (by omega))
    rw [net_zero, tnI0_label_hi (by omega) (by omega)] at hlab
    obtain rfl : a = i + 2 + 2 := (Sum.inl.inj hlab).symm
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · -- `p₁`
      refine ⟨1, j, C, R, Pa, Pb, A₁, A₂, ?_⟩
      exact { g with
        hM := by
          rw [erase_X g.hC (by norm_num) (b' := j + 2) (a' := 1 + 2) (fun y => by omega)]
          exact add_comm _ _
        hij := by omega
        hi := by norm_num
        tOK_sf := by simp [mem_nxtF]
        aDone_sf := by simp [mem_nxtF, g.aDone_sf]
        bDone_sf := by simp [mem_nxtF]
        pb_of_i := by omega
        pb_i := fun _ => le_rfl
        a₂_i := fun _ => le_rfl
        comp_a := fun h₁ h₂ h₃ => g.comp_a h₁ h₂ fun hb =>
          h₃ (bad_mono (by norm_num) le_rfl (fun h _ _ _ => h) (fun _ => Iff.rfl) hb)
        comp_b := fun h₁ h₂ h₃ => g.comp_b h₁ h₂ fun hb =>
          h₃ (bad_mono (by norm_num) le_rfl (fun h _ _ _ => h) (fun _ => Iff.rfl) hb) }
    · -- `p₂`: needs `bDone`, so a `b` ran in phase `1`
      have h3 : 3 ∈ sf := happ 3 (by simp)
      have hPb := g.bDone_sf rfl h3
      refine ⟨2, j, C, R, Pa, Pb, A₁, A₂, ?_⟩
      exact { g with
        hM := by
          rw [erase_X g.hC (by norm_num) (b' := j + 2) (a' := 2 + 2) (fun y => by omega)]
          exact add_comm _ _
        hij := by omega
        hi := le_rfl
        tOK_sf := by simp [mem_nxtF, g.tOK_sf]
        aDone_sf := by simp [mem_nxtF]
        bDone_sf := by omega
        pb_of_i := fun _ => hPb
        pb_i := fun _ => by norm_num
        a₂_i := fun _ => by norm_num
        comp_a := fun h₁ h₂ h₃ => g.comp_a h₁ h₂ fun hb =>
          h₃ (bad_mono (by norm_num) le_rfl (fun h _ _ _ => h) (fun _ => Iff.rfl) hb)
        comp_b := fun h₁ h₂ h₃ => g.comp_b h₁ h₂ fun hb =>
          h₃ (bad_mono (by norm_num) le_rfl (fun h _ _ _ => h) (fun _ => Iff.rfl) hb) }
    · -- `p₃`: needs `aDone`, which no progressed action adds
      exact absurd (happ 4 (by simp)) g.aDone_sf
  · rw [erase_rest hR']
    rcases g.hR _ hR' with ⟨hk, hS⟩ | he
    · -- a `cont` piece: only `b` can be progressed
      obtain rfl : k = 1 := hk
      obtain ⟨h1S, hS3⟩ := shape_basic S hS
      have hx3 := hS3 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx3
      obtain rfl : x = 0 := by
        rcases hx3 with h | rfl | rfl
        · exact h
        · cases hlab
        · exact absurd (ordK_iff.2 rfl) (hmin 1 h1S)
      obtain rfl : a = 1 := (Sum.inl.inj hlab).symm
      obtain ⟨hS', hne⟩ := shape_erase_b S hS hx
      refine ⟨i, j, C, R.erase (1, S) + piece 1 (S.erase 0), Pa, Pb ∨ i = 1, A₁, A₂, ?_⟩
      have h₁ : (1, S.erase 0) ∈ R.erase (1, S) + piece 1 (S.erase 0) :=
        Multiset.mem_add.2 (Or.inr (mem_piece.2 ⟨hne, rfl⟩))
      exact { g with
        hM := by rw [add_assoc]
        hR := restOk_add (restOk_erase g.hR _) (restOk_cont hS')
        tOK_sf := by simp [mem_nxtF, g.tOK_sf]
        aDone_sf := by simp [mem_nxtF, g.aDone_sf]
        bDone_sf := fun h _ => Or.inr h
        pb_of_i := fun h => Or.inl (g.pb_of_i h)
        pb_i := by rintro (h | h); exacts [g.pb_i h, h.ge]
        comp_a := fun _ _ _ => one_le_ncomp h₁
        comp_b := fun _ _ _ => one_le_ncomp h₁ }
    · -- a `stop` piece: `t` needs `tOK`, so the forward search is in phase `0`
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Finset.mem_singleton] at hx
      subst hx
      obtain rfl : a = 3 := (Sum.inl.inj hlab).symm
      have hi0 : i = 0 := g.tOK_sf.1 (happ 2 (by simp))
      refine ⟨i, j, C, R.erase (2, {0}), Pa, Pb, A₁, A₂, ?_⟩
      have hcnt := countP_eq_erase hR'
      simp only [show (2 : ℕ) = 1 ↔ False by decide, if_false, add_zero] at hcnt
      have hbad : Bad sb R i j → Bad sb (R.erase (2, {0})) i j :=
        bad_mono le_rfl le_rfl (fun _ h => absurd h (by omega)) (fun _ => Iff.rfl)
      exact { g with
        hM := by simp [piece]
        hR := restOk_erase g.hR _
        tOK_sf := by rw [nxtF_t]; exact g.tOK_sf
        aDone_sf := by rw [nxtF_t]; exact g.aDone_sf
        bDone_sf := by rw [nxtF_t]; exact g.bDone_sf
        comp_a := fun h₁ h₂ h₃ => by
          have := g.comp_a h₁ h₂ (fun hb => h₃ (hbad hb)); unfold ncomp at this ⊢; omega
        comp_b := fun h₁ h₂ h₃ => by
          have := g.comp_b h₁ h₂ (fun hb => h₃ (hbad hb)); unfold ncomp at this ⊢; omega }

/-- **Regression preserves the invariant.** -/
theorem inv_regr (g : Good sf sb M i j C R Pa Pb A₁ A₂) {s : Finset ℕ} {k : ℕ} {S : Finset ℕ}
    {x a : ℕ} (hmem : (k, S) ∈ M) (hx : x ∈ S) (hmax : ∀ y ∈ S, ¬ ordK cxD cxQ k x y)
    (hlab : (net cxD cxQ k).label x = Sum.inl a) (happ : appF cxD s a)
    (hnxt : nxtF cxD s a = sb) :
    Inv (sf, s, M.erase (k, S) + piece k (S.erase x)) := by
  rw [g.hM] at hmem ⊢
  rcases mem_split hmem with ⟨rfl, rfl, hX⟩ | hR'
  · -- a task of the initial network: the last task of the chain
    rw [erase_zero R hX]
    rcases mem_X.1 hx with hxC | ⟨hx₁, hx₂⟩
    · rw [net_zero, tnI0_label_lo (le_one_of_mem g.hC hxC)] at hlab
      exact absurd hlab (by simp)
    have hj3 := g.hj3
    have hj1 := g.hj
    obtain rfl : x = j + 1 := by
      by_contra hne
      exact hmax (j + 1) (mem_X.2 (Or.inr ⟨by omega, by omega⟩)) (tnI0_ord (by omega) (by omega)
        (by omega))
    rw [net_zero, tnI0_label_hi (by omega) (by omega)] at hlab
    obtain rfl : a = j + 1 + 2 := (Sum.inl.inj hlab).symm
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl
    · -- `p₁` cannot be regressed: the backward state holds `bDone`
      have h3 := g.bDone_sb rfl
      rw [← hnxt] at h3
      simp [mem_nxtF] at h3
    · -- `p₂`: the backward state lacks `aDone`, so an `a` was regressed in phase `2`
      have h4 : 4 ∉ sb := by rw [← hnxt]; simp [mem_nxtF]
      have hPa := g.pa_of_aDone rfl h4
      have h2 : 2 ∈ s ↔ 2 ∈ sb := by rw [← hnxt]; simp [mem_nxtF]
      refine ⟨i, 1, C, R, Pa, Pb, A₁, A₂, ?_⟩
      exact { g with
        hM := by
          rw [erase_X g.hC (by norm_num) (b' := 1 + 2) (a' := i + 2) (fun y => by omega)]
          exact add_comm _ _
        hij := by omega
        hj := le_rfl
        hj3 := by norm_num
        bDone_sb := fun _ => happ 3 (by simp)
        pa_of_aDone := by omega
        pa_of_j := fun _ => hPa
        pa_j := fun _ => by norm_num
        a₁_j := fun _ => by norm_num
        comp_a := fun h₁ h₂ h₃ => g.comp_a h₁ h₂ fun hb =>
          h₃ (bad_mono le_rfl (by norm_num) (fun h _ _ _ => h) (fun _ => h2) hb)
        comp_b := fun h₁ h₂ h₃ => g.comp_b h₁ h₂ fun hb =>
          h₃ (bad_mono le_rfl (by norm_num) (fun h _ _ _ => h) (fun _ => h2) hb) }
    · -- `p₃`
      have h4 : 4 ∈ s := happ 4 (by simp)
      refine ⟨i, 2, C, R, Pa, Pb, A₁, A₂, ?_⟩
      exact { g with
        hM := by
          rw [erase_X g.hC (by norm_num) (b' := 2 + 2) (a' := i + 2) (fun y => by omega)]
          exact add_comm _ _
        hij := g.hi
        hj := by norm_num
        hj3 := by norm_num
        bDone_sb := by omega
        pa_of_aDone := fun _ h => absurd h4 h
        pa_of_j := by omega
        pa_j := fun _ => le_rfl
        a₁_j := fun _ => le_rfl
        comp_a := fun h₁ h₂ _ => g.comp_a h₁ h₂ not_bad_three
        comp_b := fun h₁ h₂ _ => g.comp_b h₁ h₂ not_bad_three }
  · rw [erase_rest hR']
    rcases g.hR _ hR' with ⟨hk, hS⟩ | he
    · -- a `cont` piece: only `a` can be regressed
      obtain rfl : k = 1 := hk
      obtain ⟨h1S, hS3⟩ := shape_basic S hS
      have hx3 := hS3 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx3
      obtain rfl : x = 2 := by
        rcases hx3 with rfl | rfl | h
        · exact absurd (ordK_iff.2 rfl) (hmax 1 h1S)
        · cases hlab
        · exact h
      obtain rfl : a = 2 := (Sum.inl.inj hlab).symm
      obtain ⟨hS', hne⟩ := shape_erase_a S hS hx
      refine ⟨i, j, C, R.erase (1, S) + piece 1 (S.erase 2), Pa ∨ j = 2, Pb, A₁, A₂, ?_⟩
      have h₁ : (1, S.erase 2) ∈ R.erase (1, S) + piece 1 (S.erase 2) :=
        Multiset.mem_add.2 (Or.inr (mem_piece.2 ⟨hne, rfl⟩))
      exact { g with
        hM := by rw [add_assoc]
        hR := restOk_add (restOk_erase g.hR _) (restOk_cont hS')
        bDone_sb := fun h => by
          have := g.bDone_sb h
          rw [← hnxt] at this
          simpa [mem_nxtF] using this
        pa_of_aDone := fun h _ => Or.inr h
        pa_of_j := fun h => Or.inl (g.pa_of_j h)
        pa_j := by rintro (h | h); exacts [g.pa_j h, h.le]
        comp_a := fun _ _ _ => one_le_ncomp h₁
        comp_b := fun _ _ _ => one_le_ncomp h₁ }
    · -- a `stop` piece: `t` changes nothing, and needs `tOK` in the backward state
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Finset.mem_singleton] at hx
      subst hx
      obtain rfl : a = 3 := (Sum.inl.inj hlab).symm
      rw [nxtF_t] at hnxt
      subst hnxt
      have h2 : 2 ∈ s := happ 2 (by simp)
      refine ⟨i, j, C, R.erase (2, {0}), Pa, Pb, A₁, A₂, ?_⟩
      have hcnt := countP_eq_erase hR'
      simp only [show (2 : ℕ) = 1 ↔ False by decide, if_false, add_zero] at hcnt
      have hbad : Bad s R i j → Bad s (R.erase (2, {0})) i j :=
        bad_mono le_rfl le_rfl (fun _ _ _ h => absurd h2 h) (fun _ => Iff.rfl)
      exact { g with
        hM := by simp [piece]
        hR := restOk_erase g.hR _
        comp_a := fun h₁ h₂ h₃ => by
          have := g.comp_a h₁ h₂ (fun hb => h₃ (hbad hb)); unfold ncomp at this ⊢; omega
        comp_b := fun h₁ h₂ h₃ => by
          have := g.comp_b h₁ h₂ (fun hb => h₃ (hbad hb)); unfold ncomp at this ⊢; omega }

theorem new_cont : piece (0 + 1) (net cxD cxQ (0 + 1)).ids.toFinset = {(1, {0, 1, 2})} := by
  decide

theorem new_stop : piece (1 + 1) (net cxD cxQ (1 + 1)).ids.toFinset = {(2, {0})} := by decide

/-- **Decomposition preserves the invariant.** -/
theorem inv_dec (g : Good sf sb M i j C R Pa Pb A₁ A₂) {k : ℕ} {S : Finset ℕ} {x c m : ℕ}
    (hmem : (k, S) ∈ M) (hx : x ∈ S)
    (hiso : ∀ y ∈ S, ¬ ordK cxD cxQ k y x ∧ ¬ ordK cxD cxQ k x y)
    (hlab : (net cxD cxQ k).label x = Sum.inr c) (hm : m < cxD.methods.length) :
    Inv (sf, sb, M.erase (k, S) + piece k (S.erase x) +
      piece (m + 1) (net cxD cxQ (m + 1)).ids.toFinset) := by
  have hm' : m = 0 ∨ m = 1 := by
    have : cxD.methods.length = 2 := rfl
    omega
  rw [g.hM] at hmem ⊢
  rcases mem_split hmem with ⟨rfl, rfl, hX⟩ | hR'
  · -- `c₁` or `c₂`
    rw [erase_zero R hX]
    have hxC : x ∈ C := by
      rcases mem_X.1 hx with h | ⟨hx₁, hx₂⟩
      · exact h
      · have := g.hj3
        rw [net_zero, tnI0_label_hi (by omega) (by omega)] at hlab
        cases hlab
    have hx1 := le_one_of_mem g.hC hxC
    rw [erase_X_comp hx1]
    have hC' : C.erase x ⊆ {0, 1} := (Finset.erase_subset _ _).trans g.hC
    have hcard : (C.erase x).card + 1 = C.card := Finset.card_erase_add_one hxC
    rcases hm' with rfl | rfl
    · refine ⟨i, j, C.erase x, R + {(1, {0, 1, 2})}, Pa, Pb, A₁, A₂, ?_⟩
      refine good_cont g ?_ hC' (restOk_add g.hR (by
        rw [← piece_eq_singleton (by decide)]; exact restOk_cont (by decide)))
        (S' := {0, 1, 2}) (by simp)
      dsimp only
      rw [new_cont]
      abel
    · refine ⟨i, j, C.erase x, R + {(2, {0})}, Pa, Pb, A₁ ∨ (i = 0 ∧ j ≤ 2),
        A₂ ∨ (1 ≤ i ∧ j = 3), ?_⟩
      refine good_stop g ?_ hC' (restOk_add g.hR (by
        rw [← piece_eq_singleton (by decide)]; exact restOk_stop)) (by simp)
      dsimp only
      rw [new_stop]
      abel
  · rw [erase_rest hR']
    rcases g.hR _ hR' with ⟨hk, hS⟩ | he
    · -- a hole: `b` and `a` are gone
      obtain rfl : k = 1 := hk
      obtain ⟨h1S, hS3⟩ := shape_basic S hS
      have hx3 := hS3 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx3
      obtain rfl : x = 1 := by
        rcases hx3 with rfl | h | rfl
        · cases hlab
        · exact h
        · cases hlab
      obtain rfl : S = {1} := shape_iso S hS (fun h => (hiso 0 h).1 (ordK_iff.2 rfl))
        (fun h => (hiso 2 h).2 (ordK_iff.2 rfl))
      have hcnt := countP_eq_erase (q := (1, {1})) hR'
      simp only [if_true] at hcnt
      have hempty : piece 1 (({1} : Finset ℕ).erase 1) = 0 := by simp [piece]
      rw [hempty, add_zero]
      rcases hm' with rfl | rfl
      · refine ⟨i, j, C, R.erase (1, {1}) + {(1, {0, 1, 2})}, Pa, Pb, A₁, A₂, ?_⟩
        refine good_cont g ?_ g.hC (restOk_add (restOk_erase g.hR _) (by
          rw [← piece_eq_singleton (by decide)]; exact restOk_cont (by decide)))
          (S' := {0, 1, 2}) (by simp)
        dsimp only
        rw [new_cont, add_assoc]
      · refine ⟨i, j, C, R.erase (1, {1}) + {(2, {0})}, Pa, Pb, A₁ ∨ (i = 0 ∧ j ≤ 2),
          A₂ ∨ (1 ≤ i ∧ j = 3), ?_⟩
        refine good_stop g ?_ g.hC (restOk_add (restOk_erase g.hR _) (by
          rw [← piece_eq_singleton (by decide)]; exact restOk_stop)) (by simp)
        dsimp only
        rw [new_stop, add_assoc]
    · -- `t` is not compound
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Finset.mem_singleton] at hx
      subst hx
      cases hlab

/-- **Every step of the search preserves the invariant.** -/
theorem inv_step {c c' : HCfg} (h : HStep cxD cxQ c c') (hc : Inv c) : Inv c' := by
  obtain ⟨i, j, C, R, Pa, Pb, A₁, A₂, g⟩ := hc
  cases h with
  | prog sf sb M k S x a hmem hx hmin hlab happ => exact inv_prog g hmem hx hmin hlab happ
  | regr sf sb s M k S x a hmem hx hmax hlab _ happ hnxt =>
    exact inv_regr g hmem hx hmax hlab happ hnxt
  | dec sf sb M k S x c m hmem hx hiso hlab hm _ => exact inv_dec g hmem hx hiso hlab hm

end Steps

/-! ### The initial and the final configurations -/

theorem inv_init (sω : Finset ℕ) : Inv (cxQ.initList.toFinset, sω, initPieces cxQ) := by
  refine ⟨0, 3, {0, 1}, 0, False, False, False, False, ?_⟩
  exact {
    hM := by show initPieces cxQ = _; decide
    hC := Finset.Subset.refl _
    hR := fun _ h => absurd h (Multiset.notMem_zero _)
    hij := by norm_num
    hi := by norm_num
    hj := by norm_num
    hj3 := le_rfl
    tOK_sf := by show 2 ∈ cxQ.initList.toFinset ↔ _; decide
    aDone_sf := by show 4 ∉ cxQ.initList.toFinset; decide
    bDone_sf := by omega
    pb_of_i := by omega
    bDone_sb := by omega
    pa_of_aDone := by omega
    pa_of_j := by omega
    pa_j := False.elim
    pb_i := False.elim
    a₁_j := False.elim
    a₂_i := False.elim
    not_both := fun h => h.1
    comp_a := False.elim
    comp_b := False.elim }

/-- **No final configuration satisfies the invariant.** -/
theorem not_final {s : Finset ℕ} {i j : ℕ} {C : Finset ℕ} {R : Multiset Piece}
    {Pa Pb A₁ A₂ : Prop} (g : Good s s 0 i j C R Pa Pb A₁ A₂) : False := by
  obtain ⟨hp, hR⟩ := add_eq_zero.1 g.hM.symm
  have hX : C ∪ Finset.Ico (i + 2) (j + 2) = ∅ := by
    by_contra h
    rw [piece_eq_singleton (Finset.nonempty_iff_ne_empty.2 h)] at hp
    exact Multiset.singleton_ne_zero _ hp
  obtain ⟨hC, hI⟩ := Finset.union_eq_empty.1 hX
  have hji : j ≤ i := by
    by_contra h
    have : i + 2 ∈ Finset.Ico (i + 2) (j + 2) := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    rw [hI] at this
    exact Finset.notMem_empty _ this
  have hj := g.hj
  have hi := g.hi
  have hij := g.hij
  have hn : ncomp C R = 0 := by simp [ncomp, hC, hR]
  have hbad : ¬ Bad s R i j := by
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · rw [hR] at h; exact Multiset.notMem_zero _ h
    · have := g.tOK_sf.1 h; omega
  have hPa : Pa := by
    rcases (by omega : j ≤ 1 ∨ j = 2) with h | h
    · exact g.pa_of_j h
    · exact g.pa_of_aDone h g.aDone_sf
  have hPb : Pb := by
    rcases (by omega : i = 1 ∨ 2 ≤ i) with h | h
    · exact g.bDone_sf h (g.bDone_sb (by omega))
    · exact g.pb_of_i h
  have hA₁ : A₁ := by
    by_contra h
    have := g.comp_a hPa h hbad
    omega
  have hA₂ : A₂ := by
    by_contra h
    have := g.comp_b hPb h hbad
    omega
  exact g.not_both ⟨hA₁, hA₂⟩

/-! ### The results -/

/-- **The search on pieces fails on the instance.** -/
theorem not_piecesSolvable : ¬ PiecesSolvable cxD cxQ := by
  rintro ⟨sω, s, -, -, h⟩
  have key : ∀ c, HReach cxD cxQ (cxQ.initList.toFinset, sω, initPieces cxQ) c → Inv c := by
    intro c hc
    induction hc with
    | refl => exact inv_init sω
    | tail _ hstep ih => exact inv_step hstep ih
  obtain ⟨i, j, C, R, Pa, Pb, A₁, A₂, g⟩ := key _ h
  exact not_final g

/-- **Lemma 6 of Dekker and Behnke fails for `2-HD-HTN ∩ L`**: there is a solvable
two-hole-digging, loop-unrolling description that the bidirectional search on pieces does not
solve. -/
theorem exists_hd2LU_solvable_not_piecesSolvable :
    ∃ d q, d.MethodsHD1 ∧ q.IsHD2 ∧ (problem d q).IsLU ∧ Solvable d q ∧ ¬ PiecesSolvable d q :=
  ⟨cxD, cxQ, methodsHD1, isHD2, isLU, cx_solvable, not_piecesSolvable⟩

/-- **The Petri net of Prop. 7 does not decide `2-HD-HTN ∩ L`**: for the instance, the final
marking is unreachable although the problem is solvable. -/
theorem not_solvable_iff_reach :
    ¬ ∀ d q, d.MethodsHD1 → q.IsHD2 → (problem d q).IsLU →
      (Solvable d q ↔ Petri.Reach (hdNet d q) (hdM0 q : Multiset ℕ) (hdM1 : Multiset ℕ)) :=
  fun h => not_piecesSolvable (piecesSolvable_iff_reach.2
    ((h cxD cxQ methodsHD1 isHD2 isLU).1 cx_solvable))

end Cex

end HD

end HTN
