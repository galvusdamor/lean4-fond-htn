import HtnPlanning.Interleave.InterleaveSplit
import HtnComplexity.Hypotheses.Partition
/-!
# The merge problem of the block family is the equal-sum partition problem

`HtnComplexity/Computable/MergeCorrect.lean` identifies the instance problem of the fixed
domain description `HTN.Merge.mergeDom` with the **merge (shuffle) problem**: is the word `z` an
interleaving of the words `ws`?  §21.4 of `NOTES.md` records what is still owed there — a
*hardness* statement for that problem, i.e. a reduction of a problem known to be hard to it.

This file is that reduction, as a statement about interleavings alone; the planning side is drawn
in `HtnCompilability/Computable/MergePartHard.lean`.

## The family

For a natural number `a` put

    zoWord a = 0^a 1^a          (`HTN.Merge.zoWord`)

and for a block size `B` and a number of blocks `m`

    zoBlocks B m = (0^B 1^B)^m  (`HTN.Merge.zoBlocks`).

**`HTN.Merge.interleave_zoWords_iff`**: for a list `as` of *positive* numbers,

    InterleaveList (as.map zoWord) (zoBlocks B m)  ↔  EqualSumPartition as B m,

where `HTN.Merge.EqualSumPartition as B m` says that `as` can be split into `m` groups each of
sum `B`.

## Why the equivalence holds

The interesting direction is left to right, and it is a counting argument, not a scheduling one.
Cut the interleaving at the end of the first block (`HTN.InterleaveList.exists_split`): every
component `0^{a} 1^{a}` is cut into a prefix `p` and a rest.  A prefix of `0^a 1^a` has at least
as many `0`s as `1`s, and has *equally* many only when it is empty or the whole word
(`HTN.Merge.zoWord_split`).  The first block `0^B 1^B` has `B` letters of each kind, and the two
counts are additive over the components, so the pointwise inequalities are all equalities: each
component is either untouched by the first block or entirely consumed by it.  The components
consumed by it therefore have `0`-count summing to `B`, i.e. their indices form a group of sum
`B`, and the remaining components interleave the remaining `m - 1` blocks.  Induction on `m`
finishes the argument, and the converse builds the interleaving group by group.

## What it is good for

`EqualSumPartition` with the side condition `B/4 < a < B/2` on the items is exactly
**3-Partition** — the side condition forces every group to have exactly three elements
(`HTN.Merge.length_eq_three_of_threePartition`) — which is NP-complete *in the strong sense*, so
the fact that the reduction writes the numbers in unary (the words have length `2a`) does not
spoil it.
-/

namespace HTN

namespace Merge

/-! ### The family -/

@[simp] theorem zoBlocks_zero (B : ℕ) : zoBlocks B 0 = [] := rfl

theorem zoBlocks_succ (B m : ℕ) : zoBlocks B (m + 1) = zoWord B ++ zoBlocks B m := rfl

/-! ### Counting in the words -/

@[simp] theorem countP_id_replicate_false (n : ℕ) :
    (List.replicate n false).countP (fun b => b) = 0 := by
  induction n <;> simp [List.replicate_succ, *]

@[simp] theorem countP_not_replicate_false (n : ℕ) :
    (List.replicate n false).countP (fun b => !b) = n := by
  induction n <;> simp [List.replicate_succ, *]

@[simp] theorem countP_id_replicate_true (n : ℕ) :
    (List.replicate n true).countP (fun b => b) = n := by
  induction n <;> simp [List.replicate_succ, *]

@[simp] theorem countP_not_replicate_true (n : ℕ) :
    (List.replicate n true).countP (fun b => !b) = 0 := by
  induction n <;> simp [List.replicate_succ, *]

@[simp] theorem countP_not_zoWord (a : ℕ) : (zoWord a).countP (fun b => !b) = a := by
  simp [zoWord, List.countP_append, List.countP_replicate]

@[simp] theorem countP_id_zoWord (a : ℕ) : (zoWord a).countP (fun b => b) = a := by
  simp [zoWord, List.countP_append, List.countP_replicate]

theorem zoWord_eq_nil_iff {a : ℕ} : zoWord a = [] ↔ a = 0 := by
  constructor
  · intro h
    have : (zoWord a).length = 0 := by rw [h]; rfl
    simpa [zoWord] using this
  · rintro rfl
    rfl

/-! ### The prefixes of `0^a 1^a` -/

/-- **The cuts of `0^a 1^a`.**  If `p ++ q = 0^a 1^a` then `p` has at least as many zeros as
ones, and exactly as many only if `p` is empty or `q` is. -/
theorem zoWord_split {a : ℕ} {p q : List Bool} (h : p ++ q = zoWord a) :
    p.countP (fun b => b) ≤ p.countP (fun b => !b) ∧
      (p.countP (fun b => b) = p.countP (fun b => !b) → p = [] ∨ q = []) := by
  rw [zoWord] at h
  rcases (List.append_eq_append_iff.1 h) with ⟨c, hc₁, hc₂⟩ | ⟨c, hc₁, hc₂⟩
  · -- `replicate a false = p ++ c`, so `p` consists of zeros only
    have hp : ∀ x ∈ p, x = false := by
      intro x hx
      have : x ∈ List.replicate a false := by rw [hc₁]; exact List.mem_append_left _ hx
      exact List.eq_of_mem_replicate this
    have hrep : p = List.replicate p.length false := List.eq_replicate_iff.2 ⟨rfl, hp⟩
    refine ⟨by rw [hrep]; simp, ?_⟩
    intro heq
    rw [hrep] at heq
    simp at heq
    left
    rw [hrep, ← heq]
    rfl
  · -- `p = replicate a false ++ c` with `c` a prefix of `replicate a true`
    have hc : ∀ x ∈ c, x = true := by
      intro x hx
      have : x ∈ List.replicate a true := by rw [hc₂]; exact List.mem_append_left _ hx
      exact List.eq_of_mem_replicate this
    have hrep : c = List.replicate c.length true := List.eq_replicate_iff.2 ⟨rfl, hc⟩
    have hlen : c.length + q.length = a := by
      have := congrArg List.length hc₂
      simpa using this.symm
    refine ⟨?_, ?_⟩
    · rw [hc₁, hrep]
      simp
      omega
    · intro heq
      rw [hc₁, hrep] at heq
      simp at heq
      right
      have : q.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero this

/-! ### Interleaving the words of one group into one block -/

/-- **One group of items fills one block.** -/
theorem interleaveList_group (g : List ℕ) :
    InterleaveList (g.map zoWord) (zoWord g.sum) := by
  induction g with
  | nil => simpa [zoWord] using (InterleaveList.nil : InterleaveList ([] : List (List Bool)) [])
  | cons a g ih =>
      refine InterleaveList.cons ih ?_
      have h0 : Interleave (List.replicate a false) (List.replicate g.sum false)
          (List.replicate (a + g.sum) false) := by
        rw [List.replicate_add]
        exact Interleave.append _ _
      have h1 : Interleave (List.replicate a true) (List.replicate g.sum true)
          (List.replicate (a + g.sum) true) := by
        rw [List.replicate_add]
        exact Interleave.append _ _
      have := h0.append_append h1
      simpa [zoWord, List.sum_cons] using this

/-! ### The equivalence -/

/-- The easy direction: a partition yields an interleaving. -/
theorem interleaveList_of_equalSumPartition {as : List ℕ} {B m : ℕ}
    (h : EqualSumPartition as B m) : InterleaveList (as.map zoWord) (zoBlocks B m) := by
  obtain ⟨gs, hlen, hperm, hsum⟩ := h
  have key : ∀ gs : List (List ℕ), (∀ g ∈ gs, g.sum = B) →
      InterleaveList (gs.flatten.map zoWord) (zoBlocks B gs.length) := by
    intro gs
    induction gs with
    | nil => intro _; simpa using (InterleaveList.nil : InterleaveList ([] : List (List Bool)) [])
    | cons g gs ih =>
        intro hsum
        have hg : g.sum = B := hsum g (by simp)
        have hrest := ih fun g' hg' => hsum g' (by simp [hg'])
        have hgroup : InterleaveList (g.map zoWord) (zoWord B) := by
          rw [← hg]; exact interleaveList_group g
        have := InterleaveList.append hgroup hrest
          (Interleave.append (zoWord B) (zoBlocks B gs.length))
        simpa [List.flatten_cons, zoBlocks_succ] using this
  have h1 := key gs hsum
  rw [hlen] at h1
  exact h1.perm ((hperm.map zoWord))

/-- Pointwise comparison with equal sums forces pointwise equality. -/
private theorem forall_eq_of_le_of_sum_eq {l : List (ℕ × ℕ)} (hle : ∀ p ∈ l, p.1 ≤ p.2)
    (hsum : (l.map Prod.fst).sum = (l.map Prod.snd).sum) : ∀ p ∈ l, p.1 = p.2 := by
  induction l with
  | nil => intro p hp; simp at hp
  | cons p l ih =>
      simp only [List.map_cons, List.sum_cons] at hsum
      have hrest : (l.map Prod.fst).sum ≤ (l.map Prod.snd).sum := by
        clear hsum ih
        induction l with
        | nil => simp
        | cons q l ih2 =>
            simp only [List.map_cons, List.sum_cons]
            have h1 : q.1 ≤ q.2 := hle q (by simp)
            have h2 := ih2 fun r hr => hle r (by
              rcases List.mem_cons.1 hr with rfl | hr
              · simp
              · simp [hr])
            omega
      have hp1 : p.1 ≤ p.2 := hle p (by simp)
      have hpeq : p.1 = p.2 := by omega
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hpeq
      · exact ih (fun r hr => hle r (by simp [hr])) (by omega) q hq

/-- The bookkeeping of the hard direction: the components that the first block consumes entirely
are recorded as a sublist `sel` of the items, the others as `other`. -/
private theorem exists_select {as : List ℕ} :
    ∀ {prs : List (List Bool × List Bool)}, as.map zoWord = prs.map (fun p => p.1 ++ p.2) →
      (∀ p ∈ prs, p.1 = [] ∨ p.2 = []) → (∀ a ∈ as, 0 < a) →
      ∃ sel other : List ℕ, (sel ++ other).Perm as ∧
        (prs.map Prod.fst).Perm (sel.map zoWord ++ List.replicate other.length []) ∧
        (prs.map Prod.snd).Perm (other.map zoWord ++ List.replicate sel.length []) := by
  induction as with
  | nil =>
      intro prs hmap _ _
      have : prs = [] := by
        cases prs with
        | nil => rfl
        | cons p prs => simp at hmap
      subst this
      exact ⟨[], [], List.Perm.refl _, by simp, by simp⟩
  | cons a as ih =>
      intro prs hmap hsplit hpos
      cases prs with
      | nil => simp at hmap
      | cons p prs =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          obtain ⟨hp, hmap'⟩ := hmap
          obtain ⟨sel, other, hperm, hfst, hsnd⟩ :=
            ih hmap' (fun q hq => hsplit q (by simp [hq])) (fun b hb => hpos b (by simp [hb]))
          rcases hsplit p (by simp) with h1 | h2
          · -- `p.1 = []`: the item survives the first block
            refine ⟨sel, a :: other, ?_, ?_, ?_⟩
            · exact List.perm_middle.trans (hperm.cons a)
            · simp only [List.map_cons, h1, List.length_cons, List.replicate_succ]
              exact (hfst.cons _).trans List.perm_middle.symm
            · have hp2 : p.2 = zoWord a := by
                have := hp
                rw [h1] at this
                simpa using this.symm
              simp only [List.map_cons, hp2]
              exact hsnd.cons _
          · -- `p.2 = []`: the item is consumed by the first block
            have hp1 : p.1 = zoWord a := by
              have := hp
              rw [h2] at this
              simpa using this.symm
            refine ⟨a :: sel, other, ?_, ?_, ?_⟩
            · exact hperm.cons a
            · simp only [List.map_cons, hp1]
              exact hfst.cons _
            · simp only [List.map_cons, h2, List.length_cons, List.replicate_succ]
              exact (hsnd.cons _).trans List.perm_middle.symm

/-- The sum of a group that fills one block is the block size. -/
theorem sum_eq_of_interleaveList_block {sel : List ℕ} {B : ℕ}
    (h : InterleaveList (sel.map zoWord) (zoWord B)) : sel.sum = B := by
  have := h.countP (fun b => !b)
  rw [countP_not_zoWord] at this
  rw [this, List.map_map]
  simp [Function.comp_def]

/-- The hard direction: an interleaving yields a partition. -/
theorem equalSumPartition_of_interleaveList {B : ℕ} :
    ∀ {m : ℕ} {as : List ℕ}, (∀ a ∈ as, 0 < a) →
      InterleaveList (as.map zoWord) (zoBlocks B m) → EqualSumPartition as B m := by
  intro m
  induction m with
  | zero =>
      intro as hpos h
      have hnil : ∀ l ∈ as.map zoWord, l = [] := h.eq_nil_of_interleave_nil rfl
      have : as = [] := by
        cases as with
        | nil => rfl
        | cons a as =>
            have := hnil (zoWord a) (by simp)
            have ha : a = 0 := zoWord_eq_nil_iff.1 this
            have := hpos a (by simp)
            omega
      subst this
      exact ⟨[], rfl, by simp, by simp⟩
  | succ m ihm =>
      intro as hpos h
      rw [zoBlocks_succ] at h
      obtain ⟨prs, hmap, hfst, hsnd⟩ := h.exists_split
      -- every component is either untouched or entirely consumed by the first block
      have hcount₁ := hfst.countP (fun b => b)
      have hcount₀ := hfst.countP (fun b => !b)
      rw [countP_id_zoWord] at hcount₁
      rw [countP_not_zoWord] at hcount₀
      have hle : ∀ p ∈ prs, (p.1.countP (fun b => b)) ≤ (p.1.countP (fun b => !b)) := by
        intro p hp
        have hmem : (p.1 ++ p.2) ∈ as.map zoWord := by
          rw [hmap]; exact List.mem_map_of_mem hp
        obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
        exact (zoWord_split ha.symm).1
      have hpairs : ∀ p ∈ prs, p.1.countP (fun b => b) = p.1.countP (fun b => !b) := by
        have hsum : ((prs.map (fun p => (p.1.countP (fun b => b), p.1.countP (fun b => !b)))).map
            Prod.fst).sum
            = ((prs.map (fun p => (p.1.countP (fun b => b), p.1.countP (fun b => !b)))).map
              Prod.snd).sum := by
          simp only [List.map_map, Function.comp_def]
          simp only [List.map_map, Function.comp_def] at hcount₁ hcount₀
          omega
        have := forall_eq_of_le_of_sum_eq (l := prs.map
          (fun p => (p.1.countP (fun b => b), p.1.countP (fun b => !b))))
          (by
            intro q hq
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
            exact hle p hp) hsum
        intro p hp
        exact this _ (List.mem_map_of_mem hp)
      have hsplit : ∀ p ∈ prs, p.1 = [] ∨ p.2 = [] := by
        intro p hp
        have hmem : (p.1 ++ p.2) ∈ as.map zoWord := by
          rw [hmap]; exact List.mem_map_of_mem hp
        obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
        exact (zoWord_split ha.symm).2 (hpairs p hp)
      obtain ⟨sel, other, hperm, hfperm, hsperm⟩ := exists_select hmap hsplit hpos
      -- the consumed components fill the first block, the others the remaining blocks
      have hselB : InterleaveList (sel.map zoWord) (zoWord B) :=
        InterleaveList.of_append_replicate_nil (hfst.perm hfperm)
      have hother : InterleaveList (other.map zoWord) (zoBlocks B m) :=
        InterleaveList.of_append_replicate_nil (hsnd.perm hsperm)
      have hsum : sel.sum = B := sum_eq_of_interleaveList_block hselB
      have hposother : ∀ a ∈ other, 0 < a := by
        intro a ha
        exact hpos a (hperm.subset (List.mem_append_right _ ha))
      -- `other` is shorter than `as` unless `sel` is empty
      by_cases hsel : sel = []
      · subst hsel
        have hB : B = 0 := by simpa using hsum.symm
        subst hB
        have hperm' : other.Perm as := by simpa using hperm
        have hother' : InterleaveList (as.map zoWord) (zoBlocks 0 m) :=
          hother.perm (hperm'.map zoWord)
        obtain ⟨gs, hlen, hgperm, hgsum⟩ := ihm hpos hother'
        exact ⟨[] :: gs, by simp [hlen], by simpa using hgperm, by
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg
          · simp
          · exact hgsum g hg⟩
      · obtain ⟨gs, hlen, hgperm, hgsum⟩ := ihm hposother hother
        refine ⟨sel :: gs, by simp [hlen], ?_, ?_⟩
        · simpa using (hgperm.append_left sel).trans hperm
        · intro g hg
          rcases List.mem_cons.1 hg with rfl | hg
          · exact hsum
          · exact hgsum g hg

/-- **The instance problem of the block family is the equal-sum partition problem.** -/
theorem interleave_zoWords_iff {as : List ℕ} {B m : ℕ} (hpos : ∀ a ∈ as, 0 < a) :
    InterleaveList (as.map zoWord) (zoBlocks B m) ↔ EqualSumPartition as B m :=
  ⟨equalSumPartition_of_interleaveList hpos, interleaveList_of_equalSumPartition⟩

/-! ### The side condition of 3-Partition -/

private theorem sum_map_mul (c : ℕ) (g : List ℕ) : (g.map (fun x => c * x)).sum = c * g.sum := by
  induction g with
  | nil => simp
  | cons a g ih => simp [ih, Nat.mul_add]

private theorem sum_lt_length_mul {g : List ℕ} {c : ℕ} (h : ∀ a ∈ g, a < c) (hne : g ≠ []) :
    g.sum < g.length * c := by
  induction g with
  | nil => exact absurd rfl hne
  | cons a g ih =>
      have ha : a < c := h a (by simp)
      rcases eq_or_ne g [] with rfl | hg
      · simpa using ha
      · have := ih (fun x hx => h x (by simp [hx])) hg
        simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
        omega

private theorem length_mul_lt_sum {g : List ℕ} {c : ℕ} (h : ∀ a ∈ g, c < a) (hne : g ≠ []) :
    g.length * c < g.sum := by
  induction g with
  | nil => exact absurd rfl hne
  | cons a g ih =>
      have ha : c < a := h a (by simp)
      rcases eq_or_ne g [] with rfl | hg
      · simpa using ha
      · have := ih (fun x hx => h x (by simp [hx])) hg
        simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
        omega

/-- **Under the 3-Partition side condition every group has exactly three elements.**  If every
item `a` satisfies `B < 4 * a` and `2 * a < B`, then a group of sum `B` has three elements. -/
theorem length_eq_three_of_threePartition {g : List ℕ} {B : ℕ} (hB : 0 < B)
    (hlow : ∀ a ∈ g, B < 4 * a) (hhigh : ∀ a ∈ g, 2 * a < B) (hsum : g.sum = B) :
    g.length = 3 := by
  have hne : g ≠ [] := by
    rintro rfl
    simp at hsum
    omega
  have h1 : g.length * B < 4 * g.sum := by
    have := length_mul_lt_sum (g := g.map (4 * ·)) (c := B)
      (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact hlow a ha)
      (by simpa using hne)
    simpa [List.length_map, sum_map_mul] using this
  have h2 : 2 * g.sum < g.length * B := by
    have := sum_lt_length_mul (g := g.map (2 * ·)) (c := B)
      (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact hhigh a ha)
      (by simpa using hne)
    simpa [List.length_map, sum_map_mul] using this
  rw [hsum] at h1 h2
  have hlt4 : g.length < 4 := by
    by_contra hcon
    push_neg at hcon
    have : 4 * B ≤ g.length * B := Nat.mul_le_mul_right B hcon
    omega
  have hgt2 : 2 < g.length := by
    by_contra hcon
    push_neg at hcon
    have : g.length * B ≤ 2 * B := Nat.mul_le_mul_right B hcon
    omega
  omega

/-- **3-Partition.**  Under the side condition every group of an equal-sum partition is a triple,
so the partition is a partition into `m` triples of sum `B`. -/
theorem threePartition_of_equalSumPartition {as : List ℕ} {B m : ℕ} (hB : 0 < B)
    (hlow : ∀ a ∈ as, B < 4 * a) (hhigh : ∀ a ∈ as, 2 * a < B) (h : EqualSumPartition as B m) :
    ∃ gs : List (List ℕ), gs.length = m ∧ gs.flatten.Perm as ∧
      ∀ g ∈ gs, g.sum = B ∧ g.length = 3 := by
  obtain ⟨gs, hlen, hperm, hsum⟩ := h
  refine ⟨gs, hlen, hperm, fun g hg => ⟨hsum g hg, ?_⟩⟩
  have hmem : ∀ a ∈ g, a ∈ as := by
    intro a ha
    exact hperm.subset (List.mem_flatten.2 ⟨g, hg, ha⟩)
  exact length_eq_three_of_threePartition hB (fun a ha => hlow a (hmem a ha))
    (fun a ha => hhigh a (hmem a ha)) (hsum g hg)

/-! ### Both answers occur -/

example : InterleaveList ([2, 2].map zoWord) (zoBlocks 2 2) :=
  interleaveList_of_equalSumPartition ⟨[[2], [2]], rfl, by simp, by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · rfl
    · rcases List.mem_cons.1 hg with rfl | hg
      · rfl
      · simp at hg⟩

example : ¬ InterleaveList ([3].map zoWord) (zoBlocks 1 3) := by
  intro h
  obtain ⟨gs, -, hperm, hsum⟩ := equalSumPartition_of_interleaveList (by simp) h
  have h3 : (3 : ℕ) ∈ gs.flatten := hperm.symm.subset (by simp)
  obtain ⟨g, hg, h3g⟩ := List.mem_flatten.1 h3
  have : (3 : ℕ) ≤ g.sum := List.single_le_sum (fun _ _ => Nat.zero_le _) 3 h3g
  rw [hsum g hg] at this
  omega

end Merge

end HTN
