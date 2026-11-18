import ComplexityTheory.Collapse.Quant
/-!
# Savitch's recursion, and bounded paths

The target bridge of cells 1 and 2 of Table 3 (`HtnCompilability/Space/Table3Sep.lean`) is
Savitch's theorem: a *nondeterministic* polynomial-space machine can be replaced by a
*deterministic* one.  Its mathematical content is the halving recursion

    R 0       u v  =  stp u v
    R (k + 1) u v  =  ∃ m of the right width,  R k u m  ∧  R k m v,

which decides reachability within `2 ^ k` steps while only ever holding `k` midpoints, and hence
runs in space `k` times the width of a node.

This file is the part of the argument that mentions neither the machine model nor polynomial
time: the recursion `HTN.Savitch.Rec` above, taken over an abstract *reflexive* step predicate
`stp` on bit strings of a fixed width `E`, is proved equivalent to the existence of a path of
exactly `2 ^ k` steps (`HTN.Savitch.rec_eq_true_iff`), and paths are proved shortenable: a path
through nodes of a finite pool may be taken to visit no node twice, hence to be shorter than the
pool (`HTN.Savitch.exists_pathN_le_of_pathN`).

Nodes are bit strings of one fixed width `E`; reflexivity of `stp` at that width is what makes a
path extendable, so that "at most `n` steps" and "exactly `n` steps" agree.
-/

namespace HTN

namespace Savitch

open PTime PSpace

/-! ### Paths -/

/-- **A path of exactly `n` steps** from `u` to `v`: a sequence of nodes of width `E`, each a
`stp`-successor of the previous one. -/
def PathN (stp : List Bool → List Bool → Bool) (E n : ℕ) (u v : List Bool) : Prop :=
  ∃ f : ℕ → List Bool, f 0 = u ∧ f n = v ∧ (∀ i ≤ n, (f i).length = E) ∧
    ∀ i < n, stp (f i) (f (i + 1)) = true

variable {stp : List Bool → List Bool → Bool} {E : ℕ}

theorem pathN_zero {u v : List Bool} (h : u = v) (hu : u.length = E) : PathN stp E 0 u v :=
  ⟨fun _ => u, rfl, h, fun _ _ => hu, fun i hi => absurd hi (by omega)⟩

theorem PathN.length_left {n : ℕ} {u v : List Bool} (h : PathN stp E n u v) : u.length = E := by
  obtain ⟨f, h0, -, hlen, -⟩ := h
  rw [← h0]; exact hlen 0 (Nat.zero_le _)

theorem PathN.length_right {n : ℕ} {u v : List Bool} (h : PathN stp E n u v) : v.length = E := by
  obtain ⟨f, -, hn, hlen, -⟩ := h
  rw [← hn]; exact hlen n le_rfl

/-- One step is a path of one step. -/
theorem pathN_one {u v : List Bool} (h : stp u v = true) (hu : u.length = E)
    (hv : v.length = E) : PathN stp E 1 u v := by
  refine ⟨fun i => if i = 0 then u else v, by simp, by simp, ?_, ?_⟩
  · intro i _
    by_cases hi : i = 0 <;> simp [hi, hu, hv]
  · intro i hi
    have hi0 : i = 0 := by omega
    simp [hi0, h]

/-- Paths compose. -/
theorem PathN.trans {m n : ℕ} {u v w : List Bool} (h₁ : PathN stp E m u v)
    (h₂ : PathN stp E n v w) : PathN stp E (m + n) u w := by
  obtain ⟨f, hf0, hfm, hflen, hfstep⟩ := h₁
  obtain ⟨g, hg0, hgn, hglen, hgstep⟩ := h₂
  refine ⟨fun i => if i ≤ m then f i else g (i - m), by simp [hf0], ?_, ?_, ?_⟩
  · by_cases h : m + n ≤ m
    · have hn : n = 0 := by omega
      subst hn
      simp only [Nat.add_zero, le_refl, if_pos]
      rw [hfm]
      exact hg0.symm.trans hgn
    · simp only [if_neg h]
      have hmn : m + n - m = n := by omega
      rw [hmn, hgn]
  · intro i hi
    by_cases h : i ≤ m
    · simp only [if_pos h]; exact hflen i h
    · simp only [if_neg h]; exact hglen (i - m) (by omega)
  · intro i hi
    by_cases h : i + 1 ≤ m
    · simp only [if_pos (show i ≤ m by omega), if_pos h]
      exact hfstep i (by omega)
    · by_cases h' : i ≤ m
      · have him : i = m := by omega
        subst him
        simp only [if_pos h', if_neg h, hfm]
        have hone : i + 1 - i = 1 := by omega
        rw [hone]
        have hstep := hgstep 0 (by omega)
        rw [hg0] at hstep
        simpa using hstep
      · simp only [if_neg h', if_neg h]
        have hstep := hgstep (i - m) (by omega)
        have hsucc : i + 1 - m = (i - m) + 1 := by omega
        rw [hsucc]
        exact hstep

/-- A path may be split at any point. -/
theorem PathN.split {m n : ℕ} {u w : List Bool} (h : PathN stp E (m + n) u w) :
    ∃ v, PathN stp E m u v ∧ PathN stp E n v w := by
  obtain ⟨f, hf0, hfmn, hflen, hfstep⟩ := h
  refine ⟨f m, ⟨f, hf0, rfl, fun i hi => hflen i (by omega), fun i hi => hfstep i (by omega)⟩,
    ⟨fun i => f (m + i), rfl, by show f (m + n) = w; exact hfmn, fun i hi => hflen _ (by omega), fun i hi => ?_⟩⟩
  have hstep := hfstep (m + i) (by omega)
  rwa [show m + i + 1 = m + (i + 1) by omega] at hstep

/-- With a reflexive step, a node has a path of any length to itself. -/
theorem pathN_refl (hrefl : ∀ y : List Bool, y.length = E → stp y y = true) (d : ℕ)
    {v : List Bool} (hv : v.length = E) : PathN stp E d v v := by
  induction d with
  | zero => exact pathN_zero rfl hv
  | succ d ih => simpa using ih.trans (pathN_one (hrefl v hv) hv hv)

/-- With a reflexive step, a path of `m` steps is a path of any longer length. -/
theorem PathN.mono (hrefl : ∀ y : List Bool, y.length = E → stp y y = true) {m n : ℕ}
    (hmn : m ≤ n) {u v : List Bool} (h : PathN stp E m u v) : PathN stp E n u v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact h.trans (pathN_refl hrefl d h.length_right)

/-! ### The recursion -/

/-- **Savitch's recursion**: `Rec stp E k u v` is "there is a path of `2 ^ k` steps from `u` to
`v`", computed by halving. -/
def Rec (stp : List Bool → List Bool → Bool) (E : ℕ) : ℕ → List Bool → List Bool → Bool
  | 0, u, v => stp u v
  | k + 1, u, v => anyLen E (fun m => Rec stp E k u m && Rec stp E k m v)

@[simp] theorem Rec_zero (u v : List Bool) : Rec stp E 0 u v = stp u v := rfl

theorem Rec_succ (k : ℕ) (u v : List Bool) :
    Rec stp E (k + 1) u v = anyLen E (fun m => Rec stp E k u m && Rec stp E k m v) := rfl

/-- **The recursion decides reachability within `2 ^ k` steps.**  The two nodes are assumed to
have the width of the recursion; nothing is assumed about the one-step test, which may well hold
of strings of other widths — the recursion never looks at those. -/
theorem rec_eq_true_iff :
    ∀ (k : ℕ) (u v : List Bool), u.length = E → v.length = E →
      (Rec stp E k u v = true ↔ PathN stp E (2 ^ k) u v) := by
  intro k
  induction k with
  | zero =>
    intro u v hu hv
    simp only [pow_zero, Rec_zero]
    constructor
    · intro h
      exact pathN_one h hu hv
    · rintro ⟨f, hf0, hf1, -, hstep⟩
      have := hstep 0 (by omega)
      rwa [hf0, show (0 : ℕ) + 1 = 1 from rfl, hf1] at this
  | succ k ih =>
    intro u v hu hv
    rw [Rec_succ, anyLen_eq_true]
    constructor
    · rintro ⟨m, hm, hmv⟩
      rcases Bool.and_eq_true_iff.1 hmv with ⟨h₁, h₂⟩
      have p₁ := (ih u m hu hm).1 h₁
      have p₂ := (ih m v hm hv).1 h₂
      have := p₁.trans p₂
      rwa [show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring] at this
    · intro h
      rw [show (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k by ring] at h
      obtain ⟨m, p₁, p₂⟩ := h.split
      exact ⟨m, p₁.length_right, by
        rw [(ih u m hu p₁.length_right).2 p₁, (ih m v p₁.length_right hv).2 p₂]; rfl⟩

/-! ### Shortening a path -/

/-- **A path through a finite pool of nodes may be shortened** to one that visits no node twice,
hence of length below the size of the pool. -/
theorem exists_pathN_le_of_pathN {S : Finset (List Bool)}
    (hS : ∀ y z : List Bool, y.length = E → z.length = E → stp y z = true → y ∈ S → z ∈ S) :
    ∀ (n : ℕ) {u v : List Bool}, u ∈ S → PathN stp E n u v →
      ∃ m, m < S.card ∧ PathN stp E m u v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v hu hpath
    by_cases hn : n < S.card
    · exact ⟨n, hn, hpath⟩
    · -- pigeonhole: two of the `n + 1` nodes coincide
      obtain ⟨f, hf0, hfn, hflen, hfstep⟩ := hpath
      have hmaps : ∀ i ∈ Finset.range (n + 1), f i ∈ S := by
        intro i hi
        simp only [Finset.mem_range] at hi
        clear hn
        induction i with
        | zero => rwa [hf0]
        | succ j ihj =>
          exact hS _ _ (hflen j (by omega)) (hflen (j + 1) (by omega)) (hfstep j (by omega))
            (ihj (by omega))
      have hcard : S.card < (Finset.range (n + 1)).card := by
        simp only [Finset.card_range]; omega
      obtain ⟨i, hi, j, hj, hij, hfij⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
      simp only [Finset.mem_range] at hi hj
      -- cut the loop between the two equal nodes
      rcases Nat.lt_or_ge i j with hlt | hge
      · have hp₁ : PathN stp E i u (f i) :=
          ⟨f, hf0, rfl, fun l hl => hflen l (by omega), fun l hl => hfstep l (by omega)⟩
        have hp₂ : PathN stp E (n - j) (f j) v :=
          ⟨fun l => f (j + l), rfl, by
              show f (j + (n - j)) = v
              rw [show j + (n - j) = n by omega, hfn],
            fun l hl => hflen _ (by omega), fun l hl => by
              have := hfstep (j + l) (by omega)
              rwa [show j + l + 1 = j + (l + 1) by omega] at this⟩
        have hp : PathN stp E (i + (n - j)) u v := hp₁.trans (hfij ▸ hp₂)
        have hlt' : i + (n - j) < n := by omega
        exact ih _ hlt' hu hp
      · have hjlt : j < i := by omega
        have hp₁ : PathN stp E j u (f j) :=
          ⟨f, hf0, rfl, fun l hl => hflen l (by omega), fun l hl => hfstep l (by omega)⟩
        have hp₂ : PathN stp E (n - i) (f i) v :=
          ⟨fun l => f (i + l), rfl, by
              show f (i + (n - i)) = v
              rw [show i + (n - i) = n by omega, hfn],
            fun l hl => hflen _ (by omega), fun l hl => by
              have := hfstep (i + l) (by omega)
              rwa [show i + l + 1 = i + (l + 1) by omega] at this⟩
        have hp : PathN stp E (j + (n - i)) u v := hp₁.trans (hfij ▸ hp₂)
        have hlt' : j + (n - i) < n := by omega
        exact ih _ hlt' hu hp

/-! ### All strings of one width -/

/-- **The pool of all bit strings of a given length**, as a finite set. -/
def allLenF : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => ((allLenF n).image (fun l => false :: l)) ∪ ((allLenF n).image (fun l => true :: l))

theorem card_allLenF_le : ∀ n : ℕ, (allLenF n).card ≤ 2 ^ n
  | 0 => by simp [allLenF]
  | n + 1 => by
    have h1 : ((allLenF n).image (fun l : List Bool => false :: l)).card ≤ (allLenF n).card :=
      Finset.card_image_le
    have h2 : ((allLenF n).image (fun l : List Bool => true :: l)).card ≤ (allLenF n).card :=
      Finset.card_image_le
    have h3 := Finset.card_union_le ((allLenF n).image (fun l : List Bool => false :: l))
      ((allLenF n).image (fun l : List Bool => true :: l))
    have h4 := card_allLenF_le n
    have h5 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    simp only [allLenF]
    omega

theorem mem_allLenF : ∀ (n : ℕ) (y : List Bool), y.length = n → y ∈ allLenF n
  | 0, y, h => by
    rw [List.length_eq_zero_iff.1 h]
    simp [allLenF]
  | n + 1, y, h => by
    rcases y with _ | ⟨b, t⟩
    · simp at h
    · have ht : t.length = n := by simpa using h
      rcases b with _ | _
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_allLenF n t ht))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_allLenF n t ht))

/-- **A path may be taken shorter than the number of nodes of its width.** -/
theorem exists_pathN_lt_two_pow {n : ℕ} {u v : List Bool} (h : PathN stp E n u v) :
    ∃ m < 2 ^ E, PathN stp E m u v := by
  obtain ⟨m, hm, hp⟩ := exists_pathN_le_of_pathN
    (S := allLenF E) (fun y z _ hz _ _ => mem_allLenF E z hz) n
    (mem_allLenF E u h.length_left) h
  exact ⟨m, lt_of_lt_of_le hm (card_allLenF_le E), hp⟩

end Savitch

end HTN
