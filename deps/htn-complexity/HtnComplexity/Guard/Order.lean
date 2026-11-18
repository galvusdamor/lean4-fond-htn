import HtnPlanning.Core.TaskNetwork
import Mathlib.Tactic

/-!
# Extending a linearization to a network with extra tasks

The method-guard construction (see `HtnComplexity/Guard/Insert.lean`) turns a task network
`tn` into a network `tng` that carries, besides the tasks of `tn`, a set `K` of extra primitive
*guard* tasks.  On the tasks of `tn` the two networks have the same ordering; the guard tasks
may be ordered with respect to the old ones in any way the derivation produced.

To read a plan of `tn` as a plan of `tng` one needs the combinatorial half of the argument:

> `HTN.GuardTask.exists_linearization_ext` — every linearization `l` of `tn` extends to a
> linearization `lg` of `tng` whose restriction to the tasks of `tn` is `l` again.

The proof is a *scheduling* argument with an explicit key rather than a topological sort.  Each
task gets a natural number and the extension is the list of tasks sorted by it:

* a task `x` of `tn` gets the key `(2 · i + 1) · M`, where `i` is its position in `l` and
  `M = |K| + 1`;
* a guard task `k` gets `2 · p(k) · M + c(k)`, where `p(k)` is one more than the largest position
  in `l` of a `tng`-predecessor of `k` that belongs to `tn` (and `0` if there is none) and `c(k)`
  counts the guard tasks below `k`.

The two ingredients of the correctness of the key are that a guard task sits strictly between
the old tasks it must sit between — which is `HTN.GuardTask.pos_le_of_ord`, itself a consequence
of transitivity of the ordering — and that `c` breaks ties between guard tasks that are
comparable to each other.
-/

namespace HTN

namespace GuardTask

universe u v w x

variable {I : Type x} {A : Type v} {C : Type w} [DecidableEq I]

/-! ### Positions in a linearization -/

/-- Two members of a list with the same index are equal. -/
theorem idxOf_inj {m : List I} {x y : I} (hx : x ∈ m) (hy : y ∈ m)
    (h : m.idxOf x = m.idxOf y) : x = y := by
  have h1 : m[m.idxOf x]'(List.idxOf_lt_length_of_mem hx) = x := List.getElem_idxOf _
  have h2 : m[m.idxOf y]'(List.idxOf_lt_length_of_mem hy) = y := List.getElem_idxOf _
  rw [← h1, ← h2]
  simp only [h]

/-- **The order of a network is the order of the positions of any linearization.** -/
theorem idx_lt_of_ord {tn : TaskNetwork I A C} {l : List I} (hwf : tn.WF)
    (hlin : tn.IsLinearization l)
    {x y : I} (hx : x ∈ tn.T) (hy : y ∈ tn.T) (hord : tn.ord x y) : l.idxOf x < l.idxOf y := by
  obtain ⟨hnodup, hmem, hpair⟩ := hlin
  have hxl : x ∈ l := (hmem x).2 hx
  have hyl : y ∈ l := (hmem y).2 hy
  have hxlt : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hxl
  have hylt : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hyl
  have hgx : l[l.idxOf x]'hxlt = x := List.getElem_idxOf _
  have hgy : l[l.idxOf y]'hylt = y := List.getElem_idxOf _
  have hforbid : ∀ i j : ℕ, ∀ hi : i < l.length, ∀ hj : j < l.length, i < j →
      ¬ tn.ord (l[j]'hj) (l[i]'hi) := by
    intro i j hi hj hij
    rw [List.pairwise_iff_getElem] at hpair
    exact hpair i j hi hj hij
  rcases lt_trichotomy (l.idxOf x) (l.idxOf y) with h | h | h
  · exact h
  · exact absurd (idxOf_inj hxl hyl h ▸ hord) (hwf.irrefl x)
  · exact absurd hord (by
      have := hforbid (l.idxOf y) (l.idxOf x) hylt hxlt h
      rwa [hgx, hgy] at this)

/-! ### The key -/

open Classical in
/-- The largest position in `l` of a `tn`-task below `x`, plus one; `0` if there is none. -/
noncomputable def posKey (tn tng : TaskNetwork I A C) (l : List I) (x : I) : ℕ :=
  tn.T.sup fun y => if tng.ord y x then l.idxOf y + 1 else 0

open Classical in
/-- The number of guard tasks below `x`; it breaks the ties between comparable guard tasks. -/
noncomputable def depthKey (tng : TaskNetwork I A C) (K : Finset I) (x : I) : ℕ :=
  (K.filter fun y => tng.ord y x).card

open Classical in
/-- **The scheduling key.**  Old tasks are put at the odd multiples of `M = |K| + 1`, guard
tasks into the gaps below the old task they have to precede. -/
noncomputable def schedKey (tn tng : TaskNetwork I A C) (l : List I) (K : Finset I) (x : I) :
    ℕ :=
  if x ∈ tn.T then (2 * l.idxOf x + 1) * (K.card + 1)
  else 2 * posKey tn tng l x * (K.card + 1) + depthKey tng K x

section

variable {tn tng : TaskNetwork I A C} {K : Finset I} {l : List I}

/-- A `tn`-task below `x` bounds the position key of `x` from below. -/
theorem le_posKey {y x : I} (hy : y ∈ tn.T) (h : tng.ord y x) :
    l.idxOf y + 1 ≤ posKey tn tng l x := by
  classical
  have := Finset.le_sup (f := fun y => if tng.ord y x then l.idxOf y + 1 else 0) hy
  simpa [posKey, h] using this

/-- **A guard task fits below the old tasks above it**: if `x` precedes the `tn`-task `z`, its
position key is at most the position of `z`. -/
theorem posKey_le_of_ord (hwf : tn.WF) (hwfg : tng.WF) (hlin : tn.IsLinearization l)
    (hord : ∀ a ∈ tn.T, ∀ b ∈ tn.T, tng.ord a b → tn.ord a b)
    {x z : I} (hz : z ∈ tn.T) (h : tng.ord x z) : posKey tn tng l x ≤ l.idxOf z := by
  classical
  refine Finset.sup_le ?_
  intro y hy
  by_cases hyx : tng.ord y x
  · have hyz : tng.ord y z := hwfg.trans hyx h
    have : tn.ord y z := hord y hy z hz hyz
    have := idx_lt_of_ord hwf hlin hy hz this
    simp [hyx]
    omega
  · simp [hyx]

/-- The position key is monotone along the ordering. -/
theorem posKey_mono (hwfg : tng.WF) {x y : I} (h : tng.ord x y) :
    posKey tn tng l x ≤ posKey tn tng l y := by
  classical
  refine Finset.sup_le ?_
  intro z hz
  by_cases hzx : tng.ord z x
  · have hzy : tng.ord z y := hwfg.trans hzx h
    have := le_posKey (tng := tng) (l := l) hz hzy
    simp [hzx]
    omega
  · simp [hzx]

omit [DecidableEq I] in
/-- The tie-breaking key is strictly monotone along the ordering of the guard tasks. -/
theorem depthKey_lt (hwfg : tng.WF) {x y : I} (hx : x ∈ K) (h : tng.ord x y) :
    depthKey tng K x < depthKey tng K y := by
  classical
  refine Finset.card_lt_card ?_
  constructor
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hwfg.trans hz.2 h⟩
  · intro hsub
    have hmem : x ∈ K.filter fun z => tng.ord z y := by
      simp [hx, h]
    have := hsub hmem
    simp only [Finset.mem_filter] at this
    exact hwfg.irrefl x this.2

omit [DecidableEq I] in
/-- The tie-breaking key is bounded by the number of guard tasks. -/
theorem depthKey_le_card (x : I) : depthKey tng K x ≤ K.card := by
  classical
  exact Finset.card_filter_le _ _

/-- **The key is strictly monotone along the ordering.** -/
theorem schedKey_lt_of_ord (hwf : tn.WF) (hwfg : tng.WF) (hlin : tn.IsLinearization l)
    (hT : ∀ z, z ∈ tng.T ↔ (z ∈ tn.T ∨ z ∈ K))
    (hordr : ∀ a ∈ tn.T, ∀ b ∈ tn.T, tng.ord a b → tn.ord a b)
    {x y : I} (h : tng.ord x y) :
    schedKey tn tng l K x < schedKey tn tng l K y := by
  classical
  have hxT : x ∈ tng.T := hwfg.mem_left h
  have hyT : y ∈ tng.T := hwfg.mem_right h
  by_cases hx : x ∈ tn.T <;> by_cases hy : y ∈ tn.T
  · have hlt : l.idxOf x < l.idxOf y := idx_lt_of_ord hwf hlin hx hy (hordr x hx y hy h)
    simp only [schedKey, if_pos hx, if_pos hy]
    have : 2 * l.idxOf x + 1 < 2 * l.idxOf y + 1 := by omega
    exact Nat.mul_lt_mul_of_lt_of_le this (le_refl _) (Nat.succ_pos _)
  · -- `x` old, `y` a guard task
    have hpos : l.idxOf x + 1 ≤ posKey tn tng l y := le_posKey hx h
    simp only [schedKey, if_pos hx, if_neg hy]
    have h1 : (2 * l.idxOf x + 1) * (K.card + 1) < (2 * (l.idxOf x + 1)) * (K.card + 1) := by
      have : 2 * l.idxOf x + 1 < 2 * (l.idxOf x + 1) := by omega
      exact Nat.mul_lt_mul_of_lt_of_le this (le_refl _) (Nat.succ_pos _)
    have h2 : (2 * (l.idxOf x + 1)) * (K.card + 1) ≤ 2 * posKey tn tng l y * (K.card + 1) := by
      have : 2 * (l.idxOf x + 1) ≤ 2 * posKey tn tng l y := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  · -- `x` a guard task, `y` old
    have hpos : posKey tn tng l x ≤ l.idxOf y := posKey_le_of_ord hwf hwfg hlin hordr hy h
    have hd : depthKey tng K x ≤ K.card := depthKey_le_card x
    simp only [schedKey, if_neg hx, if_pos hy]
    have h1 : 2 * posKey tn tng l x * (K.card + 1) ≤ 2 * l.idxOf y * (K.card + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 * l.idxOf y + 1) * (K.card + 1)
        = 2 * l.idxOf y * (K.card + 1) + (K.card + 1) := by ring
    omega
  · -- both guard tasks
    have hxK : x ∈ K := by
      rcases (hT x).1 hxT with h' | h'
      · exact absurd h' hx
      · exact h'
    have hp : posKey tn tng l x ≤ posKey tn tng l y := posKey_mono hwfg h
    have hd : depthKey tng K x < depthKey tng K y := depthKey_lt hwfg hxK h
    simp only [schedKey, if_neg hx, if_neg hy]
    have h1 : 2 * posKey tn tng l x * (K.card + 1) ≤ 2 * posKey tn tng l y * (K.card + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- Two distinct old tasks have distinct keys. -/
theorem schedKey_inj_on {x y : I} (hlin : tn.IsLinearization l) (hx : x ∈ tn.T) (hy : y ∈ tn.T)
    (hne : x ≠ y) : schedKey tn tng l K x ≠ schedKey tn tng l K y := by
  classical
  have hxl : x ∈ l := (hlin.2.1 x).2 hx
  have hyl : y ∈ l := (hlin.2.1 y).2 hy
  have hidx : l.idxOf x ≠ l.idxOf y := by
    intro hcon
    exact hne (idxOf_inj hxl hyl hcon)
  simp only [schedKey, if_pos hx, if_pos hy]
  intro hcon
  have := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos K.card) hcon
  omega

end

/-! ### The extension theorem -/

/-- **Every linearization of the old network extends to one of the network with guard tasks.**
The extension restricts to the given linearization on the old tasks. -/
theorem exists_linearization_ext {tn tng : TaskNetwork I A C} {K : Finset I} {l : List I}
    (hwf : tn.WF) (hwfg : tng.WF) (hT : ∀ z, z ∈ tng.T ↔ (z ∈ tn.T ∨ z ∈ K))
    (hordr : ∀ a ∈ tn.T, ∀ b ∈ tn.T, tng.ord a b → tn.ord a b)
    (hlin : tn.IsLinearization l) :
    ∃ lg : List I, tng.IsLinearization lg ∧ lg.filter (fun z => decide (z ∈ tn.T)) = l := by
  classical
  set key : I → ℕ := schedKey tn tng l K with hkey
  set r : I → I → Prop := fun a b => key a ≤ key b with hr
  haveI : DecidableRel r := fun a b => Nat.decLe _ _
  haveI : Std.Total r := ⟨fun a b => le_total (key a) (key b)⟩
  haveI : IsTrans I r := ⟨fun a b c hab hbc => le_trans hab hbc⟩
  set lg : List I := List.insertionSort r tng.T.toList with hlg
  have hperm : lg.Perm tng.T.toList := List.perm_insertionSort r _
  have hnodup : lg.Nodup := hperm.nodup_iff.2 (Finset.nodup_toList _)
  have hmem : ∀ z, z ∈ lg ↔ z ∈ tng.T := by
    intro z
    rw [hperm.mem_iff, Finset.mem_toList]
  have hsorted : lg.Pairwise r := List.pairwise_insertionSort r _
  have hlinlg : tng.IsLinearization lg := by
    refine ⟨hnodup, hmem, ?_⟩
    refine List.Pairwise.imp_of_mem ?_ hsorted
    intro a b ha hb hab hcon
    have hlt : key b < key a := schedKey_lt_of_ord hwf hwfg hlin hT hordr hcon
    omega
  refine ⟨lg, hlinlg, ?_⟩
  -- the restriction to the old tasks is `l`
  set lf : List I := lg.filter (fun z => decide (z ∈ tn.T)) with hlf
  have hmemf : ∀ z, z ∈ lf ↔ z ∈ l := by
    intro z
    rw [hlf, List.mem_filter]
    constructor
    · rintro ⟨-, hz⟩
      exact (hlin.2.1 z).2 (by simpa using hz)
    · intro hz
      have hzT : z ∈ tn.T := (hlin.2.1 z).1 hz
      exact ⟨(hmem z).2 ((hT z).2 (Or.inl hzT)), by simpa using hzT⟩
  have hnodupf : lf.Nodup := hnodup.filter _
  have hpermf : lf.Perm l := (List.perm_ext_iff_of_nodup hnodupf hlin.1).2 hmemf
  have hmemT : ∀ z ∈ lf, z ∈ tn.T := by
    intro z hz
    rw [hlf, List.mem_filter] at hz
    simpa using hz.2
  -- both lists are sorted strictly by the key
  have hpairf : lf.Pairwise (fun a b => key a < key b) := by
    have hsub : lf.Pairwise r := by
      refine List.Pairwise.sublist ?_ hsorted
      exact List.filter_sublist
    have hcomb : lf.Pairwise (fun a b => r a b ∧ a ≠ b) := List.Pairwise.and hsub hnodupf
    refine List.Pairwise.imp_of_mem ?_ hcomb
    rintro a b ha hb ⟨hab, hne⟩
    have hne' : key a ≠ key b := schedKey_inj_on (tng := tng) (K := K) hlin (hmemT a ha) (hmemT b hb) hne
    have : key a ≤ key b := hab
    omega
  have hpairl : l.Pairwise (fun a b => key a < key b) := by
    have hidx : l.Pairwise (fun a b => l.idxOf a < l.idxOf b) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.Nodup.idxOf_getElem hlin.1, List.Nodup.idxOf_getElem hlin.1]
      exact hij
    refine List.Pairwise.imp_of_mem ?_ hidx
    intro a b ha hb hab
    have haT : a ∈ tn.T := (hlin.2.1 a).1 ha
    have hbT : b ∈ tn.T := (hlin.2.1 b).1 hb
    simp only [hkey, schedKey, if_pos haT, if_pos hbT]
    have : 2 * l.idxOf a + 1 < 2 * l.idxOf b + 1 := by omega
    exact Nat.mul_lt_mul_of_lt_of_le this (le_refl _) (Nat.succ_pos _)
  refine List.Perm.eq_of_pairwise ?_ hpairf hpairl hpermf
  intro a b _ _ hab hba
  omega

end GuardTask

end HTN
