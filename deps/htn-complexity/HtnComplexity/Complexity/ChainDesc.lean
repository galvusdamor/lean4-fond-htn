import HtnComplexity.Computable.GridDesc
import HtnComplexity.Computable.Window
/-!
# Renaming the identifiers of a described task network, and chains

A hardness family has to *write down* its instance description in polynomial time, which means
that every numeral occurring in the description has to be computable in Cobham's class from the
input word.  The descriptions of the development name the tasks of a grid by `Nat.pair i j`
(`HtnComplexity/Computable/GridDesc.lean`), and a numeral produced by `Nat.pair` is
quadratic in its arguments: writing one down requires binary multiplication, which the counting
gadget of `ComplexityTheory/Complexity/Counter.lean` does not provide.

Identifiers, however, carry no meaning: solvability of a described problem depends on the
initial task network only up to isomorphism (`HTN.Syn.solvable_congr_tnI_iso`), and renaming the
identifiers of a description injectively is an isomorphism.  This file proves that, in the form
needed for the machine families:

* `HTN.Syn.TnDesc.mapIds` — renaming the identifiers of a description, and
  `HTN.Syn.TnDesc.mapIds_iso`: the renamed description denotes an isomorphic network, provided
  the renaming is injective on the listed identifiers and the description lists no pair or
  label outside them;
* `HTN.Syn.chainOn` — the description of a *chain* of tasks whose `j`-th task is named `g j`;
  `HTN.Syn.gridDesc_pair_nil_eq_chainOn` identifies the grid description of a single row
  (followed by an empty one, which is the shape of the two-stack encoding) with the chain named
  by `Nat.pair 0`, and `HTN.Syn.chainOn_mapIds` says that renaming a chain composes the naming
  function.

Together these let a family name the tasks of a chain by numerals it can actually write
(`HtnCompilability/Complexity/MachineFamily.lean` names them by the number of tasks that
follow, which a recursion on the input word counts down).
-/

namespace HTN

namespace Syn

namespace TnDesc

/-! ### Renaming identifiers -/

/-- **Renaming the identifiers of a described task network** along `f`. -/
def mapIds (f : ℕ → ℕ) (t : TnDesc) : TnDesc :=
  (t.ids.map f, t.ordList.map fun p => (f p.1, f p.2), t.lbl.map fun l => (f l.1, l.2))

@[simp] lemma mapIds_ids (f : ℕ → ℕ) (t : TnDesc) : (t.mapIds f).ids = t.ids.map f := rfl

@[simp] lemma mapIds_ordList (f : ℕ → ℕ) (t : TnDesc) :
    (t.mapIds f).ordList = t.ordList.map fun p => (f p.1, f p.2) := rfl

@[simp] lemma mapIds_lbl (f : ℕ → ℕ) (t : TnDesc) :
    (t.mapIds f).lbl = t.lbl.map fun l => (f l.1, l.2) := rfl

variable {f : ℕ → ℕ} {t : TnDesc}

/-- A step of the renamed listed relation comes from a step of the original one. -/
lemma listRel_mapIds_iff (hord : ∀ p ∈ t.ordList, p.1 ∈ t.ids ∧ p.2 ∈ t.ids)
    (hinj : Set.InjOn f {x | x ∈ t.ids}) {a b : ℕ} (ha : a ∈ t.ids) (hb : b ∈ t.ids) :
    (t.mapIds f).listRel (f a) (f b) ↔ t.listRel a b := by
  constructor
  · intro h
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h
    obtain ⟨hp1, hp2⟩ := hord p hp
    have h1 : f p.1 = f a := congrArg Prod.fst hpe
    have h2 : f p.2 = f b := congrArg Prod.snd hpe
    have e1 : p.1 = a := hinj hp1 ha h1
    have e2 : p.2 = b := hinj hp2 hb h2
    have hpe' : p = (a, b) := by
      obtain ⟨x, y⟩ := p
      simp_all
    show (a, b) ∈ t.ordList
    rw [← hpe']
    exact hp
  · intro h
    exact List.mem_map.2 ⟨(a, b), h, rfl⟩

/-- Every step of the renamed listed relation joins images of listed identifiers. -/
lemma exists_of_listRel_mapIds (hord : ∀ p ∈ t.ordList, p.1 ∈ t.ids ∧ p.2 ∈ t.ids) {x y : ℕ}
    (h : (t.mapIds f).listRel x y) :
    ∃ a b, a ∈ t.ids ∧ b ∈ t.ids ∧ x = f a ∧ y = f b ∧ t.listRel a b := by
  obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h
  obtain ⟨hp1, hp2⟩ := hord p hp
  refine ⟨p.1, p.2, hp1, hp2, (congrArg Prod.fst hpe).symm, (congrArg Prod.snd hpe).symm, ?_⟩
  show (p.1, p.2) ∈ t.ordList
  simpa using hp

private lemma preOrd_mapIds_of (hord : ∀ p ∈ t.ordList, p.1 ∈ t.ids ∧ p.2 ∈ t.ids)
    (hinj : Set.InjOn f {x | x ∈ t.ids}) :
    ∀ x y : ℕ, Relation.TransGen (t.mapIds f).listRel x y →
      ∀ b, b ∈ t.ids → y = f b → ∃ a, a ∈ t.ids ∧ x = f a ∧ t.preOrd a b := by
  intro x y h
  induction h with
  | single hxy =>
    intro b hb hyb
    obtain ⟨a, b', ha, hb', hxa, hyb', hrel⟩ := exists_of_listRel_mapIds hord hxy
    have : b' = b := hinj hb' hb (by rw [← hyb', hyb])
    subst this
    exact ⟨a, ha, hxa, Relation.TransGen.single hrel⟩
  | tail hxc hcy ih =>
    intro b hb hyb
    obtain ⟨c0, b', hc0, hb', hce, hyb', hrel⟩ := exists_of_listRel_mapIds hord hcy
    have hbb : b' = b := hinj hb' hb (by rw [← hyb', hyb])
    subst hbb
    obtain ⟨a, ha, hxa, hpre⟩ := ih c0 hc0 hce
    exact ⟨a, ha, hxa, hpre.tail hrel⟩

/-- The transitive closure is preserved by any renaming. -/
lemma preOrd_mapIds_of_preOrd {a b : ℕ} (h : t.preOrd a b) : (t.mapIds f).preOrd (f a) (f b) := by
  have step : ∀ x y : ℕ, t.listRel x y → (t.mapIds f).listRel (f x) (f y) := by
    intro x y hxy
    show (f x, f y) ∈ t.ordList.map fun p => (f p.1, f p.2)
    exact List.mem_map.2 ⟨(x, y), hxy, rfl⟩
  induction h with
  | single hab => exact Relation.TransGen.single (step _ _ hab)
  | tail _ hcb ih => exact Relation.TransGen.tail ih (step _ _ hcb)

/-- The transitive closure transports along an injective renaming. -/
lemma preOrd_mapIds_iff (hord : ∀ p ∈ t.ordList, p.1 ∈ t.ids ∧ p.2 ∈ t.ids)
    (hinj : Set.InjOn f {x | x ∈ t.ids}) {a b : ℕ} (ha : a ∈ t.ids) (hb : b ∈ t.ids) :
    (t.mapIds f).preOrd (f a) (f b) ↔ t.preOrd a b := by
  constructor
  · intro h
    obtain ⟨a', ha', hfa, hpre⟩ := preOrd_mapIds_of hord hinj _ _ h b hb rfl
    have : a' = a := hinj ha' ha hfa.symm
    rwa [this] at hpre
  · exact preOrd_mapIds_of_preOrd

/-- The label of a renamed description at a renamed identifier. -/
lemma label_mapIds (hlbl : ∀ l ∈ t.lbl, l.1 ∈ t.ids) (hinj : Set.InjOn f {x | x ∈ t.ids})
    {a : ℕ} (ha : a ∈ t.ids) : (t.mapIds f).label (f a) = t.label a := by
  have hlookup : ∀ l : List (ℕ × Bool × ℕ), (∀ e ∈ l, e.1 ∈ t.ids) →
      (l.map fun e => (f e.1, e.2)).lookup (f a) = l.lookup a := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p ps ih =>
      intro hmem
      have hp : p.1 ∈ t.ids := hmem p (by simp)
      have ih' := ih fun e he => hmem e (by simp [he])
      by_cases h : p.1 = a
      · obtain ⟨k, v⟩ := p
        simp only at h
        subst h
        simp
      · have hne : ¬ (f a = f p.1) := fun he => h (hinj hp ha he.symm)
        obtain ⟨k, v⟩ := p
        simp only at h hne
        rw [List.map_cons, List.lookup_cons, List.lookup_cons]
        rw [show ((f a == f k) = false) by simpa using hne,
          show ((a == k) = false) by simpa using fun hh => h hh.symm]
        exact ih'
  simp only [label, mapIds_lbl, hlookup t.lbl hlbl]

/-- **A description and its injective renaming denote isomorphic task networks.** -/
theorem mapIds_iso (hord : ∀ p ∈ t.ordList, p.1 ∈ t.ids ∧ p.2 ∈ t.ids)
    (hlbl : ∀ l ∈ t.lbl, l.1 ∈ t.ids) (hinj : Set.InjOn f {x | x ∈ t.ids}) :
    t.toTaskNetwork.Iso (t.mapIds f).toTaskNetwork := by
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ t.ids := by simpa using hx
    show f x ∈ ((t.mapIds f).ids.toFinset : Set ℕ)
    simpa using List.mem_map.2 ⟨x, hx', rfl⟩
  · intro x hx y hy hxy
    exact hinj (by simpa using hx) (by simpa using hy) hxy
  · intro y hy
    have hy' : y ∈ (t.mapIds f).ids := by simpa using hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
    exact ⟨x, by simpa using hx, rfl⟩
  · intro a ha b hb
    have ha : a ∈ t.ids := by simpa using ha
    have hb : b ∈ t.ids := by simpa using hb
    show (t.ordOf a b) ↔ ((t.mapIds f).ordOf (f a) (f b))
    simp only [ordOf, mapIds_ids]
    constructor
    · rintro ⟨-, -, h1, h2⟩
      exact ⟨List.mem_map.2 ⟨a, ha, rfl⟩, List.mem_map.2 ⟨b, hb, rfl⟩,
        (preOrd_mapIds_iff hord hinj ha hb).2 h1,
        fun h => h2 ((preOrd_mapIds_iff hord hinj hb ha).1 h)⟩
    · rintro ⟨-, -, h1, h2⟩
      exact ⟨ha, hb, (preOrd_mapIds_iff hord hinj ha hb).1 h1,
        fun h => h2 ((preOrd_mapIds_iff hord hinj hb ha).2 h)⟩
  · intro a ha
    have ha : a ∈ t.ids := by simpa using ha
    exact (label_mapIds hlbl hinj ha).symm

end TnDesc

/-! ### Chains -/

/-- **The description of a chain of tasks** whose `j`-th task is named `g j`: the identifiers are
the values of `g` on `0, …, |row| - 1`, the ordering pairs are the consecutive ones, and the
`j`-th task carries the `j`-th label of `row`. -/
def chainOn (g : ℕ → ℕ) (row : List (Bool × ℕ)) : TnDesc :=
  ((List.range row.length).map g,
   (List.range (row.length - 1)).map fun j => (g j, g (j + 1)),
   (List.range row.length).map fun j => (g j, row.getD j (false, 0)))

@[simp] lemma chainOn_ids (g : ℕ → ℕ) (row : List (Bool × ℕ)) :
    (chainOn g row).ids = (List.range row.length).map g := rfl

@[simp] lemma chainOn_ordList (g : ℕ → ℕ) (row : List (Bool × ℕ)) :
    (chainOn g row).ordList = (List.range (row.length - 1)).map fun j => (g j, g (j + 1)) := rfl

@[simp] lemma chainOn_lbl (g : ℕ → ℕ) (row : List (Bool × ℕ)) :
    (chainOn g row).lbl = (List.range row.length).map fun j => (g j, row.getD j (false, 0)) := rfl

/-- Renaming a chain composes the naming function. -/
theorem chainOn_mapIds (f g : ℕ → ℕ) (row : List (Bool × ℕ)) :
    (chainOn g row).mapIds f = chainOn (f ∘ g) row := by
  simp [chainOn, TnDesc.mapIds, TnDesc.ids, TnDesc.ordList, TnDesc.lbl, List.map_map,
    Function.comp_def]

/-- The naming function of a chain matters only on the positions of the row. -/
theorem chainOn_congr {g g' : ℕ → ℕ} {row : List (Bool × ℕ)}
    (h : ∀ j < row.length, g j = g' j) : chainOn g row = chainOn g' row := by
  have h1 : (List.range row.length).map g = (List.range row.length).map g' :=
    List.map_congr_left fun j hj => h j (List.mem_range.1 hj)
  have h2 : ((List.range (row.length - 1)).map fun j => (g j, g (j + 1))) =
      (List.range (row.length - 1)).map fun j => (g' j, g' (j + 1)) := by
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.1 hj
    rw [h j (by omega), h (j + 1) (by omega)]
  have h3 : ((List.range row.length).map fun j => (g j, row.getD j (false, 0))) =
      (List.range row.length).map fun j => (g' j, row.getD j (false, 0)) :=
    List.map_congr_left fun j hj => by rw [h j (List.mem_range.1 hj)]
  simp only [chainOn, h1, h2, h3]

/-- The pairs of a chain stay inside its identifiers. -/
theorem chainOn_ordList_mem {g : ℕ → ℕ} {row : List (Bool × ℕ)} :
    ∀ p ∈ (chainOn g row).ordList, p.1 ∈ (chainOn g row).ids ∧ p.2 ∈ (chainOn g row).ids := by
  intro p hp
  simp only [chainOn_ordList, List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  exact ⟨List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩,
    List.mem_map.2 ⟨j + 1, List.mem_range.2 (by omega), rfl⟩⟩

/-- The labels of a chain stay inside its identifiers. -/
theorem chainOn_lbl_mem {g : ℕ → ℕ} {row : List (Bool × ℕ)} :
    ∀ l ∈ (chainOn g row).lbl, l.1 ∈ (chainOn g row).ids := by
  intro l hl
  simp only [chainOn_lbl, List.mem_map, List.mem_range] at hl
  obtain ⟨j, hj, rfl⟩ := hl
  exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

/-! ### A chain preceded by an isolated task

The initial task network of the two-stack encoding has one chain per stack.  A hardness family
that puts the input word on one stack and a fixed bottom marker on the other therefore needs a
description of *one isolated task together with a chain*. -/

/-- **The description of an isolated task named `h`, carrying the label `t`, together with a
chain whose `j`-th task is named `g j`.**  The two are unordered relative to each other. -/
def chainWith (h : ℕ) (t : Bool × ℕ) (g : ℕ → ℕ) (row : List (Bool × ℕ)) : TnDesc :=
  (h :: (List.range row.length).map g,
   (List.range (row.length - 1)).map fun j => (g j, g (j + 1)),
   (h, t) :: (List.range row.length).map fun j => (g j, row.getD j (false, 0)))

@[simp] lemma chainWith_ids (h : ℕ) (t : Bool × ℕ) (g : ℕ → ℕ) (row : List (Bool × ℕ)) :
    (chainWith h t g row).ids = h :: (List.range row.length).map g := rfl

@[simp] lemma chainWith_ordList (h : ℕ) (t : Bool × ℕ) (g : ℕ → ℕ) (row : List (Bool × ℕ)) :
    (chainWith h t g row).ordList =
      (List.range (row.length - 1)).map fun j => (g j, g (j + 1)) := rfl

@[simp] lemma chainWith_lbl (h : ℕ) (t : Bool × ℕ) (g : ℕ → ℕ) (row : List (Bool × ℕ)) :
    (chainWith h t g row).lbl =
      (h, t) :: (List.range row.length).map fun j => (g j, row.getD j (false, 0)) := rfl

theorem chainWith_mapIds (f : ℕ → ℕ) (h : ℕ) (t : Bool × ℕ) (g : ℕ → ℕ)
    (row : List (Bool × ℕ)) :
    (chainWith h t g row).mapIds f = chainWith (f h) t (f ∘ g) row := by
  simp [chainWith, TnDesc.mapIds, TnDesc.ids, TnDesc.ordList, TnDesc.lbl, List.map_map,
    Function.comp_def]

theorem chainWith_congr {g g' : ℕ → ℕ} {h : ℕ} {t : Bool × ℕ} {row : List (Bool × ℕ)}
    (hg : ∀ j < row.length, g j = g' j) : chainWith h t g row = chainWith h t g' row := by
  have h1 : (List.range row.length).map g = (List.range row.length).map g' :=
    List.map_congr_left fun j hj => hg j (List.mem_range.1 hj)
  have h2 : ((List.range (row.length - 1)).map fun j => (g j, g (j + 1))) =
      (List.range (row.length - 1)).map fun j => (g' j, g' (j + 1)) := by
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.1 hj
    rw [hg j (by omega), hg (j + 1) (by omega)]
  have h3 : ((List.range row.length).map fun j => (g j, row.getD j (false, 0))) =
      (List.range row.length).map fun j => (g' j, row.getD j (false, 0)) :=
    List.map_congr_left fun j hj => by rw [hg j (List.mem_range.1 hj)]
  simp only [chainWith, h1, h2, h3]

theorem chainWith_ordList_mem {g : ℕ → ℕ} {h : ℕ} {t : Bool × ℕ} {row : List (Bool × ℕ)} :
    ∀ p ∈ (chainWith h t g row).ordList,
      p.1 ∈ (chainWith h t g row).ids ∧ p.2 ∈ (chainWith h t g row).ids := by
  intro p hp
  simp only [chainWith_ordList, List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  refine ⟨List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩),
    List.mem_cons_of_mem _ (List.mem_map.2 ⟨j + 1, List.mem_range.2 (by omega), rfl⟩)⟩

theorem chainWith_lbl_mem {g : ℕ → ℕ} {h : ℕ} {t : Bool × ℕ} {row : List (Bool × ℕ)} :
    ∀ l ∈ (chainWith h t g row).lbl, l.1 ∈ (chainWith h t g row).ids := by
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · exact List.mem_cons_self
  · simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

/-- **The grid description of a single task followed by a row is that shape**, with the isolated
task named `Nat.pair 0 0` and the chain named by `Nat.pair 1`. -/
theorem gridDesc_single_cons_eq_chainWith (t : Bool × ℕ) (row : List (Bool × ℕ)) :
    gridDesc [[t], row] = chainWith (Nat.pair 0 0) t (Nat.pair 1) row := by
  have h0 : gridRow [[t], row] 0 = [t] := rfl
  have h1 : gridRow [[t], row] 1 = row := rfl
  simp [gridDesc, cellIds, cellOrd, cellLbl, chainWith, h0, h1, List.range_succ]

/-- **The grid description of a single row, followed by an empty row, is the chain named by
`Nat.pair 0`** — an empty row contributes no identifier, no pair and no label.  This is the
shape of the initial task network of the two-stack encoding with an empty second stack. -/
theorem gridDesc_pair_nil_eq_chainOn (row : List (Bool × ℕ)) :
    gridDesc [row, []] = chainOn (Nat.pair 0) row := by
  have h0 : gridRow [row, []] 0 = row := rfl
  have h1 : gridRow [row, []] 1 = [] := rfl
  simp [gridDesc, cellIds, cellOrd, cellLbl, chainOn, h0, h1, List.range_succ]

end Syn

end HTN
