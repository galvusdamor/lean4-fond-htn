import HtnComplexity.Computable.AcTasks
/-!
# The action model of the compiled acyclic domain, as a description

`HTN.ToAc.actionModel` gives the precondition, add and delete list of each compiled action as
*sets*.  A description lists them, so this file provides

* `HTN.Syn.Ac.actInfo` — the three lists of a compiled action, computed from its **number** by
  a case distinction on its tag (`HTN.Syn.Ac.atag`), exactly as `HTN.Syn.Ac.bodyNum` computes
  the bodies of a compound task;
* `HTN.Syn.Ac.allActs` — the compiled actions a description lists.  It contains *every*
  compiled action (`HTN.Syn.Ac.encAct_mem_allActs`), as soon as the three lists of the source
  cover the source signature;
* `HTN.Syn.Ac.actInfo_prec`, `…_add`, `…_del` — the agreement of `actInfo` with
  `HTN.ToAc.prec`, `HTN.ToAc.add`, `HTN.ToAc.del`.

A description looks an action up with `List.lookup`, which returns the *first* entry.  The
action list is therefore built as `allActs.map fun x => (x, actInfo x)`, for which the lookup
is correct without any distinctness of the keys (`HTN.Syn.Ac.lookup_map_self`).
-/

namespace HTN

namespace Syn

namespace Ac

/-! ### Looking up a list of the form `l.map fun x => (x, F x)` -/

lemma lookup_map_self {β : Type} (F : ℕ → β) (l : List ℕ) {k : ℕ} (hk : k ∈ l) :
    (l.map fun x => (x, F x)).lookup k = some (F k) := by
  induction l with
  | nil => simp at hk
  | cons x xs ih =>
    rw [List.map_cons, List.lookup_cons]
    by_cases h : k = x
    · subst h; simp
    · rw [show (k == x) = false by simp [h]]
      exact ih (by rcases List.mem_cons.1 hk with rfl | h' <;> [exact absurd rfl h; exact h'])

/-! ### The tag and the payload of a compiled action number -/

/-- The constructor tag of a compiled action number. -/
def atag (x : ℕ) : ℕ := x % 13

/-- The argument of a compiled action number. -/
def apayload (x : ℕ) : ℕ := x / 13

private lemma atag_payload (x r : ℕ) (h : r < 13) :
    atag (13 * x + r) = r ∧ apayload (13 * x + r) = x := by
  refine ⟨by simp [atag, Nat.mod_eq_of_lt h], ?_⟩
  rw [apayload, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt h, Nat.add_zero]

@[simp] lemma atag_aSetV (v i : ℕ) : atag (aSetV v i) = 0 := by
  simpa using (atag_payload (5 * v + i) 0 (by norm_num)).1
@[simp] lemma apayload_aSetV (v i : ℕ) : apayload (aSetV v i) = 5 * v + i := by
  simpa using (atag_payload (5 * v + i) 0 (by norm_num)).2
@[simp] lemma atag_aDelV (v i : ℕ) : atag (aDelV v i) = 1 := (atag_payload _ 1 (by norm_num)).1
@[simp] lemma apayload_aDelV (v i : ℕ) : apayload (aDelV v i) = 5 * v + i :=
  (atag_payload _ 1 (by norm_num)).2
@[simp] lemma atag_aPrePV (v i j : ℕ) : atag (aPrePV v i j) = 2 :=
  (atag_payload _ 2 (by norm_num)).1
@[simp] lemma apayload_aPrePV (v i j : ℕ) : apayload (aPrePV v i j) = 25 * v + 5 * i + j :=
  (atag_payload _ 2 (by norm_num)).2
@[simp] lemma atag_aPreNV (v i j : ℕ) : atag (aPreNV v i j) = 3 :=
  (atag_payload _ 3 (by norm_num)).1
@[simp] lemma apayload_aPreNV (v i j : ℕ) : apayload (aPreNV v i j) = 25 * v + 5 * i + j :=
  (atag_payload _ 3 (by norm_num)).2
@[simp] lemma atag_aSetC (t : ℕ) : atag (aSetC t) = 4 := (atag_payload _ 4 (by norm_num)).1
@[simp] lemma apayload_aSetC (t : ℕ) : apayload (aSetC t) = t :=
  (atag_payload _ 4 (by norm_num)).2
@[simp] lemma atag_aPreC (t : ℕ) : atag (aPreC t) = 5 := (atag_payload _ 5 (by norm_num)).1
@[simp] lemma apayload_aPreC (t : ℕ) : apayload (aPreC t) = t :=
  (atag_payload _ 5 (by norm_num)).2
@[simp] lemma atag_aLock : atag aLock = 6 := rfl
@[simp] lemma atag_aUnlock : atag aUnlock = 7 := rfl
@[simp] lemma atag_aAsk (x : ℕ) : atag (aAsk x) = 8 := (atag_payload _ 8 (by norm_num)).1
@[simp] lemma apayload_aAsk (x : ℕ) : apayload (aAsk x) = x :=
  (atag_payload _ 8 (by norm_num)).2
@[simp] lemma atag_aAccept (x : ℕ) : atag (aAccept x) = 9 := (atag_payload _ 9 (by norm_num)).1
@[simp] lemma apayload_aAccept (x : ℕ) : apayload (aAccept x) = x :=
  (atag_payload _ 9 (by norm_num)).2
@[simp] lemma atag_aDone (x : ℕ) : atag (aDone x) = 10 := (atag_payload _ 10 (by norm_num)).1
@[simp] lemma apayload_aDone (x : ℕ) : apayload (aDone x) = x :=
  (atag_payload _ 10 (by norm_num)).2
@[simp] lemma atag_aWait (x : ℕ) : atag (aWait x) = 11 := (atag_payload _ 11 (by norm_num)).1
@[simp] lemma apayload_aWait (x : ℕ) : apayload (aWait x) = x :=
  (atag_payload _ 11 (by norm_num)).2
@[simp] lemma atag_aOp2 (o : ℕ) : atag (aOp2 o) = 12 := (atag_payload _ 12 (by norm_num)).1
@[simp] lemma apayload_aOp2 (o : ℕ) : apayload (aOp2 o) = o :=
  (atag_payload _ 12 (by norm_num)).2

/-! ### The description of a compiled action -/

/-- The names of the source signature, numbered. -/
def nameListOf (UA UC : List ℕ) : List ℕ := UA.map nA ++ UC.map nC

/-- **The precondition, add and delete list of the compiled action numbered `x`.**  `nameList`
is the list of numbered source task names, and `pre`, `ad`, `de` are the precondition, add and
delete list of the source actions. -/
def actInfo (nameList : List ℕ) (pre ad de : ℕ → List ℕ) (x : ℕ) :
    List ℕ × List ℕ × List ℕ :=
  if atag x = 0 then
    ([], [fPos (apayload x / 5) (apayload x % 5)], [fNeg (apayload x / 5) (apayload x % 5)])
  else if atag x = 1 then
    ([], [fNeg (apayload x / 5) (apayload x % 5)], [fPos (apayload x / 5) (apayload x % 5)])
  else if atag x = 2 then
    ([fPos (apayload x / 25) (apayload x % 25 / 5), fPos (apayload x / 25) (apayload x % 5)],
      [], [])
  else if atag x = 3 then
    ([fNeg (apayload x / 25) (apayload x % 25 / 5), fNeg (apayload x / 25) (apayload x % 5)],
      [], [])
  else if atag x = 4 then
    ([], [fTask (apayload x)],
      (nameList.filter fun u => !(u == apayload x)).map fTask)
  else if atag x = 5 then ([fTask (apayload x)], [], [])
  else if atag x = 6 then ([fKey0], [], [fKey0])
  else if atag x = 7 then ([], [fKey0], [])
  else if atag x = 8 then ([], [fKey1 (apayload x)], [])
  else if atag x = 9 then ([fKey1 (apayload x)], [], [fKey1 (apayload x)])
  else if atag x = 10 then ([], [fKey2 (apayload x)], [])
  else if atag x = 11 then ([fKey2 (apayload x)], [], [fKey2 (apayload x)])
  else ((pre (apayload x)).map fun v => fPos v 1,
    ((ad (apayload x)).map fun v => fPos v 1) ++ ((de (apayload x)).map fun v => fNeg v 1),
    ((ad (apayload x)).map fun v => fNeg v 1) ++ ((de (apayload x)).map fun v => fPos v 1))

/-- **The compiled actions a description lists.** -/
def allActs (V nameList UA : List ℕ) : List ℕ :=
  (V.flatMap fun v => (List.range 5).flatMap fun i => [aSetV v i, aDelV v i]) ++
  (V.flatMap fun v => (List.range 5).flatMap fun i => (List.range 5).flatMap fun j =>
    [aPrePV v i j, aPreNV v i j]) ++
  (nameList.flatMap fun t => [aSetC t, aPreC t]) ++
  [aLock, aUnlock] ++
  ([rwRead, rwWrite].flatMap fun x => [aAsk x, aAccept x, aDone x, aWait x]) ++
  (UA.map aOp2)

/-! ### Correctness -/

section Correct

open ToAc

variable {F A C I : Type} {f : F → ℕ} {a : A → ℕ} {c : C → ℕ} {D : Domain F A C I}
  {vars : List F} {V UA UC : List ℕ} {pre ad de : ℕ → List ℕ}

/-- The data the source contributes to the action model of the compiled description. -/
structure ActData (f : F → ℕ) (a : A → ℕ) (c : C → ℕ) (D : Domain F A C I) (vars : List F)
    (V UA UC : List ℕ) (pre ad de : ℕ → List ℕ) : Prop where
  /-- `V` is the list of source facts, numbered. -/
  facts : V = vars.map f
  /-- `vars` exhausts the facts of the source. -/
  vars_all : ∀ v : F, v ∈ vars
  /-- Every source action name is listed in `UA`. -/
  actions_mem : ∀ o : A, a o ∈ UA
  /-- Every source compound task name is listed in `UC`. -/
  names_mem : ∀ y : C, c y ∈ UC
  /-- Every entry of `nameListOf UA UC` is a source task name. -/
  names_onto : ∀ u ∈ nameListOf UA UC, ∃ t : A ⊕ C, encName a c t = u
  /-- `a` is injective. -/
  act_inj : Function.Injective a
  /-- `c` is injective. -/
  name_inj : Function.Injective c
  /-- `pre` describes the preconditions of the source. -/
  pre_spec : ∀ o : A, {u | u ∈ pre (a o)} = f '' D.prec o
  /-- `ad` describes the add lists of the source. -/
  add_spec : ∀ o : A, {u | u ∈ ad (a o)} = f '' D.add o
  /-- `de` describes the delete lists of the source. -/
  del_spec : ∀ o : A, {u | u ∈ de (a o)} = f '' D.del o

lemma encName_mem_nameListOf (h : ActData f a c D vars V UA UC pre ad de) (t : A ⊕ C) :
    encName a c t ∈ nameListOf UA UC := by
  cases t with
  | inl o => exact List.mem_append_left _ (List.mem_map_of_mem (h.actions_mem o))
  | inr y => exact List.mem_append_right _ (List.mem_map_of_mem (h.names_mem y))

/-- **Every compiled action is listed.** -/
lemma encAct_mem_allActs (h : ActData f a c D vars V UA UC pre ad de) (o : AcAct F A C) :
    encAct f a c o ∈ allActs V (nameListOf UA UC) UA := by
  have hV : ∀ v : F, f v ∈ V := by
    intro v; rw [h.facts]; exact List.mem_map_of_mem (h.vars_all v)
  cases o with
  | setV v i =>
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ ?_))))
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons]
      exact ⟨f v, hV v, i, i.isLt, Or.inl rfl⟩
  | delV v i =>
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ ?_))))
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons]
      exact ⟨f v, hV v, i, i.isLt, Or.inr (Or.inl rfl)⟩
  | prePV v i j =>
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ ?_))))
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons]
      exact ⟨f v, hV v, i, i.isLt, j, j.isLt, Or.inl rfl⟩
  | preNV v i j =>
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ ?_))))
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons]
      exact ⟨f v, hV v, i, i.isLt, j, j.isLt, Or.inr (Or.inl rfl)⟩
  | setC t =>
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ ?_)))
      simp only [List.mem_flatMap, List.mem_cons]
      exact ⟨encName a c t, encName_mem_nameListOf h t, Or.inl rfl⟩
  | preC t =>
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ ?_)))
      simp only [List.mem_flatMap, List.mem_cons]
      exact ⟨encName a c t, encName_mem_nameListOf h t, Or.inr (Or.inl rfl)⟩
  | lock =>
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  | unlock =>
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  | ask x =>
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      cases x <;> simp [rwRead, rwWrite]
  | accept x =>
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      cases x <;> simp [rwRead, rwWrite]
  | doneA x =>
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      cases x <;> simp [rwRead, rwWrite]
  | waitA x =>
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      cases x <;> simp [rwRead, rwWrite]
  | op2 o =>
      exact List.mem_append_right _ (List.mem_map_of_mem (h.actions_mem o))

private lemma pos_five {i : Fin 5} {v : F} :
    (5 * f v + (i : ℕ)) / 5 = f v ∧ (5 * f v + (i : ℕ)) % 5 = (i : ℕ) := by
  have := i.isLt; omega

private lemma pos_twentyfive {i j : Fin 5} {v : F} :
    (25 * f v + 5 * (i : ℕ) + (j : ℕ)) / 25 = f v ∧
      (25 * f v + 5 * (i : ℕ) + (j : ℕ)) % 25 / 5 = (i : ℕ) ∧
      (25 * f v + 5 * (i : ℕ) + (j : ℕ)) % 5 = (j : ℕ) := by
  have := i.isLt; have := j.isLt; refine ⟨by omega, by omega, by omega⟩

private lemma mem_of_spec {S : Set F} {l : List ℕ} (hs : {u | u ∈ l} = f '' S) (u : ℕ) :
    u ∈ l ↔ ∃ v ∈ S, f v = u := by
  constructor
  · intro hu
    have hu' : u ∈ f '' S := by rw [← hs]; exact hu
    obtain ⟨v, hv, hvu⟩ := hu'
    exact ⟨v, hv, hvu⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : f v ∈ f '' S := ⟨v, hv, rfl⟩
    rw [← hs] at hv'
    exact hv'

variable (h : ActData f a c D vars V UA UC pre ad de)

include h

/-- **The described precondition is the precondition.** -/
theorem actInfo_prec (o : AcAct F A C) :
    {x | x ∈ (actInfo (nameListOf UA UC) pre ad de (encAct f a c o)).1} =
      encFact f a c '' ToAc.prec D.toActionModel o := by
  cases o with
  | setV v i => simp [actInfo, ToAc.prec]
  | delV v i => simp [actInfo, ToAc.prec]
  | prePV v i j =>
      obtain ⟨h1, h2, h3⟩ := pos_twentyfive (f := f) (i := i) (j := j) (v := v)
      simp only [enc_aPrePV, actInfo, atag_aPrePV, apayload_aPrePV, h1, h2, h3]
      norm_num
      ext x
      simp [ToAc.prec, Set.image_insert_eq]
  | preNV v i j =>
      obtain ⟨h1, h2, h3⟩ := pos_twentyfive (f := f) (i := i) (j := j) (v := v)
      simp only [enc_aPreNV, actInfo, atag_aPreNV, apayload_aPreNV, h1, h2, h3]
      norm_num
      ext x
      simp [ToAc.prec, Set.image_insert_eq]
  | setC t => simp [actInfo, ToAc.prec]
  | preC t =>
      simp only [enc_aPreC, actInfo, atag_aPreC, apayload_aPreC]
      norm_num
      ext x
      simp [ToAc.prec]
  | lock => ext x; simp [actInfo, atag, aLock, ToAc.prec]
  | unlock => ext x; simp [actInfo, atag, aUnlock, ToAc.prec]
  | ask x => cases x <;> simp [actInfo, ToAc.prec]
  | accept x =>
      cases x <;>
        · simp only [enc_aAccept, actInfo, atag_aAccept, apayload_aAccept]
          norm_num
          ext y
          simp [ToAc.prec]
  | doneA x => cases x <;> simp [actInfo, ToAc.prec]
  | waitA x =>
      cases x <;>
        · simp only [enc_aWait, actInfo, atag_aWait, apayload_aWait]
          norm_num
          ext y
          simp [ToAc.prec]
  | op2 o =>
      simp only [enc_aOp2, actInfo, atag_aOp2, apayload_aOp2]
      norm_num
      have hp := mem_of_spec (h.pre_spec o)
      ext x
      simp only [Set.mem_setOf_eq, ToAc.prec, Set.mem_image, Set.image_image, hp]
      constructor
      · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨f v, ⟨v, hv, rfl⟩, rfl⟩

/-- **The described add list is the add list.** -/
theorem actInfo_add (o : AcAct F A C) :
    {x | x ∈ (actInfo (nameListOf UA UC) pre ad de (encAct f a c o)).2.1} =
      encFact f a c '' ToAc.add D.toActionModel o := by
  cases o with
  | setV v i =>
      obtain ⟨h1, h2⟩ := pos_five (f := f) (i := i) (v := v)
      simp only [enc_aSetV, actInfo, atag_aSetV, apayload_aSetV, h1, h2]
      norm_num
      ext x
      simp [ToAc.add]
  | delV v i =>
      obtain ⟨h1, h2⟩ := pos_five (f := f) (i := i) (v := v)
      simp only [enc_aDelV, actInfo, atag_aDelV, apayload_aDelV, h1, h2]
      norm_num
      ext x
      simp [ToAc.add]
  | prePV v i j => simp [actInfo, ToAc.add]
  | preNV v i j => simp [actInfo, ToAc.add]
  | setC t =>
      simp only [enc_aSetC, actInfo, atag_aSetC, apayload_aSetC]
      norm_num
      ext x
      simp [ToAc.add]
  | preC t => simp [actInfo, ToAc.add]
  | lock => ext x; simp [actInfo, atag, aLock, ToAc.add]
  | unlock => ext x; simp [actInfo, atag, aUnlock, ToAc.add]
  | ask x =>
      cases x <;>
        · simp only [enc_aAsk, actInfo, atag_aAsk, apayload_aAsk]
          norm_num
          ext y
          simp [ToAc.add]
  | accept x => cases x <;> simp [actInfo, ToAc.add]
  | doneA x =>
      cases x <;>
        · simp only [enc_aDone, actInfo, atag_aDone, apayload_aDone]
          norm_num
          ext y
          simp [ToAc.add]
  | waitA x => cases x <;> simp [actInfo, ToAc.add]
  | op2 o =>
      simp only [enc_aOp2, actInfo, atag_aOp2, apayload_aOp2]
      norm_num
      have hA := mem_of_spec (h.add_spec o)
      have hD := mem_of_spec (h.del_spec o)
      ext x
      simp only [Set.mem_setOf_eq, ToAc.add, Set.mem_image,
        Set.image_union, Set.image_image, Set.mem_union, hA, hD]
      constructor
      · rintro (⟨u, ⟨v, hv, rfl⟩, rfl⟩ | ⟨u, ⟨v, hv, rfl⟩, rfl⟩)
        · exact Or.inl ⟨v, hv, rfl⟩
        · exact Or.inr ⟨v, hv, rfl⟩
      · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
        · exact Or.inl ⟨f v, ⟨v, hv, rfl⟩, rfl⟩
        · exact Or.inr ⟨f v, ⟨v, hv, rfl⟩, rfl⟩

/-- **The described delete list is the delete list.** -/
theorem actInfo_del (o : AcAct F A C) :
    {x | x ∈ (actInfo (nameListOf UA UC) pre ad de (encAct f a c o)).2.2} =
      encFact f a c '' ToAc.del D.toActionModel o := by
  cases o with
  | setV v i =>
      obtain ⟨h1, h2⟩ := pos_five (f := f) (i := i) (v := v)
      simp only [enc_aSetV, actInfo, atag_aSetV, apayload_aSetV, h1, h2]
      norm_num
      ext x
      simp [ToAc.del]
  | delV v i =>
      obtain ⟨h1, h2⟩ := pos_five (f := f) (i := i) (v := v)
      simp only [enc_aDelV, actInfo, atag_aDelV, apayload_aDelV, h1, h2]
      norm_num
      ext x
      simp [ToAc.del]
  | prePV v i j => simp [actInfo, ToAc.del]
  | preNV v i j => simp [actInfo, ToAc.del]
  | setC t =>
      simp only [enc_aSetC, actInfo, atag_aSetC, apayload_aSetC]
      norm_num
      ext x
      simp only [Set.mem_setOf_eq, ToAc.del, Set.mem_image]
      constructor
      · rintro ⟨u, ⟨hu, hne⟩, rfl⟩
        obtain ⟨t', rfl⟩ := h.names_onto u hu
        refine ⟨AcFact.task t', ⟨t', rfl, ?_⟩, rfl⟩
        intro hc; exact hne (by rw [hc])
      · rintro ⟨y, ⟨t', rfl, hne⟩, rfl⟩
        refine ⟨encName a c t', ⟨encName_mem_nameListOf h t', ?_⟩, rfl⟩
        intro hc
        exact hne (encName_injective h.act_inj h.name_inj hc)
  | preC t => simp [actInfo, ToAc.del]
  | lock => ext x; simp [actInfo, atag, aLock, ToAc.del]
  | unlock => ext x; simp [actInfo, atag, aUnlock, ToAc.del]
  | ask x => cases x <;> simp [actInfo, ToAc.del]
  | accept x =>
      cases x <;>
        · simp only [enc_aAccept, actInfo, atag_aAccept, apayload_aAccept]
          norm_num
          ext y
          simp [ToAc.del]
  | doneA x => cases x <;> simp [actInfo, ToAc.del]
  | waitA x =>
      cases x <;>
        · simp only [enc_aWait, actInfo, atag_aWait, apayload_aWait]
          norm_num
          ext y
          simp [ToAc.del]
  | op2 o =>
      simp only [enc_aOp2, actInfo, atag_aOp2, apayload_aOp2]
      norm_num
      have hA := mem_of_spec (h.add_spec o)
      have hD := mem_of_spec (h.del_spec o)
      ext x
      simp only [Set.mem_setOf_eq, ToAc.del, Set.mem_image,
        Set.image_union, Set.image_image, Set.mem_union, hA, hD]
      constructor
      · rintro (⟨u, ⟨v, hv, rfl⟩, rfl⟩ | ⟨u, ⟨v, hv, rfl⟩, rfl⟩)
        · exact Or.inl ⟨v, hv, rfl⟩
        · exact Or.inr ⟨v, hv, rfl⟩
      · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
        · exact Or.inl ⟨f v, ⟨v, hv, rfl⟩, rfl⟩
        · exact Or.inr ⟨f v, ⟨v, hv, rfl⟩, rfl⟩

end Correct

end Ac

end Syn

end HTN
