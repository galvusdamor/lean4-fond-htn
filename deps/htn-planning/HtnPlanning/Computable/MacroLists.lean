import HtnPlanning.Core.Macro
import HtnPlanning.Computable.Syntax
/-!
# The macro action of a sequence of described actions

`HtnPlanning/Core/Macro.lean` contracts a sequence of actions `o₁ … oₙ` into a single STRIPS
action: its precondition `seqPre`, add list `seqAdd` and delete list `seqDel`, and the static
feasibility test `SeqFeasible` which decides whether the sequence is applicable at all.  All
four are defined as *sets* and as a *predicate*; a compilation that has to write the macro
action down needs them as **lists** and as a **Bool**.

This file computes them by a single `List.foldr` over the sequence
(`HTN.Syn.DomDesc.macroFold`) and proves that the result denotes the semantic notions
(`HTN.Syn.DomDesc.seqPreList_eq`, `seqAddList_eq`, `seqDelList_eq`, `feasibleB_iff`).  The fold
is primitive recursive.
-/

namespace HTN

namespace Syn

/-! ### Difference and intersection of listed sets -/

/-- The elements of `X` that are not in `Y`. -/
def filt (X Y : List ℕ) : List ℕ := X.filterMap fun f => if memB Y f then none else some f

/-- The elements of `X` that are in `Y`. -/
def inter (X Y : List ℕ) : List ℕ := X.filterMap fun f => if memB Y f then some f else none

@[simp] theorem mem_filt {X Y : List ℕ} {f : ℕ} : f ∈ filt X Y ↔ f ∈ X ∧ f ∉ Y := by
  simp only [filt, List.mem_filterMap]
  constructor
  · rintro ⟨g, hg, hgf⟩
    by_cases h : memB Y g = true
    · rw [if_pos h] at hgf; exact absurd hgf (by simp)
    · rw [if_neg h] at hgf
      have : g = f := by simpa using hgf
      subst this
      exact ⟨hg, fun hc => h (memB_iff.2 hc)⟩
  · rintro ⟨hf, hY⟩
    refine ⟨f, hf, ?_⟩
    rw [if_neg (fun hc : memB Y f = true => hY (memB_iff.1 hc))]

@[simp] theorem mem_inter {X Y : List ℕ} {f : ℕ} : f ∈ inter X Y ↔ f ∈ X ∧ f ∈ Y := by
  simp only [inter, List.mem_filterMap]
  constructor
  · rintro ⟨g, hg, hgf⟩
    by_cases h : memB Y g = true
    · rw [if_pos h] at hgf
      have : g = f := by simpa using hgf
      subst this
      exact ⟨hg, memB_iff.1 h⟩
    · rw [if_neg h] at hgf; exact absurd hgf (by simp)
  · rintro ⟨hf, hY⟩
    exact ⟨f, hf, by simp [memB_iff.2 hY]⟩

theorem length_filt_le (X Y : List ℕ) : (filt X Y).length ≤ X.length :=
  (List.length_filterMap_le _ _)

theorem inter_eq_nil_iff {X Y : List ℕ} : inter X Y = [] ↔ ∀ f ∈ X, f ∉ Y := by
  constructor
  · intro h f hf hY
    have : f ∈ inter X Y := mem_inter.2 ⟨hf, hY⟩
    rw [h] at this
    exact absurd this (by simp)
  · intro h
    rcases hnil : inter X Y with _ | ⟨f, l⟩
    · rfl
    · have hmem : f ∈ inter X Y := by rw [hnil]; simp
      obtain ⟨hf, hY⟩ := mem_inter.1 hmem
      exact absurd hY (h f hf)

namespace DomDesc

/-! ### The lists of a described action -/

/-- The precondition of a described action, as a list. -/
def precList (d : DomDesc) (a : ℕ) : List ℕ := (d.actions.lookup a).elim [] fun x => x.1

/-- The add list of a described action. -/
def addList (d : DomDesc) (a : ℕ) : List ℕ := (d.actions.lookup a).elim [] fun x => x.2.1

/-- The delete list of a described action. -/
def delList (d : DomDesc) (a : ℕ) : List ℕ := (d.actions.lookup a).elim [] fun x => x.2.2

@[simp] theorem prec_eq (d : DomDesc) (a : ℕ) : d.prec a = {f | f ∈ d.precList a} := rfl

@[simp] theorem add_eq (d : DomDesc) (a : ℕ) : d.add a = {f | f ∈ d.addList a} := rfl

@[simp] theorem del_eq (d : DomDesc) (a : ℕ) : d.del a = {f | f ∈ d.delList a} := rfl

/-! ### The macro action of a sequence -/

/-- **The macro action of a sequence of described actions**, computed by one pass from the
right: the precondition, the add list and the delete list of the contracted action, together
with the static feasibility flag. -/
def macroFold (d : DomDesc) (os : List ℕ) : (List ℕ × List ℕ × List ℕ) × Bool :=
  os.foldr
    (fun o acc =>
      ((d.precList o ++ filt acc.1.1 (d.addList o),
        acc.1.2.1 ++ filt (d.addList o) acc.1.2.2,
        d.delList o ++ acc.1.2.2),
        acc.2 && (inter (filt acc.1.1 (d.addList o)) (d.delList o)).isEmpty))
    (([], [], []), true)

/-- The precondition of the macro action, as a list. -/
def seqPreList (d : DomDesc) (os : List ℕ) : List ℕ := (macroFold d os).1.1

/-- The add list of the macro action. -/
def seqAddList (d : DomDesc) (os : List ℕ) : List ℕ := (macroFold d os).1.2.1

/-- The delete list of the macro action. -/
def seqDelList (d : DomDesc) (os : List ℕ) : List ℕ := (macroFold d os).1.2.2

/-- The static feasibility test of a sequence of described actions. -/
def feasibleB (d : DomDesc) (os : List ℕ) : Bool := (macroFold d os).2

variable (d : DomDesc)

@[simp] theorem seqPreList_nil : d.seqPreList [] = [] := rfl
@[simp] theorem seqAddList_nil : d.seqAddList [] = [] := rfl
@[simp] theorem seqDelList_nil : d.seqDelList [] = [] := rfl
@[simp] theorem feasibleB_nil : d.feasibleB [] = true := rfl

@[simp] theorem seqPreList_cons (o : ℕ) (os : List ℕ) :
    d.seqPreList (o :: os) = d.precList o ++ filt (d.seqPreList os) (d.addList o) := rfl

@[simp] theorem seqAddList_cons (o : ℕ) (os : List ℕ) :
    d.seqAddList (o :: os) = d.seqAddList os ++ filt (d.addList o) (d.seqDelList os) := rfl

@[simp] theorem seqDelList_cons (o : ℕ) (os : List ℕ) :
    d.seqDelList (o :: os) = d.delList o ++ d.seqDelList os := rfl

@[simp] theorem feasibleB_cons (o : ℕ) (os : List ℕ) :
    d.feasibleB (o :: os) =
      (d.feasibleB os && (inter (filt (d.seqPreList os) (d.addList o))
        (d.delList o)).isEmpty) := rfl

/-! ### Correctness -/

theorem seqDelList_eq (os : List ℕ) : {f | f ∈ d.seqDelList os} = d.toDomain.seqDel os := by
  induction os with
  | nil => ext f; simp [ActionModel.seqDel]
  | cons o os ih =>
    ext f
    simp only [seqDelList_cons, Set.mem_setOf_eq, List.mem_append,
      ActionModel.seqDel_cons, Set.mem_union]
    rw [show (d.toDomain.del o) = {g | g ∈ d.delList o} from rfl, ← ih]
    simp

theorem seqAddList_eq (os : List ℕ) : {f | f ∈ d.seqAddList os} = d.toDomain.seqAdd os := by
  induction os with
  | nil => ext f; simp [ActionModel.seqAdd]
  | cons o os ih =>
    ext f
    simp only [seqAddList_cons, Set.mem_setOf_eq, List.mem_append, mem_filt,
      ActionModel.seqAdd_cons, Set.mem_union, Set.mem_diff]
    rw [← ih, ← seqDelList_eq d os]
    simp only [Set.mem_setOf_eq]
    rw [show (d.toDomain.add o) = {g | g ∈ d.addList o} from rfl]
    simp

theorem seqPreList_eq (os : List ℕ) : {f | f ∈ d.seqPreList os} = d.toDomain.seqPre os := by
  induction os with
  | nil => ext f; simp [ActionModel.seqPre]
  | cons o os ih =>
    ext f
    simp only [seqPreList_cons, Set.mem_setOf_eq, List.mem_append, mem_filt,
      ActionModel.seqPre_cons, Set.mem_union, Set.mem_diff]
    rw [← ih]
    simp only [Set.mem_setOf_eq]
    rw [show (d.toDomain.prec o) = {g | g ∈ d.precList o} from rfl,
      show (d.toDomain.add o) = {g | g ∈ d.addList o} from rfl]
    simp

theorem feasibleB_iff (os : List ℕ) : d.feasibleB os = true ↔ d.toDomain.SeqFeasible os := by
  induction os with
  | nil => simp [ActionModel.SeqFeasible]
  | cons o os ih =>
    rw [feasibleB_cons, Bool.and_eq_true, ih, ActionModel.seqFeasible_cons]
    refine and_congr Iff.rfl ?_
    rw [List.isEmpty_iff, inter_eq_nil_iff, Set.disjoint_left]
    constructor
    · intro h f hf
      rw [← seqPreList_eq d os] at hf
      have hf' : f ∈ filt (d.seqPreList os) (d.addList o) :=
        mem_filt.2 ⟨hf.1, fun hc => hf.2 hc⟩
      exact h f hf'
    · intro h f hf
      obtain ⟨hf₁, hf₂⟩ := mem_filt.1 hf
      have : f ∈ d.toDomain.seqPre os \ d.toDomain.add o := by
        rw [← seqPreList_eq d os]
        exact ⟨hf₁, hf₂⟩
      exact h this

/-! ### Size -/

theorem mem_le_sum {α : Type} (f : α → ℕ) {l : List α} {x : α} (hx : x ∈ l) :
    f x ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · have := ih hx
      simp only [List.map_cons, List.sum_cons]
      omega

theorem length_lists_le (d : DomDesc) (a : ℕ) :
    (d.precList a).length ≤ d.size ∧ (d.addList a).length ≤ d.size ∧
      (d.delList a).length ≤ d.size := by
  rcases h : d.actions.lookup a with _ | x
  · simp [precList, addList, delList, h]
  · have hmem : (a, x) ∈ d.actions := mem_of_lookup_eq_some h
    have hsum : ActionDesc.size (a, x) ≤ (d.actions.map ActionDesc.size).sum :=
      mem_le_sum ActionDesc.size hmem
    have hsize : ActionDesc.size (a, x) = 1 + x.1.length + x.2.1.length + x.2.2.length := rfl
    have hd : (d.actions.map ActionDesc.size).sum ≤ d.size := by
      simp only [DomDesc.size]; omega
    refine ⟨?_, ?_, ?_⟩ <;> simp only [precList, addList, delList, h, Option.elim] <;> omega

theorem length_precList_le (d : DomDesc) (a : ℕ) : (d.precList a).length ≤ d.size :=
  (length_lists_le d a).1

theorem length_addList_le (d : DomDesc) (a : ℕ) : (d.addList a).length ≤ d.size :=
  (length_lists_le d a).2.1

theorem length_delList_le (d : DomDesc) (a : ℕ) : (d.delList a).length ≤ d.size :=
  (length_lists_le d a).2.2

theorem length_seqPreList_le (d : DomDesc) (os : List ℕ) :
    (d.seqPreList os).length ≤ os.length * d.size := by
  induction os with
  | nil => simp
  | cons o os ih =>
    have h1 := length_precList_le d o
    have h2 := length_filt_le (d.seqPreList os) (d.addList o)
    simp only [seqPreList_cons, List.length_append, List.length_cons]
    have : (os.length + 1) * d.size = d.size + os.length * d.size := by ring
    omega

theorem length_seqAddList_le (d : DomDesc) (os : List ℕ) :
    (d.seqAddList os).length ≤ os.length * d.size := by
  induction os with
  | nil => simp
  | cons o os ih =>
    have h1 := length_addList_le d o
    have h2 := length_filt_le (d.addList o) (d.seqDelList os)
    simp only [seqAddList_cons, List.length_append, List.length_cons]
    have : (os.length + 1) * d.size = d.size + os.length * d.size := by ring
    omega

theorem length_seqDelList_le (d : DomDesc) (os : List ℕ) :
    (d.seqDelList os).length ≤ os.length * d.size := by
  induction os with
  | nil => simp
  | cons o os ih =>
    have h1 := length_delList_le d o
    simp only [seqDelList_cons, List.length_append, List.length_cons]
    have : (os.length + 1) * d.size = d.size + os.length * d.size := by ring
    omega

/-! ### Computability -/

open Primrec

theorem primrec_filt : Primrec₂ filt := by
  refine listFilterMap (β := ℕ) (σ := ℕ) Primrec.fst ?_
  refine Primrec.ite ?_ (Primrec.const none) (option_some.comp Primrec.snd)
  exact PrimrecRel.comp Primrec.eq
    (primrec_memB.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
    (Primrec.const true)

theorem primrec_inter : Primrec₂ inter := by
  refine listFilterMap (β := ℕ) (σ := ℕ) Primrec.fst ?_
  refine Primrec.ite ?_ (option_some.comp Primrec.snd) (Primrec.const none)
  exact PrimrecRel.comp Primrec.eq
    (primrec_memB.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
    (Primrec.const true)

theorem primrec_isEmptyList : Primrec fun l : List ℕ => l.isEmpty :=
  (Primrec.list_casesOn Primrec.id (Primrec.const true)
    (Primrec.const false).to₂).of_eq fun l => by cases l <;> rfl

theorem primrec_lookupAction : Primrec₂ fun (d : DomDesc) (a : ℕ) => d.actions.lookup a :=
  Primrec.to₂ ((Primrec.listLookup).comp Primrec.snd (primrec_actions.comp Primrec.fst))

theorem primrec_precList : Primrec₂ precList := by
  have hg : Primrec₂ fun (_ : DomDesc × ℕ) (x : List ℕ × List ℕ × List ℕ) => x.1 :=
    Primrec.to₂ (Primrec.fst.comp Primrec.snd)
  refine Primrec.of_eq (Primrec.option_casesOn (σ := List ℕ)
    (primrec_lookupAction.comp Primrec.fst Primrec.snd) (Primrec.const ([] : List ℕ)) hg) ?_
  rintro ⟨d, a⟩
  cases h : d.actions.lookup a <;> simp [precList, h]

theorem primrec_addList : Primrec₂ addList := by
  have hg : Primrec₂ fun (_ : DomDesc × ℕ) (x : List ℕ × List ℕ × List ℕ) => x.2.1 :=
    Primrec.to₂ (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  refine Primrec.of_eq (Primrec.option_casesOn (σ := List ℕ)
    (primrec_lookupAction.comp Primrec.fst Primrec.snd) (Primrec.const ([] : List ℕ)) hg) ?_
  rintro ⟨d, a⟩
  cases h : d.actions.lookup a <;> simp [addList, h]

theorem primrec_delList : Primrec₂ delList := by
  have hg : Primrec₂ fun (_ : DomDesc × ℕ) (x : List ℕ × List ℕ × List ℕ) => x.2.2 :=
    Primrec.to₂ (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  refine Primrec.of_eq (Primrec.option_casesOn (σ := List ℕ)
    (primrec_lookupAction.comp Primrec.fst Primrec.snd) (Primrec.const ([] : List ℕ)) hg) ?_
  rintro ⟨d, a⟩
  cases h : d.actions.lookup a <;> simp [delList, h]

theorem primrec_macroFold : Primrec₂ macroFold := by
  set W := (DomDesc × List ℕ) × ℕ × ((List ℕ × List ℕ × List ℕ) × Bool) with hW
  have hd : Primrec fun w : W => w.1.1 := Primrec.fst.comp Primrec.fst
  have ho : Primrec fun w : W => w.2.1 := Primrec.fst.comp Primrec.snd
  have hpre : Primrec fun w : W => w.2.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hadd : Primrec fun w : W => w.2.2.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hdel : Primrec fun w : W => w.2.2.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hok : Primrec fun w : W => w.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hpl : Primrec fun w : W => (w.1.1).precList w.2.1 := primrec_precList.comp hd ho
  have hal : Primrec fun w : W => (w.1.1).addList w.2.1 := primrec_addList.comp hd ho
  have hdl : Primrec fun w : W => (w.1.1).delList w.2.1 := primrec_delList.comp hd ho
  have hfp : Primrec fun w : W => filt w.2.2.1.1 ((w.1.1).addList w.2.1) :=
    primrec_filt.comp hpre hal
  have hstep : Primrec₂ fun (p : DomDesc × List ℕ)
      (z : ℕ × ((List ℕ × List ℕ × List ℕ) × Bool)) =>
      ((p.1.precList z.1 ++ filt z.2.1.1 (p.1.addList z.1),
        z.2.1.2.1 ++ filt (p.1.addList z.1) z.2.1.2.2,
        p.1.delList z.1 ++ z.2.1.2.2),
        z.2.2 && (inter (filt z.2.1.1 (p.1.addList z.1)) (p.1.delList z.1)).isEmpty) := by
    refine Primrec.pair (Primrec.pair (Primrec.list_append.comp hpl hfp)
      (Primrec.pair (Primrec.list_append.comp hadd (primrec_filt.comp hal hdel))
        (Primrec.list_append.comp hdl hdel))) ?_
    exact Primrec.and.comp hok (primrec_isEmptyList.comp (primrec_inter.comp hfp hdl))
  exact Primrec.list_foldr Primrec.snd (Primrec.const (([], [], []), true)) hstep

end DomDesc

end Syn

end HTN
