import HtnPlanning.Core.Size
/-!
# The proof-tuple characterisation of totally ordered HTN planning

The compilation of totally ordered HTN problems into acyclic ones (`compilation.tex`,
Theorem "TO-HTN is poly-compilable to HTN-AC") does not encode plans directly.  Instead, a plan
of the compiled problem is a *proof* that a plan of the original problem exists, in the sense of
the EXPTIME-membership argument of Erol, Hendler and Nau:

> The proof that a plan for a TO-HTN problem exists can be viewed as an ordered list of triples
> `(s, T, s')` where `s`, `s'` are states and `T` is a primitive or a compound task, such that
> * if `T` is primitive, then `s' = γ(s, T)`;
> * if `T` is compound, then there is a method `T ↦ A B` and a state `s''` such that the
>   triples `(s, A, s'')` and `(s'', B, s')` occur *before* `(s, T, s')` in the list.

Following the source we assume that every method has at most two subtasks ("which can always be
obtained by a linear compilation").

This file formalises the two sides of that characterisation and proves them equivalent:

* `HTN.Domain.Yield D x as` — the task `x` can be *refined* into the action sequence `as`;
* `HTN.Domain.Provable D s x s'` — the triple `(s, x, s')` is derivable by the rules above
  (`Provable` is exactly the set of triples that occur in some valid proof list: the inductive
  definition is the closure of the two rules, and being *derivable* is the same as occurring in
  such a list);
* `HTN.Domain.provable_iff_yield` — **the triple `(s, x, s')` is derivable iff `x` can be
  refined into an action sequence that is executable in `s` and leads to `s'`.**

This is the correctness statement of the dynamic programming table that the HTN-AC compilation
of `HtnComplexity/ToHtnAc/ToHtnAc.lean` simulates with its `TUPLE` and `MEM` tasks.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- The method `m` has the totally ordered body `xs`: some linearization of its subtask network
enumerates the tasks in the order `xs`, and the subtask network is totally ordered along it. -/
def Method.HasSeqBody (m : Method I A C) (xs : List (A ⊕ C)) : Prop :=
  ∃ l : List I, m.subtasks.IsLinearization l ∧ l.map m.subtasks.α = xs ∧
    l.Pairwise m.subtasks.ord

namespace Domain

variable (D : Domain F A C I)

/-- The domain contains a method that decomposes `c` into the totally ordered body `xs`. -/
def SeqBody (c : C) (xs : List (A ⊕ C)) : Prop :=
  ∃ m ∈ D.methods, m.abstractTask = c ∧ m.HasSeqBody xs

/-- `D.Yield x as`: the (primitive or compound) task `x` can be refined into the action
sequence `as`.  As in the source, methods are assumed to have at most two subtasks. -/
inductive Yield : (A ⊕ C) → List A → Prop
  /-- A primitive task yields itself. -/
  | prim (a : A) : Yield (Sum.inl a) [a]
  /-- A method without subtasks yields the empty action sequence. -/
  | zero {c : C} (h : D.SeqBody c []) : Yield (Sum.inr c) []
  /-- A method with one subtask yields what the subtask yields. -/
  | one {c : C} {x : A ⊕ C} {as : List A} (h : D.SeqBody c [x]) (hx : Yield x as) :
      Yield (Sum.inr c) as
  /-- A method with two subtasks yields the concatenation. -/
  | two {c : C} {x y : A ⊕ C} {as bs : List A} (h : D.SeqBody c [x, y]) (hx : Yield x as)
      (hy : Yield y bs) : Yield (Sum.inr c) (as ++ bs)

/-- `D.Provable s x s'`: the triple `(s, x, s')` is derivable by the rules of the
proof-tuple characterisation. -/
inductive Provable : Set F → (A ⊕ C) → Set F → Prop
  /-- A primitive task: `s' = γ(s, a)`, provided `a` is applicable in `s`. -/
  | prim {a : A} {s : Set F} (h : D.Applicable a s) :
      Provable s (Sum.inl a) (D.transition a s)
  /-- A method without subtasks does not change the state. -/
  | zero {c : C} {s : Set F} (h : D.SeqBody c []) : Provable s (Sum.inr c) s
  /-- A method with one subtask. -/
  | one {c : C} {x : A ⊕ C} {s s' : Set F} (h : D.SeqBody c [x]) (hx : Provable s x s') :
      Provable s (Sum.inr c) s'
  /-- A method with two subtasks: the two triples are chained through the intermediate
  state `s''`. -/
  | two {c : C} {x y : A ⊕ C} {s s'' s' : Set F} (h : D.SeqBody c [x, y])
      (hx : Provable s x s'') (hy : Provable s'' y s') : Provable s (Sum.inr c) s'

variable {D}

/-- **The proof-tuple characterisation is correct.**  A triple `(s, x, s')` is derivable
exactly when the task `x` can be refined into an action sequence that is executable in `s` and
transforms `s` into `s'`. -/
theorem provable_iff_yield (s : Set F) (x : A ⊕ C) (s' : Set F) :
    D.Provable s x s' ↔
      ∃ as : List A, D.Yield x as ∧ D.SeqApplicable as s ∧ D.transitionSeq as s = s' := by
  constructor
  · intro h
    induction h with
    | prim h => exact ⟨[_], Yield.prim _, ⟨h, trivial⟩, rfl⟩
    | zero h => exact ⟨[], Yield.zero h, trivial, rfl⟩
    | one h _ ih =>
        obtain ⟨as, hy, happ, htr⟩ := ih
        exact ⟨as, Yield.one h hy, happ, htr⟩
    | two h _ _ ihx ihy =>
        obtain ⟨as, hya, happa, htra⟩ := ihx
        obtain ⟨bs, hyb, happb, htrb⟩ := ihy
        refine ⟨as ++ bs, Yield.two h hya hyb, ?_, ?_⟩
        · rw [ActionModel.seqApplicable_append]
          exact ⟨happa, htra ▸ happb⟩
        · rw [ActionModel.transitionSeq_append, htra]
          exact htrb
  · rintro ⟨as, hy, happ, rfl⟩
    induction hy generalizing s with
    | prim a => exact Provable.prim happ.1
    | zero h => exact Provable.zero h
    | one h _ ih => exact Provable.one h (ih s happ)
    | two h _ _ ihx ihy =>
        rw [ActionModel.seqApplicable_append] at happ
        rw [ActionModel.transitionSeq_append]
        exact Provable.two h (ihx s happ.1) (ihy _ happ.2)

/-- The "only if" direction: from a derivation of `(s, x, s')` one extracts an executable
refinement of `x`. -/
theorem exists_yield_of_provable {s s' : Set F} {x : A ⊕ C} (h : D.Provable s x s') :
    ∃ as : List A, D.Yield x as ∧ D.SeqApplicable as s ∧ D.transitionSeq as s = s' :=
  (provable_iff_yield s x s').1 h

/-- The "if" direction: an executable refinement of `x` gives a derivation of the
corresponding triple. -/
theorem provable_of_yield {s : Set F} {x : A ⊕ C} {as : List A} (hy : D.Yield x as)
    (happ : D.SeqApplicable as s) : D.Provable s x (D.transitionSeq as s) :=
  (provable_iff_yield s x _).2 ⟨as, hy, happ, rfl⟩

end Domain

end HTN
