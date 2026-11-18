import ComplexityTheory.Collapse.Fun
import ComplexityTheory.Complexity.CobhamExamples
/-!
# Boolean combinations inside the polynomial-space class

The closure properties of `HTN.PSpace.PSpaceB` that the advice-elimination argument uses, in the
shape `ComplexityTheory/Complexity/CobhamString.lean` gives them for polynomial time: a
predicate of the class may be negated, two of them may be combined by any Boolean operation, and
a predicate may be applied to arguments computed by functions of the class.
-/

namespace HTN

namespace PSpace

open PTime

theorem psConst (z : List Bool) : PSpaceF (fun _ => z) := PSpaceF.cobham (cobham_const z)

theorem psAppend {a b : Fn} (ha : PSpaceF a) (hb : PSpaceF b) :
    PSpaceF (fun args => a args ++ b args) :=
  PSpaceF.of_eq (psC2 (PSpaceF.cobham cobham_append) ha hb) fun args => by simp [compFn, proj]

/-- Two one-bit answers may be combined by any Boolean operation. -/
theorem PSpaceB.op2 {p q : Args → Bool} (hp : PSpaceB p) (hq : PSpaceB q)
    (op : Bool → Bool → Bool) : PSpaceB (fun args => op (p args) (q args)) := by
  set T : List Bool → List Bool := fun z => [op (z.getD 0 false) (z.getD 1 false)] with hT
  have hdep : ∀ x, T x = T (x.take 2) := by
    intro x
    match x with
    | [] => rfl
    | [a] => rfl
    | a :: b :: t => rfl
  have htab : Cobham (fun args : Args => T (args.getD 0 [])) :=
    cobham_ofTake 2 1 T hdep (fun x => by simp [hT])
  have happ : PSpaceF (fun args : Args => [p args] ++ [q args]) := psAppend hp hq
  exact PSpaceF.of_eq (psC1 (PSpaceF.cobham htab) happ) fun args => by simp [compFn, hT]

theorem PSpaceB.not {p : Args → Bool} (hp : PSpaceB p) : PSpaceB (fun args => !p args) :=
  (hp.op2 hp (fun a _ => !a)).of_eq fun _ => rfl

theorem PSpaceB.and {p q : Args → Bool} (hp : PSpaceB p) (hq : PSpaceB q) :
    PSpaceB (fun args => p args && q args) := hp.op2 hq (· && ·)

theorem PSpaceB.or {p q : Args → Bool} (hp : PSpaceB p) (hq : PSpaceB q) :
    PSpaceB (fun args => p args || q args) := hp.op2 hq (· || ·)

theorem psConstB (b : Bool) : PSpaceB (fun _ => b) := PSpaceB.of_cobhamB (cobhamB_const b)

/-! ### Applying a predicate of the class to computed arguments -/

theorem PSpaceB.comp1 {p : Args → Bool} (hp : PSpaceB p) {a : Fn} (ha : PSpaceF a) :
    PSpaceB fun args => p [a args] :=
  PSpaceF.of_eq (psC1 hp ha) fun args => by simp [compFn]

theorem PSpaceB.comp2 {p : Args → Bool} (hp : PSpaceB p) {a b : Fn} (ha : PSpaceF a)
    (hb : PSpaceF b) : PSpaceB fun args => p [a args, b args] :=
  PSpaceF.of_eq (psC2 hp ha hb) fun args => by simp [compFn]

theorem PSpaceB.comp3 {p : Args → Bool} (hp : PSpaceB p) {a b c : Fn} (ha : PSpaceF a)
    (hb : PSpaceF b) (hc : PSpaceF c) : PSpaceB fun args => p [a args, b args, c args] :=
  PSpaceF.of_eq (psC3 hp ha hb hc) fun args => by simp [compFn]

theorem PSpaceB.comp4 {p : Args → Bool} (hp : PSpaceB p) {a b c d : Fn} (ha : PSpaceF a)
    (hb : PSpaceF b) (hc : PSpaceF c) (hd : PSpaceF d) :
    PSpaceB fun args => p [a args, b args, c args, d args] :=
  PSpaceF.of_eq (psC4 hp ha hb hc hd) fun args => by simp [compFn]

end PSpace

end HTN
