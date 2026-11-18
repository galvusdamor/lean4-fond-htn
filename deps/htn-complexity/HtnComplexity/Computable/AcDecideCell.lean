import HtnComplexity.Computable.AcDecide
import HtnComplexity.Computable.Decider
import HtnComplexity.Computable.AcNumPrimrec
import HtnComplexity.Computable.TrStripsCell
/-!
# The decision procedure for `HTN-AC` is primitive recursive

`HtnComplexity/Computable/AcDecide.lean` builds the search `HTN.Syn.acSolvableB` and proves
that it decides plan existence for described HTN problems with an **acyclic** domain description
and an arbitrary partially ordered initial task network.  This file shows that the procedure is
primitive recursive and packages it as

`HTN.Syn.decider_HTN_AC : HTN.Syn.SynClass.HTN_AC.Decider`,

which discharges the decidability hypothesis of the cells (`HTN`, `HTN-AC`) of the compilability
table.
-/

namespace HTN

namespace Syn

open Primrec

/-! ### Generic helpers -/

theorem filterB_eq_filterMap {α : Type} (p : α → Bool) (L : List α) :
    L.filter p = L.filterMap fun x => if p x = true then some x else none := by
  induction L with
  | nil => rfl
  | cons x xs ih => by_cases h : p x <;> simp [h, ih]

/-- Filtering with a primitive-recursive predicate is primitive recursive. -/
theorem primrec_filterB {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun x => (f x).filter (p x) := by
  have h : Primrec₂ fun (x : α) (b : β) => if p x b = true then some b else none := by
    refine Primrec₂.mk (Primrec.ite ?_ (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none))
    exact PrimrecRel.comp Primrec.eq (hp.comp Primrec.fst Primrec.snd) (Primrec.const true)
  refine (Primrec.listFilterMap hf h).of_eq fun x => ?_
  rw [filterB_eq_filterMap]

theorem allB_eq_foldr {α : Type} (p : α → Bool) (L : List α) :
    L.all p = L.foldr (fun x b => p x && b) true := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem anyB_eq_foldr {α : Type} (p : α → Bool) (L : List α) :
    L.any p = L.foldr (fun x b => p x || b) false := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- `List.all` with a primitive-recursive predicate is primitive recursive. -/
theorem primrec_allB {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun x => (f x).all (p x) := by
  have h : Primrec₂ fun (x : α) (z : β × Bool) => p x z.1 && z.2 :=
    Primrec₂.mk (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
  refine (Primrec.list_foldr hf (Primrec.const true) h).of_eq fun x => ?_
  rw [allB_eq_foldr]

/-- `List.any` with a primitive-recursive predicate is primitive recursive. -/
theorem primrec_anyB {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun x => (f x).any (p x) := by
  have h : Primrec₂ fun (x : α) (z : β × Bool) => p x z.1 || z.2 :=
    Primrec₂.mk (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
  refine (Primrec.list_foldr hf (Primrec.const false) h).of_eq fun x => ?_
  rw [anyB_eq_foldr]

/-- Exponentiation is primitive recursive. -/
theorem primrec_pow : Primrec₂ (fun a b : ℕ => a ^ b) := by
  have hstep : Primrec₂ (fun (a : ℕ) (z : ℕ × ℕ) => a * z.2) :=
    Primrec.nat_mul.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  refine Primrec₂.mk ((Primrec.nat_rec (f := fun _ : ℕ => 1) (Primrec.const 1) hstep).comp
    Primrec.fst Primrec.snd |>.of_eq fun w => ?_)
  obtain ⟨a, b⟩ := w
  induction b with
  | zero => rfl
  | succ k ih =>
    show a * Nat.rec 1 (fun _ IH => a * IH) k = a ^ (k + 1)
    rw [pow_succ]
    simp only at ih
    rw [ih]
    ring

/-- The maximum of a list of naturals is primitive recursive. -/
theorem primrec_foldrMax {α : Type} [Primcodable α] {f : α → List ℕ} (hf : Primrec f) :
    Primrec fun x => (f x).foldr Nat.max 0 := by
  have h : Primrec₂ fun (_ : α) (z : ℕ × ℕ) => Nat.max z.1 z.2 :=
    Primrec₂.mk (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr hf (Primrec.const 0) h).of_eq fun _ => rfl

/-! ### The pieces of a search network -/

theorem lblPair_eq_getD (t : TnDesc) (i : ℕ) : t.lblPair i = (t.lbl.lookup i).getD (false, 0) := by
  cases h : t.lbl.lookup i with
  | none => simp [TnDesc.lblPair, h]
  | some v => simp [TnDesc.lblPair, h]

theorem primrec_lblPair : Primrec fun w : TnDesc × ℕ => w.1.lblPair w.2 := by
  have ht : Primrec fun w : TnDesc × ℕ => w.1 := Primrec.fst
  have hi : Primrec fun w : TnDesc × ℕ => w.2 := Primrec.snd
  have hlook := Ac.primrec_lookup.comp (primrec_lbl.comp ht) hi
  have h := (Primrec.option_getD (α := Bool × ℕ)).comp hlook
    (Primrec.const ((false, 0) : Bool × ℕ))
  exact h.of_eq fun w => (lblPair_eq_getD w.1 w.2).symm

theorem primrec_keysOf : Primrec PNet.keysOf := by
  have hids : Primrec fun t : TnDesc => t.ids := primrec_ids
  have hlbl : Primrec fun t : TnDesc => t.lbl.map fun q => q.1 :=
    Primrec.list_map primrec_lbl (Primrec₂.mk (Primrec.fst.comp Primrec.snd))
  exact Ac.primrec_dedup.comp (Primrec.list_append.comp hids hlbl)

theorem primrec_allIds : Primrec PNet.allIds :=
  Primrec.list_map Primrec.id (Primrec₂.mk (Primrec.fst.comp Primrec.snd))

theorem primrec_pIds : Primrec PNet.ids := by
  have hfil : Primrec fun p : PNet => p.filter fun x => x.2.2.1 :=
    primrec_filterB Primrec.id
      (Primrec₂.mk (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec.list_map hfil (Primrec₂.mk (Primrec.fst.comp Primrec.snd))

theorem primrec_deps : Primrec fun w : PNet × ℕ => w.1.deps w.2 := by
  have h : Primrec₂ fun (w : PNet × ℕ) (z : PItem × List ℕ) =>
      if z.1.1 = w.2 then z.1.2.2.2 else z.2 := by
    refine Primrec₂.mk (Primrec.ite ?_
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd))
    exact PrimrecRel.comp Primrec.eq (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.list_foldr Primrec.fst (Primrec.const ([] : List ℕ)) h).of_eq fun _ => rfl

theorem primrec_freshOff : Primrec PNet.freshOff :=
  Primrec.succ.comp (primrec_foldrMax primrec_allIds)

theorem primrec_ofTnDesc : Primrec PNet.ofTnDesc := by
  have hitem : Primrec₂ fun (t : TnDesc) (x : ℕ) =>
      ((x, t.lblPair x, memB t.ids x,
        t.ids.dedup.filter fun y => TnDesc.ordB t y x) : PItem) := by
    have ht : Primrec fun w : TnDesc × ℕ => w.1 := Primrec.fst
    have hx : Primrec fun w : TnDesc × ℕ => w.2 := Primrec.snd
    have hlp := primrec_lblPair
    have hmem := primrec_memB.comp (primrec_ids.comp ht) hx
    have hded := Ac.primrec_dedup.comp (primrec_ids.comp ht)
    have hfil : Primrec fun w : TnDesc × ℕ =>
        w.1.ids.dedup.filter fun y => TnDesc.ordB w.1 y w.2 := by
      refine primrec_filterB hded (Primrec₂.mk ?_)
      exact TnDesc.primrec_ordB.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))
    exact Primrec₂.mk (Primrec.pair hx (Primrec.pair hlp (Primrec.pair hmem hfil)))
  exact (Primrec.list_map primrec_keysOf hitem).of_eq fun _ => rfl

/-- Removing one value from a list is primitive recursive. -/
theorem primrec_filterNe {α : Type} [Primcodable α] {f : α → List ℕ} {g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun x => (f x).filter fun y => y ≠ g x := by
  have h : Primrec₂ fun (x : α) (y : ℕ) => if y = g x then false else true :=
    Primrec₂.mk (Primrec.ite
      (PrimrecRel.comp Primrec.eq Primrec.snd (hg.comp Primrec.fst))
      (Primrec.const false) (Primrec.const true))
  refine (primrec_filterB hf h).of_eq fun x => ?_
  have hfun : (fun y : ℕ => if y = g x then false else true) = fun y : ℕ => decide (y ≠ g x) := by
    funext y
    by_cases hy : y = g x <;> simp [hy]
  rw [hfun]

/-! ### The two operations -/

theorem primrec_finish : Primrec fun w : PNet × ℕ => w.1.finish w.2 := by
  have hbody : Primrec₂ fun (w : PNet × ℕ) (x : PItem) =>
      (if x.1 = w.2 then (x.1, x.2.1, false, ([] : List ℕ))
        else (x.1, x.2.1, x.2.2.1, x.2.2.2.filter fun y => y ≠ w.2) : PItem) := by
    have hid : Primrec fun v : (PNet × ℕ) × PItem => v.2.1 := Primrec.fst.comp Primrec.snd
    have hlbl : Primrec fun v : (PNet × ℕ) × PItem => v.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hpres : Primrec fun v : (PNet × ℕ) × PItem => v.2.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hdep : Primrec fun v : (PNet × ℕ) × PItem => v.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hi : Primrec fun v : (PNet × ℕ) × PItem => v.1.2 := Primrec.snd.comp Primrec.fst
    have hfil := primrec_filterNe hdep hi
    refine Primrec₂.mk (Primrec.ite (PrimrecRel.comp Primrec.eq hid hi)
      (Primrec.pair hid (Primrec.pair hlbl (Primrec.pair (Primrec.const false)
        (Primrec.const ([] : List ℕ)))))
      (Primrec.pair hid (Primrec.pair hlbl (Primrec.pair hpres hfil))))
  exact (Primrec.list_map Primrec.fst hbody).of_eq fun _ => rfl

theorem primrec_newIds : Primrec fun w : PNet × MethodDesc => w.1.newIds w.2 := by
  have hded : Primrec fun w : PNet × MethodDesc => w.2.2.ids.dedup :=
    Ac.primrec_dedup.comp (primrec_ids.comp (Primrec.snd.comp Primrec.snd))
  have hbody : Primrec₂ fun (w : PNet × MethodDesc) (x : ℕ) => w.1.freshOff + x :=
    Primrec₂.mk (Primrec.nat_add.comp (primrec_freshOff.comp (Primrec.fst.comp Primrec.fst))
      Primrec.snd)
  exact (Primrec.list_map hded hbody).of_eq fun _ => rfl

theorem primrec_substDep :
    Primrec fun w : (ℕ × List ℕ) × List ℕ => PNet.substDep w.1.1 w.1.2 w.2 := by
  have hbody : Primrec₂ fun (w : (ℕ × List ℕ) × List ℕ) (y : ℕ) =>
      if y = w.1.1 then w.1.2 else [y] := by
    refine Primrec₂.mk (Primrec.ite ?_ (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ))))
    exact PrimrecRel.comp Primrec.eq Primrec.snd
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  exact (Primrec.list_flatMap Primrec.snd hbody).of_eq fun _ => rfl

theorem primrec_newItems :
    Primrec fun w : PNet × ℕ × MethodDesc => PNet.newItems w.1 w.2.1 w.2.2 := by
  have hded : Primrec fun w : PNet × ℕ × MethodDesc => w.2.2.2.ids.dedup :=
    Ac.primrec_dedup.comp (primrec_ids.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hbody : Primrec₂ fun (w : PNet × ℕ × MethodDesc) (x : ℕ) =>
      ((w.1.freshOff + x, w.2.2.2.lblPair x, true,
        w.1.deps w.2.1 ++ (w.2.2.2.ids.dedup.filter fun y => TnDesc.ordB w.2.2.2 y x).map
          fun y => w.1.freshOff + y) : PItem) := by
    have hp : Primrec fun v : (PNet × ℕ × MethodDesc) × ℕ => v.1.1 :=
      Primrec.fst.comp Primrec.fst
    have ht : Primrec fun v : (PNet × ℕ × MethodDesc) × ℕ => v.1.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hx : Primrec fun v : (PNet × ℕ × MethodDesc) × ℕ => v.2 := Primrec.snd
    have hfresh := primrec_freshOff.comp hp
    have hnew := Primrec.nat_add.comp hfresh hx
    have hlp := primrec_lblPair.comp (Primrec.pair ht hx)
    have hdeps := primrec_deps.comp (Primrec.pair hp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    have hdedv : Primrec fun v : (PNet × ℕ × MethodDesc) × ℕ => v.1.2.2.2.ids.dedup :=
      Ac.primrec_dedup.comp (primrec_ids.comp ht)
    have hfil : Primrec fun v : (PNet × ℕ × MethodDesc) × ℕ =>
        v.1.2.2.2.ids.dedup.filter fun y => TnDesc.ordB v.1.2.2.2 y v.2 := by
      refine primrec_filterB hdedv (Primrec₂.mk ?_)
      exact TnDesc.primrec_ordB.comp (Primrec.pair (ht.comp Primrec.fst)
        (Primrec.pair Primrec.snd (hx.comp Primrec.fst)))
    have hshift : Primrec fun v : (PNet × ℕ × MethodDesc) × ℕ =>
        (v.1.2.2.2.ids.dedup.filter fun y => TnDesc.ordB v.1.2.2.2 y v.2).map
          fun y => v.1.1.freshOff + y := by
      refine Primrec.list_map hfil (Primrec₂.mk ?_)
      exact Primrec.nat_add.comp (hfresh.comp Primrec.fst) Primrec.snd
    exact Primrec₂.mk (Primrec.pair hnew (Primrec.pair hlp (Primrec.pair (Primrec.const true)
      (Primrec.list_append.comp hdeps hshift))))
  exact (Primrec.list_map hded hbody).of_eq fun _ => rfl

theorem primrec_oldItems :
    Primrec fun w : PNet × ℕ × MethodDesc => PNet.oldItems w.1 w.2.1 w.2.2 := by
  have hbody : Primrec₂ fun (w : PNet × ℕ × MethodDesc) (x : PItem) =>
      (if x.1 = w.2.1 then (x.1, x.2.1, false, ([] : List ℕ))
        else (x.1, x.2.1, x.2.2.1, PNet.substDep w.2.1 (w.1.newIds w.2.2) x.2.2.2) : PItem) := by
    have hid : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem => v.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hlbl : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem => v.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hpres : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem => v.2.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hdep : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem => v.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hi : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem => v.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hpn : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem => v.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hme : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem => v.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hnew : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem => PNet.newIds v.1.1 v.1.2.2 :=
      primrec_newIds.comp (Primrec.pair hpn hme)
    have hsub : Primrec fun v : (PNet × ℕ × MethodDesc) × PItem =>
        PNet.substDep v.1.2.1 (PNet.newIds v.1.1 v.1.2.2) v.2.2.2.2 :=
      primrec_substDep.comp (Primrec.pair (Primrec.pair hi hnew) hdep)
    refine Primrec₂.mk (Primrec.ite (PrimrecRel.comp Primrec.eq hid hi)
      (Primrec.pair hid (Primrec.pair hlbl (Primrec.pair (Primrec.const false)
        (Primrec.const ([] : List ℕ)))))
      (Primrec.pair hid (Primrec.pair hlbl (Primrec.pair hpres hsub))))
  exact (Primrec.list_map Primrec.fst hbody).of_eq fun _ => rfl

theorem primrec_expand :
    Primrec fun w : PNet × ℕ × MethodDesc => PNet.expand w.1 w.2.1 w.2.2 :=
  Primrec.list_append.comp primrec_oldItems primrec_newItems

/-! ### The search space -/

theorem primrec_readyItems : Primrec readyItems := by
  refine primrec_filterB Primrec.id (Primrec₂.mk ?_)
  have hpres : Primrec fun v : PNet × PItem => v.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hdep : Primrec fun v : PNet × PItem => v.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.and.comp hpres (DomDesc.primrec_isEmptyList.comp hdep)

/-- The listed methods for a compound name. -/
theorem primrec_methodsFor :
    Primrec fun w : DomDesc × ℕ => w.1.methods.filter fun e => e.1 = w.2 := by
  have h : Primrec₂ fun (w : DomDesc × ℕ) (e : MethodDesc) =>
      if e.1 = w.2 then true else false := by
    refine Primrec₂.mk (Primrec.ite ?_ (Primrec.const true) (Primrec.const false))
    exact PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  refine (primrec_filterB (primrec_methods.comp Primrec.fst) h).of_eq fun w => ?_
  have hfun : (fun e : MethodDesc => if e.1 = w.2 then true else false) =
      fun e : MethodDesc => decide (e.1 = w.2) := by
    funext e
    by_cases he : e.1 = w.2 <;> simp [he]
  rw [hfun]

set_option maxHeartbeats 2000000 in
theorem primrec_succsOf : Primrec fun w : DomDesc × PConfig => succsOf w.1 w.2 := by
  have hbody : Primrec₂ fun (w : DomDesc × PConfig) (x : PItem) =>
      (if x.2.1.1 then
          (w.1.methods.filter fun e => e.1 = x.2.1.2).map fun e =>
            ((w.2.1, PNet.expand w.2.2 x.1 e) : PConfig)
        else if applB w.1 w.2.1 x.2.1.2 then
          [((stepL w.1 w.2.1 x.2.1.2, PNet.finish w.2.2 x.1) : PConfig)]
        else []) := by
    have hd : Primrec fun v : (DomDesc × PConfig) × PItem => v.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hst : Primrec fun v : (DomDesc × PConfig) × PItem => v.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hnet : Primrec fun v : (DomDesc × PConfig) × PItem => v.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hid : Primrec fun v : (DomDesc × PConfig) × PItem => v.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hkind : Primrec fun v : (DomDesc × PConfig) × PItem => v.2.2.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have hname : Primrec fun v : (DomDesc × PConfig) × PItem => v.2.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have hmeths : Primrec fun v : (DomDesc × PConfig) × PItem =>
        v.1.1.methods.filter fun e => e.1 = v.2.2.1.2 :=
      primrec_methodsFor.comp (Primrec.pair hd hname)
    have hdec : Primrec fun v : (DomDesc × PConfig) × PItem =>
        (v.1.1.methods.filter fun e => e.1 = v.2.2.1.2).map fun e =>
          ((v.1.2.1, PNet.expand v.1.2.2 v.2.1 e) : PConfig) := by
      refine Primrec.list_map hmeths (Primrec₂.mk ?_)
      have hexp : Primrec fun u : ((DomDesc × PConfig) × PItem) × MethodDesc =>
          PNet.expand u.1.1.2.2 u.1.2.1 u.2 :=
        primrec_expand.comp (Primrec.pair (hnet.comp Primrec.fst)
          (Primrec.pair (hid.comp Primrec.fst) Primrec.snd))
      exact Primrec.pair (hst.comp Primrec.fst) hexp
    have happ : Primrec fun v : (DomDesc × PConfig) × PItem => applB v.1.1 v.1.2.1 v.2.2.1.2 :=
      primrec_applB.comp (Primrec.pair hd hst) hname
    have hstep : Primrec fun v : (DomDesc × PConfig) × PItem => stepL v.1.1 v.1.2.1 v.2.2.1.2 :=
      primrec_stepL.comp (Primrec.pair hd hst) hname
    have hfin : Primrec fun v : (DomDesc × PConfig) × PItem => PNet.finish v.1.2.2 v.2.1 :=
      primrec_finish.comp (Primrec.pair hnet hid)
    have hexec : Primrec fun v : (DomDesc × PConfig) × PItem =>
        [((stepL v.1.1 v.1.2.1 v.2.2.1.2, PNet.finish v.1.2.2 v.2.1) : PConfig)] :=
      Primrec.list_cons.comp (Primrec.pair hstep hfin) (Primrec.const ([] : List PConfig))
    refine Primrec₂.mk (Primrec.ite (PrimrecRel.comp Primrec.eq hkind (Primrec.const true)) hdec
      (Primrec.ite (PrimrecRel.comp Primrec.eq happ (Primrec.const true)) hexec
        (Primrec.const ([] : List PConfig))))
  exact (Primrec.list_flatMap (primrec_readyItems.comp (Primrec.snd.comp Primrec.snd)) hbody).of_eq
    fun _ => rfl

theorem primrec_initConfig : Primrec initConfig :=
  Primrec.pair primrec_initList (primrec_ofTnDesc.comp primrec_tnI)

theorem primrec_isGoalB : Primrec fun w : InstDesc × PConfig => isGoalB w.1 w.2 := by
  have hempty : Primrec fun w : InstDesc × PConfig => w.2.2.ids.isEmpty :=
    DomDesc.primrec_isEmptyList.comp (primrec_pIds.comp (Primrec.snd.comp Primrec.snd))
  have hall : Primrec fun w : InstDesc × PConfig => w.1.goalList.all fun f => memB w.2.1 f := by
    refine primrec_allB (primrec_goalList.comp Primrec.fst) (Primrec₂.mk ?_)
    exact primrec_memB.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  exact Primrec.and.comp hempty hall

/-! ### The measure -/

theorem compEdges_eq (d : DomDesc) :
    compEdges d = d.methods.flatMap fun e =>
      e.2.ids.dedup.filterMap fun x =>
        if (e.2.lblPair x).1 then some (e.1, (e.2.lblPair x).2) else none := by
  unfold compEdges
  congr 1
  funext e
  congr 1
  funext x
  rw [← TnDesc.ofPair_lblPair]
  rcases h : e.2.lblPair x with ⟨b, n⟩
  cases b <;> simp [TnDesc.ofPair]

theorem primrec_compEdges : Primrec compEdges := by
  have hbody : Primrec₂ fun (d : DomDesc) (e : MethodDesc) =>
      e.2.ids.dedup.filterMap fun x =>
        if (e.2.lblPair x).1 then some (e.1, (e.2.lblPair x).2) else none := by
    have hded : Primrec fun v : DomDesc × MethodDesc => v.2.2.ids.dedup :=
      Ac.primrec_dedup.comp (primrec_ids.comp (Primrec.snd.comp Primrec.snd))
    refine Primrec₂.mk (Primrec.listFilterMap hded (Primrec₂.mk ?_))
    have ht : Primrec fun u : (DomDesc × MethodDesc) × ℕ => u.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hlp : Primrec fun u : (DomDesc × MethodDesc) × ℕ => u.1.2.2.lblPair u.2 :=
      primrec_lblPair.comp (Primrec.pair ht Primrec.snd)
    have hname : Primrec fun u : (DomDesc × MethodDesc) × ℕ => u.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    refine Primrec.ite (PrimrecRel.comp Primrec.eq (Primrec.fst.comp hlp) (Primrec.const true))
      (Primrec.option_some.comp (Primrec.pair hname (Primrec.snd.comp hlp)))
      (Primrec.const none)
  exact (Primrec.list_flatMap primrec_methods hbody).of_eq fun d => (compEdges_eq d).symm

theorem primrec_graphNames : Primrec compNames := by
  refine Primrec.list_flatMap primrec_compEdges (Primrec₂.mk ?_)
  exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const ([] : List ℕ)))

theorem primrec_rkD : Primrec fun w : DomDesc × ℕ => rkD w.1 w.2 := by
  have hded : Primrec fun w : DomDesc × ℕ => (compNames w.1).dedup :=
    Ac.primrec_dedup.comp (primrec_graphNames.comp Primrec.fst)
  have hfil : Primrec fun w : DomDesc × ℕ =>
      (compNames w.1).dedup.filter fun c' => reachB (compEdges w.1) w.2 c' := by
    refine primrec_filterB hded (Primrec₂.mk ?_)
    exact primrec_reachB.comp
      (Primrec.pair (primrec_compEdges.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)) Primrec.snd
  exact Primrec.list_length.comp hfil

theorem primrec_maxBody : Primrec maxBody := by
  refine primrec_foldrMax (Primrec.list_map primrec_methods (Primrec₂.mk ?_))
  exact Primrec.list_length.comp
    (Ac.primrec_dedup.comp (primrec_ids.comp (Primrec.snd.comp Primrec.snd)))

theorem primrec_wOf : Primrec fun w : DomDesc × Bool × ℕ => wOf w.1 w.2 := by
  have hd : Primrec fun w : DomDesc × Bool × ℕ => w.1 := Primrec.fst
  have hk : Primrec fun w : DomDesc × Bool × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hn : Primrec fun w : DomDesc × Bool × ℕ => w.2.2 := Primrec.snd.comp Primrec.snd
  have hbase : Primrec fun w : DomDesc × Bool × ℕ => maxBody w.1 + 1 :=
    Primrec.succ.comp (primrec_maxBody.comp hd)
  have hexp : Primrec fun w : DomDesc × Bool × ℕ => rkD w.1 w.2.2 + 1 :=
    Primrec.succ.comp (primrec_rkD.comp (Primrec.pair hd hn))
  exact Primrec.ite (PrimrecRel.comp Primrec.eq hk (Primrec.const true))
    (primrec_pow.comp hbase hexp) (Primrec.const 1)

theorem primrec_phi : Primrec fun w : DomDesc × PNet => phi w.1 w.2 := by
  have hbody : Primrec₂ fun (w : DomDesc × PNet) (x : PItem) =>
      if x.2.2.1 then wOf w.1 x.2.1 else 0 := by
    have hpres : Primrec fun v : (DomDesc × PNet) × PItem => v.2.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hw : Primrec fun v : (DomDesc × PNet) × PItem => wOf v.1.1 v.2.2.1 :=
      primrec_wOf.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    exact Primrec₂.mk (Primrec.ite (PrimrecRel.comp Primrec.eq hpres (Primrec.const true)) hw
      (Primrec.const 0))
  exact primrec_natSum.comp (Primrec.list_map Primrec.snd hbody)

/-! ### The decision procedure -/

theorem bfs_eq_rec (d : DomDesc) (c₀ : PConfig) (n : ℕ) :
    Nat.rec [c₀] (fun (_ : ℕ) (IH : List PConfig) => IH ++ IH.flatMap (succsOf d)) n
      = bfs d c₀ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show _ ++ List.flatMap _ _ = _
    rw [ih]
    rfl

theorem primrec_bfs : Primrec fun w : (DomDesc × PConfig) × ℕ => bfs w.1.1 w.1.2 w.2 := by
  have hstart : Primrec fun a : DomDesc × PConfig => [a.2] :=
    Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List PConfig))
  have hstep : Primrec₂ fun (a : DomDesc × PConfig) (z : ℕ × List PConfig) =>
      z.2 ++ z.2.flatMap (succsOf a.1) := by
    have hlist : Primrec fun v : (DomDesc × PConfig) × (ℕ × List PConfig) => v.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hfm : Primrec fun v : (DomDesc × PConfig) × (ℕ × List PConfig) =>
        v.2.2.flatMap (succsOf v.1.1) := by
      refine Primrec.list_flatMap hlist (Primrec₂.mk ?_)
      exact primrec_succsOf.comp (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
    exact Primrec₂.mk (Primrec.list_append.comp hlist hfm)
  have h := Primrec.nat_rec hstart hstep
  refine (h.comp Primrec.fst Primrec.snd).of_eq fun w => ?_
  exact bfs_eq_rec w.1.1 w.1.2 w.2

set_option maxHeartbeats 2000000 in
theorem primrec_acSolvableB : Primrec₂ acSolvableB := by
  have hinit : Primrec fun p : DomDesc × InstDesc => initConfig p.2 :=
    primrec_initConfig.comp Primrec.snd
  have hphi : Primrec fun p : DomDesc × InstDesc => phi p.1 (initConfig p.2).2 :=
    primrec_phi.comp (Primrec.pair Primrec.fst (Primrec.snd.comp hinit))
  have hbfs : Primrec fun p : DomDesc × InstDesc =>
      bfs p.1 (initConfig p.2) (phi p.1 (initConfig p.2).2) :=
    primrec_bfs.comp (Primrec.pair (Primrec.pair Primrec.fst hinit) hphi)
  have hgoal : Primrec₂ fun (p : DomDesc × InstDesc) (c : PConfig) => isGoalB p.2 c :=
    Primrec₂.mk (primrec_isGoalB.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact Primrec₂.mk (primrec_anyB hbfs hgoal)

/-! ### Sanity checks

Two **partially ordered** instances of an acyclic hierarchy.  The first one has a single method
splitting the compound task `0` into two unordered actions; both effects are needed, and the
problem is solvable exactly when the goal asks for no more than that.

The second one is the characteristic partially ordered situation: two unordered compound tasks,
each with a *totally ordered* method, whose refinements have to be **interleaved**
(`a₁ a₂ a₃ a₄` with `a₁, a₃` from the first and `a₂, a₄` from the second).  It is solvable, and
becomes unsolvable as soon as the two compound tasks are ordered. -/

/-- `c₀ ↦ {a₁, a₂}` unordered, with `a₁` adding the fact `0` and `a₂` the fact `1`. -/
def exAcDom : DomDesc :=
  ([(1, [], [0], []), (2, [], [1], [])],
   [(0, ([0, 1], [], [(0, false, 1), (1, false, 2)]))])

/-- The instance: goal `{0, 1}`, the single compound task `c₀`. -/
def exAcInst : InstDesc := ([], [0, 1], ([0], [], [(0, true, 0)]))

/-- The same instance with the unreachable goal `{0, 1, 2}`. -/
def exAcInstBad : InstDesc := ([], [0, 1, 2], ([0], [], [(0, true, 0)]))

example : acSolvableB exAcDom exAcInst = true := by decide

example : acSolvableB exAcDom exAcInstBad = false := by decide

/-- `c₀ ↦ a₁ a₃` and `c₁ ↦ a₂ a₄`, where each action needs the effect of the previous one in the
order `a₁ a₂ a₃ a₄`. -/
def exPoDom : DomDesc :=
  ([(1, [], [0], []), (2, [0], [1], []), (3, [1], [2], []), (4, [2], [3], [])],
   [(0, ([0, 1], [(0, 1)], [(0, false, 1), (1, false, 3)])),
    (1, ([0, 1], [(0, 1)], [(0, false, 2), (1, false, 4)]))])

/-- The instance: goal `{3}`, the two compound tasks unordered. -/
def exPoInst : InstDesc := ([], [3], ([0, 1], [], [(0, true, 0), (1, true, 1)]))

/-- The same instance with the two compound tasks ordered, which forbids the interleaving. -/
def exPoInstSeq : InstDesc := ([], [3], ([0, 1], [(0, 1)], [(0, true, 0), (1, true, 1)]))

set_option maxRecDepth 10000 in
example : acSolvableB exPoDom exPoInst = true := by decide

set_option maxRecDepth 10000 in
example : acSolvableB exPoDom exPoInstSeq = false := by decide

/-! ### The decider -/

/-- **Plan existence is decidable for the class `HTN-AC`** — for an arbitrary *partially ordered*
initial task network, and with no restriction on the methods beyond acyclicity of the hierarchy.
The decision procedure is the bounded progression search of `Computable/AcDecide.lean`, and it is
primitive recursive. -/
theorem decider_HTN_AC : SynClass.HTN_AC.Decider :=
  ⟨acSolvableB, primrec_acSolvableB.to_comp, fun _ _ hd _ => acSolvableB_iff hd⟩

end Syn

end HTN
