import HtnComplexity.Computable.ToDecide
import HtnComplexity.Computable.Decider
/-!
# The decision procedure for `TO-HTN` is primitive recursive

`HtnComplexity/Computable/ToDecide.lean` builds the saturation `HTN.Syn.ToDec.toSolvableB`
and proves that it decides plan existence for described totally ordered HTN problems.  This file
shows that it is primitive recursive and packages it as

`HTN.Syn.decider_TO_HTN : HTN.Syn.SynClass.TO_HTN.Decider`,

which discharges the decidability hypothesis of the cell (`HTN`, `TO-HTN`) of the compilability
table.
-/

namespace HTN

namespace Syn

namespace ToDec

open Primrec

/-! ### Auxiliary shapes -/

/-- The parameters of the propagation: the domain description, the relevant facts and the
current triples. -/
abbrev Par : Type := DomDesc × List ℕ × List Trip

/-- The argument of `succTask`, packed. -/
abbrev ArgTask : Type := Par × (List ℕ × (ℕ ⊕ ℕ))

/-- The argument of `succBody`, packed. -/
abbrev ArgBody : Type := Par × (List (List ℕ) × List (ℕ ⊕ ℕ))

/-- The argument of `stepR`, packed. -/
abbrev ArgStep : Type := (DomDesc × List ℕ) × List Trip

theorem filter_eq_filterMap {α : Type} (p : α → Bool) (L : List α) :
    L.filter p = L.filterMap fun x => if p x then some x else none := by
  induction L with
  | nil => rfl
  | cons x xs ih => by_cases h : p x <;> simp [h, ih]

theorem subsets_eq_foldr (U : List ℕ) :
    subsets U = U.foldr (fun f ss => ss ++ ss.map fun l => f :: l) [[]] := by
  induction U with
  | nil => rfl
  | cons f U ih => rw [subsets, ih, List.foldr_cons]

/-! ### The pieces of the computation are primitive recursive -/

theorem primrec_subsets : Primrec subsets := by
  have h : Primrec₂ (fun (_ : List ℕ) (z : ℕ × List (List ℕ)) =>
      z.2 ++ z.2.map fun l => z.1 :: l) := by
    have hmap : Primrec (fun w : List ℕ × (ℕ × List (List ℕ)) =>
        w.2.2.map fun l => w.2.1 :: l) := by
      refine list_map (Primrec.snd.comp Primrec.snd) ?_
      exact Primrec₂.mk (list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
    exact Primrec₂.mk (list_append.comp (Primrec.snd.comp Primrec.snd) hmap)
  refine (list_foldr Primrec.id (Primrec.const [[]]) h).of_eq fun U => ?_
  rw [subsets_eq_foldr]
  rfl

theorem primrec_nrm : Primrec₂ nrm := by
  have h : Primrec₂ (fun (w : List ℕ × List ℕ) (f : ℕ) =>
      if memB w.2 f then some f else none) := by
    refine Primrec₂.mk (Primrec.ite ?_ (option_some.comp Primrec.snd) (Primrec.const none))
    exact PrimrecRel.comp Primrec.eq
      (primrec_memB.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const true)
  refine Primrec₂.mk ((listFilterMap Primrec.fst h).of_eq fun w => ?_)
  rw [nrm, filter_eq_filterMap]

theorem primrec_memT : Primrec₂ memT := by
  have h : Primrec₂ (fun (w : List Trip × Trip) (z : Trip × Bool) =>
      if z.1 = w.2 then true else z.2) := by
    refine Primrec₂.mk (Primrec.ite ?_ (Primrec.const true) (Primrec.snd.comp Primrec.snd))
    exact PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  exact Primrec₂.mk (list_foldr Primrec.fst (Primrec.const false) h)

set_option maxHeartbeats 1000000 in
theorem primrec_succTask :
    Primrec fun w : ArgTask => succTask w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2 := by
  have hprim : Primrec₂ (fun (w : ArgTask) (a : ℕ) =>
      if applB w.1.1 w.2.1 a then [nrm w.1.2.1 (stepL w.1.1 w.2.1 a)] else []) := by
    have hd : Primrec (fun v : ArgTask × ℕ => v.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hfacts : Primrec (fun v : ArgTask × ℕ => v.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hl : Primrec (fun v : ArgTask × ℕ => v.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hpair := Primrec.pair hd hl
    have happ := primrec_applB.comp hpair Primrec.snd
    have hstep := primrec_stepL.comp hpair Primrec.snd
    have hnrm := primrec_nrm.comp hfacts hstep
    have hstate := list_cons.comp hnrm (Primrec.const ([] : List (List ℕ)))
    refine Primrec₂.mk (Primrec.ite ?_ hstate (Primrec.const []))
    exact PrimrecRel.comp Primrec.eq happ (Primrec.const true)
  have hcomp : Primrec₂ (fun (w : ArgTask) (c : ℕ) =>
      (subsets w.1.2.1).filter fun l' => memT w.1.2.2 (c, w.2.1, l')) := by
    have hfacts : Primrec (fun v : ArgTask × ℕ => v.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hsub := primrec_subsets.comp hfacts
    have hR : Primrec (fun u : (ArgTask × ℕ) × List ℕ => u.1.1.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hc : Primrec (fun u : (ArgTask × ℕ) × List ℕ => u.1.2) := Primrec.snd.comp Primrec.fst
    have hstate : Primrec (fun u : (ArgTask × ℕ) × List ℕ => u.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hnew : Primrec (fun u : (ArgTask × ℕ) × List ℕ => u.2) := Primrec.snd
    have htrip := Primrec.pair hc (Primrec.pair hstate hnew)
    have hm := primrec_memT.comp hR htrip
    have hmem : Primrec₂ (fun (v : ArgTask × ℕ) (l' : List ℕ) =>
        if memT v.1.1.2.2 (v.2, v.1.2.1, l') then some l' else none) := by
      refine Primrec₂.mk (Primrec.ite ?_ (option_some.comp Primrec.snd) (Primrec.const none))
      exact PrimrecRel.comp Primrec.eq hm (Primrec.const true)
    refine Primrec₂.mk ((listFilterMap hsub hmem).of_eq fun v => ?_)
    rw [filter_eq_filterMap]
  refine (Primrec.sumCasesOn (f := fun w : ArgTask => w.2.2)
    (g := fun w a => if applB w.1.1 w.2.1 a then [nrm w.1.2.1 (stepL w.1.1 w.2.1 a)] else [])
    (h := fun w c => (subsets w.1.2.1).filter fun l' => memT w.1.2.2 (c, w.2.1, l'))
    (Primrec.snd.comp Primrec.snd) hprim hcomp).of_eq fun w => ?_
  cases w.2.2 with
  | inl a => simp [succTask]
  | inr c => simp [succTask]

set_option maxHeartbeats 1000000 in
theorem primrec_succBody :
    Primrec fun w : ArgBody => succBody w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2 := by
  have hstep : Primrec₂ (fun (w : ArgBody) (z : List (List ℕ) × (ℕ ⊕ ℕ)) =>
      z.1.flatMap fun l => succTask w.1.1 w.1.2.1 w.1.2.2 l z.2) := by
    have hpar : Primrec (fun u : (ArgBody × (List (List ℕ) × (ℕ ⊕ ℕ))) × List ℕ =>
        u.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hl : Primrec (fun u : (ArgBody × (List (List ℕ) × (ℕ ⊕ ℕ))) × List ℕ => u.2) :=
      Primrec.snd
    have hx : Primrec (fun u : (ArgBody × (List (List ℕ) × (ℕ ⊕ ℕ))) × List ℕ => u.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have harg := Primrec.pair hpar (Primrec.pair hl hx)
    have hinner := primrec_succTask.comp harg
    have hls : Primrec (fun v : ArgBody × (List (List ℕ) × (ℕ ⊕ ℕ)) => v.2.1) :=
      Primrec.fst.comp Primrec.snd
    exact Primrec₂.mk (list_flatMap hls (Primrec₂.mk hinner))
  refine (list_foldl (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd) hstep).of_eq
    fun w => ?_
  rw [succBody]

set_option maxHeartbeats 1000000 in
theorem primrec_stepR : Primrec fun w : ArgStep => stepR w.1.1 w.1.2 w.2 := by
  have hbody : Primrec₂ (fun (v : ArgStep × MethodDesc) (l : List ℕ) =>
      (succBody v.1.1.1 v.1.1.2 v.1.2 [l] (TnDesc.seqBody v.2.2)).map
        fun l' => ((v.2.1, l, l') : Trip)) := by
    have hdom : Primrec (fun u : (ArgStep × MethodDesc) × List ℕ => u.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hfacts : Primrec (fun u : (ArgStep × MethodDesc) × List ℕ => u.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have htrips : Primrec (fun u : (ArgStep × MethodDesc) × List ℕ => u.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hpar := Primrec.pair hdom (Primrec.pair hfacts htrips)
    have hstart := list_cons.comp (show Primrec (fun u : (ArgStep × MethodDesc) × List ℕ => u.2)
      from Primrec.snd) (Primrec.const ([] : List (List ℕ)))
    have hseq := DomDesc.primrec_seqBody.comp
      (show Primrec (fun u : (ArgStep × MethodDesc) × List ℕ => u.1.2.2) from
        Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    have hsucc := primrec_succBody.comp (Primrec.pair hpar (Primrec.pair hstart hseq))
    have hname : Primrec (fun u : (ArgStep × MethodDesc) × List ℕ => u.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hl : Primrec (fun u : (ArgStep × MethodDesc) × List ℕ => u.2) := Primrec.snd
    have htrip : Primrec₂ (fun (u : (ArgStep × MethodDesc) × List ℕ) (l' : List ℕ) =>
        ((u.1.2.1, u.2, l') : Trip)) :=
      Primrec₂.mk (Primrec.pair (hname.comp Primrec.fst)
        (Primrec.pair (hl.comp Primrec.fst) Primrec.snd))
    exact Primrec₂.mk (list_map hsucc htrip)
  have hmeth : Primrec₂ (fun (w : ArgStep) (e : MethodDesc) =>
      (subsets w.1.2).flatMap fun l =>
        (succBody w.1.1 w.1.2 w.2 [l] (TnDesc.seqBody e.2)).map
          fun l' => ((e.1, l, l') : Trip)) := by
    have hsub := primrec_subsets.comp
      (show Primrec (fun v : ArgStep × MethodDesc => v.1.1.2) from
        Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    exact Primrec₂.mk (list_flatMap hsub hbody)
  have hmethods := primrec_methods.comp
    (show Primrec (fun w : ArgStep => w.1.1) from Primrec.fst.comp Primrec.fst)
  have hall := list_flatMap hmethods hmeth
  exact list_append.comp Primrec.snd hall

theorem primrec_iterR : Primrec₂ fun (p : DomDesc × List ℕ) (n : ℕ) => iterR p.1 p.2 n := by
  have hstep : Primrec₂ (fun (p : DomDesc × List ℕ) (z : ℕ × List Trip) =>
      stepR p.1 p.2 z.2) :=
    Primrec₂.mk (primrec_stepR.comp (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)))
  refine Primrec₂.of_eq (Primrec.nat_rec (Primrec.const ([] : List Trip)) hstep) ?_
  intro p n
  induction n with
  | zero => rfl
  | succ n ih => simpa [iterR] using congrArg (stepR p.1 p.2) ih

set_option maxHeartbeats 1000000 in
theorem primrec_allTrips : Primrec₂ allTrips := by
  have hmeth : Primrec₂ (fun (w : DomDesc × List ℕ) (e : MethodDesc) =>
      (subsets w.2).flatMap fun l => (subsets w.2).map fun l' => ((e.1, l, l') : Trip)) := by
    have hinner : Primrec₂ (fun (v : (DomDesc × List ℕ) × MethodDesc) (l : List ℕ) =>
        (subsets v.1.2).map fun l' => ((v.2.1, l, l') : Trip)) := by
      have hsub := primrec_subsets.comp
        (show Primrec (fun u : ((DomDesc × List ℕ) × MethodDesc) × List ℕ => u.1.1.2) from
          Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      have htrip : Primrec₂ (fun (u : ((DomDesc × List ℕ) × MethodDesc) × List ℕ)
          (l' : List ℕ) => ((u.1.2.1, u.2, l') : Trip)) :=
        Primrec₂.mk (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
      exact Primrec₂.mk (list_map hsub htrip)
    have hsub := primrec_subsets.comp
      (show Primrec (fun v : (DomDesc × List ℕ) × MethodDesc => v.1.2) from
        Primrec.snd.comp Primrec.fst)
    exact Primrec₂.mk (list_flatMap hsub hinner)
  exact Primrec₂.mk (list_flatMap (primrec_methods.comp Primrec.fst) hmeth)

theorem primrec_satR : Primrec₂ satR := by
  have hlen := list_length.comp (primrec_allTrips.comp Primrec.fst Primrec.snd)
  have h := primrec_iterR.comp (Primrec.pair Primrec.fst Primrec.snd) (Primrec.succ.comp hlen)
  exact Primrec₂.mk h

theorem primrec_facts : Primrec₂ facts := by
  have hacts : Primrec (fun p : DomDesc × InstDesc =>
      p.1.actions.flatMap fun a => a.2.1) := by
    refine list_flatMap (primrec_actions.comp Primrec.fst) ?_
    exact Primrec₂.mk (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec₂.mk (list_append.comp (primrec_goalList.comp Primrec.snd) hacts)

set_option maxHeartbeats 1000000 in
theorem primrec_toSolvableB : Primrec₂ toSolvableB := by
  have hfacts := primrec_facts.comp
    (show Primrec (fun p : DomDesc × InstDesc => p.1) from Primrec.fst)
    (show Primrec (fun p : DomDesc × InstDesc => p.2) from Primrec.snd)
  have hsat := primrec_satR.comp
    (show Primrec (fun p : DomDesc × InstDesc => p.1) from Primrec.fst) hfacts
  have hstart := list_cons.comp
    (primrec_nrm.comp hfacts (primrec_initList.comp Primrec.snd))
    (Primrec.const ([] : List (List ℕ)))
  have hseq := DomDesc.primrec_seqBody.comp (primrec_tnI.comp
    (show Primrec (fun p : DomDesc × InstDesc => p.2) from Primrec.snd))
  have hbody := primrec_succBody.comp
    (Primrec.pair (Primrec.pair Primrec.fst (Primrec.pair hfacts hsat))
      (Primrec.pair hstart hseq))
  have hgoal : Primrec₂ (fun (p : DomDesc × InstDesc) (z : List ℕ × Bool) =>
      (p.2.goalList.foldr (fun f b => memB z.1 f && b) true) || z.2) := by
    have hinner : Primrec₂ (fun (v : (DomDesc × InstDesc) × (List ℕ × Bool)) (y : ℕ × Bool) =>
        memB v.2.1 y.1 && y.2) :=
      Primrec₂.mk (Primrec.and.comp
        (primrec_memB.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
    exact Primrec₂.mk (Primrec.or.comp
      (list_foldr (primrec_goalList.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.const true) hinner)
      (Primrec.snd.comp Primrec.snd))
  have hres := list_foldr hbody (Primrec.const false) hgoal
  refine Primrec₂.mk (hres.of_eq fun p => ?_)
  rw [toSolvableB]
  induction (succBody p.1 (facts p.1 p.2) (satR p.1 (facts p.1 p.2))
      [nrm (facts p.1 p.2) p.2.initList] (TnDesc.seqBody p.2.tnI)) with
  | nil => rfl
  | cons x xs ih => simp [List.any_cons, ← ih]

/-! ### Sanity checks

A **cyclic** hierarchy, which no enumeration of refinements could handle: the compound task `0`
decomposes either into the action `1` followed by `0` again, or into nothing; the action `1`
adds the fact `0`, which is the goal.  One unfolding solves it.  The second domain offers only
the rule `0 ↦ 0`, so it has no terminating refinement at all. -/

/-- `c₀ ↦ a₁ c₀ | ε`, with `a₁` adding the fact `0`. -/
def exRecDom : DomDesc :=
  ([(1, [], [0], [])],
   [(0, ([0, 1], [(0, 1)], [(0, false, 1), (1, true, 0)])), (0, ([], [], []))])

/-- The instance: empty initial state, goal `{0}`, the single compound task `0`. -/
def exRecInst : InstDesc := ([], [0], ([0], [], [(0, true, 0)]))

/-- `c₀ ↦ c₀` — no terminating refinement. -/
def exLoopDom : DomDesc := ([(1, [], [0], [])], [(0, ([0], [], [(0, true, 0)]))])

example : toSolvableB exRecDom exRecInst = true := by decide

example : toSolvableB exLoopDom exRecInst = false := by decide

end ToDec

/-! ### The decider -/

/-- **Plan existence is decidable for the class `TO-HTN`** — for a cyclic hierarchy as well, and
for an arbitrary totally ordered initial task network.  The decision procedure is the saturation
of `Computable/ToDecide.lean`, and it is primitive recursive. -/
theorem decider_TO_HTN : SynClass.TO_HTN.Decider :=
  ⟨ToDec.toSolvableB, ToDec.primrec_toSolvableB.to_comp,
    fun _ _ hd hq => ToDec.toSolvableB_iff hd hq⟩

end Syn

end HTN
