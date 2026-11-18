import HtnComplexity.Computable.TokCorrect
import HtnComplexity.Computable.RegStripsCell
import HtnComplexity.Computable.AcNumPrimrec
import HtnPlanning.SynClasses.Basic
/-!
# The cell (`HTN-REG` rooted, `TO-HTN-REG` rooted) of the computable table

The construction is in [`TokDom.lean`](TokDom.lean) and its correctness in
[`TokCorrect.lean`](TokCorrect.lean); this file adds the two remaining halves of a cell of the
computable compilability table — the **size** of the compiled description (cubic in the source
description) and the **computability** of the two translations (both primitive recursive) — and
assembles them into `HTN.Syn.compSyn_HTN_REG_root_to_TO_HTN_REG_root`, together with the cells
that follow by composition.
-/

namespace HTN

namespace Syn

/-! ### Size -/

theorem sum_map_flatMap {α β : Type} (g : β → ℕ) (l : List α) (f : α → List β) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem length_pOf_le (d : DomDesc) (i : ℕ) : (pOf d i).length ≤ d.size := by
  have h1 : (pOf d i).length ≤ ((tOf d i).ids.dedup).length := List.length_filter_le _ _
  have h2 : ((tOf d i).ids.dedup).length ≤ (tOf d i).ids.length :=
    (List.dedup_sublist _).length_le
  have h3 : (tOf d i).ids.length ≤ d.size := length_ids_getI_le d i
  omega

theorem length_predsOf_le (d : DomDesc) (i x : ℕ) :
    ((tOf d i).predsOf x).length ≤ d.size :=
  le_trans (List.length_filter_le _ _) (length_pOf_le d i)

theorem size_tokAction_le {d : DomDesc} {i : ℕ} {p : ActionDesc} (hp : p ∈ tokActionsOf d i) :
    ActionDesc.size p ≤ 5 * d.size + 5 := by
  have hpO := length_pOf_le d i
  rcases mem_tokActionsOf_iff.1 hp with rfl | ⟨x, -, rfl⟩ | rfl
  · simp only [ActionDesc.size, List.length_nil, List.length_map]
    omega
  · have h1 := length_predsOf_le d i x
    have h2 := DomDesc.length_precList_le d (TnDesc.actOf (tOf d i) x)
    have h3 := DomDesc.length_addList_le d (TnDesc.actOf (tOf d i) x)
    have h4 := DomDesc.length_delList_le d (TnDesc.actOf (tOf d i) x)
    simp only [ActionDesc.size, doPre, doAdd, doDel, List.length_append, List.length_cons,
      List.length_map]
    omega
  · simp only [ActionDesc.size, List.length_nil, List.length_map]
    omega

theorem size_tokMethod_le {d : DomDesc} {i : ℕ} {e : MethodDesc} (he : e ∈ tokMethodsOf d i) :
    MethodDesc.size e ≤ 6 := by
  rcases tokMethodsOf_shape he with ⟨a, c, hb⟩ | ⟨a, hb⟩
  · have : MethodDesc.size e = 1 + (body2 a c).size := by rw [MethodDesc.size, hb]
    simp [this, body2, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  · have : MethodDesc.size e = 1 + (body1 a).size := by rw [MethodDesc.size, hb]
    simp [this, body1, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]

theorem length_tokActionsOf (d : DomDesc) (i : ℕ) :
    (tokActionsOf d i).length = (pOf d i).length + 2 := by
  simp [tokActionsOf]

theorem length_tokMethodsOf (d : DomDesc) (i : ℕ) :
    (tokMethodsOf d i).length = (pOf d i).length * (pOf d i).length + 2 := by
  simp [tokMethodsOf, List.length_flatMap]

theorem sum_tokActionsOf_le (d : DomDesc) (i : ℕ) :
    ((tokActionsOf d i).map ActionDesc.size).sum ≤ ((pOf d i).length + 2) * (5 * d.size + 5) := by
  have h := sum_le_length_mul (l := (tokActionsOf d i).map ActionDesc.size)
    (B := 5 * d.size + 5) ?_
  · rwa [List.length_map, length_tokActionsOf] at h
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact size_tokAction_le hp

theorem sum_tokMethodsOf_le (d : DomDesc) (i : ℕ) :
    ((tokMethodsOf d i).map MethodDesc.size).sum ≤
      ((pOf d i).length * (pOf d i).length + 2) * 6 := by
  have h := sum_le_length_mul (l := (tokMethodsOf d i).map MethodDesc.size) (B := 6) ?_
  · rwa [List.length_map, length_tokMethodsOf] at h
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact size_tokMethod_le he

theorem size_tokDom_le (d : DomDesc) :
    (tokDom d).size ≤ 60 * ((d.size + 1) * (d.size + 1) * (d.size + 1)) := by
  set s := d.size with hs
  have hn : d.methods.length ≤ s := length_methods_le_size d
  have hsize : (tokDom d).size =
      (((List.range d.methods.length).flatMap (tokActionsOf d)).map ActionDesc.size).sum +
        (((List.range d.methods.length).flatMap (tokMethodsOf d)).map MethodDesc.size).sum :=
    rfl
  have hacts : (((List.range d.methods.length).flatMap (tokActionsOf d)).map
      ActionDesc.size).sum ≤ d.methods.length * ((s + 2) * (5 * s + 5)) := by
    rw [sum_map_flatMap]
    have h := sum_le_length_mul
      (l := (List.range d.methods.length).map fun i => ((tokActionsOf d i).map
        ActionDesc.size).sum) (B := (s + 2) * (5 * s + 5)) ?_
    · rwa [List.length_map, List.length_range] at h
    · intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact le_trans (sum_tokActionsOf_le d i)
        (Nat.mul_le_mul_right _ (by have := length_pOf_le d i; omega))
  have hmeths : (((List.range d.methods.length).flatMap (tokMethodsOf d)).map
      MethodDesc.size).sum ≤ d.methods.length * ((s * s + 2) * 6) := by
    rw [sum_map_flatMap]
    have h := sum_le_length_mul
      (l := (List.range d.methods.length).map fun i => ((tokMethodsOf d i).map
        MethodDesc.size).sum) (B := (s * s + 2) * 6) ?_
    · rwa [List.length_map, List.length_range] at h
    · intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      refine le_trans (sum_tokMethodsOf_le d i) (Nat.mul_le_mul_right _ ?_)
      have hp := length_pOf_le d i
      have : (pOf d i).length * (pOf d i).length ≤ s * s := Nat.mul_le_mul hp hp
      omega
  have h1 : d.methods.length * ((s + 2) * (5 * s + 5)) ≤ s * ((s + 2) * (5 * s + 5)) :=
    Nat.mul_le_mul_right _ hn
  have h2 : d.methods.length * ((s * s + 2) * 6) ≤ s * ((s * s + 2) * 6) :=
    Nat.mul_le_mul_right _ hn
  have h3 : s * ((s + 2) * (5 * s + 5)) + s * ((s * s + 2) * 6) ≤
      60 * ((s + 1) * (s + 1) * (s + 1)) := by nlinarith [Nat.zero_le s]
  omega

theorem size_tokInst_le (q : InstDesc) : (tokInst q).size ≤ q.size + 2 := by
  have h : (tokInst q).size = q.initList.length + q.goalList.length + 2 := by
    simp [tokInst, InstDesc.size, InstDesc.initList, InstDesc.goalList, InstDesc.tnI,
      TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have h2 : q.size = q.initList.length + q.goalList.length + q.tnI.size := rfl
  omega

/-! ### Computability -/

open Primrec

section Encodings

variable {γ : Type} [Primcodable γ] {f g : γ → ℕ}

theorem primrec_stateF (hf : Primrec f) : Primrec fun x => stateF (f x) :=
  Primrec.nat_mul.comp (Primrec.const 3) hf

theorem primrec_tokF (hf : Primrec f) (hg : Primrec g) : Primrec fun x => tokF (f x) (g x) :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 3)
    (Primrec₂.natPair.comp hf hg))

theorem primrec_donF (hf : Primrec f) (hg : Primrec g) : Primrec fun x => donF (f x) (g x) :=
  Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 3)
    (Primrec₂.natPair.comp hf hg)))

theorem primrec_ctName (hf : Primrec f) : Primrec fun x => ctName (f x) :=
  Primrec.nat_mul.comp (Primrec.const 2) hf

theorem primrec_qName (hf : Primrec f) (hg : Primrec g) : Primrec fun x => qName (f x) (g x) :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec₂.natPair.comp hf hg))

theorem primrec_strtA (hf : Primrec f) : Primrec fun x => strtA (f x) :=
  Primrec.nat_mul.comp (Primrec.const 3) hf

theorem primrec_doA (hf : Primrec f) (hg : Primrec g) : Primrec fun x => doA (f x) (g x) :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 3)
    (Primrec₂.natPair.comp hf hg))

theorem primrec_finA (hf : Primrec f) : Primrec fun x => finA (f x) :=
  Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 3) hf))

/-- The described task network `a ≺ c`, as a function of `a` and `c`. -/
theorem primrec_body2 (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => body2 (f x) (g x) := by
  have h1 : Primrec fun x : γ => ((0, false, f x) : ℕ × Bool × ℕ) :=
    Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hf)
  have h2 : Primrec fun x : γ => ((1, true, g x) : ℕ × Bool × ℕ) :=
    Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hg)
  exact Primrec.pair (Primrec.const [0, 1])
    (Primrec.pair (Primrec.const [(0, 1)])
      (Primrec.list_cons.comp h1 (Primrec.list_cons.comp h2 (Primrec.const []))))

/-- The described task network consisting of a single action. -/
theorem primrec_body1 (hf : Primrec f) : Primrec fun x => body1 (f x) := by
  have h1 : Primrec fun x : γ => ((0, false, f x) : ℕ × Bool × ℕ) :=
    Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hf)
  exact Primrec.pair (Primrec.const [0])
    (Primrec.pair (Primrec.const []) (Primrec.list_cons.comp h1 (Primrec.const [])))

end Encodings

/-! #### Reading a described task network -/

namespace TnDesc

theorem primIds_eq_filterMap (t : TnDesc) :
    primIds t = t.ids.dedup.filterMap fun x => if labelIsCompound t x then none else some x := by
  simp only [primIds]
  induction t.ids.dedup with
  | nil => rfl
  | cons a l ih =>
      by_cases h : labelIsCompound t a <;> simp [h, ih]

theorem primrec_primIds : Primrec primIds := by
  refine Primrec.of_eq (f := fun t : TnDesc =>
    t.ids.dedup.filterMap fun x => if labelIsCompound t x then none else some x) ?_
    (fun t => (primIds_eq_filterMap t).symm)
  refine listFilterMap (β := ℕ) (σ := ℕ) (Ac.primrec_dedup.comp primrec_ids) ?_
  refine Primrec.ite ?_ (Primrec.const none) (option_some.comp Primrec.snd)
  exact PrimrecRel.comp Primrec.eq
    (primrec_labelIsCompound.comp Primrec.fst Primrec.snd) (Primrec.const true)

theorem predsOf_eq_filterMap (t : TnDesc) (x : ℕ) :
    predsOf t x = (primIds t).filterMap fun y => if ordB t y x then some y else none := by
  simp only [predsOf]
  induction primIds t with
  | nil => rfl
  | cons a l ih =>
      by_cases h : ordB t a x <;> simp [h, ih]

theorem primrec_predsOf : Primrec₂ predsOf := by
  refine Primrec₂.of_eq (f := fun (t : TnDesc) (x : ℕ) =>
    (primIds t).filterMap fun y => if ordB t y x then some y else none) ?_
    (fun t x => (predsOf_eq_filterMap t x).symm)
  refine listFilterMap (β := ℕ) (σ := ℕ) (primrec_primIds.comp Primrec.fst) ?_
  refine Primrec.ite ?_ (option_some.comp Primrec.snd) (Primrec.const none)
  exact PrimrecRel.comp Primrec.eq
    (primrec_ordB.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))))
    (Primrec.const true)

theorem primrec_hasNextB : Primrec hasNextB :=
  Primrec.not.comp (DomDesc.primrec_isEmptyList.comp primrec_compoundNames)

theorem primrec_nextName : Primrec nextName :=
  Primrec.list_headI.comp primrec_compoundNames

end TnDesc

/-! #### The compiled description -/

theorem primrec_cOf : Primrec₂ cOf :=
  Primrec.to₂ (Primrec.fst.comp
    (Primrec.list_getI.comp (primrec_methods.comp Primrec.fst) Primrec.snd))

theorem primrec_tOf : Primrec₂ tOf :=
  Primrec.to₂ (Primrec.snd.comp
    (Primrec.list_getI.comp (primrec_methods.comp Primrec.fst) Primrec.snd))

theorem primrec_pOf : Primrec₂ pOf :=
  Primrec.to₂ (TnDesc.primrec_primIds.comp (primrec_tOf.comp Primrec.fst Primrec.snd))

theorem primrec_tokActionsOf : Primrec₂ tokActionsOf := by
  have hd : Primrec fun w : DomDesc × ℕ => w.1 := Primrec.fst
  have hi : Primrec fun w : DomDesc × ℕ => w.2 := Primrec.snd
  have hp : Primrec fun w : DomDesc × ℕ => pOf w.1 w.2 := primrec_pOf.comp hd hi
  have hstrt : Primrec fun w : DomDesc × ℕ =>
      ((strtA w.2, [], (pOf w.1 w.2).map (tokF w.2), []) : ActionDesc) :=
    Primrec.pair (primrec_strtA hi) (Primrec.pair (Primrec.const [])
      (Primrec.pair (Primrec.list_map hp
        (primrec_tokF (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂) (Primrec.const [])))
  have hfin : Primrec fun w : DomDesc × ℕ =>
      ((finA w.2, (pOf w.1 w.2).map (donF w.2), [], (pOf w.1 w.2).map (donF w.2)) :
        ActionDesc) := by
    have hm : Primrec fun w : DomDesc × ℕ => (pOf w.1 w.2).map (donF w.2) :=
      Primrec.list_map hp (primrec_donF (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
    exact Primrec.pair (primrec_finA hi) (Primrec.pair hm (Primrec.pair (Primrec.const []) hm))
  -- the actions executing one primitive subtask
  have hd' : Primrec fun p : (DomDesc × ℕ) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
  have hi' : Primrec fun p : (DomDesc × ℕ) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
  have hx' : Primrec fun p : (DomDesc × ℕ) × ℕ => p.2 := Primrec.snd
  have ht' : Primrec fun p : (DomDesc × ℕ) × ℕ => tOf p.1.1 p.1.2 := primrec_tOf.comp hd' hi'
  have ha' : Primrec fun p : (DomDesc × ℕ) × ℕ => TnDesc.actOf (tOf p.1.1 p.1.2) p.2 :=
    TnDesc.primrec_actOf.comp ht' hx'
  have hpre : Primrec fun p : (DomDesc × ℕ) × ℕ => doPre p.1.1 p.1.2 p.2 := by
    have h1 : Primrec fun p : (DomDesc × ℕ) × ℕ =>
        ((tOf p.1.1 p.1.2).predsOf p.2).map (donF p.1.2) :=
      Primrec.list_map (TnDesc.primrec_predsOf.comp ht' hx')
        (primrec_donF (hi'.comp Primrec.fst) Primrec.snd).to₂
    have h2 : Primrec fun p : (DomDesc × ℕ) × ℕ =>
        (p.1.1.precList (TnDesc.actOf (tOf p.1.1 p.1.2) p.2)).map stateF :=
      Primrec.list_map (DomDesc.primrec_precList.comp hd' ha')
        (primrec_stateF Primrec.snd).to₂
    exact Primrec.list_append.comp h1
      (Primrec.list_cons.comp (primrec_tokF hi' hx') h2)
  have hadd : Primrec fun p : (DomDesc × ℕ) × ℕ => doAdd p.1.1 p.1.2 p.2 :=
    Primrec.list_cons.comp (primrec_donF hi' hx')
      (Primrec.list_map (DomDesc.primrec_addList.comp hd' ha')
        (primrec_stateF Primrec.snd).to₂)
  have hdel : Primrec fun p : (DomDesc × ℕ) × ℕ => doDel p.1.1 p.1.2 p.2 :=
    Primrec.list_cons.comp (primrec_tokF hi' hx')
      (Primrec.list_map (DomDesc.primrec_delList.comp hd' ha')
        (primrec_stateF Primrec.snd).to₂)
  have hdos : Primrec fun w : DomDesc × ℕ =>
      (pOf w.1 w.2).map fun x =>
        ((doA w.2 x, doPre w.1 w.2 x, doAdd w.1 w.2 x, doDel w.1 w.2 x) : ActionDesc) :=
    Primrec.list_map hp
      (Primrec.pair (primrec_doA hi' hx') (Primrec.pair hpre (Primrec.pair hadd hdel))).to₂
  exact Primrec.to₂ (Primrec.list_cons.comp hstrt
    (Primrec.list_append.comp hdos (Primrec.list_cons.comp hfin (Primrec.const []))))

theorem primrec_finBody : Primrec₂ finBody := by
  have hd : Primrec fun w : DomDesc × ℕ => w.1 := Primrec.fst
  have hi : Primrec fun w : DomDesc × ℕ => w.2 := Primrec.snd
  have ht : Primrec fun w : DomDesc × ℕ => tOf w.1 w.2 := primrec_tOf.comp hd hi
  refine Primrec₂.mk (Primrec.ite ?_ ?_ ?_)
  · exact PrimrecRel.comp Primrec.eq (TnDesc.primrec_hasNextB.comp ht) (Primrec.const true)
  · exact primrec_body2 (primrec_finA hi)
      (primrec_ctName (TnDesc.primrec_nextName.comp ht))
  · exact primrec_body1 (primrec_finA hi)

theorem primrec_tokMethodsOf : Primrec₂ tokMethodsOf := by
  have hd : Primrec fun w : DomDesc × ℕ => w.1 := Primrec.fst
  have hi : Primrec fun w : DomDesc × ℕ => w.2 := Primrec.snd
  have hp : Primrec fun w : DomDesc × ℕ => pOf w.1 w.2 := primrec_pOf.comp hd hi
  have hentry : Primrec fun w : DomDesc × ℕ =>
      ((ctName (cOf w.1 w.2), body2 (strtA w.2) (qName w.2 0)) : MethodDesc) :=
    Primrec.pair (primrec_ctName (primrec_cOf.comp hd hi))
      (primrec_body2 (primrec_strtA hi) (primrec_qName hi (Primrec.const 0)))
  have hclose : Primrec fun w : DomDesc × ℕ =>
      ((qName w.2 (pOf w.1 w.2).length, finBody w.1 w.2) : MethodDesc) :=
    Primrec.pair (primrec_qName hi (Primrec.list_length.comp hp))
      (primrec_finBody.comp hd hi)
  have hstep : Primrec fun w : DomDesc × ℕ =>
      (List.range (pOf w.1 w.2).length).flatMap fun k =>
        (pOf w.1 w.2).map fun x =>
          ((qName w.2 k, body2 (doA w.2 x) (qName w.2 (k + 1))) : MethodDesc) := by
    have hpp : Primrec fun p : (DomDesc × ℕ) × ℕ => pOf p.1.1 p.1.2 := hp.comp Primrec.fst
    have hii : Primrec fun r : ((DomDesc × ℕ) × ℕ) × ℕ => r.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hkk : Primrec fun r : ((DomDesc × ℕ) × ℕ) × ℕ => r.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hxx : Primrec fun r : ((DomDesc × ℕ) × ℕ) × ℕ => r.2 := Primrec.snd
    have hinner : Primrec fun r : ((DomDesc × ℕ) × ℕ) × ℕ =>
        ((qName r.1.1.2 r.1.2, body2 (doA r.1.1.2 r.2) (qName r.1.1.2 (r.1.2 + 1))) :
          MethodDesc) :=
      Primrec.pair (primrec_qName hii hkk)
        (primrec_body2 (primrec_doA hii hxx) (primrec_qName hii (Primrec.succ.comp hkk)))
    exact Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp hp))
      (Primrec.to₂ (Primrec.list_map hpp (Primrec.to₂ hinner)))
  exact Primrec.to₂ (Primrec.list_cons.comp hentry
    (Primrec.list_append.comp hstep (Primrec.list_cons.comp hclose (Primrec.const []))))

theorem primrec_tokDom : Primrec tokDom := by
  have hrange : Primrec fun d : DomDesc => List.range d.methods.length :=
    Primrec.list_range.comp (Primrec.list_length.comp primrec_methods)
  exact Primrec.pair
    (Primrec.list_flatMap hrange (primrec_tokActionsOf.comp Primrec.fst Primrec.snd))
    (Primrec.list_flatMap hrange (primrec_tokMethodsOf.comp Primrec.fst Primrec.snd))

theorem primrec_tokInst : Primrec tokInst := by
  have hinit : Primrec fun q : InstDesc => q.initList.map stateF :=
    Primrec.list_map primrec_initList (primrec_stateF Primrec.snd).to₂
  have hgoal : Primrec fun q : InstDesc => q.goalList.map stateF :=
    Primrec.list_map primrec_goalList (primrec_stateF Primrec.snd).to₂
  have hlbl : Primrec fun q : InstDesc =>
      ([(0, true, ctName (rootName q))] : List (ℕ × Bool × ℕ)) :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const true) (primrec_ctName primrec_rootName)))
      (Primrec.const [])
  exact Primrec.pair hinit
    (Primrec.pair hgoal
      (Primrec.pair (Primrec.const [0]) (Primrec.pair (Primrec.const []) hlbl)))

theorem computable_tokDom : Computable tokDom := primrec_tokDom.to_comp

theorem computable_tokInst : Computable tokInst := primrec_tokInst.to_comp

/-! ### The class of rooted regular descriptions, and the cell -/

namespace SynClass

open Table

theorem sub_HTN_REG_root_HTN_REG : SynSub HTN_REG_root HTN_REG :=
  ⟨fun _ hd => hd, fun _ hq => hq.isRegular⟩

theorem sub_TO_HTN_REG_root_HTN_REG_root : SynSub TO_HTN_REG_root HTN_REG_root :=
  ⟨fun _ hd => hd.2, fun _ hq => hq⟩

theorem sub_STRIPS_HTN_REG_root : SynSub STRIPS HTN_REG_root :=
  sub_STRIPS_TO_HTN_REG_root.trans sub_TO_HTN_REG_root_HTN_REG_root

end SynClass

end Syn

end HTN
