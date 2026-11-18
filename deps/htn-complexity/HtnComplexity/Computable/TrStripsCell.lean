import HtnComplexity.Computable.TrStripsCorrect
import HtnComplexity.Computable.RegStripsCell
import HtnPlanning.SynClasses.Basic
/-!
# The cells (`TO-HTN-TR` rooted, `STRIPS`) and (`TO-HTN-AC` rooted, `STRIPS`)

The stack-machine construction and its correctness are in
[`TrStrips.lean`](TrStrips.lean) and [`TrStripsCorrect.lean`](TrStripsCorrect.lean); this file
adds the two remaining halves of a cell of the computable compilability table — the **size** of
the compiled description (polynomial, of degree five, in the source description) and the
**computability** of the two translations (both are primitive recursive) — and assembles them
into `HTN.Syn.compSyn_TO_HTN_TR_root_to_STRIPS` and, by monotonicity in the source class,
`HTN.Syn.compSyn_TO_HTN_AC_root_to_STRIPS`.
-/

namespace HTN

namespace Syn

/-! ### The classes of rooted totally ordered tail-recursive and acyclic descriptions -/

namespace SynClass

open Table

theorem sub_TO_HTN_TR_root_TO_HTN_TR : SynSub TO_HTN_TR_root TO_HTN_TR :=
  ⟨fun _ hd => hd, fun _ hq => hq.isTO⟩

theorem sub_TO_HTN_AC_root_TO_HTN_AC : SynSub TO_HTN_AC_root TO_HTN_AC :=
  ⟨fun _ hd => hd, fun _ hq => hq.isTO⟩

theorem sub_TO_HTN_AC_root_TO_HTN_TR_root : SynSub TO_HTN_AC_root TO_HTN_TR_root :=
  ⟨fun _ hd => ⟨hd.1, isAcyclic_isTailRec hd.2⟩, fun _ hq => hq⟩

theorem sub_STRIPS_TO_HTN_TR_root : SynSub STRIPS TO_HTN_TR_root :=
  ⟨fun _ hd => ⟨isStrips_methodsTO hd, methodsReg_isTailRec (isStrips_methodsReg hd)⟩,
    fun _ hq => hq.isRooted⟩

theorem sub_TO_HTN_REG_root_TO_HTN_TR_root : SynSub TO_HTN_REG_root TO_HTN_TR_root :=
  ⟨fun _ hd => ⟨hd.1, methodsReg_isTailRec hd.2⟩, fun _ hq => hq⟩

end SynClass

/-! ### Size -/

/-- The three lists of a described action are, together, no longer than the description. -/
theorem length_lists_le_size (d : DomDesc) (a : ℕ) :
    (d.precList a).length + (d.addList a).length + (d.delList a).length ≤ d.size := by
  rcases h : d.actions.lookup a with _ | x
  · simp [DomDesc.precList, DomDesc.addList, DomDesc.delList, h]
  · have hmem : (a, x) ∈ d.actions := mem_of_lookup_eq_some h
    have hle : ActionDesc.size (a, x) ≤ (d.actions.map ActionDesc.size).sum :=
      DomDesc.mem_le_sum ActionDesc.size hmem
    have he : ActionDesc.size (a, x) = 1 + x.1.length + x.2.1.length + x.2.2.length := rfl
    have hs : d.size = (d.actions.map ActionDesc.size).sum +
      (d.methods.map MethodDesc.size).sum := rfl
    simp only [DomDesc.precList, DomDesc.addList, DomDesc.delList, h, Option.elim]
    omega

/-- The number of symbols of the specification of a compiled action. -/
def specSize (p : List ℕ × List ℕ × List ℕ) : ℕ := 1 + p.1.length + p.2.1.length + p.2.2.length

theorem size_eq_specSize (n : ℕ) (p : List ℕ × List ℕ × List ℕ) :
    ActionDesc.size (n, p) = specSize p := rfl

/-- **Every compiled action is short**: only the `exec` actions copy anything from the source
description, and they copy the three lists of a single source action. -/
theorem size_specOf_le (d : DomDesc) (x : ℕ × ℕ × ℕ × ℕ × ℕ) :
    specSize (specOf d x) ≤ d.size + 6 := by
  have hbad : specSize badSpec ≤ d.size + 6 := by simp [specSize, badSpec]
  have hbeg : ∀ m, specSize (begSpec d m) ≤ d.size + 6 := by
    intro m; rw [begSpec]; split_ifs
    · simp [specSize]
    · exact hbad
  have hexec : ∀ i m j, specSize (execSpec d i m j) ≤ d.size + 6 := by
    intro i m j; rw [execSpec]; split_ifs
    · have := length_lists_le_size d (d.actAt m j)
      simp only [specSize, List.length_cons, List.length_map]
      omega
    · exact hbad
  have hpush : ∀ i m j m', specSize (pushSpec d i m j m') ≤ d.size + 6 := by
    intro i m j m'; rw [pushSpec]; split_ifs
    · simp [specSize]
    · exact hbad
  have htail : ∀ i m j m', specSize (tailSpec d i m j m') ≤ d.size + 6 := by
    intro i m j m'; rw [tailSpec]; split_ifs
    · simp [specSize]
    · exact hbad
  have hret : ∀ i m j' m', specSize (retSpec d i m j' m') ≤ d.size + 6 := by
    intro i m j' m'; rw [retSpec]; split_ifs
    · simp [specSize]
    · exact hbad
  have hfin : ∀ m, specSize (finSpec d m) ≤ d.size + 6 := by
    intro m; simp [specSize, finSpec]
  rw [specOf]
  split_ifs
  · exact hbeg _
  · exact hexec _ _ _
  · exact hpush _ _ _ _
  · exact htail _ _ _ _
  · exact hret _ _ _ _
  · exact hfin _
  · exact hbad

/-- There are `O(size⁴)` compiled actions. -/
theorem length_cacts_le (d : DomDesc) :
    (cacts d).length ≤
      6 * ((d.size + 1) * ((d.size + 1) * ((d.size + 2) * (d.size + 1)))) := by
  set s := d.size with hs
  set M := d.methods.length with hM
  have hMs : M ≤ s + 1 := le_trans (length_methods_le_size d) (by omega)
  have h1 : ∀ k i m : ℕ, ((List.range (s + 2)).flatMap fun j =>
      (List.range M).map fun m' => ((k, i, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ)).length ≤
      (s + 2) * (s + 1) := by
    intro k i m
    have := length_flatMap_le (List.range (s + 2))
      (fun j => (List.range M).map fun m' => ((k, i, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ)) (s + 1)
      (by intro x _; simpa using hMs)
    simpa using this
  have h2 : ∀ k i : ℕ, ((List.range M).flatMap fun m =>
      (List.range (s + 2)).flatMap fun j =>
        (List.range M).map fun m' => ((k, i, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ)).length ≤
      (s + 1) * ((s + 2) * (s + 1)) := by
    intro k i
    have := length_flatMap_le (List.range M) _ ((s + 2) * (s + 1)) (fun x _ => h1 k i x)
    simp only [List.length_range] at this
    exact le_trans this (Nat.mul_le_mul_right _ hMs)
  have h3 : ∀ k : ℕ, ((List.range M).flatMap fun i =>
      (List.range M).flatMap fun m =>
        (List.range (s + 2)).flatMap fun j =>
          (List.range M).map fun m' => ((k, i, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ)).length ≤
      (s + 1) * ((s + 1) * ((s + 2) * (s + 1))) := by
    intro k
    have := length_flatMap_le (List.range M) _ ((s + 1) * ((s + 2) * (s + 1)))
      (fun x _ => h2 k x)
    simp only [List.length_range] at this
    exact le_trans this (Nat.mul_le_mul_right _ hMs)
  have := length_flatMap_le (List.range 6) _
    ((s + 1) * ((s + 1) * ((s + 2) * (s + 1)))) (fun x _ => h3 x)
  simpa [cacts] using this

theorem size_trStripsInst_le (q : InstDesc) : (trStripsInst q).size ≤ q.size + 4 := by
  have h : (trStripsInst q).size =
      (q.initList.length + 1) + (q.goalList.length + 1) + 2 := by
    simp [trStripsInst, InstDesc.size, stripsInst, InstDesc.initList, InstDesc.goalList,
      InstDesc.tnI, initTn, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have h2 : q.size = q.initList.length + q.goalList.length + q.tnI.size := rfl
  omega

/-- **The compiled description is of polynomial size** — of degree five in the source. -/
theorem size_trStripsDom_le (d : DomDesc) :
    (trStripsDom d).size ≤ 145 * ((d.size + 1) ^ 5) := by
  have hspec := size_specOf_le d
  have hcacts := length_cacts_le d
  set s := d.size with hs
  set L := (cacts d).length with hL
  have hlen : (trActions d).length = L := by simp [trActions]; exact hL.symm
  have hacts : ((trActions d).map ActionDesc.size).sum ≤ L * (s + 6) := by
    have h := sum_le_length_mul (l := (trActions d).map ActionDesc.size) (B := s + 6) ?_
    · rwa [List.length_map, hlen] at h
    · intro y hy
      obtain ⟨ad, had, rfl⟩ := List.mem_map.1 hy
      obtain ⟨n, -, rfl⟩ := List.mem_map.1 had
      exact hspec _
  have hmeth : ((trStripsDom d).methods.map MethodDesc.size).sum = 1 + 6 * L := by
    have h1 : MethodDesc.size ((0, emptyBody) : MethodDesc) = 1 := rfl
    simp only [trStripsDom, stripsDom_methods, List.map_cons, List.sum_cons, h1,
      sum_map_stepMethods, hlen]
  have hsize : (trStripsDom d).size =
      ((trActions d).map ActionDesc.size).sum +
        ((trStripsDom d).methods.map MethodDesc.size).sum := rfl
  set t := s + 1 with ht
  have hLt : L ≤ 12 * t ^ 4 := by
    refine le_trans hcacts ?_
    have h2 : s + 2 ≤ 2 * t := by omega
    calc 6 * (t * (t * ((s + 2) * t))) ≤ 6 * (t * (t * ((2 * t) * t))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_right _ h2)))
      _ = 12 * t ^ 4 := by ring
  have hs12 : s + 12 ≤ 12 * t := by omega
  have hkey : L * (s + 12) ≤ 144 * t ^ 5 := by
    calc L * (s + 12) ≤ (12 * t ^ 4) * (12 * t) := Nat.mul_le_mul hLt hs12
      _ = 144 * t ^ 5 := by ring
  have hone : 1 ≤ t ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hexp : L * (s + 6) + (1 + 6 * L) = L * (s + 12) + 1 := by ring
  omega

/-! ### Computability -/

open Primrec

/-! #### The subtask at a position, and the fact encodings -/

theorem primrec_bdAt : Primrec fun w : DomDesc × ℕ × ℕ => DomDesc.bdAt w.1 w.2.1 w.2.2 :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (DomDesc.primrec_bd.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
    (Primrec.const (Sum.inl 0))).of_eq fun _ => rfl

theorem primrec_isCompAt : Primrec fun w : DomDesc × ℕ × ℕ => DomDesc.isCompAt w.1 w.2.1 w.2.2 :=
  (Primrec.sumCasesOn primrec_bdAt (Primrec.const false).to₂ (Primrec.const true).to₂).of_eq
    fun w => by rcases h : DomDesc.bdAt w.1 w.2.1 w.2.2 with a | c <;> simp [DomDesc.isCompAt, h]

theorem primrec_actAt : Primrec fun w : DomDesc × ℕ × ℕ => DomDesc.actAt w.1 w.2.1 w.2.2 :=
  (Primrec.sumCasesOn primrec_bdAt Primrec.snd.to₂ (Primrec.const 0).to₂).of_eq
    fun w => by rcases h : DomDesc.bdAt w.1 w.2.1 w.2.2 with a | c <;> simp [DomDesc.actAt, h]

theorem primrec_compAt : Primrec fun w : DomDesc × ℕ × ℕ => DomDesc.compAt w.1 w.2.1 w.2.2 :=
  (Primrec.sumCasesOn primrec_bdAt (Primrec.const 0).to₂ Primrec.snd.to₂).of_eq
    fun w => by rcases h : DomDesc.bdAt w.1 w.2.1 w.2.2 with a | c <;> simp [DomDesc.compAt, h]

variable {γ : Type} [Primcodable γ]

theorem primrec_encSt {f : γ → ℕ} (hf : Primrec f) : Primrec fun x => encSt (f x) :=
  (Primrec.nat_mul.comp (Primrec.const 6) hf).of_eq fun _ => rfl

theorem primrec_encCall {f : γ → ℕ} (hf : Primrec f) : Primrec fun x => encCall (f x) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) hf)
    (Primrec.const 3)).of_eq fun _ => rfl

theorem primrec_encCur {fi fm fj : γ → ℕ} (hi : Primrec fi) (hm : Primrec fm) (hj : Primrec fj) :
    Primrec fun x => encCur (fi x) (fm x) (fj x) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec₂.natPair.comp hi (Primrec₂.natPair.comp hm hj))) (Primrec.const 1)).of_eq
      fun _ => rfl

theorem primrec_encSav {fi fm fj : γ → ℕ} (hi : Primrec fi) (hm : Primrec fm) (hj : Primrec fj) :
    Primrec fun x => encSav (fi x) (fm x) (fj x) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec₂.natPair.comp hi (Primrec₂.natPair.comp hm hj))) (Primrec.const 2)).of_eq
      fun _ => rfl

/-! #### The six kinds of compiled action -/

theorem primrec_begSpec : Primrec fun w : DomDesc × ℕ => begSpec w.1 w.2 := by
  have hlen : Primrec fun w : DomDesc × ℕ => w.1.methods.length :=
    Primrec.list_length.comp (primrec_methods.comp Primrec.fst)
  have hhd : Primrec fun w : DomDesc × ℕ => w.1.hd w.2 :=
    DomDesc.primrec_hd.comp Primrec.fst Primrec.snd
  have hcall : Primrec fun w : DomDesc × ℕ => [encCall (w.1.hd w.2)] :=
    Primrec.list_cons.comp (primrec_encCall hhd) (Primrec.const [])
  have hcur : Primrec fun w : DomDesc × ℕ => [encCur 0 w.2 0] :=
    Primrec.list_cons.comp
      (primrec_encCur (Primrec.const 0) Primrec.snd (Primrec.const 0)) (Primrec.const [])
  have hmain := Primrec.ite (PrimrecRel.comp Primrec.nat_lt Primrec.snd hlen)
    (Primrec.pair hcall (Primrec.pair hcur hcall)) (Primrec.const badSpec)
  exact hmain.of_eq fun w => rfl

theorem primrec_execSpec :
    Primrec fun w : DomDesc × ℕ × ℕ × ℕ => execSpec w.1 w.2.1 w.2.2.1 w.2.2.2 := by
  have hd : Primrec fun w : DomDesc × ℕ × ℕ × ℕ => w.1 := Primrec.fst
  have hi : Primrec fun w : DomDesc × ℕ × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hm : Primrec fun w : DomDesc × ℕ × ℕ × ℕ => w.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec fun w : DomDesc × ℕ × ℕ × ℕ => w.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hmj : Primrec fun w : DomDesc × ℕ × ℕ × ℕ => ((w.1, w.2.2.1, w.2.2.2) : DomDesc × ℕ × ℕ) :=
    Primrec.pair hd (Primrec.pair hm hj)
  have hbdlen := Primrec.list_length.comp (DomDesc.primrec_bd.comp hd hm)
  have hcomp := primrec_isCompAt.comp hmj
  have hact := primrec_actAt.comp hmj
  have hpre := Primrec.list_map (DomDesc.primrec_precList.comp hd hact)
    (primrec_encSt Primrec.snd).to₂
  have hadd := Primrec.list_map (DomDesc.primrec_addList.comp hd hact)
    (primrec_encSt Primrec.snd).to₂
  have hdel := Primrec.list_map (DomDesc.primrec_delList.comp hd hact)
    (primrec_encSt Primrec.snd).to₂
  have hcur := primrec_encCur hi hm hj
  have hcur1 := primrec_encCur hi hm (Primrec.succ.comp hj)
  have hcond := PrimrecPred.and (PrimrecRel.comp Primrec.nat_lt hj hbdlen)
    (PrimrecRel.comp Primrec.eq hcomp (Primrec.const false))
  have hmain := Primrec.ite hcond
    (Primrec.pair (Primrec.list_cons.comp hcur hpre)
      (Primrec.pair (Primrec.list_cons.comp hcur1 hadd)
        (Primrec.list_cons.comp hcur hdel)))
    (Primrec.const badSpec)
  exact hmain.of_eq fun w => rfl

theorem primrec_pushSpec :
    Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ =>
      pushSpec w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 := by
  have hd : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.1 := Primrec.fst
  have hi : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hm : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm' : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hmj : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ =>
      ((w.1, w.2.2.1, w.2.2.2.1) : DomDesc × ℕ × ℕ) := Primrec.pair hd (Primrec.pair hm hj)
  have hlen := Primrec.list_length.comp (primrec_methods.comp hd)
  have hbdlen := Primrec.list_length.comp (DomDesc.primrec_bd.comp hd hm)
  have hcomp := primrec_isCompAt.comp hmj
  have hcompAt := primrec_compAt.comp hmj
  have hhd := DomDesc.primrec_hd.comp hd hm'
  have hcond := PrimrecPred.and (PrimrecRel.comp Primrec.nat_lt (Primrec.succ.comp hj) hbdlen)
    (PrimrecPred.and (PrimrecRel.comp Primrec.eq hcomp (Primrec.const true))
      (PrimrecPred.and (PrimrecRel.comp Primrec.eq hcompAt hhd)
        (PrimrecPred.and (PrimrecRel.comp Primrec.nat_lt hm' hlen)
          (PrimrecRel.comp Primrec.nat_lt (Primrec.succ.comp hi) hlen))))
  have hcur := primrec_encCur hi hm hj
  have hcurP := primrec_encCur (Primrec.succ.comp hi) hm' (Primrec.const 0)
  have hsav := primrec_encSav hi hm (Primrec.succ.comp hj)
  have hmain := Primrec.ite hcond
    (Primrec.pair (Primrec.list_cons.comp hcur (Primrec.const []))
      (Primrec.pair
        (Primrec.list_cons.comp hcurP (Primrec.list_cons.comp hsav (Primrec.const [])))
        (Primrec.list_cons.comp hcur (Primrec.const []))))
    (Primrec.const badSpec)
  exact hmain.of_eq fun w => rfl

theorem primrec_tailSpec :
    Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ =>
      tailSpec w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 := by
  have hd : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.1 := Primrec.fst
  have hi : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hm : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm' : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hmj : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ =>
      ((w.1, w.2.2.1, w.2.2.2.1) : DomDesc × ℕ × ℕ) := Primrec.pair hd (Primrec.pair hm hj)
  have hlen := Primrec.list_length.comp (primrec_methods.comp hd)
  have hbdlen := Primrec.list_length.comp (DomDesc.primrec_bd.comp hd hm)
  have hcomp := primrec_isCompAt.comp hmj
  have hcompAt := primrec_compAt.comp hmj
  have hhd := DomDesc.primrec_hd.comp hd hm'
  have hcond := PrimrecPred.and (PrimrecRel.comp Primrec.eq (Primrec.succ.comp hj) hbdlen)
    (PrimrecPred.and (PrimrecRel.comp Primrec.eq hcomp (Primrec.const true))
      (PrimrecPred.and (PrimrecRel.comp Primrec.eq hcompAt hhd)
        (PrimrecRel.comp Primrec.nat_lt hm' hlen)))
  have hcur := primrec_encCur hi hm hj
  have hcurT := primrec_encCur hi hm' (Primrec.const 0)
  have hmain := Primrec.ite hcond
    (Primrec.pair (Primrec.list_cons.comp hcur (Primrec.const []))
      (Primrec.pair (Primrec.list_cons.comp hcurT (Primrec.const []))
        (Primrec.list_cons.comp hcur (Primrec.const []))))
    (Primrec.const badSpec)
  exact hmain.of_eq fun w => rfl

theorem primrec_retSpec :
    Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ =>
      retSpec w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2 := by
  have hd : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.1 := Primrec.fst
  have hi : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hm : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj' : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm' : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ => w.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hbdlen := Primrec.list_length.comp (DomDesc.primrec_bd.comp hd hm)
  have hpred := Primrec.nat_sub.comp hi (Primrec.const 1)
  have hcur := primrec_encCur hi hm hbdlen
  have hsav := primrec_encSav hpred hm' hj'
  have hcurR := primrec_encCur hpred hm' hj'
  have hcond := PrimrecRel.comp Primrec.nat_lt (Primrec.const 0) hi
  have hmain := Primrec.ite hcond
    (Primrec.pair (Primrec.list_cons.comp hcur (Primrec.list_cons.comp hsav (Primrec.const [])))
      (Primrec.pair (Primrec.list_cons.comp hcurR (Primrec.const []))
        (Primrec.list_cons.comp hcur (Primrec.list_cons.comp hsav (Primrec.const [])))))
    (Primrec.const badSpec)
  exact hmain.of_eq fun w => rfl

theorem primrec_finSpec : Primrec fun w : DomDesc × ℕ => finSpec w.1 w.2 := by
  have hd : Primrec fun w : DomDesc × ℕ => w.1 := Primrec.fst
  have hm : Primrec fun w : DomDesc × ℕ => w.2 := Primrec.snd
  have hbdlen := Primrec.list_length.comp (DomDesc.primrec_bd.comp hd hm)
  have hcur := primrec_encCur (Primrec.const 0) hm hbdlen
  have hmain := Primrec.pair (Primrec.list_cons.comp hcur (Primrec.const []))
    (Primrec.pair (Primrec.const [encDone]) (Primrec.list_cons.comp hcur (Primrec.const [])))
  exact hmain.of_eq fun w => rfl

/-! #### The specification of a compiled action -/

theorem primrec_specOf : Primrec₂ specOf := by
  have hd : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ × ℕ => w.1 := Primrec.fst
  have hk : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ × ℕ => w.2.1 := Primrec.fst.comp Primrec.snd
  have hi : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ × ℕ => w.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ × ℕ => w.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hj : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ × ℕ => w.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hm' : Primrec fun w : DomDesc × ℕ × ℕ × ℕ × ℕ × ℕ => w.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hbeg := primrec_begSpec.comp (Primrec.pair hd hm)
  have hexec := primrec_execSpec.comp (Primrec.pair hd (Primrec.pair hi (Primrec.pair hm hj)))
  have hpush := primrec_pushSpec.comp
    (Primrec.pair hd (Primrec.pair hi (Primrec.pair hm (Primrec.pair hj hm'))))
  have htail := primrec_tailSpec.comp
    (Primrec.pair hd (Primrec.pair hi (Primrec.pair hm (Primrec.pair hj hm'))))
  have hret := primrec_retSpec.comp
    (Primrec.pair hd (Primrec.pair hi (Primrec.pair hm (Primrec.pair hj hm'))))
  have hfin := primrec_finSpec.comp (Primrec.pair hd hm)
  have hmain := Primrec.ite (PrimrecRel.comp Primrec.eq hk (Primrec.const 0)) hbeg
    (Primrec.ite (PrimrecRel.comp Primrec.eq hk (Primrec.const 1)) hexec
      (Primrec.ite (PrimrecRel.comp Primrec.eq hk (Primrec.const 2)) hpush
        (Primrec.ite (PrimrecRel.comp Primrec.eq hk (Primrec.const 3)) htail
          (Primrec.ite (PrimrecRel.comp Primrec.eq hk (Primrec.const 4)) hret
            (Primrec.ite (PrimrecRel.comp Primrec.eq hk (Primrec.const 5)) hfin
              (Primrec.const badSpec))))))
  exact Primrec.to₂ (hmain.of_eq fun w => rfl)

/-! #### The size of a description -/

theorem primrec_natSum : Primrec (fun l : List ℕ => l.sum) := by
  have h : Primrec (fun l : List ℕ => l.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.to₂ (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a t ih => simp [List.sum_cons, ← ih]

theorem primrec_actionSize : Primrec ActionDesc.size := by
  have h : Primrec fun a : ActionDesc =>
      1 + a.2.1.length + a.2.2.1.length + a.2.2.2.length :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.const 1)
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq fun a => rfl

theorem primrec_methodSize : Primrec MethodDesc.size := by
  have h : Primrec fun m : MethodDesc =>
      1 + (m.2.1.length + m.2.2.1.length + m.2.2.2.length) :=
    Primrec.nat_add.comp (Primrec.const 1)
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact h.of_eq fun m => rfl

theorem primrec_domSize : Primrec DomDesc.size := by
  have h : Primrec fun d : DomDesc =>
      (d.actions.map ActionDesc.size).sum + (d.methods.map MethodDesc.size).sum :=
    Primrec.nat_add.comp
      (primrec_natSum.comp
        (Primrec.list_map primrec_actions (primrec_actionSize.comp Primrec.snd)))
      (primrec_natSum.comp
        (Primrec.list_map primrec_methods (primrec_methodSize.comp Primrec.snd)))
  exact h.of_eq fun d => rfl

/-! #### The parameter tuples of the compiled actions -/

theorem primrec_cacts : Primrec cacts := by
  have hlen : ∀ {γ : Type} [Primcodable γ] {f : γ → DomDesc}, Primrec f →
      Primrec fun x => (f x).methods.length :=
    fun hf => Primrec.list_length.comp (primrec_methods.comp hf)
  have g4 : Primrec₂ fun (a : DomDesc × ℕ × ℕ × ℕ × ℕ) (m' : ℕ) =>
      ((a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2, m') : ℕ × ℕ × ℕ × ℕ × ℕ) :=
    Primrec.to₂ (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
            Primrec.snd))))
  have h4 : Primrec fun a : DomDesc × ℕ × ℕ × ℕ × ℕ =>
      (List.range a.1.methods.length).map fun m' =>
        ((a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2, m') : ℕ × ℕ × ℕ × ℕ × ℕ) :=
    Primrec.list_map (Primrec.list_range.comp (hlen Primrec.fst)) g4
  have g3 : Primrec₂ fun (a : DomDesc × ℕ × ℕ × ℕ) (j : ℕ) =>
      (List.range a.1.methods.length).map fun m' =>
        ((a.2.1, a.2.2.1, a.2.2.2, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ) := by
    have hp : Primrec fun w : (DomDesc × ℕ × ℕ × ℕ) × ℕ =>
        ((w.1.1, w.1.2.1, w.1.2.2.1, w.1.2.2.2, w.2) : DomDesc × ℕ × ℕ × ℕ × ℕ) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
              Primrec.snd)))
    exact Primrec.to₂ ((h4.comp hp).of_eq fun w => rfl)
  have h3 : Primrec fun a : DomDesc × ℕ × ℕ × ℕ =>
      (List.range (a.1.size + 2)).flatMap fun j =>
        (List.range a.1.methods.length).map fun m' =>
          ((a.2.1, a.2.2.1, a.2.2.2, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ) :=
    Primrec.list_flatMap (Primrec.list_range.comp
      (Primrec.nat_add.comp (primrec_domSize.comp Primrec.fst) (Primrec.const 2))) g3
  have g2 : Primrec₂ fun (a : DomDesc × ℕ × ℕ) (m : ℕ) =>
      (List.range (a.1.size + 2)).flatMap fun j =>
        (List.range a.1.methods.length).map fun m' =>
          ((a.2.1, a.2.2, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ) := by
    have hp : Primrec fun w : (DomDesc × ℕ × ℕ) × ℕ =>
        ((w.1.1, w.1.2.1, w.1.2.2, w.2) : DomDesc × ℕ × ℕ × ℕ) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
    exact Primrec.to₂ ((h3.comp hp).of_eq fun w => rfl)
  have h2 : Primrec fun a : DomDesc × ℕ × ℕ =>
      (List.range a.1.methods.length).flatMap fun m =>
        (List.range (a.1.size + 2)).flatMap fun j =>
          (List.range a.1.methods.length).map fun m' =>
            ((a.2.1, a.2.2, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ) :=
    Primrec.list_flatMap (Primrec.list_range.comp (hlen Primrec.fst)) g2
  have g1 : Primrec₂ fun (a : DomDesc × ℕ) (i : ℕ) =>
      (List.range a.1.methods.length).flatMap fun m =>
        (List.range (a.1.size + 2)).flatMap fun j =>
          (List.range a.1.methods.length).map fun m' =>
            ((a.2, i, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ) := by
    have hp : Primrec fun w : (DomDesc × ℕ) × ℕ =>
        ((w.1.1, w.1.2, w.2) : DomDesc × ℕ × ℕ) :=
      Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
    exact Primrec.to₂ ((h2.comp hp).of_eq fun w => rfl)
  have h1 : Primrec fun a : DomDesc × ℕ =>
      (List.range a.1.methods.length).flatMap fun i =>
        (List.range a.1.methods.length).flatMap fun m =>
          (List.range (a.1.size + 2)).flatMap fun j =>
            (List.range a.1.methods.length).map fun m' =>
              ((a.2, i, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ) :=
    Primrec.list_flatMap (Primrec.list_range.comp (hlen Primrec.fst)) g1
  have g0 : Primrec₂ fun (d : DomDesc) (k : ℕ) =>
      (List.range d.methods.length).flatMap fun i =>
        (List.range d.methods.length).flatMap fun m =>
          (List.range (d.size + 2)).flatMap fun j =>
            (List.range d.methods.length).map fun m' =>
              ((k, i, m, j, m') : ℕ × ℕ × ℕ × ℕ × ℕ) :=
    Primrec.to₂ ((h1.comp (Primrec.pair Primrec.fst Primrec.snd)).of_eq fun w => rfl)
  exact (Primrec.list_flatMap (Primrec.const (List.range 6)) g0).of_eq fun d => rfl

theorem primrec_trActions : Primrec trActions := by
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp primrec_cacts)) ?_
  exact Primrec.pair Primrec.snd
    (primrec_specOf.comp Primrec.fst
      (Primrec.list_getI.comp (primrec_cacts.comp Primrec.fst) Primrec.snd))

theorem primrec_trStripsDom : Primrec trStripsDom :=
  primrec_stripsDom.comp primrec_trActions

theorem primrec_trStripsInst : Primrec trStripsInst := by
  have hinit : Primrec fun q : InstDesc => (q.initList.map encSt) ++ [encCall (rootName q)] := by
    refine Primrec.list_append.comp
      (Primrec.list_map primrec_initList
        (Primrec.nat_mul.comp (Primrec.const 6) Primrec.snd).to₂) ?_
    exact Primrec.list_cons.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 6) primrec_rootName) (Primrec.const 3))
      (Primrec.const [])
  have hgoal : Primrec fun q : InstDesc => (q.goalList.map encSt) ++ [encDone] :=
    Primrec.list_append.comp
      (Primrec.list_map primrec_goalList
        (Primrec.nat_mul.comp (Primrec.const 6) Primrec.snd).to₂)
      (Primrec.const [encDone])
  exact primrec_stripsInst.comp hinit hgoal

theorem computable_trStripsDom : Computable trStripsDom := primrec_trStripsDom.to_comp

theorem computable_trStripsInst : Computable trStripsInst := primrec_trStripsInst.to_comp

end Syn

end HTN
