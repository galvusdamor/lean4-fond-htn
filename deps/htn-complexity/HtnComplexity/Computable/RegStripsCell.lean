import HtnComplexity.Computable.RegStrips
/-!
# The cell (`TO-HTN-REG` rooted, `STRIPS`) of the computable table

The construction and its correctness are in
[`RegStrips.lean`](RegStrips.lean); this file adds the two remaining halves of a cell of the
computable compilability table — the **size** of the compiled description (polynomial, in fact
cubic, in the source description) and the **computability** of the two translations (both are
primitive recursive) — and assembles them into
`HTN.Syn.compSyn_TO_HTN_REG_root_to_STRIPS`.
-/

namespace HTN

namespace Syn

/-! ### Size -/

theorem sum_le_length_mul {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) :
    l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a (by simp)
    have : (t.length + 1) * B = B + t.length * B := by ring
    simp only [List.sum_cons, List.length_cons]
    omega

theorem length_le_sum_map_methodSize (l : List MethodDesc) :
    l.length ≤ (l.map MethodDesc.size).sum := by
  induction l with
  | nil => simp
  | cons e es ih =>
    have h1 : MethodDesc.size e = 1 + e.2.size := rfl
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem length_methods_le_size (d : DomDesc) : d.methods.length ≤ d.size := by
  have h := length_le_sum_map_methodSize d.methods
  simp only [DomDesc.size]
  omega

/-- Every listed method mentions at most `d.size` task identifiers. -/
theorem length_ids_getI_le (d : DomDesc) (i : ℕ) :
    (d.methods.getI i).2.ids.length ≤ d.size := by
  by_cases hi : i < d.methods.length
  · have hmem : d.methods.getI i ∈ d.methods := mem_methods_getI hi
    have h1 : MethodDesc.size (d.methods.getI i) ≤ (d.methods.map MethodDesc.size).sum :=
      DomDesc.mem_le_sum MethodDesc.size hmem
    have h2 : MethodDesc.size (d.methods.getI i) = 1 + (d.methods.getI i).2.size := rfl
    have h3 : (d.methods.getI i).2.size =
      (d.methods.getI i).2.ids.length + (d.methods.getI i).2.ordList.length +
        (d.methods.getI i).2.lbl.length := rfl
    simp only [DomDesc.size]
    omega
  · rw [List.getI_eq_default (l := d.methods) (by omega)]
    exact Nat.zero_le _

theorem length_body_getI_le (d : DomDesc) (i : ℕ) :
    (TnDesc.bodyOf (d.methods.getI i).2).1.length ≤ d.size + 1 := by
  have h1 := TnDesc.length_bodyOf_le (d.methods.getI i).2
  have h2 := length_ids_getI_le d i
  omega

theorem size_regAction_le (d : DomDesc) (i : ℕ) :
    ActionDesc.size (regAction d i) ≤ 8 * ((d.size + 1) * (d.size + 1)) := by
  set s := d.size with hs
  set b := (TnDesc.bodyOf (d.methods.getI i).2).1 with hb
  have hblen : b.length ≤ s + 1 := length_body_getI_le d i
  have hmono : ∀ n : ℕ, n ≤ b.length * s → n ≤ (s + 1) * s := fun n hn =>
    le_trans hn (Nat.mul_le_mul_right s hblen)
  have hp : (d.seqPreList b).length ≤ (s + 1) * s :=
    hmono _ (DomDesc.length_seqPreList_le d b)
  have ha : (d.seqAddList b).length ≤ (s + 1) * s :=
    hmono _ (DomDesc.length_seqAddList_le d b)
  have hd : (d.seqDelList b).length ≤ (s + 1) * s :=
    hmono _ (DomDesc.length_seqDelList_le d b)
  have hl1 : (regAction d i).2.1.length ≤ (d.seqPreList b).length + 2 := by
    rcases hf : (d.macroFold b).2 with _ | _ <;>
      simp [regAction, DomDesc.seqPreList, ← hb, hf]
  have hl2 : (regAction d i).2.2.1.length ≤ (d.seqAddList b).length + 1 := by
    rcases hn : (TnDesc.bodyOf (d.methods.getI i).2).2 with _ | c' <;>
      simp [regAction, DomDesc.seqAddList, ← hb, hn]
  have hl3 : (regAction d i).2.2.2.length ≤ (d.seqDelList b).length + 1 := by
    simp [regAction, DomDesc.seqDelList, ← hb]
  have hA : ActionDesc.size (regAction d i) =
      1 + (regAction d i).2.1.length + (regAction d i).2.2.1.length +
        (regAction d i).2.2.2.length := rfl
  have hq1 : (s + 1) * s ≤ (s + 1) * (s + 1) := Nat.mul_le_mul_left _ (by omega)
  have hq2 : 1 ≤ (s + 1) * (s + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

theorem sum_map_stepMethods (acts : List ActionDesc) :
    ((acts.map fun ad => ((0, stepBody ad.1) : MethodDesc)).map MethodDesc.size).sum =
      6 * acts.length := by
  induction acts with
  | nil => rfl
  | cons a l ih =>
    have h6 : MethodDesc.size ((0, stepBody a.1) : MethodDesc) = 6 := rfl
    simp only [List.map_cons, List.sum_cons, h6, ih, List.length_cons]
    ring

theorem size_regStripsInst_le (q : InstDesc) : (regStripsInst q).size ≤ q.size + 4 := by
  have h : (regStripsInst q).size =
      (q.initList.length + 1) + (q.goalList.length + 1) + 2 := by
    simp [regStripsInst, InstDesc.size, stripsInst, InstDesc.initList, InstDesc.goalList,
      InstDesc.tnI, initTn, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have h2 : q.size = q.initList.length + q.goalList.length + q.tnI.size := rfl
  omega

theorem size_regStripsDom_le (d : DomDesc) :
    (regStripsDom d).size ≤ 20 * ((d.size + 1) * (d.size + 1) * (d.size + 1)) := by
  set s := d.size with hs
  have hlen : (regActions d).length = d.methods.length := by
    simp [regActions]
  have hn : d.methods.length ≤ s := length_methods_le_size d
  have hacts : ((regActions d).map ActionDesc.size).sum ≤
      d.methods.length * (8 * ((s + 1) * (s + 1))) := by
    have h := sum_le_length_mul (l := (regActions d).map ActionDesc.size)
      (B := 8 * ((s + 1) * (s + 1))) ?_
    · rwa [List.length_map, hlen] at h
    · intro x hx
      obtain ⟨ad, had, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 had
      exact size_regAction_le d i
  have hmeth : ((regStripsDom d).methods.map MethodDesc.size).sum =
      1 + 6 * d.methods.length := by
    have h1 : MethodDesc.size ((0, emptyBody) : MethodDesc) = 1 := rfl
    simp only [regStripsDom, stripsDom_methods, List.map_cons, List.sum_cons, h1,
      sum_map_stepMethods, hlen]
  have hsize : (regStripsDom d).size =
      ((regActions d).map ActionDesc.size).sum +
        ((regStripsDom d).methods.map MethodDesc.size).sum := rfl
  -- assemble
  have hb : 0 < (s + 1) * (s + 1) := by positivity
  have hkey : d.methods.length * (8 * ((s + 1) * (s + 1))) ≤
      8 * ((s + 1) * (s + 1) * (s + 1)) := by
    have : d.methods.length * (8 * ((s + 1) * (s + 1))) ≤
        (s + 1) * (8 * ((s + 1) * (s + 1))) := Nat.mul_le_mul_right _ (by omega)
    calc d.methods.length * (8 * ((s + 1) * (s + 1)))
        ≤ (s + 1) * (8 * ((s + 1) * (s + 1))) := this
      _ = 8 * ((s + 1) * (s + 1) * (s + 1)) := by ring
  have hsmall : 1 + 6 * d.methods.length ≤ 12 * ((s + 1) * (s + 1) * (s + 1)) := by
    have h1 : (s + 1) ≤ (s + 1) * (s + 1) * (s + 1) := by nlinarith
    omega
  omega

/-! ### Computability -/

open Primrec

theorem primrec_regAction : Primrec₂ regAction := by
  have hd : Primrec fun w : DomDesc × ℕ => w.1 := Primrec.fst
  have he : Primrec fun w : DomDesc × ℕ => w.1.methods.getI w.2 :=
    Primrec.list_getI.comp (primrec_methods.comp Primrec.fst) Primrec.snd
  have hb : Primrec fun w : DomDesc × ℕ => TnDesc.bodyOf (w.1.methods.getI w.2).2 :=
    TnDesc.primrec_bodyOf.comp (Primrec.snd.comp he)
  have hb1 : Primrec fun w : DomDesc × ℕ => (TnDesc.bodyOf (w.1.methods.getI w.2).2).1 :=
    Primrec.fst.comp hb
  have hb2 : Primrec fun w : DomDesc × ℕ => (TnDesc.bodyOf (w.1.methods.getI w.2).2).2 :=
    Primrec.snd.comp hb
  have hm : Primrec fun w : DomDesc × ℕ =>
      w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1 :=
    DomDesc.primrec_macroFold.comp hd hb1
  have hquad : ∀ {γ : Type} [Primcodable γ] {f : γ → List ℕ}, Primrec f →
      Primrec fun x => (f x).map fun v => 4 * v := by
    intro γ _ f hf
    exact Primrec.list_map hf (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd).to₂
  have hpre : Primrec fun w : DomDesc × ℕ =>
      (w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1).1.1.map fun v => 4 * v :=
    hquad (Primrec.fst.comp (Primrec.fst.comp hm))
  have hadd : Primrec fun w : DomDesc × ℕ =>
      (w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1).1.2.1.map fun v => 4 * v :=
    hquad (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hm)))
  have hdel : Primrec fun w : DomDesc × ℕ =>
      (w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1).1.2.2.map fun v => 4 * v :=
    hquad (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hm)))
  have hpend : Primrec fun w : DomDesc × ℕ => 4 * (w.1.methods.getI w.2).1 + 1 :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.fst.comp he))
  have hflag : Primrec fun w : DomDesc × ℕ =>
      (if (w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1).2 then [] else [3] :
        List ℕ) := by
    refine Primrec.ite (PrimrecRel.comp Primrec.eq (Primrec.snd.comp hm)
      (Primrec.const true)) (Primrec.const []) (Primrec.const [3])
  have hnext : Primrec fun w : DomDesc × ℕ =>
      (match (TnDesc.bodyOf (w.1.methods.getI w.2).2).2 with
        | none => [2]
        | some c' => [4 * c' + 1] : List ℕ) := by
    have hg : Primrec₂ fun (_ : DomDesc × ℕ) (c' : ℕ) => ([4 * c' + 1] : List ℕ) :=
      Primrec.to₂ (Primrec.list_cons.comp
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd))
        (Primrec.const []))
    refine Primrec.of_eq
      (Primrec.option_casesOn (σ := List ℕ) hb2 (Primrec.const [2]) hg) ?_
    intro w
    rcases (TnDesc.bodyOf (w.1.methods.getI w.2).2).2 with _ | c' <;> simp
  have hmain : Primrec fun w : DomDesc × ℕ =>
      ((w.2,
        ((w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1).1.1.map fun v => 4 * v) ++
          (4 * (w.1.methods.getI w.2).1 + 1) ::
            (if (w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1).2 then [] else [3]),
        ((w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1).1.2.1.map fun v => 4 * v) ++
          (match (TnDesc.bodyOf (w.1.methods.getI w.2).2).2 with
            | none => [2]
            | some c' => [4 * c' + 1]),
        ((w.1.macroFold (TnDesc.bodyOf (w.1.methods.getI w.2).2).1).1.2.2.map fun v => 4 * v) ++
          [4 * (w.1.methods.getI w.2).1 + 1]) : ActionDesc) :=
    Primrec.pair Primrec.snd
      (Primrec.pair (Primrec.list_append.comp hpre (Primrec.list_cons.comp hpend hflag))
        (Primrec.pair (Primrec.list_append.comp hadd hnext)
          (Primrec.list_append.comp hdel
            (Primrec.list_cons.comp hpend (Primrec.const [])))))
  exact Primrec.to₂ (hmain.of_eq fun w => rfl)

theorem primrec_regActions : Primrec regActions := by
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp primrec_methods)) ?_
  exact primrec_regAction.comp Primrec.fst Primrec.snd

theorem primrec_regStripsDom : Primrec regStripsDom :=
  primrec_stripsDom.comp primrec_regActions

theorem primrec_rootName : Primrec rootName :=
  Primrec.list_headI.comp (primrec_compoundNames.comp primrec_tnI)

theorem primrec_regStripsInst : Primrec regStripsInst := by
  have hinit : Primrec fun q : InstDesc => (q.initList.map fun v => 4 * v) ++
      [4 * rootName q + 1] := by
    refine Primrec.list_append.comp
      (Primrec.list_map primrec_initList
        (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd).to₂) ?_
    exact Primrec.list_cons.comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 4) primrec_rootName))
      (Primrec.const [])
  have hgoal : Primrec fun q : InstDesc => (q.goalList.map fun v => 4 * v) ++ [2] :=
    Primrec.list_append.comp
      (Primrec.list_map primrec_goalList
        (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd).to₂)
      (Primrec.const [2])
  exact primrec_stripsInst.comp hinit hgoal

theorem computable_regStripsDom : Computable regStripsDom := primrec_regStripsDom.to_comp

theorem computable_regStripsInst : Computable regStripsInst := primrec_regStripsInst.to_comp


end Syn

end HTN
