import HtnComplexity.PT.Core
/-!
# List combinators of the polynomial-time calculus

The workhorse is **emission over the entries of a list with full context**
(`HTN.Syn.PolyDom.PT.flatMapSplits`): for every decomposition `l = l₁ ++ b :: l₂` of a list
computed in polynomial time, a list computed in polynomial time from the context, `l₁`, `b` and
`l₂` is emitted, and the results are concatenated.  On the codes this is one pass over the entry
positions of the serialised list (`HTN.PTime.cobham_fmTailsC`), so no size bookkeeping is needed.
From it: `flatMap`, `map`, `filter`, `dedup`, membership, `getI`, `List.range` of a length, and
the arithmetic comparisons and affine maps on numbers.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime Compress TOPlan PolyInst

variable {α β γ δ ε : Type} [BEnc α] [BEnc β] [BEnc γ] [BEnc δ] [BEnc ε]

/-! ### Emission over the entries, with full context -/

/-- At every entry position `s` of the serialised list `y`, the chunk `H` of the context `x`, the
list of earlier entries, the entry and the list of later entries. -/
def emitEnt (H : List Bool → List Bool) (x y : List Bool) : List Bool :=
  y.tails.flatMap fun s =>
    if entPos y s = true then H (x ++ ((cutS y s ++ [false]) ++ (undbl (nvAt s) ++ tailCode s)))
    else []

theorem emitEnt_enc (H : List Bool → List Bool) (x : List Bool) (l : List β) :
    emitEnt H x (enc l) =
      (splits l).flatMap fun p => H (x ++ (enc p.1 ++ (enc p.2.1 ++ enc p.2.2))) := by
  unfold emitEnt
  rw [enc_list]
  have h := flatMap_entPos (enc : β → List Bool) l []
    (fun s => H (x ++ ((cutS (blist (l.map enc)) s ++ [false]) ++ (undbl (nvAt s) ++ tailCode s))))
  simp only [List.append_nil] at h
  rw [h]
  refine List.flatMap_congr fun p hp => ?_
  have hl := mem_splits.1 hp
  have h1 : cutS (blist (l.map enc)) (blist ((p.2.1 :: p.2.2).map enc)) ++ [false] = enc p.1 := by
    have := cutS_entry (enc : β → List Bool) hl []
    simp only [List.append_nil] at this
    rw [this, enc_list, blist_eq_entriesEnc]
  have h2 : undbl (nvAt (blist ((p.2.1 :: p.2.2).map enc))) = enc p.2.1 := by
    simp only [nvAt, List.map_cons, blist_cons, List.tail_cons]
    rw [show bstr (enc p.2.1) ++ blist (p.2.2.map enc) = bstr (enc p.2.1) ++ blist (p.2.2.map enc)
      from rfl, bpre_bstr, undbl_bstr]
  have h3 : tailCode (blist ((p.2.1 :: p.2.2).map enc)) = enc p.2.2 := tailCode_cons p.2.1 p.2.2
  rw [h1, h2, h3]

theorem uc_emitEnt {H : List Bool → List Bool} (hH : UC H) {Y : List Bool → List Bool}
    (hY : UC Y) : UC fun x => emitEnt H x (Y x) := by
  have hY' : Cobham fun args : Args => Y (args.tail.getD 0 []) := cobham_tailArgs hY
  have hx' : Cobham fun args : Args => args.tail.getD 0 [] := cobham_tailArgs cobham_var0
  refine (cobham_fmTailsC (G := fun args =>
      if entPos (Y (args.tail.getD 0 [])) (args.getD 0 []) = true then
        H (args.tail.getD 0 [] ++ ((cutS (Y (args.tail.getD 0 [])) (args.getD 0 []) ++ [false]) ++
          (undbl (nvAt (args.getD 0 [])) ++ tailCode (args.getD 0 []))))
      else [])
    (cobham_ifNil (cobhamB_entPos hY' cobham_var0)
      (hH.app (PH.cobham_app hx' (PH.cobham_app
        (PH.cobham_app (cobham_cut hY' cobham_var0) (cobham_const _))
        (PH.cobham_app (cobham_undbl (cobham_nvAt cobham_var0)) (uc_tailCode.app cobham_var0))))))
    hY).of_eq' fun args => ?_
  simp [fmTailsL, emitEnt]

/-- **Emission over the decompositions of a list, with full context.** -/
theorem PT.flatMapSplits {f : α → List β} {g : α → List β → β → List β → List γ} (hf : PT f)
    (hg : PT fun q : α × List β × β × List β => g q.1 q.2.1 q.2.2.1 q.2.2.2) :
    PT fun a => (splits (f a)).flatMap fun p => g a p.1 p.2.1 p.2.2 := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  have hD : UC fun x : List Bool => x.dropLast :=
    (cobham_rev (cobham_tail' (cobham_rev cobham_var0))).of_eq' fun args => by
      simp [List.tail_reverse]
  refine ⟨fun x => emitEnt (fun z => (G z).dropLast) x (F x) ++ [false],
    PH.cobham_app (uc_emitEnt (hD.comp hG) hF) (cobham_const _), fun a => ?_⟩
  beta_reduce
  rw [hFf, emitEnt_enc, enc_list, blist_eq_entriesEnc]
  congr 1
  simp only [entriesEnc, List.map_flatMap, List.flatMap_assoc]
  refine List.flatMap_congr fun p _ => ?_
  have := hGg (a, p.1, p.2.1, p.2.2)
  simp only [enc_prod] at this
  rw [this, enc_list, blist_eq_entriesEnc, List.dropLast_concat, entriesEnc, List.flatMap_map]

end PolyDom

end Syn

end HTN
