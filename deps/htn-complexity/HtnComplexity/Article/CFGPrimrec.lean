import HtnComplexity.Article.CFGDesc
/-!
# The grammar encoding is primitive recursive

`HTN.Article.CFGEnc.primrec_cfgProb` — the description `cfgProb g₁ g₂` of the encoding of
Thm. 4.1.1 is a primitive recursive function of the two grammars, so the encoding is a
computable reduction.  Along the way: the full grid descriptions are primitive recursive
(`HTN.Article.primrec_gridDescFull`), and so is the embedding `HTN.Article.ofSyn` of positive
descriptions.
-/

namespace HTN

namespace Article

open CFG Syn

/-! ### Grid descriptions -/

theorem primrec_gridRow : Primrec₂ gridRow := (Primrec.list_getD []).of_eq fun _ _ => rfl

private theorem primrec_len_row : Primrec fun p : List (List (Bool × ℕ)) × ℕ =>
    (gridRow p.1 p.2).length :=
  Primrec.list_length.comp (primrec_gridRow.comp Primrec.fst Primrec.snd)

theorem primrec_cellIds : Primrec cellIds := by
  unfold cellIds
  refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) ?_
  have h : Primrec fun x : (List (List (Bool × ℕ)) × ℕ) × ℕ => Nat.pair x.1.2 x.2 :=
    Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map (Primrec.list_range.comp primrec_len_row) h.to₂

theorem primrec_cellLbl : Primrec cellLbl := by
  unfold cellLbl
  refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) ?_
  have h1 : Primrec fun x : (List (List (Bool × ℕ)) × ℕ) × ℕ => Nat.pair x.1.2 x.2 :=
    Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h2 : Primrec fun x : (List (List (Bool × ℕ)) × ℕ) × ℕ =>
      (gridRow x.1.1 x.1.2).getD x.2 (false, 0) :=
    (Primrec.list_getD (false, 0)).comp
      (primrec_gridRow.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  exact Primrec.list_map (Primrec.list_range.comp primrec_len_row) (h1.pair h2).to₂

/-- One pair of `cellOrdFull`, as a function of `(((ls, i), j), d)`. -/
private def ordAt (x : ((List (List (Bool × ℕ)) × ℕ) × ℕ) × ℕ) : ℕ × ℕ :=
  (Nat.pair x.1.1.2 x.1.2, Nat.pair x.1.1.2 (x.1.2 + x.2 + 1))

private theorem primrec_ordAt : Primrec ordAt := by
  unfold ordAt
  have hi : Primrec fun x : ((List (List (Bool × ℕ)) × ℕ) × ℕ) × ℕ => x.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hj : Primrec fun x : ((List (List (Bool × ℕ)) × ℕ) × ℕ) × ℕ => x.1.2 :=
    Primrec.snd.comp Primrec.fst
  exact Primrec.pair (Primrec₂.natPair.comp hi hj) (Primrec₂.natPair.comp hi
    (Primrec.succ.comp (Primrec.nat_add.comp hj Primrec.snd)))

theorem primrec_cellOrdFull : Primrec cellOrdFull := by
  have e : cellOrdFull = fun ls => (List.range ls.length).flatMap fun i =>
      (List.range (gridRow ls i).length).flatMap fun j =>
        (List.range ((gridRow ls i).length - j - 1)).map fun d => ordAt (((ls, i), j), d) := rfl
  rw [e]
  refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) ?_
  refine Primrec.list_flatMap (Primrec.list_range.comp primrec_len_row) ?_
  refine Primrec.list_map ?_ (primrec_ordAt.comp
    ((Primrec.fst.pair Primrec.snd).comp (Primrec.fst.pair Primrec.snd))).to₂
  · have hlen : Primrec fun x : (List (List (Bool × ℕ)) × ℕ) × ℕ => (gridRow x.1.1 x.1.2).length :=
      primrec_len_row.comp Primrec.fst
    exact Primrec.list_range.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp hlen Primrec.snd)
      (Primrec.const 1))

/-- **Full grid descriptions are primitive recursive.** -/
theorem primrec_gridDescFull : Primrec gridDescFull :=
  Primrec.pair primrec_cellIds (Primrec.pair primrec_cellOrdFull primrec_cellLbl)

theorem primrec_encLabel : Primrec (encLabel (A := ℕ) (C := ℕ) id id) := by
  have : encLabel (A := ℕ) (C := ℕ) id id = fun x => Sum.casesOn x (fun a => (false, a))
      (fun c => (true, c)) := by
    funext x; cases x <;> rfl
  rw [this]
  exact Primrec.sumCasesOn Primrec.id ((Primrec.const false).pair Primrec.snd).to₂
    ((Primrec.const true).pair Primrec.snd).to₂

theorem primrec_gridDescFullOf : Primrec (gridDescFullOf (A := ℕ) (C := ℕ) id id) :=
  primrec_gridDescFull.comp (Primrec.list_map Primrec.id
    (Primrec.list_map Primrec.snd (primrec_encLabel.comp Primrec.snd).to₂).to₂)

/-! ### The embedding of positive descriptions -/

theorem primrec_ofSynAct : Primrec ofSynAct := by
  unfold ofSynAct
  exact Primrec.pair Primrec.fst (Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair (Primrec.const []) (Primrec.snd.comp Primrec.snd)))

theorem primrec_ofSyn : Primrec₂ ofSyn := by
  unfold ofSyn
  refine Primrec.pair (Primrec.pair ?_ (Primrec.snd.comp Primrec.fst)) ?_
  · exact Primrec.list_map (Primrec.fst.comp Primrec.fst) (primrec_ofSynAct.comp Primrec.snd).to₂
  · exact Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const [])))

namespace CFGEnc

/-! ### The encoding -/

theorem primrec_terms : Primrec terms := by
  unfold terms
  refine Primrec.list_flatMap (Primrec.snd : Primrec fun g : Grammar => g.2) ?_
  refine Primrec.list_flatMap (Primrec.snd.comp Primrec.snd : Primrec fun p : Grammar × Rule => p.2.2) ?_
  have : (fun (_ : Grammar × Rule) (x : Sym) => Sum.elim (fun a => [a]) (fun _ => []) x) =
      fun _ x => Sum.casesOn x (fun a => [a]) (fun _ => ([] : List ℕ)) := by
    funext _ x; cases x <;> rfl
  rw [this]
  exact (Primrec.sumCasesOn Primrec.snd
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂ (Primrec.const []).to₂).to₂

theorem primrec_bnd : Primrec₂ bnd := by
  unfold bnd
  refine (Primrec.succ.comp (?_ : Primrec fun p : Grammar × Grammar =>
    (terms p.1 ++ terms p.2).foldr max 0)).to₂
  exact Primrec.list_foldr (Primrec.list_append.comp (primrec_terms.comp Primrec.fst)
      (primrec_terms.comp Primrec.snd)) (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem primrec_actOf : Primrec actOf := by
  unfold actOf
  have hv : Primrec fun n : ℕ => n / 2 + 2 :=
    Primrec.nat_add.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)) (Primrec.const 2)
  have hl : Primrec fun n : ℕ => [1, n / 2 + 2] :=
    Primrec.list_cons.comp (Primrec.const 1) (Primrec.list_cons.comp hv (Primrec.const []))
  refine Primrec.ite ?_ ?_ ?_
  · exact Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  · exact Primrec.pair (Primrec.const [0]) (Primrec.pair hl (Primrec.const [0]))
  · exact Primrec.pair hl (Primrec.pair (Primrec.const [0]) hl)

theorem primrec_actD : Primrec actD := by
  unfold actD
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2)
    Primrec.id)) (Primrec.pair Primrec.snd (primrec_actOf.comp Primrec.snd)).to₂

theorem primrec_trS (k : ℕ) : Primrec (trS k) := by
  have : trS k = fun x => Sum.casesOn x (fun a => Sum.inl (2 * a + k))
      (fun X => Sum.inr (2 * X + k)) := by
    funext x; cases x <;> rfl
  rw [this]
  have h : Primrec fun a : ℕ => 2 * a + k :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const k)
  exact Primrec.sumCasesOn Primrec.id ((Primrec.sumInl (β := ℕ)).comp (h.comp Primrec.snd)).to₂
    ((Primrec.sumInr (α := ℕ)).comp (h.comp Primrec.snd)).to₂

theorem primrec_methD (k : ℕ) : Primrec (methD k) := by
  unfold methD
  refine Primrec.pair ?_ ?_
  · exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      (Primrec.const k)
  · exact primrec_gridDescFullOf.comp (Primrec.list_cons.comp
      (Primrec.list_map Primrec.snd ((primrec_trS k).comp Primrec.snd).to₂) (Primrec.const []))

theorem primrec_cfgDom : Primrec₂ cfgDom := by
  unfold cfgDom
  refine Primrec.pair (primrec_actD.comp primrec_bnd) ?_
  exact Primrec.list_append.comp
    (Primrec.list_map (Primrec.snd.comp Primrec.fst) ((primrec_methD 0).comp Primrec.snd).to₂)
    (Primrec.list_map (Primrec.snd.comp Primrec.snd) ((primrec_methD 1).comp Primrec.snd).to₂)

theorem primrec_cfgInst : Primrec₂ cfgInst := by
  unfold cfgInst
  refine Primrec.pair (Primrec.const [0]) (Primrec.pair (Primrec.const [0]) ?_)
  have h1 : Primrec fun p : Grammar × Grammar => (Sum.inr (2 * p.1.1) : ℕ ⊕ ℕ) :=
    (Primrec.sumInr (α := ℕ)).comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.fst.comp Primrec.fst))
  have h2 : Primrec fun p : Grammar × Grammar => (Sum.inr (2 * p.2.1 + 1) : ℕ ⊕ ℕ) :=
    (Primrec.sumInr (α := ℕ)).comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.fst.comp Primrec.snd)) (Primrec.const 1))
  refine primrec_gridDescFullOf.comp ?_
  exact Primrec.list_cons.comp (Primrec.list_cons.comp h1 (Primrec.const []))
    (Primrec.list_cons.comp (Primrec.list_cons.comp h2 (Primrec.const [])) (Primrec.const []))

/-- **The encoding is primitive recursive in the two grammars.** -/
theorem primrec_cfgProb : Primrec₂ cfgProb :=
  primrec_ofSyn.comp primrec_cfgDom primrec_cfgInst

end CFGEnc

end Article

end HTN
