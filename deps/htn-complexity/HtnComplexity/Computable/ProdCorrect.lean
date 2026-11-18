import HtnComplexity.Computable.ProdDom
import HtnComplexity.Computable.ChainSplit
/-!
# Correctness of the product construction

The product domain of `HtnComplexity/Computable/ProdDom.lean` folds the chain that is still
to be executed into the compound names.  This file proves that it is correct:

* `HTN.Syn.netYield_singleTn_iff_derivesW` — for a regular described domain, the refinements of a
  single compound task are its derivations (the description-level form of
  `HTN.Problem.netYield_iff_derivesW`);
* `HTN.Syn.netYield_chainTn_iff_derivesChainW` — the refinements of a described chain are the
  concatenations of derivations of its entries;
* `HTN.Syn.derivesW_prod_iff` — **the derivations of the product name `⟨c₁, c₂ … c_j⟩` are
  exactly the derivations of the chain `c₁ … c_j`**, for every chain of at most `k` names;
* `HTN.Syn.solvable_prod_iff` — hence the compiled problem is solvable exactly when the source
  problem is.

Neither translation looks at the other side: `prodDom k d` reads only the domain description and
`prodInst q` only the instance description, so the construction is a modular compilation.
-/

namespace HTN

namespace Syn

/-! ### The source side: refinements are derivations -/

/-- **The refinements of a single described compound task are its derivations.** -/
theorem netYield_singleTn_iff_derivesW {d : DomDesc} {q : InstDesc} (hreg : d.MethodsReg)
    {c : ℕ} {as : List ℕ} :
    d.toDomain.NetYield (singleTn c).toTaskNetwork as ↔ (problem d q).DerivesW c as := by
  have hT : (problem d ((q.initList, q.goalList, singleTn c) : InstDesc)).tnI.T = {0} := rfl
  have hα : (problem d ((q.initList, q.goalList, singleTn c) : InstDesc)).tnI.α 0 =
      Sum.inr c := rfl
  have h := Problem.netYield_iff_derivesW
    (P := problem d ((q.initList, q.goalList, singleTn c) : InstDesc))
    (problem_wf _ _) (isRegularM_problem hreg) hT hα (as := as)
  exact h.trans (Problem.derivesW_congr
    (P := problem d ((q.initList, q.goalList, singleTn c) : InstDesc)) (P' := problem d q) rfl)

/-- **The refinements of a described chain are the derivations of its entries, concatenated.** -/
theorem netYield_chainTn_iff_derivesChainW {d : DomDesc} {q : InstDesc} (hreg : d.MethodsReg) :
    ∀ (ws : List ℕ) (as : List ℕ),
      d.toDomain.NetYield (chainTn ws).toTaskNetwork as ↔ (problem d q).DerivesChainW ws as
  | [], as => by rw [netYield_chainTn_nil_iff, Problem.derivesChainW_nil]
  | c :: ws, as => by
      rw [netYield_chainTn_cons_iff, Problem.derivesChainW_cons]
      exact exists_congr fun as₁ => exists_congr fun as₂ =>
        and_congr Iff.rfl (and_congr (netYield_singleTn_iff_derivesW hreg)
          (netYield_chainTn_iff_derivesChainW hreg ws as₂))

/-! ### Derivable names are heads -/

theorem mem_heads_of_derivesW {d : DomDesc} {q : InstDesc} {c : ℕ} {as : List ℕ}
    (h : (problem d q).DerivesW c as) : c ∈ d.heads := by
  cases h with
  | @last c os m hm hc _ =>
      obtain ⟨e, he, rfl⟩ := hm
      exact mem_heads_iff.2 ⟨e, he, hc⟩
  | @cons c c' os rest m hm hc _ _ =>
      obtain ⟨e, he, rfl⟩ := hm
      exact mem_heads_iff.2 ⟨e, he, hc⟩

theorem mem_heads_of_derivesChainW {d : DomDesc} {q : InstDesc} :
    ∀ {ws : List ℕ} {as : List ℕ}, (problem d q).DerivesChainW ws as → ∀ c ∈ ws, c ∈ d.heads
  | [], _, _ => by simp
  | c :: ws, as, h => by
      obtain ⟨as₁, as₂, -, h₁, h₂⟩ := h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact mem_heads_of_derivesW h₁
      · exact mem_heads_of_derivesChainW h₂ y hy

/-! ### The empty chain -/

theorem derivesW_prod_nil_iff {k : ℕ} {d : DomDesc} {q : InstDesc} {as : List ℕ} :
    (problem (prodDom k d) (prodInst q)).DerivesW (chainName []) as ↔ as = [] := by
  constructor
  · intro h
    cases h with
    | @last c os m hm hc hb =>
        obtain ⟨e, he, rfl⟩ := hm
        rcases mem_prodMethods_iff.1 he with rfl | ⟨e₀, he₀, w, -, rfl⟩
        · exact (TnDesc.hasBlock_nil.1 hb).1
        · exact absurd (chainName_inj.1 hc) (by simp)
    | @cons c c' os rest m hm hc hb _ =>
        obtain ⟨e, he, rfl⟩ := hm
        rcases mem_prodMethods_iff.1 he with rfl | ⟨e₀, he₀, w, -, rfl⟩
        · exact absurd (TnDesc.hasBlock_nil.1 hb).2 (by simp)
        · exact absurd (chainName_inj.1 hc) (by simp)
  · rintro rfl
    exact Problem.DerivesW.last (c := chainName []) ⟨(chainName [], TnDesc.nil),
      mem_prodMethods_nil, rfl⟩ rfl (TnDesc.hasBlock_nil.2 ⟨rfl, rfl⟩)

/-! ### From a source derivation to a product derivation -/

theorem derivesW_prod_of_derivesW {k : ℕ} {d : DomDesc} {q : InstDesc} (hreg : d.MethodsReg)
    {c : ℕ} {as₁ : List ℕ} (h : (problem d q).DerivesW c as₁) :
    ∀ w ∈ tuplesLe (k - 1) d.heads, ∀ as₂ : List ℕ,
      (problem (prodDom k d) (prodInst q)).DerivesW (chainName w) as₂ →
        (problem (prodDom k d) (prodInst q)).DerivesW (chainName (c :: w)) (as₁ ++ as₂) := by
  induction h with
  | @last c os m hm hc hb =>
      obtain ⟨e, he, rfl⟩ := hm
      have hc1 : e.1 = c := hc
      subst hc1
      intro w hw as₂ h₂
      have hregE : e.2.toTaskNetwork.IsRegular := hreg e he
      obtain ⟨xs, hxs, hos, hnx⟩ := (hasBlock_source hregE e.1).1 hb
      have hnext : TnDesc.hasNextB e.2 = false := by
        rcases hcase : TnDesc.hasNextB e.2 with _ | _
        · rfl
        · rw [TnDesc.tailName, hcase, if_pos rfl] at hnx
          exact absurd hnx.symm (by simp)
      rcases w with _ | ⟨u, w⟩
      · have hnil : as₂ = [] := derivesW_prod_nil_iff.1 h₂
        subst hnil
        rw [List.append_nil]
        exact Problem.DerivesW.last
          ⟨(chainName (e.1 :: []), prodBody e.2 []), mem_prodMethods_of_source he hw, rfl⟩ rfl
          ((hasBlock_prodBody_nil hregE hnext _).2 ⟨xs, hxs, hos, rfl⟩)
      · exact Problem.DerivesW.cons
          ⟨(chainName (e.1 :: u :: w), prodBody e.2 (u :: w)),
            mem_prodMethods_of_source he hw, rfl⟩ rfl
          ((hasBlock_prodBody_cons hnext u w _).2 ⟨xs, hxs, hos, rfl⟩) h₂
  | @cons c c' os rest m hm hc hb _ ih =>
      obtain ⟨e, he, rfl⟩ := hm
      have hc1 : e.1 = c := hc
      subst hc1
      intro w hw as₂ h₂
      have hregE : e.2.toTaskNetwork.IsRegular := hreg e he
      obtain ⟨xs, hxs, hos, hnx⟩ := (hasBlock_source hregE e.1).1 hb
      have hnext : TnDesc.hasNextB e.2 = true := by
        rcases hcase : TnDesc.hasNextB e.2 with _ | _
        · rw [TnDesc.tailName, hcase, if_neg (by simp)] at hnx
          exact absurd hnx (by simp)
        · rfl
      have hname : TnDesc.nextName e.2 = c' := by
        rw [TnDesc.tailName, hnext, if_pos rfl] at hnx
        exact (Option.some_injective ℕ hnx).symm
      have hstep := ih w hw as₂ h₂
      have hblock : (MethodDesc.toMethod
          ((chainName (e.1 :: w), prodBody e.2 w) : MethodDesc)).HasBlock os
            (some (chainName (c' :: w))) :=
        (hasBlock_prodBody_hasNext hregE hnext w _).2 ⟨xs, hxs, hos, by rw [hname]⟩
      rw [List.append_assoc]
      exact Problem.DerivesW.cons
        ⟨(chainName (e.1 :: w), prodBody e.2 w), mem_prodMethods_of_source he hw, rfl⟩ rfl
        hblock hstep

theorem derivesW_prod_of_derivesChainW {k : ℕ} {d : DomDesc} {q : InstDesc}
    (hreg : d.MethodsReg) :
    ∀ {ws : List ℕ}, ws.length ≤ k → ∀ {as : List ℕ}, (problem d q).DerivesChainW ws as →
      (problem (prodDom k d) (prodInst q)).DerivesW (chainName ws) as
  | [], _, as, h => by
      rw [Problem.derivesChainW_nil] at h
      subst h
      exact derivesW_prod_nil_iff.2 rfl
  | c :: ws, hlen, as, h => by
      obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h
      have hws : ws ∈ tuplesLe (k - 1) d.heads := by
        refine mem_tuplesLe.2 ⟨?_, fun y hy => mem_heads_of_derivesChainW h₂ y hy⟩
        simp only [List.length_cons] at hlen
        omega
      exact derivesW_prod_of_derivesW hreg h₁ ws hws as₂
        (derivesW_prod_of_derivesChainW hreg (by simp only [List.length_cons] at hlen; omega) h₂)

/-! ### From a product derivation to a source derivation -/

theorem derivesChainW_of_derivesW_prod {k : ℕ} {d : DomDesc} {q : InstDesc}
    (hreg : d.MethodsReg) {x : ℕ} {as : List ℕ}
    (h : (problem (prodDom k d) (prodInst q)).DerivesW x as) :
    ∀ ws : List ℕ, x = chainName ws → (problem d q).DerivesChainW ws as := by
  induction h with
  | @last x os m hm hc hb =>
      obtain ⟨e, he, rfl⟩ := hm
      intro ws hx
      rcases mem_prodMethods_iff.1 he with rfl | ⟨e₀, he₀, w, -, rfl⟩
      · have hws : ws = [] := (chainName_inj.1 (hc.trans hx)).symm
        subst hws
        rw [Problem.derivesChainW_nil]
        exact (TnDesc.hasBlock_nil.1 hb).1
      · have hws : ws = e₀.1 :: w := (chainName_inj.1 (hc.trans hx)).symm
        subst hws
        have hregE : e₀.2.toTaskNetwork.IsRegular := hreg e₀ he₀
        rcases hnext : TnDesc.hasNextB e₀.2 with _ | _
        · rcases w with _ | ⟨u, w⟩
          · obtain ⟨xs, hxs, hos, -⟩ := (hasBlock_prodBody_nil hregE hnext _).1 hb
            refine ⟨os, [], by simp, ?_, rfl⟩
            exact Problem.DerivesW.last ⟨e₀, he₀, rfl⟩ rfl
              ((hasBlock_source hregE e₀.1).2
                ⟨xs, hxs, hos, by rw [TnDesc.tailName, hnext, if_neg (by simp)]⟩)
          · obtain ⟨-, -, -, hnx⟩ := (hasBlock_prodBody_cons hnext u w _).1 hb
            exact absurd hnx (by simp)
        · obtain ⟨-, -, -, hnx⟩ := (hasBlock_prodBody_hasNext hregE hnext w _).1 hb
          exact absurd hnx (by simp)
  | @cons x x' os rest m hm hc hb _ ih =>
      obtain ⟨e, he, rfl⟩ := hm
      intro ws hx
      rcases mem_prodMethods_iff.1 he with rfl | ⟨e₀, he₀, w, -, rfl⟩
      · exact absurd (TnDesc.hasBlock_nil.1 hb).2 (by simp)
      · have hws : ws = e₀.1 :: w := (chainName_inj.1 (hc.trans hx)).symm
        subst hws
        have hregE : e₀.2.toTaskNetwork.IsRegular := hreg e₀ he₀
        rcases hnext : TnDesc.hasNextB e₀.2 with _ | _
        · rcases w with _ | ⟨u, w⟩
          · obtain ⟨-, -, -, hnx⟩ := (hasBlock_prodBody_nil hregE hnext _).1 hb
            exact absurd hnx (by simp)
          · obtain ⟨xs, hxs, hos, hnx⟩ := (hasBlock_prodBody_cons hnext u w _).1 hb
            have hx' : x' = chainName (u :: w) := Option.some_injective ℕ hnx
            refine ⟨os, rest, rfl, ?_, ih (u :: w) hx'⟩
            exact Problem.DerivesW.last ⟨e₀, he₀, rfl⟩ rfl
              ((hasBlock_source hregE e₀.1).2
                ⟨xs, hxs, hos, by rw [TnDesc.tailName, hnext, if_neg (by simp)]⟩)
        · obtain ⟨xs, hxs, hos, hnx⟩ := (hasBlock_prodBody_hasNext hregE hnext w _).1 hb
          have hx' : x' = chainName (TnDesc.nextName e₀.2 :: w) := Option.some_injective ℕ hnx
          obtain ⟨r₁, r₂, hrest, hr₁, hr₂⟩ := ih (TnDesc.nextName e₀.2 :: w) hx'
          refine ⟨os ++ r₁, r₂, by rw [hrest, List.append_assoc], ?_, hr₂⟩
          exact Problem.DerivesW.cons ⟨e₀, he₀, rfl⟩ rfl
            ((hasBlock_source hregE e₀.1).2
              ⟨xs, hxs, hos, by rw [TnDesc.tailName, hnext, if_pos rfl]⟩) hr₁

/-! ### The correctness theorems -/

/-- **The derivations of a product name are the derivations of the chain it stands for.** -/
theorem derivesW_prod_iff {k : ℕ} {d : DomDesc} {q : InstDesc} (hreg : d.MethodsReg)
    {ws : List ℕ} (hlen : ws.length ≤ k) {as : List ℕ} :
    (problem (prodDom k d) (prodInst q)).DerivesW (chainName ws) as ↔
      (problem d q).DerivesChainW ws as :=
  ⟨fun h => derivesChainW_of_derivesW_prod hreg h ws rfl,
    fun h => derivesW_prod_of_derivesChainW hreg hlen h⟩

/-- **The compiled instance has exactly the refinements of the source instance.** -/
theorem netYield_prodInst_iff {k : ℕ} {d : DomDesc} {q : InstDesc} (hreg : d.MethodsReg)
    (hchain : q.IsChainLe k) {as : List ℕ} :
    (prodDom k d).toDomain.NetYield (prodInst q).tnI.toTaskNetwork as ↔
      d.toDomain.NetYield q.tnI.toTaskNetwork as := by
  rw [prodInst_tnI, netYield_singleTn_iff_derivesW (q := prodInst q) (prodDom_methodsReg hreg),
    derivesW_prod_iff hreg hchain.2]
  conv_rhs => rw [hchain.1]
  rw [netYield_chainTn_iff_derivesChainW (q := q) hreg]

/-- **Correctness of the product construction.** -/
theorem solvable_prod_iff {k : ℕ} {d : DomDesc} {q : InstDesc} (hreg : d.MethodsReg)
    (hchain : q.IsChainLe k) :
    Solvable (prodDom k d) (prodInst q) ↔ Solvable d q := by
  rw [Solvable, Solvable, Problem.solvable_iff_netYield, Problem.solvable_iff_netYield]
  exact exists_congr fun as =>
    and_congr (netYield_prodInst_iff hreg hchain) Iff.rfl

end Syn

end HTN
