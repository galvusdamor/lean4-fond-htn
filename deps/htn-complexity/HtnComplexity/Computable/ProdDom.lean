import HtnComplexity.Computable.ProdTn
/-!
# The product domain: a regular domain that carries the rest of the chain in its names

For the *regular* classes the rooting of a bounded initial chain
(`HtnCompilability/Computable/ChainRoot.lean`) is not available: a method whose body is the
chain `c₁ … c_j` has more than one compound task, so it is not regular.  The regular replacement
is the **product construction**: the compound names of the compiled domain are pairs

    ⟨c, w⟩  =  "run the compound task `c`, then the chain `w`",

written here as the single name `chainName (c :: w)`, and every method of the source domain is
copied once per remaining chain `w` of length at most `k - 1`:

* if its body has a trailing compound task `c'`, the copy renames that task to `⟨c', w⟩`
  (`HTN.Syn.TnDesc.setTail`) — the rest of the chain is passed on;
* if its body is primitive and `w = u :: w'` is nonempty, the copy appends the compound task
  `⟨u, w'⟩` — here, and only here, the next task of the chain is created
  (`HTN.Syn.TnDesc.appendTask`);
* if its body is primitive and `w` is empty, the copy is the body itself.

Both operations keep the body regular, so the compiled domain is regular
(`HTN.Syn.prodDom_methodsReg`), which is what the rooting could not achieve.

This file contains the construction and its syntactic properties; its correctness is
`HtnComplexity/Computable/ProdCorrect.lean`.
-/

namespace HTN

namespace Syn

/-! ### The names -/

/-- **The compound name of a chain**: `chainName (c :: w)` is the task "run `c`, then `w`". -/
def chainName (ws : List ℕ) : ℕ := Encodable.encode ws

theorem chainName_injective : Function.Injective chainName :=
  fun _ _ h => Encodable.encode_injective h

@[simp] theorem chainName_inj {ws us : List ℕ} : chainName ws = chainName us ↔ ws = us :=
  ⟨fun h => chainName_injective h, fun h => by rw [h]⟩

/-! ### The construction -/

/-- **The body of a copied method**: the body `t`, followed by the remaining chain `w`. -/
def prodBody (t : TnDesc) (w : List ℕ) : TnDesc :=
  if TnDesc.hasNextB t then t.setTail (chainName (TnDesc.nextName t :: w))
  else if w.isEmpty then t else t.appendTask (chainName w)

theorem prodBody_of_hasNext {t : TnDesc} (h : TnDesc.hasNextB t = true) (w : List ℕ) :
    prodBody t w = t.setTail (chainName (TnDesc.nextName t :: w)) := by
  simp [prodBody, h]

theorem prodBody_of_nil {t : TnDesc} (h : TnDesc.hasNextB t = false) :
    prodBody t [] = t := by
  simp [prodBody, h]

theorem prodBody_of_cons {t : TnDesc} (h : TnDesc.hasNextB t = false) (u : ℕ) (w : List ℕ) :
    prodBody t (u :: w) = t.appendTask (chainName (u :: w)) := by
  simp [prodBody, h]

/-- **The methods of the product domain**: one for the empty chain, and one copy of every
method of `d` per remaining chain of length at most `k - 1`. -/
def prodMethods (k : ℕ) (d : DomDesc) : List MethodDesc :=
  (chainName [], TnDesc.nil) ::
    d.methods.flatMap fun e => (tuplesLe (k - 1) d.heads).map fun w =>
      (chainName (e.1 :: w), prodBody e.2 w)

/-- **The product domain.** -/
def prodDom (k : ℕ) (d : DomDesc) : DomDesc := (d.actions, prodMethods k d)

/-- **The product instance**: the chain of the source instance, as a single compound task. -/
def prodInst (q : InstDesc) : InstDesc :=
  (q.initList, q.goalList, singleTn (chainName q.tnI.compoundNames))

@[simp] theorem prodDom_actions (k : ℕ) (d : DomDesc) : (prodDom k d).actions = d.actions := rfl

@[simp] theorem prodDom_methods (k : ℕ) (d : DomDesc) :
    (prodDom k d).methods = prodMethods k d := rfl

@[simp] theorem prodInst_initList (q : InstDesc) : (prodInst q).initList = q.initList := rfl

@[simp] theorem prodInst_goalList (q : InstDesc) : (prodInst q).goalList = q.goalList := rfl

@[simp] theorem prodInst_tnI (q : InstDesc) :
    (prodInst q).tnI = singleTn (chainName q.tnI.compoundNames) := rfl

theorem mem_prodMethods_iff {k : ℕ} {d : DomDesc} {e : MethodDesc} :
    e ∈ prodMethods k d ↔ e = (chainName [], TnDesc.nil) ∨
      ∃ e₀ ∈ d.methods, ∃ w ∈ tuplesLe (k - 1) d.heads,
        e = (chainName (e₀.1 :: w), prodBody e₀.2 w) := by
  simp only [prodMethods, List.mem_cons, List.mem_flatMap, List.mem_map]
  constructor
  · rintro (h | ⟨e₀, he₀, w, hw, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e₀, he₀, w, hw, rfl⟩
  · rintro (h | ⟨e₀, he₀, w, hw, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e₀, he₀, w, hw, rfl⟩

theorem mem_prodMethods_of_source {k : ℕ} {d : DomDesc} {e₀ : MethodDesc} (he₀ : e₀ ∈ d.methods)
    {w : List ℕ} (hw : w ∈ tuplesLe (k - 1) d.heads) :
    ((chainName (e₀.1 :: w), prodBody e₀.2 w) : MethodDesc) ∈ prodMethods k d :=
  mem_prodMethods_iff.2 (Or.inr ⟨e₀, he₀, w, hw, rfl⟩)

theorem mem_prodMethods_nil {k : ℕ} {d : DomDesc} :
    ((chainName [], TnDesc.nil) : MethodDesc) ∈ prodMethods k d :=
  mem_prodMethods_iff.2 (Or.inl rfl)

/-! ### The product domain is regular -/

theorem isRegular_prodBody {t : TnDesc} (hreg : t.toTaskNetwork.IsRegular) (w : List ℕ) :
    (prodBody t w).toTaskNetwork.IsRegular := by
  rcases hnext : TnDesc.hasNextB t with _ | _
  · rcases w with _ | ⟨u, w⟩
    · rw [prodBody_of_nil hnext]
      exact hreg
    · rw [prodBody_of_cons hnext]
      exact TnDesc.isRegular_appendTask hnext _
  · rw [prodBody_of_hasNext hnext]
    exact TnDesc.isRegular_setTail hreg _

/-- **The product domain is regular.** -/
theorem prodDom_methodsReg {k : ℕ} {d : DomDesc} (hreg : d.MethodsReg) :
    (prodDom k d).MethodsReg := by
  intro e he
  rcases mem_prodMethods_iff.1 he with rfl | ⟨e₀, he₀, w, -, rfl⟩
  · exact TnDesc.isRegular_nil
  · exact isRegular_prodBody (hreg e₀ he₀) w

/-! ### The blocks of a copied method -/

theorem hasBlock_prodBody_hasNext {t : TnDesc} (hreg : t.toTaskNetwork.IsRegular)
    (hnext : TnDesc.hasNextB t = true) (w : List ℕ) (head : ℕ) {os : List ℕ}
    {next : Option ℕ} :
    (MethodDesc.toMethod (head, prodBody t w)).HasBlock os next ↔
      ∃ xs : List ℕ, TnDesc.PrimLin t xs ∧ os = xs.map (TnDesc.actOf t) ∧
        next = some (chainName (TnDesc.nextName t :: w)) := by
  rw [prodBody_of_hasNext hnext, TnDesc.hasBlock_setTail hreg hnext]

theorem hasBlock_prodBody_nil {t : TnDesc} (hreg : t.toTaskNetwork.IsRegular)
    (hnext : TnDesc.hasNextB t = false) (head : ℕ) {os : List ℕ} {next : Option ℕ} :
    (MethodDesc.toMethod (head, prodBody t [])).HasBlock os next ↔
      ∃ xs : List ℕ, TnDesc.PrimLin t xs ∧ os = xs.map (TnDesc.actOf t) ∧ next = none := by
  rw [prodBody_of_nil hnext, TnDesc.hasBlock_iff hreg head]
  simp [TnDesc.tailName, hnext]

theorem hasBlock_prodBody_cons {t : TnDesc} (hnext : TnDesc.hasNextB t = false) (u : ℕ)
    (w : List ℕ) (head : ℕ) {os : List ℕ} {next : Option ℕ} :
    (MethodDesc.toMethod (head, prodBody t (u :: w))).HasBlock os next ↔
      ∃ xs : List ℕ, TnDesc.PrimLin t xs ∧ os = xs.map (TnDesc.actOf t) ∧
        next = some (chainName (u :: w)) := by
  rw [prodBody_of_cons hnext, TnDesc.hasBlock_appendTask hnext]

/-- The blocks of a source method, in the same shape. -/
theorem hasBlock_source {t : TnDesc} (hreg : t.toTaskNetwork.IsRegular) (head : ℕ)
    {os : List ℕ} {next : Option ℕ} :
    (MethodDesc.toMethod (head, t)).HasBlock os next ↔
      ∃ xs : List ℕ, TnDesc.PrimLin t xs ∧ os = xs.map (TnDesc.actOf t) ∧
        next = TnDesc.tailName t :=
  TnDesc.hasBlock_iff hreg head

end Syn

end HTN
