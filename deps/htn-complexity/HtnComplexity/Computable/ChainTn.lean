import HtnComplexity.Computable.AddRoots
import HtnComplexity.Computable.RenameC
import HtnComplexity.Computable.AcFreeRow
/-!
# Chains of compound tasks, and the rooting of a chain

This file collects the combinatorial material of the rooting construction of
`HtnCompilability/Computable/ChainRoot.lean`:

* `HTN.Syn.chainTn ws` — the described chain of the compound tasks `ws`, with its basic
  properties (it is totally ordered, its compound names are `ws`, and renaming the compound
  names renames the entries);
* `HTN.Syn.InstDesc.IsChainLe k q` — the source condition: the initial task network of `q` is
  the chain of its own compound names, and there are at most `k` of them;
* `HTN.Syn.tuplesEq`, `HTN.Syn.tuplesLe` — the lists of bounded length over a list, which is
  what the domain translation enumerates, with their membership characterisation and their
  length;
* the two translations `HTN.Syn.chainRootDom`, `HTN.Syn.chainRootInst` themselves.
-/

namespace HTN

namespace Syn

/-! ### The described chain of compound tasks -/

/-- **The described chain of the compound tasks `ws`**: one task per entry, ordered from left to
right. -/
def chainTn (ws : List ℕ) : TnDesc := gridDesc [ws.map fun c => (true, c)]

/-- A described chain is totally ordered. -/
theorem chainTn_isTO (ws : List ℕ) : (chainTn ws).toTaskNetwork.IsTotallyOrdered :=
  AcFree.oneRow_isTotallyOrdered

/-- The row of a described chain. -/
lemma chainRow (ws : List ℕ) :
    gridRow [ws.map fun c => ((true, c) : Bool × ℕ)] 0 = ws.map fun c => ((true, c) : Bool × ℕ) :=
  rfl

lemma chainTn_ids (ws : List ℕ) :
    (chainTn ws).ids = (List.range ws.length).map (Nat.pair 0) := by
  rw [chainTn, gridDesc_ids, AcFree.cellIds_oneRow]
  simp

lemma chainTn_label (ws : List ℕ) {j : ℕ} (hj : j < ws.length) :
    (chainTn ws).label (Nat.pair 0 j) = Sum.inr ws[j] := by
  have h : j < (ws.map fun c => ((true, c) : Bool × ℕ)).length := by simpa using hj
  rw [chainTn, AcFree.label_oneRow h]
  rw [List.getD_eq_getElem _ _ h]
  simp

lemma chainTn_labelList (ws : List ℕ) {j : ℕ} (hj : j < ws.length) :
    TnDesc.labelList true (chainTn ws).lbl (Nat.pair 0 j) = [ws.getD j 0] := by
  rw [List.getD_eq_getElem _ _ hj]
  have h : j < (ws.map fun c => ((true, c) : Bool × ℕ)).length := by simpa using hj
  have hlk := lookup_cellLbl (ls := [ws.map fun c => ((true, c) : Bool × ℕ)]) (i := 0) (j := j)
    (by simp) (by rw [chainRow]; exact h)
  rw [TnDesc.labelList_eq]
  rw [show (chainTn ws).lbl = cellLbl [ws.map fun c => ((true, c) : Bool × ℕ)] from rfl, hlk]
  rw [chainRow, List.getD_eq_getElem _ _ h]
  simp

/-- The compound names of a described chain are its entries. -/
@[simp] theorem chainTn_compoundNames (ws : List ℕ) : (chainTn ws).compoundNames = ws := by
  rw [TnDesc.compoundNames, chainTn_ids, List.flatMap_map]
  have h : ((List.range ws.length).flatMap fun j =>
      TnDesc.labelList true (chainTn ws).lbl (Nat.pair 0 j)) =
      (List.range ws.length).flatMap fun j => [ws.getD j 0] :=
    List.flatMap_congr fun j hj => chainTn_labelList ws (by simpa using hj)
  have hfm : ∀ (l : List ℕ) (f : ℕ → ℕ), (l.flatMap fun j => [f j]) = l.map f := by
    intro l f
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  rw [h, hfm]
  exact List.ext_getElem (by simp) fun n h1 h2 => by
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ h2]

/-- Renaming the compound names of a described chain renames its entries. -/
theorem renameC_chainTn (σ : ℕ → ℕ) (ws : List ℕ) :
    (chainTn ws).renameC σ = chainTn (ws.map σ) := by
  have hlen : (ws.map σ).length = ws.length := by simp
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (chainTn ws).ids = (chainTn (ws.map σ)).ids
    rw [chainTn_ids, chainTn_ids, hlen]
  · show (chainTn ws).ordList = (chainTn (ws.map σ)).ordList
    simp only [chainTn, gridDesc_ordList, cellOrd, gridRow]
    simp
  · show ((chainTn ws).renameC σ).lbl = (chainTn (ws.map σ)).lbl
    simp only [TnDesc.renameC_lbl, chainTn, gridDesc_lbl, cellLbl, gridRow, List.map_flatMap,
      List.map_map]
    refine List.flatMap_congr fun i hi => ?_
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp only [List.getD_eq_getElem?_getD]
    refine List.ext_getElem (by simp) (fun n h1 h2 => ?_)
    have hn : n < ws.length := by simpa using h1
    simp [List.getElem?_eq_getElem hn]

/-- The size of a described chain. -/
theorem size_chainTn_le (ws : List ℕ) : (chainTn ws).size ≤ 3 * ws.length := by
  have hids : (chainTn ws).ids.length = ws.length := by rw [chainTn_ids]; simp
  have hlbl : (chainTn ws).lbl.length = ws.length := by
    simp only [chainTn, gridDesc_lbl, cellLbl, gridRow]
    simp
  have hord : (chainTn ws).ordList.length ≤ ws.length := by
    simp only [chainTn, gridDesc_ordList, cellOrd, gridRow]
    simp
  rw [TnDesc.size, hids, hlbl]
  omega

/-- A one-task chain is the canonical single-task network. -/
@[simp] theorem chainTn_singleton (c : ℕ) : chainTn [c] = singleTn c := rfl

/-! ### The source condition -/

namespace InstDesc

/-- **The initial task network is a chain of at most `k` compound tasks**: it is described as
the chain of its own compound names, and there are at most `k` of them. -/
def IsChainLe (k : ℕ) (q : InstDesc) : Prop :=
  q.tnI = chainTn q.tnI.compoundNames ∧ q.tnI.compoundNames.length ≤ k

theorem IsChainLe.isTO {k : ℕ} {q : InstDesc} (h : q.IsChainLe k) : q.IsTO := by
  rw [InstDesc.IsTO, h.1]
  exact chainTn_isTO _

/-- The condition is monotone in the bound. -/
theorem IsChainLe.mono {k k' : ℕ} {q : InstDesc} (hk : k ≤ k') (h : q.IsChainLe k) :
    q.IsChainLe k' :=
  ⟨h.1, h.2.trans hk⟩

/-- **The canonical rooted instances are chains of one task**, so the class of chains of at most
`k ≥ 1` tasks contains the planning problems of the draft paper. -/
theorem isChainLe_one_of_singleTn (I G : List ℕ) (c : ℕ) :
    InstDesc.IsChainLe 1 ((I, G, singleTn c) : InstDesc) := by
  have h : (InstDesc.tnI ((I, G, singleTn c) : InstDesc)) = chainTn [c] := rfl
  constructor
  · rw [h, chainTn_compoundNames]
  · rw [h, chainTn_compoundNames]
    simp

end InstDesc

/-! ### The lists of bounded length over a list -/

/-- The lists of length exactly `n` over `l`. -/
def tuplesEq : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, l => l.flatMap fun c => (tuplesEq n l).map (c :: ·)

/-- The lists of length at most `k` over `l`. -/
def tuplesLe (k : ℕ) (l : List ℕ) : List (List ℕ) :=
  (List.range (k + 1)).flatMap fun n => tuplesEq n l

theorem mem_tuplesEq {n : ℕ} {l : List ℕ} {ws : List ℕ} :
    ws ∈ tuplesEq n l ↔ ws.length = n ∧ ∀ c ∈ ws, c ∈ l := by
  induction n generalizing ws with
  | zero =>
    simp only [tuplesEq, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨rfl, by simp⟩
    · rintro ⟨h, -⟩; exact h
  | succ n ih =>
    simp only [tuplesEq, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨c, hc, us, hus, rfl⟩
      obtain ⟨hlen, hmem⟩ := ih.1 hus
      refine ⟨by simp [hlen], ?_⟩
      rintro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hc
      · exact hmem x hx
    · rintro ⟨hlen, hmem⟩
      rcases ws with _ | ⟨c, us⟩
      · simp at hlen
      · refine ⟨c, hmem c (by simp), us, ih.2 ⟨by simpa using hlen, ?_⟩, rfl⟩
        exact fun x hx => hmem x (List.mem_cons_of_mem _ hx)

theorem mem_tuplesLe {k : ℕ} {l : List ℕ} {ws : List ℕ} :
    ws ∈ tuplesLe k l ↔ ws.length ≤ k ∧ ∀ c ∈ ws, c ∈ l := by
  simp only [tuplesLe, List.mem_flatMap, List.mem_range, mem_tuplesEq]
  constructor
  · rintro ⟨n, hn, hlen, hmem⟩
    exact ⟨by omega, hmem⟩
  · rintro ⟨hlen, hmem⟩
    exact ⟨ws.length, by omega, rfl, hmem⟩

theorem length_tuplesEq (n : ℕ) (l : List ℕ) : (tuplesEq n l).length = l.length ^ n := by
  induction n with
  | zero => simp [tuplesEq]
  | succ n ih =>
    rw [tuplesEq, List.length_flatMap]
    simp only [List.length_map, ih, List.map_const', List.sum_replicate, smul_eq_mul]
    rw [pow_succ, Nat.mul_comm]

theorem length_tuplesLe (k : ℕ) (l : List ℕ) :
    (tuplesLe k l).length ≤ (k + 1) * (l.length + 1) ^ k := by
  have hle : ∀ n ≤ k, (tuplesEq n l).length ≤ (l.length + 1) ^ k := by
    intro n hn
    rw [length_tuplesEq]
    calc l.length ^ n ≤ (l.length + 1) ^ n := Nat.pow_le_pow_left (by omega) n
      _ ≤ (l.length + 1) ^ k := Nat.pow_le_pow_right (by omega) hn
  have h := length_flatMap_le (List.range (k + 1)) (fun n => tuplesEq n l)
    ((l.length + 1) ^ k) (fun n hn => hle n (by simpa [Nat.lt_succ_iff] using hn))
  simpa [tuplesLe] using h

/-! ### The two translations -/

/-- The renaming of the compound names of the source domain: they are moved to the odd numbers,
so that the fresh root names — which are even — cannot clash with them. -/
def oddName (n : ℕ) : ℕ := 2 * n + 1

theorem oddName_injective : Function.Injective oddName := fun _ _ h => by
  simpa [oddName] using h

/-- The fresh compound name of the chain `ws`: an even number, and injectively so. -/
def chainRootName (ws : List ℕ) : ℕ := 2 * Encodable.encode ws

theorem chainRootName_injective : Function.Injective chainRootName := by
  intro x y h
  simpa [chainRootName, Encodable.encode_inj] using h

theorem oddName_ne_chainRootName (n : ℕ) (ws : List ℕ) : oddName n ≠ chainRootName ws := by
  simp only [oddName, chainRootName]
  omega

/-- The fresh methods: one per chain of at most `k` compound names of the domain. -/
def chainRootMethods (k : ℕ) (d : DomDesc) : List MethodDesc :=
  (tuplesLe k d.heads).map fun ws => (chainRootName ws, chainTn (ws.map oddName))

/-- **The compiled domain description**: the source domain with its compound names moved out of
the way, plus one method per chain of at most `k` of them. -/
def chainRootDom (k : ℕ) (d : DomDesc) : DomDesc :=
  addRootsDom (chainRootMethods k d) (d.renameC oddName)

/-- **The compiled instance description**: the initial task network is the single fresh task of
the source's chain. -/
def chainRootInst (q : InstDesc) : InstDesc :=
  (q.initList, q.goalList, singleTn (chainRootName q.tnI.compoundNames))

end Syn

end HTN
