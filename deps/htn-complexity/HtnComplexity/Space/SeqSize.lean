import HtnComplexity.Space.SeqMachine
/-!
# Sizes for the planner of totally ordered instances with a task network

* `HTN.Space.SeqM.length_vocA_le`, `HTN.Space.SeqM.length_vocC_le` — the vocabulary of a domain
  description has at most as many names as the description has symbols;
* `HTN.Space.SeqM.size_seqDom_le` — the gadget domain for sequences of length at most `N` has
  `O(N · |d|)` symbols;
* `HTN.Space.SeqM.tblSize_markRows_le`, `HTN.Space.SeqM.bits_markRows_le` — the marker rows are
  short and their facts are short.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### The vocabulary -/

theorem length_actionNames_le (t : TnDesc) : t.actionNames.length ≤ t.size := by
  have := TnDesc.length_actionNames_le t
  simp only [TnDesc.size]
  omega

theorem length_compoundNames_le (t : TnDesc) : t.compoundNames.length ≤ t.size := by
  have := TnDesc.length_compoundNames_le t
  simp only [TnDesc.size]
  omega

theorem sum_flatMap_le {α : Type} (l : List α) (f : α → List ℕ) (g : α → ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ g a) : (l.flatMap f).length ≤ (l.map g).sum := by
  rw [List.length_flatMap]
  exact List.sum_le_sum fun a ha => h a ha

theorem length_le_sum_size_actions (d : DomDesc) :
    d.actions.length ≤ (d.actions.map ActionDesc.size).sum := by
  calc d.actions.length = (d.actions.map fun _ => 1).sum := by simp
    _ ≤ _ := List.sum_le_sum fun a _ => by simp only [ActionDesc.size]; omega

theorem length_le_sum_size_methods (d : DomDesc) :
    d.methods.length + (d.methods.map fun e : MethodDesc => e.2.size).sum ≤
      (d.methods.map MethodDesc.size).sum := by
  have : ∀ l : List MethodDesc,
      l.length + (l.map fun e : MethodDesc => e.2.size).sum ≤ (l.map MethodDesc.size).sum := by
    intro l
    induction l with
    | nil => simp
    | cons e l ih => simp [MethodDesc.size] at ih ⊢; omega
  exact this _

/-- **The action vocabulary has at most `|d|` names.** -/
theorem length_vocA_le (d : DomDesc) : (vocA d).length ≤ d.size := by
  have h1 := sum_flatMap_le d.methods (fun e => e.2.actionNames) (fun e => e.2.size)
    fun e _ => length_actionNames_le e.2
  have h2 := length_le_sum_size_actions d
  have h3 := length_le_sum_size_methods d
  simp only [vocA, List.length_append, List.length_map, DomDesc.size]
  omega

/-- **The compound vocabulary has at most `|d|` names.** -/
theorem length_vocC_le (d : DomDesc) : (vocC d).length ≤ d.size := by
  have h1 := sum_flatMap_le d.methods (fun e => e.2.compoundNames) (fun e => e.2.size)
    fun e _ => length_compoundNames_le e.2
  have h3 := length_le_sum_size_methods d
  simp only [vocC, List.length_append, List.length_map, DomDesc.size]
  omega

/-! ### The gadget domain -/

theorem length_knownList_le (d : DomDesc) : (knownList d).length ≤ 2 * d.size := by
  have := length_vocA_le d
  have := length_vocC_le d
  simp only [knownList, List.length_append, List.length_map]
  omega

theorem length_gadList_le (d : DomDesc) (N : ℕ) :
    (gadList d N).length ≤ (N + 1) * (2 * d.size + 2) := by
  have hk := length_knownList_le d
  have h1 : ((List.range N).flatMap fun p => (knownList d).map (GA.pick p) ++ [GA.skip p]).length
      = N * ((knownList d).length + 1) := by
    rw [List.length_flatMap]
    simp
  simp only [gadList, List.length_append, h1, List.length_map, List.length_range]
  nlinarith

theorem size_gridDesc_le (row : List (Bool × ℕ)) :
    (gridDesc [row]).size ≤ 3 * row.length := by
  simp only [TnDesc.size, gridDesc_ids, gridDesc_ordList, gridDesc_lbl, cellIds, cellOrd, cellLbl,
    gridRow, List.length_flatMap, List.length_map, List.length_range]
  simp
  omega

theorem size_renAct (ρ : ℕ → ℕ) (a : ActionDesc) : (renAct ρ a).size = a.size := by
  simp [renAct, ActionDesc.size]

/-- **The gadget domain has `O(N · |d|)` symbols.** -/
theorem size_seqDom_le (d : DomDesc) (N : ℕ) :
    (seqDom (code d) d N).size ≤ d.size + 15 * ((N + 1) * (2 * d.size + 2)) := by
  have hg := length_gadList_le d N
  have hA : ((gadActs (code d) d N).map ActionDesc.size).sum ≤ 5 * (gadList d N).length := by
    rw [gadActs, List.map_map]
    calc _ ≤ ((gadList d N).map fun _ => 5).sum := List.sum_le_sum fun g _ => by
          cases g <;> simp [gadVal, ActionDesc.size]
      _ = 5 * (gadList d N).length := by simp [mul_comm]
  have hM : ((gadMethods (code d) d N).map MethodDesc.size).sum ≤ 10 * (gadList d N).length := by
    rw [gadMethods, List.map_map]
    calc _ ≤ ((gadList d N).map fun _ => 10).sum := List.sum_le_sum fun g _ => by
          have := size_gridDesc_le (gadRow (code d) g)
          have hr : (gadRow (code d) g).length ≤ 3 := by cases g <;> simp [gadRow]
          simp only [Function.comp_apply, MethodDesc.size]
          omega
      _ = 10 * (gadList d N).length := by simp [mul_comm]
  have hR : ((d.actions.map (renAct (code d).ρ)).map ActionDesc.size).sum =
      (d.actions.map ActionDesc.size).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun a _ => size_renAct _ a
  have hD : (d.actions.map ActionDesc.size).sum + (d.methods.map MethodDesc.size).sum = d.size :=
    rfl
  generalize d.size = D at hD hg ⊢
  simp only [DomDesc.size, seqDom, DomDesc.actions, DomDesc.methods, List.map_append,
    List.sum_append] at hR hA hM hD ⊢
  omega

/-! ### The marker rows -/

theorem tblSize_append (t t' : List Row) : tblSize (t ++ t') = tblSize t + tblSize t' := by
  simp [tblSize]
  ring

theorem tblSize_markRows_le (d : DomDesc) (K : ℕ) : tblSize (markRows d K) ≤ d.size + 3 := by
  have h1 := length_vocA_le d
  have h2 := List.length_filter_le (fun a => decide ((bitsOfNat a).length ≤ K)) (vocA d)
  simp [tblSize, markRows]
  omega

theorem length_bitsOfNat_le_self (m : ℕ) : (bitsOfNat m).length ≤ m :=
  length_bitsOfNat_le_of_lt_two_pow Nat.lt_two_pow_self

theorem bits_cRoot_le (d : DomDesc) : (bitsOfNat (cRoot d)).length ≤ d.size + 2 := by
  rw [bitsOfNat_cRoot]
  have h1 := length_bitsOfNat_le_self (leastFresh (vocC d))
  have h2 := leastFresh_le (vocC d)
  have h3 := length_vocC_le d
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem bits_markRows_le (d : DomDesc) (K : ℕ) :
    ∀ f ∈ tblFacts (markRows d K), (bitsOfNat f).length ≤ d.size + 2 * K + 2 := by
  intro f hf
  simp only [tblFacts, markRows, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, List.mem_map,
    List.mem_filter, decide_eq_true_eq] at hf
  rcases hf with rfl | ⟨a, ⟨-, ha⟩, rfl⟩
  · have := bits_cRoot_le d; omega
  · rw [bitsOfNat_vf]
    simp [serNat]
    omega

end SeqM

end Space

end HTN
