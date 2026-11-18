import HtnComplexity.Complexity.Serial
import ComplexityTheory.Complexity.Blocks
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# The serialisation is at least as long as the size, and a block code with a variable tail

Two small pieces of infrastructure used by
`HtnCompilability/Complexity/NPFamily.lean`.

* `HTN.Syn.size_le_length_instSer` — `q.size ≤ (instSer q).length`.  The size of a description
  counts its symbols and the serialisation spends at least one bit on each of them, so a family
  of descriptions whose *codes* are short is a family of descriptions that are small.  This is
  the direction the size field of a hardness family needs: a polynomial-time translation has a
  polynomially bounded output (`HTN.PTime.PolyTimeFun.poly_length`), hence produces descriptions
  of polynomial size.
* `HTN.PTime.polyTimeFun_blockMapFun` — the block code of
  `ComplexityTheory/Complexity/Blocks.lean` with a *computed* tail instead of a constant one:
  replacing every bit of the word by a fixed block and appending the value of a polynomial-time
  function is again polynomial time.  This is what serialises a description obtained from a
  reduction and then padded in front.
-/

namespace HTN

namespace PTime

/-- **Replacing every bit of a word by a fixed block and appending the value of a
polynomial-time function is polynomial time.** -/
theorem polyTimeFun_blockMapFun (A B : List Bool) {F : List Bool → List Bool}
    (hF : PolyTimeFun F) :
    PolyTimeFun (fun w : List Bool => (w.flatMap fun b => bif b then A else B) ++ F w) := by
  obtain ⟨f, hf, hFf⟩ := hF.cobham
  refine CobhamFun.polyTimeFun ⟨compFn (blockFn A B) [proj 0, f], Cobham.comp (cobham_blockFn A B) ?_, fun w => ?_⟩
  · intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Cobham.proj 0
    · rw [List.mem_singleton.1 hk]
      exact hf
  · simp [compFn, blockFn_apply, proj, hFf w]

end PTime

namespace Syn

open PTime

/-! ### Every symbol costs a bit -/

/-- A list of bit strings is no longer than its serialisation. -/
theorem length_le_length_blist (l : List (List Bool)) : l.length ≤ (blist l).length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [blist_cons, List.length_cons, List.length_append]; omega

theorem length_le_length_serNatList (l : List ℕ) : l.length ≤ (serNatList l).length := by
  simpa [serNatList] using length_le_length_blist (l.map bitsOfNat)

theorem length_le_length_serPairList (l : List (ℕ × ℕ)) : l.length ≤ (serPairList l).length := by
  simpa [serPairList] using length_le_length_blist (l.map serPair)

theorem length_le_length_serLblList (l : List (ℕ × Bool × ℕ)) :
    l.length ≤ (serLblList l).length := by
  simpa [serLblList] using length_le_length_blist (l.map serLbl)

theorem size_le_length_tnSer (t : TnDesc) : t.size ≤ (tnSer t).length := by
  have h1 := length_le_length_serNatList t.ids
  have h2 := length_le_length_serPairList t.ordList
  have h3 := length_le_length_serLblList t.lbl
  simp only [tnSer, TnDesc.size, List.length_append]
  omega

/-- **A description is no bigger than the length of its serialisation.** -/
theorem size_le_length_instSer (q : InstDesc) : q.size ≤ (instSer q).length := by
  have h1 := length_le_length_serNatList q.initList
  have h2 := length_le_length_serNatList q.goalList
  have h3 := size_le_length_tnSer q.tnI
  simp only [instSer, InstDesc.size, List.length_append]
  omega

/-! ### Serialising a list that is extended in front -/

/-- The serialisation of a list of bit strings splits along a concatenation: each entry of the
first part contributes its own block. -/
theorem blist_append (l₁ l₂ : List (List Bool)) :
    blist (l₁ ++ l₂) = (l₁.flatMap fun x => true :: bstr x) ++ blist l₂ := by
  induction l₁ with
  | nil => simp
  | cons x l ih => simp [blist_cons, ih, List.flatMap_cons]

theorem serNatList_append (l₁ l₂ : List ℕ) :
    serNatList (l₁ ++ l₂) =
      (l₁.flatMap fun n => true :: bstr (bitsOfNat n)) ++ serNatList l₂ := by
  simp only [serNatList, List.map_append, blist_append, List.flatMap_map]

end Syn

end HTN
