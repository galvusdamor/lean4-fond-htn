import HtnComplexity.Computable.TMRender
import HtnComplexity.Computable.RenderClass
/-!
# The described family construction lies in the source classes

The open cells of Table 3 have the acyclic (`HTN-AC-1`) and the tail-recursive (`HTN-TR-1`)
classes with a rooted instance as their sources.  This file shows that the descriptions of
`HtnComplexity/Computable/TMRender.lean` belong to them, *as descriptions*:

* `HTN.TMEnc.Fam.isAcyclic_famDomDesc` — the described family domain is acyclic, witnessed by
  the rank function of the original construction;
* `HTN.TMEnc.Fam.isTailRec_famDomDesc` — hence tail recursive;
* `HTN.TMEnc.Fam.isRooted_famInstDesc` — the described instance is rooted: its initial task
  network is the single compound task `sI`.
-/

namespace HTN

namespace TMEnc

namespace Fam

open scoped Classical

open TM TaskNetwork Syn

variable {Q Γ : Type} [Fintype Q] [Fintype Γ]

/-- The rank of the original construction decreases along every listed body. -/
lemma rank_lt_of_mem_famBodies {N : NTM Q Γ} {n K : ℕ}
    {p : TMTask Q Γ × Shape (GAct Q Γ) (TMTask Q Γ)} (hp : p ∈ famBodies N n K)
    {row : List (GAct Q Γ ⊕ TMTask Q Γ)} (hrow : row ∈ p.2.rows) {c : TMTask Q Γ}
    (hx : Sum.inr c ∈ row) : rank K n c < rank K n p.1 := by
  simp only [famBodies, List.mem_append, List.mem_flatMap, List.mem_map, Finset.mem_toList,
    List.mem_singleton] at hp
  rcases hp with ⟨t, -, ls, hls, rfl⟩ | rfl
  · simp only [guardShape, List.mem_append, List.mem_singleton] at hrow
    rcases hrow with hrow | rfl
    · refine rank_lt_of_mem_bodiesAll (N := N) ?_ (List.mem_flatten.2 ⟨row, hrow, hx⟩)
      rw [← coe_bodyFinsetFam]
      exact hls
    · simp at hx
  · have hmem : (Sum.inr c : GAct Q Γ ⊕ TMTask Q Γ) ∈ (sIShape (Q := Q) (Γ := Γ) K).rows.flatten :=
      List.mem_flatten.2 ⟨row, hrow, hx⟩
    simp only [sIShape, liftBody, initChainsFix, headChainFix, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false, Sum.map_inr, id,
      Sum.inr.injEq, reduceCtorEq] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [rank] <;> omega

/-- **The described family domain is acyclic.** -/
theorem isAcyclic_famDomDesc (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) (n K : ℕ) :
    DomDesc.IsAcyclic (famDomDesc N q g n K) := by
  have h := (famRendering N hq hg (wpad N n) K).isAcyclic_domDesc (rank K n)
    (fun p hp row hrow x hx c hc => by
      subst hc
      exact rank_lt_of_mem_famBodies (by simpa [famRendering] using hp) hrow hx)
  rwa [domDesc_famRendering, length_wpad] at h

/-- **The described family domain is tail recursive.** -/
theorem isTailRec_famDomDesc (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) (n K : ℕ) :
    DomDesc.IsTailRec (famDomDesc N q g n K) :=
  SynClass.isAcyclic_isTailRec (isAcyclic_famDomDesc N hq hg n K)

/-- **The described family instance is rooted.** -/
theorem isRooted_famInstDesc (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) (w : List Γ) :
    InstDesc.IsRooted (famInstDesc N q g w) := by
  have h := (famRendering N hq hg w 0).isRooted_instDesc (c := TMTask.sI) rfl
  rwa [instDesc_famRendering] at h

end Fam

end TMEnc

end HTN
