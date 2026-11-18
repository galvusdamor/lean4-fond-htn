import HtnComplexity.TMEnc.TMEncFixHeadAnalysis
/-!
# The structure of a solution plan of the repaired encoding

This file puts the three chain analyses together.  A solution plan of the repaired problem is,
by `HTN.TMEnc.isSolutionPlanFix_iff`, an executable refinement of the three chains of the initial
task network followed by one of `done`.  With

* `HTN.TMEnc.chainYield_headChain_iff` (the head counter — a rigid stream of units),
* `HTN.TMEnc.chainYield_checkers_forward` (the cell counters — `K + 1` staggered counter runs),
* `HTN.TMEnc.chainYield_tapeChain_iff` (the tape — the `(K+1)²` cells of a space–time diagram),

this yields `HTN.TMEnc.isSolutionPlanFix_structure`: **every solution plan is an interleaving of
the units of the head counter, of `K + 1` staggered cell counters and of the cells of a
space–time diagram whose first block is the input, followed by one accepting test.**

What the soundness half of the simulation argument still needs on top of it is the *alignment*
of the three streams, which is forced by the semaphore protocol, not by the hierarchy.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- **The final task of the plan is one accepting test.** -/
lemma chainYield_done_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.done] as ↔
      ∃ f ∈ N.accept, as = [TMAct.check (TMFact.st f)] := by
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ∃ f ∈ N.accept, ls = [[Sum.inl (TMAct.check (TMFact.st f))]] := by
      simpa [bodiesFix, bodies] using hls
    obtain ⟨f, hf, rfl⟩ := hls'
    rw [gridYield_singleton_iff, chainYield_cons_inl_iff] at hy
    obtain ⟨as', rfl, hy'⟩ := hy
    rw [chainYield_nil_iff] at hy'
    subst hy'
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    rw [chainYield_singleton_bod_iff]
    refine ⟨[[Sum.inl (TMAct.check (TMFact.st f))]], ?_, gridYield_singleton_iff.2 ?_⟩
    · have : [[Sum.inl (TMAct.check (TMFact.st f))]] ∈ bodies N w K (TMTask.done : TMTask Q Γ) :=
        ⟨f, hf, rfl⟩
      simpa [bodiesFix] using this
    · exact chainYield_cons_inl_iff.2 ⟨[], rfl, chainYield_nil_iff.2 rfl⟩

/-- The stream of units of the head counter that the hierarchy prescribes. -/
def headStream (Q Γ : Type) (K : ℕ) : List (TMAct Q Γ) :=
  roundStream (K * K + 3 * K + 1) fun u => headUnitActs Q Γ (headMarkStd K u)

/-- **The structure of a solution plan of the repaired encoding.**

Every solution plan is an interleaving of

* the `K² + 3K + 1` units of the head counter (a stream fixed by the hierarchy,
  `HTN.TMEnc.headStream`),
* `K + 1` cell counters with leading and trailing delays `(j, K - j)`, and
* the `(K+1)²` cells of a space–time diagram whose first block is the input, padded with blanks,
  and each of whose blocks starts with the separator,

followed by one accepting test.  The plan is executable in the initial state.

The *alignment* of the three streams — which unit of the head counter and which cell of which
counter answer the requests of a given tape cell — is not part of this statement: it is forced
by the semaphore protocol, i.e. by executability, not by the hierarchy. -/
theorem isSolutionPlanFix_structure (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)} (h : (problemFix N w K).IsSolutionPlan as) :
    ∃ (sym : ℕ → Option Γ) (ps : List (ℕ × ℕ)) (ass : List (List (TMAct Q Γ)))
      (ac bs as₁ : List (TMAct Q Γ)) (f : Q),
      (∀ j ≤ K, sym j = tapeInitSym N w j) ∧
      (∀ i ≤ K, sym (i * (K + 1)) = none) ∧
      ps.Perm ((List.range (K + 1)).map fun j => (j, K - j)) ∧
      CounterRuns N w K ps ass ∧ InterleaveList ass ac ∧
      Interleave ac (roundStream ((K + 1) * (K + 1)) fun n => cellRun Q Γ K (sym n)) bs ∧
      Interleave (headStream Q Γ K) bs as₁ ∧
      f ∈ N.accept ∧ as = as₁ ++ [TMAct.check (TMFact.st f)] ∧
      (problemFix N w K).SeqApplicable (as₁ ++ [TMAct.check (TMFact.st f)])
        (problemFix N w K).init := by
  obtain ⟨⟨as₁, as₂, rfl, hgrid, hdone⟩, happ⟩ := isSolutionPlanFix_iff.1 h
  obtain ⟨ah, ac, at', bs, hh, hc, ht, hint', hint⟩ := gridYield_initChains_iff.1 hgrid
  obtain ⟨sym, hinit, hsep, rfl⟩ := (chainYield_tapeChain_iff hw hwK).1 ht
  obtain ⟨ps, ass, hperm, hruns, hil⟩ := chainYield_checkers_forward (K + 1) hc
  obtain ⟨f, hf, rfl⟩ := chainYield_done_iff.1 hdone
  refine ⟨sym, ps, ass, ac, bs, as₁, f, hinit, hsep, ?_, hruns, hil, hint', ?_, hf, rfl, happ⟩
  · simpa using hperm
  · rwa [(chainYield_headChainFix_iff (by omega)).1 hh] at hint

end TMEnc

end HTN
