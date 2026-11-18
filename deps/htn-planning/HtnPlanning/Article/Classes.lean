import HtnPlanning.Article.Bridge
import HtnPlanning.Core.ClassHierarchy
/-!
# The problem classes of Section 3, for the article's model

Every restriction of Section 3 is a condition on the initial task network and on the methods
reachable from it.  The predicates on `HTN.Problem` (`HtnPlanning/Core/Classes.lean`) are
therefore reused: a problem of the article's model is in a class iff its dual-rail translation
`HTN.Article.Problem.toPos` — which has the same methods and the same initial task network — is.

New here are the **heights** of stratifications (Def. 3.4) in general, and with them the classes
`ACYC_h` and `TAIL-REC_h` of Cors. 4.2.8, 4.2.17, 4.3.3 and 4.3.10:

* `HTN.Problem.HasHeightLE P le h` — the stratification `le` has at most `h` strata;
* `HTN.Problem.IsAcyclicH P h`, `HTN.Problem.IsTailRecursiveH P h`;
* **Theorem 3.0.1** in the article's wording: `HTN.Article.Problem.thm_3_0_1` — a problem is
  regular iff it is `≤_r`-stratifiable with a stratification of height one.

| article | here (`HTN.Article.Problem`) |
| --- | --- |
| Def. 3.1 `TO-tn_I`, `TO-M`, `TO` | `IsTO_tnI`, `IsTO_M`, `IsTO` |
| Def. 3.2 `noHTN` | `IsNoHTN` |
| Def. 3.3 `REG` | `IsREG` (= `HTN.Problem.IsRegularM`: no condition on `tn_I`) |
| Defs. 3.5/3.6 `ACYC` | `IsACYC` |
| Defs. 3.7/3.8 `MOSTLY-ACYC` | `IsMostlyACYC` |
| Defs. 3.9/3.10 `TAIL-REC` | `IsTailREC` |
| Def. 3.11 `UNRES-REC` | every problem |
| `ACYC_h`, `TAIL-REC_h` | `IsACYC_h`, `IsTailREC_h` |
-/

namespace HTN

universe u v w x

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- **Height (Def. 3.4).** The stratification `le` has at most `h` strata: there is a ranking of
the reachable compound task names into `{0, …, h-1}` that induces `le`.  (The strata of a total
preorder are linearly ordered; the rank of a name is the index of its stratum.)  A problem
without reachable compound task names has height `0`. -/
def HasHeightLE (P : Problem F A C I) (le : C → C → Prop) (h : ℕ) : Prop :=
  ∃ f : C → ℕ, (∀ c, P.ReachableName c → f c < h) ∧
    ∀ c c', P.ReachableName c → P.ReachableName c' → (le c c' ↔ f c ≤ f c')

/-- `ACYC_h`: acyclic problems with a `≤₀`-stratification of height at most `h`. -/
def IsAcyclicH (P : Problem F A C I) (h : ℕ) : Prop :=
  ∃ le : C → C → Prop, P.IsStrat0 le ∧ P.HasHeightLE le h

/-- `TAIL-REC_h`: tail-recursive problems with a `≤_r`-stratification of height at most `h`. -/
def IsTailRecursiveH (P : Problem F A C I) (h : ℕ) : Prop :=
  ∃ le : C → C → Prop, P.IsStratR le ∧ P.HasHeightLE le h

/-- Height at most one is the condition `HasHeightOne` of `HtnPlanning/Core/Classes.lean`. -/
theorem hasHeightLE_one_iff {P : Problem F A C I} {le : C → C → Prop}
    (hs : P.IsStratification le) : P.HasHeightLE le 1 ↔ P.HasHeightOne le := by
  constructor
  · rintro ⟨f, hf, hle⟩ c c' hc hc'
    exact (hle c c' hc hc').2 (by have := hf c hc; have := hf c' hc'; omega)
  · intro h
    refine ⟨fun _ => 0, fun _ _ => Nat.zero_lt_one, fun c c' hc hc' => ?_⟩
    simp only [le_refl, iff_true]
    exact h c c' hc hc'

theorem IsTailRecursiveH.isTailRecursive {P : Problem F A C I} {h : ℕ}
    (hP : P.IsTailRecursiveH h) : P.IsTailRecursive := by
  obtain ⟨le, hle, -⟩ := hP; exact ⟨le, hle⟩

theorem IsAcyclicH.isAcyclic {P : Problem F A C I} {h : ℕ} (hP : P.IsAcyclicH h) :
    P.IsAcyclic := by
  obtain ⟨le, hle, -⟩ := hP; exact ⟨le, hle⟩

/-- `TAIL-REC₁` in the sense of heights is `IsTailRecursive1`. -/
theorem isTailRecursiveH_one_iff {P : Problem F A C I} :
    P.IsTailRecursiveH 1 ↔ P.IsTailRecursive1 := by
  constructor
  · rintro ⟨le, hR, hh⟩; exact ⟨le, hR, (hasHeightLE_one_iff hR.strat).1 hh⟩
  · rintro ⟨le, hR, hh⟩; exact ⟨le, hR, (hasHeightLE_one_iff hR.strat).2 hh⟩

end Problem

namespace Article

namespace Problem

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- **Def. 3.1** `TO-tn_I`: the initial task network is totally ordered. -/
def IsTO_tnI (P : Problem F A C I) : Prop := P.toPos.IsTO_tnI

/-- **Def. 3.1** `TO-M`: all methods reachable from `tn_I` are totally ordered. -/
def IsTO_M (P : Problem F A C I) : Prop := P.toPos.IsTO_M

/-- **Def. 3.1** `TO = TO-tn_I ∩ TO-M`. -/
def IsTO (P : Problem F A C I) : Prop := P.toPos.IsTO

/-- **Def. 3.2** `noHTN`: the initial task network is primitive. -/
def IsNoHTN (P : Problem F A C I) : Prop := P.toPos.IsNoHTN

/-- **Def. 3.3** `REG`: all methods reachable from `tn_I` are regular. -/
def IsREG (P : Problem F A C I) : Prop := P.toPos.IsRegularM

/-- **Def. 3.6** `ACYC`: `≤₀`-stratifiable problems. -/
def IsACYC (P : Problem F A C I) : Prop := P.toPos.IsAcyclic

/-- **Def. 3.8** `MOSTLY-ACYC`: `≤₁`-stratifiable problems. -/
def IsMostlyACYC (P : Problem F A C I) : Prop := P.toPos.IsMostlyAcyclic

/-- **Def. 3.10** `TAIL-REC`: `≤_r`-stratifiable problems. -/
def IsTailREC (P : Problem F A C I) : Prop := P.toPos.IsTailRecursive

/-- `ACYC_h`. -/
def IsACYC_h (P : Problem F A C I) (h : ℕ) : Prop := P.toPos.IsAcyclicH h

/-- `TAIL-REC_h`. -/
def IsTailREC_h (P : Problem F A C I) (h : ℕ) : Prop := P.toPos.IsTailRecursiveH h

/-- **Theorem 3.0.1.** Every regular planning problem is `≤_r`-stratifiable with a
stratification of height one, and vice versa. -/
theorem thm_3_0_1 (P : Problem F A C I) (hP : P.WF) : P.IsREG ↔ P.IsTailREC_h 1 := by
  rw [IsREG, IsTailREC_h, HTN.Problem.isTailRecursiveH_one_iff]
  exact HTN.Problem.isRegularM_iff_isTailRecursive1 (toPos_wf P hP)

end Problem

end Article

end HTN
