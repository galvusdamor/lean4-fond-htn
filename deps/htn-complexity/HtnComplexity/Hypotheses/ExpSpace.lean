import Mathlib
import ComplexityTheory.TM.Basic
import ComplexityTheory.Complexity.Basic
import HtnComplexity.Hypotheses.Families
import ComplexityTheory.Complexity.Hypotheses
/-!
# `EXPSPACE ⊄ NEXPTIME/poly` and the two completeness interfaces of the cell (`HTN-TR`, `HTN-AC`)

**Definitions only.**  The three cells (`HTN-TR`, `HTN-AC`), (`HTN-TR-1`, `HTN-AC`) and
(`HTN-TR-1`, `HTN-AC-1`) were refuted, in the polynomial-time reading, on the cell-specific
hypothesis `HTN.Syn.Coded.NoAdvice codingSer SynClass.HTN_TR_root SynClass.HTN_AC`.  This file
defines the standard complexity-theoretic separation that replaces it and the two interfaces
that connect the separation to planning:

* `TM.NTM.ReachesSpace`, `TM.NTM.AcceptsInSpace` — space-bounded runs of the nondeterministic
  Turing machines of `ComplexityTheory/TM/Basic.lean` (the head never reaches cell `S`);
* `HTN.Space.InExpSpace` — **`EXPSPACE`**: the languages of such machines with the space bound
  `2 ^ p(|w|)`.  The machines are nondeterministic, so this is `NEXPSPACE`, which equals
  `EXPSPACE` by Savitch's theorem (the same convention as `HTN.Space.InNSpace` for `PSPACE`);
* `HTN.Space.InNExpPoly` — **`NEXPTIME/poly`**: certificates of length `2 ^ p(|x|)`, checked by a
  predicate of Cobham's class (polynomial time in the length of all its arguments) that also
  reads an advice string of polynomial length depending on `|x|` only.  This is the verifier
  characterisation of `NEXPTIME`, the exponential analogue of `HTN.Syn.InNP`;
* `HTN.Space.ExpspaceNotInNexpPoly` — **`EXPSPACE ⊄ NEXPTIME/poly`**, the new hypothesis;
* `HTN.Space.ExpSpaceHardSource c S` — the source side: every `EXPSPACE` language has a
  polynomial-time hardness family in `S` (the family form of "`S` is `EXPSPACE`-hard", Alford et
  al. 2015 for `HTN-TR`);
* `HTN.Syn.NExpDecidableAdv c T` — the target side: plan existence for `T` is in `NEXPTIME` with
  the domain description as advice (the advice form of "`T` is in `NEXPTIME`", Alford et al. 2015
  for `HTN-AC`);
* `HTN.Space.ExpSpaceUpper c S`, `HTN.Space.NExpHardAdv c T` — the two converse completeness
  statements, used only to show that the new hypothesis is exactly as strong as `NoAdvice` once
  completeness is available (`HTN.Space.noAdvice_iff_expspaceNotInNexpPoly`).

The theorems are in `HtnCompilability/Space/ExpSpaceCell.lean`.
-/

/-! ## The two completeness interfaces -/

namespace HTN

namespace Space

open Syn Syn.Coded

variable {𝒟 : Table.Family}

/-- **The source class is `EXPSPACE`-hard in the family sense**: every `EXPSPACE` language has a
polynomial-time hardness family in `S` (computable domains, polynomial-time instance map,
polynomial sizes). -/
def ExpSpaceHardSource (cod : BitCoding InstDesc) (S : SynClass 𝒟) : Prop :=
  ∀ L : List Bool → Prop, InExpSpace L → Nonempty (HardFamilyPT cod S L)

/-- **Conversely, the languages with a hardness family in `S` are in `EXPSPACE`** (the upper bound
of the source class, in family form).  Used only for the converse
`HTN.Space.expspaceNotInNexpPoly_of_noAdvice`. -/
def ExpSpaceUpper (cod : BitCoding InstDesc) (S : SynClass 𝒟) : Prop :=
  ∀ L : List Bool → Prop, Nonempty (HardFamilyPT cod S L) → InExpSpace L

variable {ℰ : Table.Family} {S : SynClass 𝒟} {c : BitCoding InstDesc}

/-- **The source class is `EXPSPACE`-hard in the family sense, with non-uniform domains**: every
`EXPSPACE` language has a hardness family in `S` whose instance map is polynomial time and whose
domain descriptions are of polynomial size (no computability asked of them).  This is the form in
which the existing `NEXPTIME`-hardness of `HTN-TR-1` is proved
(`HTN.Space.nexpHardSourceNU_HTN_TR_root`), and the form the Karp–Lipton argument needs. -/
def ExpSpaceHardSourceNU (cod : BitCoding InstDesc) (S : SynClass 𝒟) : Prop :=
  ∀ L : List Bool → Prop, InExpSpace L → Nonempty (HardFamilyNU cod S L)

/-- The uniform source side implies the non-uniform one. -/
theorem ExpSpaceHardSource.toNU (h : ExpSpaceHardSource c S) : ExpSpaceHardSourceNU c S :=
  fun L hL => ⟨(h L hL).some.toNU⟩

/-- Non-uniform `EXPSPACE`-hardness is inherited by larger classes. -/
theorem ExpSpaceHardSourceNU.mono {S' : SynClass ℰ} (hS : ExpSpaceHardSourceNU c S)
    (h : SynSub S S') : ExpSpaceHardSourceNU c S' :=
  fun L hL => ⟨(hS L hL).some.mono h⟩

variable {cod : BitCoding InstDesc}

/-- **The source class is `NEXPTIME`-hard in the family sense**: for every language of
`NEXPTIME` it has a polynomial-time hardness family — a computable family of domain descriptions
of polynomial size, one per input length, and a polynomial-time map of words to instance
descriptions, solvable exactly for the words of the language. -/
def NExpHardSource (cod : BitCoding InstDesc) (S : SynClass 𝒟) : Prop :=
  ∀ L : List Bool → Prop, InNExp L → Nonempty (HardFamilyPT cod S L)

/-- **The source class is `NEXPTIME`-hard in the family sense, with non-uniform domains**: for
every language of `NEXPTIME` it has a hardness family whose instance map is polynomial time and
whose domain descriptions are of polynomial size. -/
def NExpHardSourceNU (cod : BitCoding InstDesc) (S : SynClass 𝒟) : Prop :=
  ∀ L : List Bool → Prop, InNExp L → Nonempty (HardFamilyNU cod S L)

/-- The uniform source side implies the non-uniform one. -/
theorem NExpHardSource.toNU (h : NExpHardSource cod S) : NExpHardSourceNU cod S :=
  fun L hL => ⟨(h L hL).some.toNU⟩

/-- `NEXPTIME`-hardness with non-uniform domains is inherited by larger classes. -/
theorem NExpHardSourceNU.mono {S' : SynClass ℰ} (h : NExpHardSourceNU cod S) (hs : SynSub S S') :
    NExpHardSourceNU cod S' :=
  fun L hL => ⟨(h L hL).some.mono hs⟩

end Space

namespace Syn

open PTime Table

variable {ℰ : Family}

/-- **Plan existence for `T` is in `NEXPTIME`, the domain description being supplied as
advice.**  For every family `D` of domain descriptions of `T` of polynomial size there are a
predicate `V` of Cobham's class, a polynomial `p` and an advice `A n` of polynomial length such
that an instance `q` of `T` (of code length at most `rq n`) is solvable over `D n` iff some
certificate of length at most `2 ^ p(n)` makes `V` accept `[code q, A n, w]`.  The
nondeterministic-exponential counterpart of `HTN.Syn.AltDecidableAdv`. -/
def NExpDecidableAdv (c : BitCoding InstDesc) (T : SynClass ℰ) : Prop :=
  ∀ (D : ℕ → DomDesc) (r rq : Polynomial ℕ), (∀ n, T.domOk (D n)) →
    (∀ n, (D n).size ≤ r.eval n) →
    ∃ (V : Args → Bool) (p s : Polynomial ℕ) (A : ℕ → List Bool), CobhamB V ∧
      (∀ n, (A n).length ≤ s.eval n) ∧
        ∀ (n : ℕ) (q : InstDesc), T.instOk q → (c.code q).length ≤ rq.eval n →
          (Solvable (D n) q ↔
            ∃ w : List Bool, w.length ≤ 2 ^ p.eval n ∧ V [c.code q, A n, w] = true)

end Syn

namespace Space

open Syn Syn.Coded

variable {ℰ : Table.Family}

/-- **Every `NEXPTIME/poly` language is decided by `T` with polynomial advice** (the hardness of
the target class, in advice form).  Used only for the converse
`HTN.Space.expspaceNotInNexpPoly_of_noAdvice`. -/
def NExpHardAdv (cod : BitCoding InstDesc) (T : SynClass ℰ) : Prop :=
  ∀ L : List Bool → Prop, InNExpPoly L → InPolyAdvice cod T L

end Space

end HTN
