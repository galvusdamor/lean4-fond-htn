import ComplexityTheory.Complexity.PolyTimeTM
import ComplexityTheory.Complexity.Hypotheses
import Mathlib.Computability.Reduce
import Mathlib.Computability.Halting
/-!
# Languages, reductions, hardness and completeness

The vocabulary in which uniform complexity results are stated.  A **language** is a predicate on
bit strings, `List Bool → Prop`.

* decidability and semi-decidability: `HTN.Cx.Decidable` (`ComputablePred`),
  `HTN.Cx.SemiDecidable` (`REPred`), with transfer along computable many-one reductions
  (`HTN.Cx.not_decidable_of_reduces`);
* **polynomial-time many-one (Karp) reductions** `HTN.Cx.RedP L L'`: a function `f` computable in
  polynomial time (`HTN.PTime.PolyTimeFun`, Turing machines of Mathlib) with `L x ↔ L' (f x)`;
  reflexive and transitive;
* **hardness and completeness** for a class of languages `𝒞 : (List Bool → Prop) → Prop`:
  `HTN.Cx.Hard 𝒞 L` (every language of `𝒞` reduces to `L`) and `HTN.Cx.Complete 𝒞 L`;
  hardness is inherited along reductions (`HTN.Cx.Hard.of_redP`);
* names for the classes defined elsewhere: `HTN.Cx.P`, `HTN.Cx.NP`, `HTN.Cx.PSPACE`,
  `HTN.Cx.NEXPTIME`, `HTN.Cx.EXPSPACE`.
-/

namespace HTN

namespace Cx

open PTime

/-- A language: a predicate on bit strings. -/
abbrev Language : Type := List Bool → Prop

/-- A class of languages. -/
abbrev LangClass : Type := Language → Prop

/-- `L` is **decidable**: its characteristic function is computable. -/
def Decidable (L : Language) : Prop := ComputablePred L

/-- `L` is **semi-decidable** (recursively enumerable). -/
def SemiDecidable (L : Language) : Prop := REPred L

/-- A computable many-one reduction. -/
def RedC (L L' : Language) : Prop := ManyOneReducible L L'

theorem not_decidable_of_reduces {L L' : Language} (h : RedC L L') (hL : ¬ Decidable L) :
    ¬ Decidable L' := fun h' => hL (ComputablePred.computable_of_manyOneReducible h h')

/-- **A polynomial-time many-one reduction** from `L` to `L'`. -/
def RedP (L L' : Language) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeFun f ∧ ∀ x, L x ↔ L' (f x)

theorem RedP.refl (L : Language) : RedP L L := ⟨id, polyTimeFun_id, fun _ => Iff.rfl⟩

theorem RedP.trans {L₁ L₂ L₃ : Language} (h₁ : RedP L₁ L₂) (h₂ : RedP L₂ L₃) : RedP L₁ L₃ := by
  obtain ⟨f, hf, hf'⟩ := h₁
  obtain ⟨g, hg, hg'⟩ := h₂
  exact ⟨fun x => g (f x), hg.comp hf, fun x => (hf' x).trans (hg' (f x))⟩

/-- A polynomial-time reduction is a computable one. -/
theorem RedP.redC {L L' : Language} (h : RedP L L') : RedC L L' := by
  obtain ⟨f, hf, hf'⟩ := h
  exact ⟨f, hf.computable, hf'⟩

/-- `L` is **`𝒞`-hard**: every language of `𝒞` reduces to `L` in polynomial time. -/
def Hard (𝒞 : LangClass) (L : Language) : Prop := ∀ L', 𝒞 L' → RedP L' L

/-- `L` is **`𝒞`-complete**: `L ∈ 𝒞` and `L` is `𝒞`-hard. -/
def Complete (𝒞 : LangClass) (L : Language) : Prop := 𝒞 L ∧ Hard 𝒞 L

/-- Hardness is inherited along reductions. -/
theorem Hard.of_redP {𝒞 : LangClass} {L L' : Language} (hL : Hard 𝒞 L) (h : RedP L L') :
    Hard 𝒞 L' := fun L'' h'' => (hL L'' h'').trans h

/-- Hardness for a larger class implies hardness for a smaller one. -/
theorem Hard.mono {𝒞 𝒟 : LangClass} {L : Language} (hL : Hard 𝒟 L) (h : ∀ L', 𝒞 L' → 𝒟 L') :
    Hard 𝒞 L := fun L' h' => hL L' (h L' h')

/-! ### The classes -/

/-- `P`: languages decided in polynomial time (`HTN.Syn.InP`). -/
def P : LangClass := Syn.InP

/-- `NP`: languages with polynomial certificates checkable in polynomial time
(`HTN.Syn.InNP`). -/
def NP : LangClass := Syn.InNP

/-- `PSPACE` (`HTN.PSpace.InPSpace`, the machine-independent class of
`ComplexityTheory/Complexity/Basic.lean`). -/
def PSPACE : LangClass := PSpace.InPSpace

/-- `NEXPTIME` (`HTN.Space.InNExp`, nondeterministic machines with an exponential clock). -/
def NEXPTIME : LangClass := Space.InNExp

/-- `EXPSPACE` (`HTN.Space.InExpSpace`, nondeterministic machines in exponential space). -/
def EXPSPACE : LangClass := Space.InExpSpace

end Cx

end HTN
