import ComplexityTheory.TM.Basic
import ComplexityTheory.Complexity.Basic
import HtnPlanning.Basic
import HtnPlanning.Classes.Basic
import HtnPlanning.SynClasses.Basic
import HtnComplexity.Complexity.BitCoding
import HtnPlanning.Computable.Classes
/-!
# Hardness families and advice

**Definitions only.**  The non-uniform reductions to plan existence used throughout:

* `HTN.Syn.HardFamily S L` — one domain description per input length and one instance description
  per input word, of polynomial size, in the class `S`, solvable exactly for the words of `L`;
* `HTN.Syn.Coded.HardFamilyPT c S L` — with a computable domain part and a polynomial-time
  instance part (relative to the coding `c`), and `HTN.Syn.Coded.HardFamilyNU c S L` — with an
  arbitrary domain part of polynomial size;
* `HTN.Syn.Coded.InPolyAdvice c T L` — `L` is decided by plan existence in the class `T` with
  polynomial advice (a domain description per length).
-/

/-! ## Hardness families -/

namespace HTN

namespace Syn

open Table

variable {𝒟 ℰ : Family} {S : SynClass 𝒟} {T : SynClass ℰ}

variable {Eff : (InstDesc → InstDesc) → Prop} {L : List Bool → Prop} {Collapse : Prop}

/-- **A hardness family for the language `L` inside the class `S`**: one domain description per
input *length* and one instance description per input *word*, both of polynomial size, both in
the class, the instance encoding injective, and the described problem solvable exactly when the
word is in `L`.

This is the shape of the encodings the complexity results of the literature produce — Theorem
5.1 of Alford et al. for `TO-HTN`, Theorem 6.1 for `HTN-TR` and `HTN-AC`.  None of them is
formalised in this development; a family is always assumed, never constructed. -/
structure HardFamily (S : SynClass 𝒟) (L : List Bool → Prop) where
  /-- The domain description for the inputs of a given length — the *fixed part*. -/
  dom : ℕ → DomDesc
  /-- The instance description that codes an input word — the *varying part*. -/
  inst : List Bool → InstDesc
  /-- The polynomial bounding both. -/
  bound : Polynomial ℕ
  /-- The domain descriptions are of polynomial size. -/
  dom_size : ∀ n, (dom n).size ≤ bound.eval n
  /-- The instance descriptions are of polynomial size. -/
  inst_size : ∀ w, (inst w).size ≤ bound.eval w.length
  /-- The domain descriptions belong to the class. -/
  dom_ok : ∀ n, S.domOk (dom n)
  /-- The instance descriptions belong to the class. -/
  inst_ok : ∀ w, S.instOk (inst w)
  /-- Different words are coded by different instance descriptions. -/
  inst_injective : Function.Injective inst
  /-- The coded problem is solvable exactly for the words of `L`. -/
  correct : ∀ w, Solvable (dom w.length) (inst w) ↔ L w

/-- A hardness family in a class is one in every larger class. -/
def HardFamily.mono {S' : SynClass ℰ} (F : HardFamily S L) (h : SynSub S S') :
    HardFamily S' L :=
  { F with
    dom_ok := fun n => h.dom _ (F.dom_ok n)
    inst_ok := fun w => h.inst _ (F.inst_ok w) }

end Syn

end HTN

/-! ## Hardness families and advice -/

namespace HTN

namespace Syn

namespace Coded

open PTime Table

variable {𝒟 ℰ : Family} {S : SynClass 𝒟} {T : SynClass ℰ}

variable {L : List Bool → Prop} {Collapse : Prop} {c : BitCoding InstDesc}

/-- **A hardness family produced by an algorithm**, relative to the coding `c`: the domain
descriptions are computable in the input length, and the instance descriptions are computed
from the word in polynomial time. -/
structure HardFamilyPT (c : BitCoding InstDesc) (S : SynClass 𝒟) (L : List Bool → Prop)
    extends HardFamily S L where
  /-- The fixed part is produced by an algorithm. -/
  dom_computable : Computable toHardFamily.dom
  /-- The varying part is produced in polynomial time. -/
  inst_polyTime : PolyTimeCode c toHardFamily.inst

/-- **The language is decided by the target class with polynomial advice**, relative to `c`. -/
def InPolyAdvice (c : BitCoding InstDesc) (T : SynClass ℰ) (L : List Bool → Prop) : Prop :=
  ∃ (E : List Bool → InstDesc) (D : ℕ → DomDesc) (r : Polynomial ℕ),
    PolyTimeCode c E ∧ (∀ n, (D n).size ≤ r.eval n) ∧ (∀ w, (E w).size ≤ r.eval w.length) ∧
      (∀ n, T.domOk (D n)) ∧ (∀ w, T.instOk (E w)) ∧
      (∀ w, Solvable (D w.length) (E w) ↔ L w)

variable {L' : List Bool → Prop}

/-- **A hardness family with a polynomial-time instance map** and an arbitrary — possibly
non-computable — family of domain descriptions of polynomial size. -/
structure HardFamilyNU (c : BitCoding InstDesc) (S : SynClass 𝒟) (L : List Bool → Prop)
    extends HardFamily S L where
  /-- The varying part is produced in polynomial time. -/
  inst_polyTime : PolyTimeCode c toHardFamily.inst

/-- Every polynomial-time hardness family is one with a non-uniform domain part. -/
def HardFamilyPT.toNU (F : HardFamilyPT c S L) : HardFamilyNU c S L :=
  { F.toHardFamily with inst_polyTime := F.inst_polyTime }

/-- A hardness family in a class is one in every larger class. -/
def HardFamilyNU.mono {S' : SynClass ℰ} (F : HardFamilyNU c S L) (h : SynSub S S') :
    HardFamilyNU c S' L :=
  { F.toHardFamily.mono h with inst_polyTime := F.inst_polyTime }

/-- A hardness family for a language is one for every equivalent language. -/
def HardFamilyNU.congrLang (F : HardFamilyNU c S L) (h : ∀ w, L w ↔ L' w) :
    HardFamilyNU c S L' :=
  { F.toHardFamily with
    correct := fun w => (F.correct w).trans (h w)
    inst_polyTime := F.inst_polyTime }

end Coded

end Syn

end HTN

