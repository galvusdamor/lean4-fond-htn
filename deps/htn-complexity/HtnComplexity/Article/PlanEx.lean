import HtnPlanning.Article.Desc
import HtnComplexity.PT.Core
import HtnComplexity.Complexity.Serial
import ComplexityTheory.Lang.Basic
/-!
# The plan-existence languages (Def. 4.1)

A planning problem is given to an algorithm as the bit code of a well-formed description
(`HtnPlanning/Article/Desc.lean`).  The code is the self-delimiting encoding `enc` of the typed
calculus of polynomial-time functions (`HtnComplexity/PT/Core.lean`): numbers in binary,
lists as self-delimiting lists, pairs by concatenation.

* `HTN.Article.PlanEx Y` — **`PlanEx^Y_htn`**: the codes of well-formed descriptions of problems
  of the class `Y` that have an HTN solution;
* `HTN.Article.PlanExTI Y` — **`PlanEx^Y_tihtn`**: the same with TIHTN solutions;
* `HTN.Article.primrec_enc_probDesc` — the code of a description is primitive recursive (so a
  reduction that builds descriptions computably is a computable reduction of languages).

A class `Y` is a predicate on problems of the article's model (`HtnPlanning/Article/Classes.lean`);
`HTN.Article.UNRES` is the class of all problems.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

/-! ### Primitive recursiveness of the codes -/

/-- An encoding that is primitive recursive. -/
class PEnc (α : Type) [BEnc α] [Primcodable α] : Prop where
  primrec_enc : Primrec (enc : α → List Bool)

instance : PEnc ℕ := ⟨primrec_serNat⟩

instance : PEnc Bool := ⟨Primrec.list_cons.comp Primrec.id (Primrec.const [])⟩

instance {α β : Type} [BEnc α] [BEnc β] [Primcodable α] [Primcodable β] [PEnc α] [PEnc β] :
    PEnc (α × β) :=
  ⟨Primrec.list_append.comp (PEnc.primrec_enc.comp Primrec.fst)
    (PEnc.primrec_enc.comp Primrec.snd)⟩

instance {α : Type} [BEnc α] [Primcodable α] [PEnc α] : PEnc (List α) :=
  ⟨primrec_blist.comp (Primrec.list_map Primrec.id (PEnc.primrec_enc.comp Primrec.snd).to₂)⟩

/-- **The code of a problem description is primitive recursive.** -/
theorem primrec_enc_probDesc : Primrec (enc : ProbDesc → List Bool) := PEnc.primrec_enc

/-! ### The languages -/

/-- A class of problems of the article's model (over `ℕ`). -/
abbrev PClass : Type := Problem ℕ ℕ ℕ ℕ → Prop

/-- `UNRES-REC`: all problems. -/
def UNRES : PClass := fun _ => True

/-- **`PlanEx^Y_htn` (Def. 4.1)**: the codes of well-formed descriptions of problems of the class
`Y` that have an HTN solution. -/
def PlanEx (Y : PClass) : Cx.Language := fun w =>
  ∃ p : ProbDesc, enc p = w ∧ p.Valid ∧ Y p.toProblem ∧ p.toProblem.Solvable

/-- **`PlanEx^Y_tihtn` (Def. 4.1)**: the same with TIHTN solutions. -/
def PlanExTI (Y : PClass) : Cx.Language := fun w =>
  ∃ p : ProbDesc, enc p = w ∧ p.Valid ∧ Y p.toProblem ∧ p.toProblem.SolvableTI

theorem planEx_enc_iff {Y : PClass} {p : ProbDesc} :
    PlanEx Y (enc p) ↔ p.Valid ∧ Y p.toProblem ∧ p.toProblem.Solvable := by
  constructor
  · rintro ⟨p', hp', h⟩
    rwa [BEnc.inj hp'] at h
  · exact fun h => ⟨p, rfl, h⟩

theorem planExTI_enc_iff {Y : PClass} {p : ProbDesc} :
    PlanExTI Y (enc p) ↔ p.Valid ∧ Y p.toProblem ∧ p.toProblem.SolvableTI := by
  constructor
  · rintro ⟨p', hp', h⟩
    rwa [BEnc.inj hp'] at h
  · exact fun h => ⟨p, rfl, h⟩

/-- **Undecidability by a computable family of descriptions.**  If a computable map `f` sends
the instances of an undecidable problem to well-formed descriptions of problems of the class `Y`
whose solvability is the problem, then `PlanEx^Y_htn` is undecidable. -/
theorem not_decidable_planEx_of {α : Type} [Primcodable α] {Q : α → Prop}
    (hQ : ¬ ComputablePred Q) {Y : PClass} {f : α → ProbDesc} (hf : Computable f)
    (hok : ∀ a, (f a).Valid ∧ Y (f a).toProblem)
    (hsol : ∀ a, (f a).toProblem.Solvable ↔ Q a) : ¬ Cx.Decidable (PlanEx Y) := by
  intro h
  apply hQ
  refine ComputablePred.computable_of_manyOneReducible ⟨fun a => enc (f a),
    primrec_enc_probDesc.to_comp.comp hf, fun a => ?_⟩ h
  rw [planEx_enc_iff, ← hsol]
  exact ⟨fun h => ⟨(hok a).1, (hok a).2, h⟩, fun h => h.2.2⟩

end Article

end HTN
