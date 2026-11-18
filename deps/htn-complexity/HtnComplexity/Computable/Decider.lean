import HtnPlanning.Computable.Classes
/-!
# Decidability of plan existence for a class of descriptions

`HTN.Syn.SynClass.Decider T`: plan existence for the class `T` is decidable;
`HTN.Syn.SynClass.DeciderAt S d`: it is decidable with the domain description `d` held fixed.
Split out of `HTN.Computable.Compilation`.
-/

namespace HTN

namespace Syn

open Table

variable {𝒟 ℰ ℱ : Family}

variable {S : SynClass 𝒟} {T : SynClass ℰ} {U : SynClass ℱ}

namespace SynClass

/-- **Plan existence is decidable for the class `T`**: a computable function that decides
solvability of every described problem *of the class*.  Nothing is required of it outside the
class. -/
def Decider (T : SynClass ℰ) : Prop :=
  ∃ f : DomDesc → InstDesc → Bool, Computable₂ f ∧
    ∀ d q, T.domOk d → T.instOk q → (f d q = true ↔ Solvable d q)

/-- **Plan existence is decidable for the class `S` with the domain `d` held fixed**: the
uniform plan existence problem of one domain description, in which only the initial state, the
goal and the initial task network vary.  Its negation — undecidability already for a single
domain — is how the undecidability of HTN planning arises: a fixed hierarchy simulating a
universal machine. -/
def DeciderAt (S : SynClass 𝒟) (d : DomDesc) : Prop :=
  ∃ g : InstDesc → Bool, Computable g ∧ ∀ q, S.instOk q → (g q = true ↔ Solvable d q)

/-- A decision procedure for the class decides the uniform problem of each of its domains. -/
theorem Decider.deciderAt (h : S.Decider) {d : DomDesc} (hd : S.domOk d) : S.DeciderAt d := by
  obtain ⟨f, hf, hcorr⟩ := h
  exact ⟨fun q => f d q, hf.comp (Computable.const d) Computable.id,
    fun q hq => hcorr d q hd hq⟩

/-- Contrapositive: undecidability for one fixed domain implies undecidability of the class. -/
theorem not_decider_of_not_deciderAt {d : DomDesc} (hd : S.domOk d) (h : ¬ S.DeciderAt d) :
    ¬ S.Decider :=
  fun hdec => h (hdec.deciderAt hd)

/-- A decision procedure for a class decides every subclass. -/
theorem Decider.of_sub (hsub : SynSub S T) (h : T.Decider) : S.Decider := by
  obtain ⟨f, hf, hcorr⟩ := h
  exact ⟨f, hf, fun d q hd hq => hcorr d q (hsub.dom d hd) (hsub.inst q hq)⟩

end SynClass

/-- A predicate with a computable Boolean decider is computable. -/
theorem computablePred_of_decider {α : Type} [Primcodable α] {p : α → Prop} {d : α → Bool}
    (hd : Computable d) (h : ∀ a, d a = true ↔ p a) : ComputablePred p := by
  classical
  refine ⟨Classical.decPred p, hd.of_eq fun a => ?_⟩
  by_cases hp : p a
  · rw [(h a).2 hp, decide_eq_true hp]
  · have hfalse : d a = false := by
      cases hda : d a
      · rfl
      · exact absurd ((h a).1 hda) hp
    rw [hfalse, decide_eq_false hp]

end Syn

end HTN
