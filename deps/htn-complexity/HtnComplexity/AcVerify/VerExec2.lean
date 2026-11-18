import HtnComplexity.AcVerify.VerExec
/-!
# Semantics of the verifier, part 6: the execution test as a chain of transitions
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc} {q : InstDesc}

/-- **The chain of transitions** checked by the execution test, from the string `S` that starts
with the current state. -/
def ExecChain (d : DomDesc) (q : InstDesc) : List Bool → List CE → Prop
  | S, [] => subEntB (yB (instSer q)) S = true
  | S, e :: r => transB (advOf d) S e.enc = true ∧ ExecChain d q (stOf e.enc) r

theorem forall_split_cons {α : Type} (Q : α → List α → Prop) (e : α) (r : List α) :
    (∀ l₁ x l₂, e :: r = l₁ ++ x :: l₂ → Q x l₂) ↔
      Q e r ∧ ∀ l₁ x l₂, r = l₁ ++ x :: l₂ → Q x l₂ := by
  constructor
  · intro h
    exact ⟨h [] e r rfl, fun l₁ x l₂ he => h (e :: l₁) x l₂ (by rw [he]; rfl)⟩
  · rintro ⟨h1, h2⟩ l₁ x l₂ he
    rcases l₁ with _ | ⟨y, l₁⟩
    · simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he; exact h1
    · simp only [List.cons_append, List.cons.injEq] at he
      exact h2 l₁ x l₂ he.2

/-- The per-entry condition of the execution test. -/
def TailBody (d : DomDesc) (q : InstDesc) (e : CE) (l₂ : List CE) : Prop :=
  (∀ e' r, l₂ = e' :: r → transB (advOf d) (stOf e.enc) e'.enc = true) ∧
    (l₂ = [] → subEntB (yB (instSer q)) (stOf e.enc) = true)

theorem execChain_iff : ∀ (cs : List CE) (S : List Bool),
    ExecChain d q S cs ↔
      (cs = [] → subEntB (yB (instSer q)) S = true) ∧
        (∀ e r, cs = e :: r → transB (advOf d) S e.enc = true) ∧
          ∀ l₁ e l₂, cs = l₁ ++ e :: l₂ → TailBody d q e l₂
  | [], S => by
    simp [ExecChain]
  | e :: r, S => by
    rw [forall_split_cons (fun x l₂ => TailBody d q x l₂), ExecChain, execChain_iff r]
    unfold TailBody
    constructor
    · rintro ⟨h0, h1, h2, h3⟩
      refine ⟨by simp, fun e' r' he => ?_, ⟨h2, h1⟩, h3⟩
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he; exact h0
    · rintro ⟨-, h0, ⟨h2, h1⟩, h3⟩
      exact ⟨h0 e r rfl, h1, h2, h3⟩

/-- **The execution test is the chain of transitions.** -/
theorem execB_iff (cs : List CE) :
    execB (instSer q) (advOf d) (blist (cs.map CE.enc)) = true ↔ ExecChain d q (instSer q) cs := by
  rw [execChain_iff]
  unfold execB
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  rw [show blist (cs.map CE.enc) = blist (cs.map CE.enc) ++ [] by simp, entAll_iff,
    forall_split_map CE.enc cs (fun l₁ w l₂ => _ = true)]
  have key : ∀ A B C D E F : Prop, (A ↔ D) → (B ↔ E) → (C ↔ F) → ((A ∧ B) ∧ C ↔ E ∧ D ∧ F) := by
    intro A B C D E F h1 h2 h3
    rw [h1, h2, h3]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨b, a, c⟩, fun ⟨b, a, c⟩ => ⟨⟨a, b⟩, c⟩⟩
  refine key _ _ _ _ _ _ ?_ ?_ (forall₃_congr fun l₁ e l₂ => imp_congr_right fun _ => ?_)
  · rcases cs with _ | ⟨e, r⟩
    · simp [hasNext]
    · rw [List.map_cons, nextEnt_blist, cont_entry]
      simp [hasNext, blist_cons]
  · rcases cs with _ | ⟨e, r⟩
    · simp [hasNext]
    · simp [hasNext, blist_cons]
  · unfold TailBody
    rw [cont_entry]
    rcases l₂ with _ | ⟨e', r⟩
    · simp [hasNext, isLast]
    · rw [List.map_cons, nextEnt_blist, cont_entry]
      simp [hasNext, isLast, blist_cons]

/-! ### From the chain to a run -/

/-- The action of a parsed entry. -/
noncomputable def actOf (d : DomDesc) (q : InstDesc) (e : CE) : ℕ := leafAct d q (stepsOf d q e)

theorem setOf_map {l : List ℕ} : setOf (l.map bitsOfNat) = {f | f ∈ l} := by
  ext f; simp [setOf, mem_map_bitsOfNat_iff]

theorem goal_iff (L : List (List Bool)) (z : List Bool) :
    subEntB (yB (instSer q)) (blist L ++ z) = true →
      (problem d q).GoalState (setOf L) := by
  rw [yB_instSer, zB, subEntB_iff]
  intro h f hf
  exact h _ (List.mem_map_of_mem hf)

theorem run_of_chain : ∀ (cs : List CE) (L : List (List Bool)) (z : List Bool),
    (∀ e ∈ cs, rowB (advOf d) e.enc = true → RowOK d e (actOf d q e)) →
    ExecChain d q (blist L ++ z) cs →
      Run d q (setOf L) (cs.map fun e => (e.f, actOf d q e, setOf e.st))
  | [], L, z, _, h => goal_iff L z h
  | e :: r, L, z, hrow, ⟨h1, h2⟩ => by
    rw [transB_iff] at h1
    have hs := trans_sem (q := q) h1.1 (hrow e (by simp) h1.2)
    rw [enc_eq_st] at h2
    refine ⟨?_, run_of_chain r e.st _ (fun e' he' => hrow e' (by simp [he'])) h2⟩
    cases hf : e.f
    · rw [hf] at hs; simpa using hs
    · rw [hf] at hs; simpa using hs

theorem runActs_map (cs : List CE) :
    runActs (cs.map fun e => (e.f, actOf d q e, setOf e.st)) =
      actsOf d q (cs.map fun e => (stepsOf d q e, e.f)) := by
  induction cs with
  | nil => rfl
  | cons e r ih =>
    cases hf : e.f <;> simp [runActs, actsOf, hf, actOf] at ih ⊢ <;> exact ih

/-- **Soundness of the execution test.** -/
theorem execOK_of_execB (cs : List CE)
    (hrow : ∀ e ∈ cs, rowB (advOf d) e.enc = true → RowOK d e (actOf d q e))
    (h : execB (instSer q) (advOf d) (blist (cs.map CE.enc)) = true) :
    ExecOK d q (actsOf d q (cs.map fun e => (stepsOf d q e, e.f))) := by
  rw [execB_iff, instSer_eq] at h
  have hr := run_of_chain cs _ _ hrow h
  rw [setOf_map] at hr
  have := exec_of_run hr
  rw [runActs_map] at this
  exact this

end AcVer

end Syn

end HTN
