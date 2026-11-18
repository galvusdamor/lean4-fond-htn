import FondHtn.HardTR.TDescL
import FondHtn.HardMP.Classes
/-!
# CB22 Thm 5: the description is tail-recursive

**`FOND.HardTR.TD.desc_TR`**: the rank `rkC` of the compound names strictly decreases from a
method to its compound subtasks, except for the loop `loop p ↦ block p · loop p`, whose recursive
call is the last task.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TD

open TL TT TE HardMP HTN HTN.Syn HTN.Article AcycHard.Sav

variable {S : Type} {cS : S → ℕ} {X : Spec S} {allS : List S} {ops : List Op} {ens : List (En S)}
  {σ₀ : S}

/-- The rank of a compound name (`m` address bits). -/
def rkC (m c : ℕ) : ℕ :=
  let t := (Nat.unpair c).1
  let k := (Nat.unpair (Nat.unpair c).2).2
  if t = 0 then 2 * m + 6 else if t = 1 then 2 * m + 5 else if t = 2 then 2 * m + 4
  else if t = 3 then m + 3 + k else if t = 4 then 2 + (m - k) else if t = 5 then 1 else 0

section Rk

variable (m : ℕ)

@[simp] theorem rk_main : rkC m (nmN .main) = 2 * m + 6 := by simp [rkC, nmN]
@[simp] theorem rk_loop (p : Bool) : rkC m (nmN (.loop p)) = 2 * m + 5 := by simp [rkC, nmN]
@[simp] theorem rk_block (p : Bool) : rkC m (nmN (.block p)) = 2 * m + 4 := by simp [rkC, nmN]
@[simp] theorem rk_tree (p : Bool) (k : ℕ) : rkC m (nmN (.tree p k)) = m + 3 + k := by simp [rkC, nmN]
@[simp] theorem rk_bit (p : Bool) (k : ℕ) : rkC m (nmN (.bit p k)) = 2 + (m - k) := by simp [rkC, nmN]
@[simp] theorem rk_core (p : Bool) : rkC m (nmN (.core p)) = 1 := by simp [rkC, nmN]
@[simp] theorem rk_incT (p : Bool) : rkC m (nmN (.incT p)) = 0 := by simp [rkC, nmN]
@[simp] theorem rk_rvT (p γ : Bool) : rkC m (nmN (.rvT p γ)) = 0 := by simp [rkC, nmN]
@[simp] theorem rk_rbT (p : Bool) (k : ℕ) (b : Bool) : rkC m (nmN (.rbT p k b)) = 0 := by
  simp [rkC, nmN]
@[simp] theorem rk_reT (p : Bool) : rkC m (nmN (.reT p)) = 0 := by simp [rkC, nmN]
@[simp] theorem rk_finT : rkC m (nmN .finT) = 0 := by simp [rkC, nmN]

end Rk

/-- The compound subtasks of a set network. -/
theorem mem_of_label_inr_set {ls : List (Bool × ℕ)} {t c : ℕ}
    (ht : t ∈ (setTn ls).toTaskNetwork.T) (h : (setTn ls).toTaskNetwork.α t = Sum.inr c) :
    (true, c) ∈ ls :=
  mem_of_label_inr (ls := ls) (by rwa [setTn_T] at ht) h

/-- The last task of a sequence of length two. -/
theorem isLast_one {a b : Bool × ℕ} : (seqTn [a, b]).toTaskNetwork.IsLastId 1 := by
  refine ⟨mem_T_seqTn.2 (by simp), fun t' ht' hne => ?_⟩
  have ht'' := mem_T_seqTn.1 ht'
  have : t' = 0 := by simp at ht''; omega
  subst this
  rw [(isSeqNet_seqTn [a, b]).ord]
  simp only [List.length_cons, List.length_nil]
  decide

/-- **The rank decreases** along every method, except for the last task of the loop. -/
theorem rank_key {e : MethodDesc} (he : e ∈ meths cS X ops ens) {t c : ℕ}
    (ht : t ∈ e.2.toTaskNetwork.T) (hc : e.2.toTaskNetwork.α t = Sum.inr c) :
    rkC (mm X) c < rkC (mm X) e.1 ∨
      (rkC (mm X) c = rkC (mm X) e.1 ∧ e.2.toTaskNetwork.IsLastId t) := by
  have hseq : ∀ {y : Nt} {ls : List (Bool × ℕ)}, e = (nmN y, seqTn ls) →
      (∀ c', (true, c') ∈ ls → rkC (mm X) c' < rkC (mm X) (nmN y)) →
      rkC (mm X) c < rkC (mm X) e.1 := by
    rintro y ls rfl h
    exact h c (mem_of_label_inr ht hc)
  have hset : ∀ {y : Nt} {ls : List (Bool × ℕ)}, e = (nmN y, setTn ls) →
      (∀ c', (true, c') ∈ ls → rkC (mm X) c' < rkC (mm X) (nmN y)) →
      rkC (mm X) c < rkC (mm X) e.1 := by
    rintro y ls rfl h
    exact h c (mem_of_label_inr_set ht hc)
  have hP : ∀ p, e ∈ methsP cS X ops ens p → rkC (mm X) c < rkC (mm X) e.1 ∨
      (rkC (mm X) c = rkC (mm X) e.1 ∧ e.2.toTaskNetwork.IsLastId t) := fun p hp => by
    simp only [methsP, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.mem_map, List.not_mem_nil, or_false] at hp
    rcases hp with ((((((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, hp⟩) | ⟨o, -, hp⟩) |
      ⟨γ, -, hp⟩) | ⟨e', -, rfl⟩) | rfl)
    · -- the loop
      have ht' := mem_T_seqTn.1 ht
      have hl := fst_of_label_inr ht' hc
      simp only [List.length_cons, List.length_nil] at ht'
      rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
      · simp only [List.getI_cons_zero, lN, Prod.mk.injEq, true_and] at hl
        subst hl; left; simp
      · simp only [List.getI_cons_succ, List.getI_cons_zero, lN, Prod.mk.injEq, true_and] at hl
        subst hl; right; exact ⟨rfl, isLast_one⟩
    · exact Or.inl (hseq rfl fun c' hc' => by simp at hc')
    · refine Or.inl (hset rfl fun c' hc' => ?_)
      simp only [lN, List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> simp <;> omega
    · refine Or.inl (hseq rfl fun c' hc' => ?_)
      simp only [lN, List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at hc'
      subst hc'; simp; omega
    · refine Or.inl (hseq rfl fun c' hc' => ?_)
      simp only [lN, List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at hc'
      subst hc'; simp
    · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
    · rcases hp with (rfl | rfl) | ⟨b, -, hp⟩
      · refine Or.inl (hset rfl fun c' hc' => ?_)
        simp only [lN, List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false,
          or_self] at hc'
        subst hc'; simp
      · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
      · rcases hp with rfl | rfl | rfl
        · refine Or.inl (hseq rfl fun c' hc' => ?_)
          simp [lN, lA] at hc'
          rcases hc' with rfl | rfl <;> simp <;> omega
        · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
        · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
    · rcases hp with rfl | rfl
      · refine Or.inl (hseq rfl fun c' hc' => ?_)
        simp [lN, lA] at hc'
        rcases hc' with rfl | rfl <;> simp
      · refine Or.inl (hseq rfl fun c' hc' => ?_)
        simp [lN, lA] at hc'
        rcases hc' with rfl | rfl <;> simp
    · rcases hp with rfl | rfl
      · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
      · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
    · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
    · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
  simp only [meths, List.mem_cons, List.mem_append] at he
  rcases he with (rfl | rfl | he) | he
  · refine Or.inl (hset rfl fun c' hc' => ?_)
    simp only [lN, List.mem_cons, Prod.mk.injEq, true_and, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl <;> simp <;> omega
  · exact Or.inl (hseq rfl fun c' hc' => by simp [lA] at hc')
  · exact hP true he
  · exact hP false he

/-- **The description is tail-recursive.** -/
theorem desc_TR : FClass.TR (desc cS X allS ops ens σ₀).toProblem := by
  refine ⟨fun x y => rkC (mm X) x ≤ rkC (mm X) y, ⟨⟨fun _ _ => le_rfl,
    fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂, fun _ _ _ _ => le_total _ _⟩, ?_, ?_⟩⟩
  · intro m hm t ht _ c hc
    obtain ⟨⟨e, he, rfl⟩, -⟩ := hm
    rw [methods_desc] at he
    rcases rank_key he ht hc with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  · intro m hm t ht hnl c hc
    obtain ⟨⟨e, he, rfl⟩, -⟩ := hm
    rw [methods_desc] at he
    rcases rank_key he ht hc with h | ⟨-, h⟩
    · exact ⟨h.le, fun h' => absurd h' (Nat.not_le.2 h)⟩
    · exact absurd h hnl

end TD

end HardTR

end FOND
