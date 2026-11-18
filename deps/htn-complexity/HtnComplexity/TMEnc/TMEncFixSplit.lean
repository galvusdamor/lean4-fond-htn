import HtnComplexity.TMEnc.TMEncFixAlignCounts
import HtnComplexity.Interleave.RoundSplit
/-!
# Splitting a prefix of a solution plan into the three streams

A solution plan of the repaired encoding interleaves the stream of the head counter, the runs of
the `K + 1` cell counters and the cells of the tape (`HTN.TMEnc.isSolutionPlanFix_normalForm`).
The lock-step argument reads a plan at selected *moments* — the ends of the cells and the ends of
their `check` halves — and has to know how far each of the three streams has come at such a
moment.  This file provides the bookkeeping:

* `HTN.TMEnc.IsPlanSplit` — a prefix `p` of the plan, split into a prefix of each stream;
* `HTN.TMEnc.countP_of_isPlanSplit` — counting is additive along a split;
* `HTN.TMEnc.IsPlanSplit.restrict` — **a shorter prefix has a split whose parts are prefixes of
  the parts of the longer one** (this is what makes the counters' progress monotone);
* `HTN.TMEnc.exists_isPlanSplit_of_tape` — **for every way of cutting the tape stream there is a
  prefix of the plan whose tape part is exactly the first piece** — the moments.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {K : ℕ}

/-- **A split of a prefix `p` of a solution plan**: `parts` are the parts of the runs of the cell
counters, `ph` the part of the stream of the head counter and `pt` the part of the tape stream
`T` that have been executed in `p`. -/
def IsPlanSplit (Q Γ : Type) (K : ℕ) (ass : List (List (TMAct Q Γ))) (T p : List (TMAct Q Γ))
    (parts : List (List (TMAct Q Γ))) (ph pt : List (TMAct Q Γ)) : Prop :=
  List.Forall₂ (· <+: ·) parts ass ∧ ph <+: headStream Q Γ K ∧ pt <+: T ∧
    ∃ pac pbs : List (TMAct Q Γ),
      InterleaveList parts pac ∧ Interleave pac pt pbs ∧ Interleave ph pbs p

/-- **Counting is additive along a split.** -/
lemma countP_of_isPlanSplit {ass : List (List (TMAct Q Γ))} {T p : List (TMAct Q Γ)}
    {parts : List (List (TMAct Q Γ))} {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K ass T p parts ph pt) (f : TMAct Q Γ → Bool) :
    p.countP f = ph.countP f + ((parts.map fun l => l.countP f).sum + pt.countP f) := by
  obtain ⟨-, -, -, pac, pbs, hpl, hpi, hph⟩ := h
  rw [hph.countP, hpi.countP, hpl.countP]

lemma IsPlanSplit.parts_prefix {ass : List (List (TMAct Q Γ))} {T p : List (TMAct Q Γ)}
    {parts : List (List (TMAct Q Γ))} {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K ass T p parts ph pt) : List.Forall₂ (· <+: ·) parts ass := h.1

lemma IsPlanSplit.tape_prefix {ass : List (List (TMAct Q Γ))} {T p : List (TMAct Q Γ)}
    {parts : List (List (TMAct Q Γ))} {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K ass T p parts ph pt) : pt <+: T := h.2.2.1

/-- Being a prefix is transitive along `List.Forall₂`. -/
lemma forall₂_prefix_trans {α : Type} : ∀ {l₁ l₂ l₃ : List (List α)},
    List.Forall₂ (· <+: ·) l₁ l₂ → List.Forall₂ (· <+: ·) l₂ l₃ →
      List.Forall₂ (· <+: ·) l₁ l₃ := by
  intro l₁ l₂ l₃ h₁
  induction h₁ generalizing l₃ with
  | nil => intro h; cases h; exact List.Forall₂.nil
  | cons hab _ ih =>
      intro h
      cases h with
      | cons hbc hrest => exact List.Forall₂.cons (hab.trans hbc) (ih hrest)

/-- **Every shorter prefix has a split refining the given one.** -/
lemma IsPlanSplit.restrict {ass : List (List (TMAct Q Γ))} {T p q : List (TMAct Q Γ)}
    {parts : List (List (TMAct Q Γ))} {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K ass T p parts ph pt) (hq : q <+: p) :
    ∃ (parts' : List (List (TMAct Q Γ))) (ph' pt' : List (TMAct Q Γ)),
      IsPlanSplit Q Γ K ass T q parts' ph' pt' ∧ List.Forall₂ (· <+: ·) parts' parts := by
  obtain ⟨hparts, hph, hpt, pac, pbs, hpl, hpi, hint⟩ := h
  obtain ⟨ph', pbs', hph', hpbs', hint'⟩ := hint.exists_prefix hq
  obtain ⟨pac', pt', hpac', hpt', hpi'⟩ := hpi.exists_prefix hpbs'
  obtain ⟨parts', hpl', hall⟩ := hpl.exists_prefix hpac'
  exact ⟨parts', ph', pt', ⟨forall₂_prefix_trans hall hparts, hph'.trans hph,
    hpt'.trans hpt, pac', pbs', hpl', hpi', hint'⟩, hall⟩

/-- **Every cut of the tape stream is realised by a prefix of the plan.**  If the tape stream
splits as `T₁ ++ T₂`, then the plan has a prefix whose tape part is exactly `T₁`. -/
lemma exists_isPlanSplit_of_tape {ass : List (List (TMAct Q Γ))}
    {ac T bs as₁ T₁ T₂ : List (TMAct Q Γ)} (hil : InterleaveList ass ac)
    (h₁ : Interleave ac T bs) (h₂ : Interleave (headStream Q Γ K) bs as₁) (hT : T = T₁ ++ T₂) :
    ∃ (p : List (TMAct Q Γ)) (parts : List (List (TMAct Q Γ))) (ph : List (TMAct Q Γ)),
      p <+: as₁ ∧ IsPlanSplit Q Γ K ass T p parts ph T₁ := by
  obtain ⟨a₁, a₂, b₁, b₂, hac, hbs, hi₁, -⟩ := h₁.split_right hT
  obtain ⟨h₁', h₂', p, p₂, hhead, has, hip, -⟩ := h₂.split_right hbs
  obtain ⟨parts, hpl, hall⟩ := hil.exists_prefix ⟨a₂, hac.symm⟩
  exact ⟨p, parts, h₁', ⟨p₂, has.symm⟩,
    ⟨hall, ⟨h₂', hhead.symm⟩, ⟨T₂, hT.symm⟩, a₁, b₁, hpl, hi₁, hip⟩⟩

end TMEnc

end HTN
