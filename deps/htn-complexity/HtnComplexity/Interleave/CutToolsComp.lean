import HtnComplexity.Interleave.CutTools
/-!
# Cutting a plan at a chosen action of one of its *components*

`HtnComplexity/Interleave/CutTools.lean` cuts an interleaving at a chosen element of the *tape*
(`HTN.Interleave.split_right_tight`, `HTN.PlanInter.cut_at`).  The head half of the soundness
argument has to cut a solution plan at the *decision* of a cell counter instead — an action of
one of the components `ls` of `HTN.PlanInter`.  This file provides the corresponding tools:

* `HTN.Interleave.split_left_tight` — the mirror image of `HTN.Interleave.split_right_tight`;
* `HTN.InterleaveList.split_at_getElem` — an interleaving of many lists can be cut at a chosen
  element of any one of them;
* `HTN.PlanInter.cut_at_comp` — hence a plan can be cut at a chosen action of any component;
* `HTN.PlanInter.cons_tape` — an action can be prepended to the tape stream of a plan.

In the conclusion the componentwise splitting is given by the two lists `fsts`, `snds`: the
first halves are prefixes of the components, at the chosen component `j` they are the two
halves `l₁`, `l₂` of `ls[j] = l₁ ++ b :: l₂`, and the chosen action `b` itself is the first
action of the second piece of the whole list.
-/

namespace HTN

variable {α : Type}

namespace Interleave

/-- **An interleaving can be cut at a chosen element of its left component.** -/
lemma split_left_tight {xs y zs : List α} (h : Interleave xs y zs) {x₁ x₂ : List α} {b : α}
    (hx : xs = x₁ ++ b :: x₂) : ∃ y₁ y₂ z₁ z₂, y = y₁ ++ y₂ ∧ zs = z₁ ++ b :: z₂ ∧
      Interleave x₁ y₁ z₁ ∧ Interleave x₂ y₂ z₂ := by
  obtain ⟨y₁, y₂, z₁, z₂, hy, hz, h₁, h₂⟩ := h.symm.split_right_tight hx
  exact ⟨y₁, y₂, z₁, z₂, hy, hz, h₁.symm, h₂.symm⟩

end Interleave

namespace InterleaveList

/-- **An interleaving of many lists can be cut at a chosen element of any one of them.** -/
lemma split_at_getElem : ∀ {ls : List (List α)} {z : List α}, InterleaveList ls z →
    ∀ {j : ℕ}, ∀ hj : j < ls.length, ∀ {l₁ l₂ : List α} {b : α}, ls[j] = l₁ ++ b :: l₂ →
      ∃ (fsts snds : List (List α)) (z₁ z₂ : List α),
        z = z₁ ++ b :: z₂ ∧ List.Forall₂ (· <+: ·) fsts ls ∧
          fsts[j]? = some l₁ ∧ snds[j]? = some l₂ ∧
          InterleaveList fsts z₁ ∧ InterleaveList snds z₂ := by
  intro ls z h
  induction h with
  | nil => intro j hj; simp at hj
  | @cons as bs cs ls hrec hint ih =>
      intro j hj l₁ l₂ b hb
      cases j with
      | zero =>
          have has : as = l₁ ++ b :: l₂ := by simpa using hb
          obtain ⟨y₁, y₂, z₁, z₂, hy, hz, h₁, h₂⟩ := hint.split_left_tight has
          obtain ⟨pss, hls, hp₁, hp₂⟩ := hrec.split_pair hy
          refine ⟨l₁ :: pss.map Prod.fst, l₂ :: pss.map Prod.snd, z₁, z₂, hz, ?_, rfl, rfl,
            InterleaveList.cons hp₁ h₁, InterleaveList.cons hp₂ h₂⟩
          refine List.Forall₂.cons (by rw [has]; exact List.prefix_append _ _) ?_
          rw [hls]
          exact forall₂_prefix_map_fst pss
      | succ j =>
          have hj' : j < ls.length := by simpa using hj
          have hb' : ls[j] = l₁ ++ b :: l₂ := by simpa using hb
          obtain ⟨fsts, snds, y₁, y₂, hy, hall, hf, hs, hp₁, hp₂⟩ := ih hj' hb'
          obtain ⟨a₁, a₂, z₁, z₂, ha, hz, h₁, h₂⟩ := hint.split_right_tight hy
          exact ⟨a₁ :: fsts, a₂ :: snds, z₁, z₂, hz,
            List.Forall₂.cons (by rw [ha]; exact List.prefix_append _ _) hall,
            by simpa using hf, by simpa using hs,
            InterleaveList.cons hp₁ h₁, InterleaveList.cons hp₂ h₂⟩

end InterleaveList

namespace PlanInter

/-- **A plan can be cut at a chosen action of one of its components**: the action itself is the
first action of the second piece, and both the head stream and the tape stream split at that
moment. -/
lemma cut_at_comp {ls : List (List α)} {H T whole : List α} (h : PlanInter ls H T whole)
    {j : ℕ} (hj : j < ls.length) {l₁ l₂ : List α} {b : α} (hb : ls[j] = l₁ ++ b :: l₂) :
    ∃ (fsts snds : List (List α)) (H₁ H₂ T₁ T₂ w₁ w₂ : List α),
      H = H₁ ++ H₂ ∧ T = T₁ ++ T₂ ∧ whole = w₁ ++ b :: w₂ ∧
        List.Forall₂ (· <+: ·) fsts ls ∧ fsts[j]? = some l₁ ∧ snds[j]? = some l₂ ∧
        PlanInter fsts H₁ T₁ w₁ ∧ PlanInter snds H₂ T₂ w₂ := by
  obtain ⟨ac, bs, hil, hi₁, hi₂⟩ := h
  obtain ⟨fsts, snds, ac₁, ac₂, hac, hall, hf, hs, hq₁, hq₂⟩ := hil.split_at_getElem hj hb
  obtain ⟨T₁, T₂, bs₁, bs₂, hT, hbs, hj₁, hj₂⟩ := hi₁.split_left_tight hac
  obtain ⟨H₁, H₂, w₁, w₂, hH, hw, hk₁, hk₂⟩ := hi₂.split_right_tight hbs
  exact ⟨fsts, snds, H₁, H₂, T₁, T₂, w₁, w₂, hH, hT, hw, hall, hf, hs,
    ⟨ac₁, bs₁, hq₁, hj₁, hk₁⟩, ⟨ac₂, bs₂, hq₂, hj₂, hk₂⟩⟩

/-- An action can be prepended to the tape stream of a plan. -/
lemma cons_tape {ls : List (List α)} {H T whole : List α} (h : PlanInter ls H T whole) (a : α) :
    PlanInter ls H (a :: T) (a :: whole) := by
  obtain ⟨ac, bs, hil, hi₁, hi₂⟩ := h
  exact ⟨ac, a :: bs, hil, Interleave.right a hi₁, Interleave.right a hi₂⟩

end PlanInter

end HTN
