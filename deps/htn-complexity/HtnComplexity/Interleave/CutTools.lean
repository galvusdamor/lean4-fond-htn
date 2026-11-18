import HtnComplexity.Interleave.RoundSplit
/-!
# Tools for cutting a plan at a chosen action

The soundness half of the simulation argument of the repaired Turing-machine encoding has to
read a solution plan *between two actions of the tape*: the tape's `assert` of a cell and the
`assert` of the next one.  This file collects the generic list combinatorics that this needs and
that is independent of the encoding:

* `HTN.Interleave.split_right_tight` — an interleaving can be cut **at** a chosen element of its
  right component: the element itself is the first element of the second piece;
* `HTN.InterleaveList.split_pair`, `HTN.InterleaveList.append_pair` — an interleaving of many
  lists splits, and re-assembles, componentwise;
* `HTN.Interleave.filter`, `HTN.InterleaveList.filter` — filtering commutes with interleaving;
* `HTN.InterleaveList.eq_getElem_of_others_nil` — an interleaving in which all but one component
  are empty is that component;
* `HTN.exists_split_of_filter_eq_cons` — a list whose filter starts with `a` splits at the
  occurrence of `a`;
* `HTN.prefix_roundStream_eq` — **a prefix of a stream of rounds whose first and last elements
  are marked, and which contains exactly `n` of each mark, is the stream of the first `n`
  rounds**.
-/

namespace HTN

variable {α : Type}

namespace Interleave

/-- **An interleaving can be cut at a chosen element of its right component.**  If `zs`
interleaves `xs` with `y₁ ++ b :: y₂`, then `zs = z₁ ++ b :: z₂` with `z₁` an interleaving of a
prefix of `xs` with `y₁` and `z₂` an interleaving of the rest with `y₂`. -/
lemma split_right_tight : ∀ {xs y zs : List α}, Interleave xs y zs → ∀ {y₁ y₂ : List α} {b : α},
    y = y₁ ++ b :: y₂ → ∃ x₁ x₂ z₁ z₂, xs = x₁ ++ x₂ ∧ zs = z₁ ++ b :: z₂ ∧
      Interleave x₁ y₁ z₁ ∧ Interleave x₂ y₂ z₂ := by
  intro xs y zs h
  induction h with
  | nil =>
      intro y₁ y₂ b hy
      exact absurd hy.symm (by simp)
  | @left xs' ys' zs' a _ ih =>
      intro y₁ y₂ b hy
      obtain ⟨x₁, x₂, z₁, z₂, hx, hz, h₁, h₂⟩ := ih hy
      exact ⟨a :: x₁, x₂, a :: z₁, z₂, by rw [hx]; rfl, by rw [hz]; rfl,
        Interleave.left a h₁, h₂⟩
  | @right xs' ys' zs' a hrec ih =>
      intro y₁ y₂ b hy
      cases y₁ with
      | nil =>
          have hb : a = b := by simpa using (List.cons.inj hy).1
          have hys : ys' = y₂ := by simpa using (List.cons.inj hy).2
          subst hb; subst hys
          exact ⟨[], xs', [], zs', rfl, rfl, Interleave.nil, hrec⟩
      | cons c y₁ =>
          have hc : c = a := by simpa using (List.cons.inj hy).1.symm
          have hys : ys' = y₁ ++ b :: y₂ := by simpa using (List.cons.inj hy).2
          subst hc
          obtain ⟨x₁, x₂, z₁, z₂, hx, hz, h₁, h₂⟩ := ih hys
          exact ⟨x₁, x₂, c :: z₁, z₂, hx, by rw [hz]; rfl, Interleave.right c h₁, h₂⟩

/-- **An interleaving splits along any splitting of the result.** -/
lemma split_result : ∀ {xs ys zs : List α}, Interleave xs ys zs → ∀ {z₁ z₂ : List α},
    zs = z₁ ++ z₂ → ∃ x₁ x₂ y₁ y₂, xs = x₁ ++ x₂ ∧ ys = y₁ ++ y₂ ∧
      Interleave x₁ y₁ z₁ ∧ Interleave x₂ y₂ z₂ := by
  intro xs ys zs h
  induction h with
  | nil =>
      intro z₁ z₂ hz
      have h₁ : z₁ = [] := by
        rcases List.append_eq_nil_iff.1 hz.symm with ⟨h, -⟩; exact h
      have h₂ : z₂ = [] := by
        rcases List.append_eq_nil_iff.1 hz.symm with ⟨-, h⟩; exact h
      subst h₁; subst h₂
      exact ⟨[], [], [], [], rfl, rfl, Interleave.nil, Interleave.nil⟩
  | @left xs ys zs a hrec ih =>
      intro z₁ z₂ hz
      cases z₁ with
      | nil =>
          refine ⟨[], a :: xs, [], ys, rfl, rfl, Interleave.nil, ?_⟩
          simpa [hz] using Interleave.left a hrec
      | cons b z₁ =>
          have hb : b = a := by simpa using (List.cons.inj hz).1.symm
          have hzs : zs = z₁ ++ z₂ := by simpa using (List.cons.inj hz).2
          subst hb
          obtain ⟨x₁, x₂, y₁, y₂, hx, hy, h₁, h₂⟩ := ih hzs
          exact ⟨b :: x₁, x₂, y₁, y₂, by rw [hx]; rfl, hy, Interleave.left b h₁, h₂⟩
  | @right xs ys zs a hrec ih =>
      intro z₁ z₂ hz
      cases z₁ with
      | nil =>
          refine ⟨[], xs, [], a :: ys, rfl, rfl, Interleave.nil, ?_⟩
          simpa [hz] using Interleave.right a hrec
      | cons b z₁ =>
          have hb : b = a := by simpa using (List.cons.inj hz).1.symm
          have hzs : zs = z₁ ++ z₂ := by simpa using (List.cons.inj hz).2
          subst hb
          obtain ⟨x₁, x₂, y₁, y₂, hx, hy, h₁, h₂⟩ := ih hzs
          exact ⟨x₁, x₂, b :: y₁, y₂, hx, by rw [hy]; rfl, Interleave.right b h₁, h₂⟩

/-- **Filtering commutes with interleaving.** -/
lemma filter (p : α → Bool) {xs ys zs : List α} (h : Interleave xs ys zs) :
    Interleave (xs.filter p) (ys.filter p) (zs.filter p) := by
  induction h with
  | nil => exact Interleave.nil
  | @left xs ys zs a _ ih =>
      by_cases ha : p a
      · simpa [List.filter_cons, ha] using Interleave.left a ih
      · simpa [List.filter_cons, ha] using ih
  | @right xs ys zs a _ ih =>
      by_cases ha : p a
      · simpa [List.filter_cons, ha] using Interleave.right a ih
      · simpa [List.filter_cons, ha] using ih

end Interleave

namespace InterleaveList

/-- **An interleaving of many lists splits componentwise.** -/
lemma split_pair : ∀ {ls : List (List α)} {z : List α}, InterleaveList ls z →
    ∀ {z₁ z₂ : List α}, z = z₁ ++ z₂ →
      ∃ pss : List (List α × List α), ls = pss.map (fun x => x.1 ++ x.2) ∧
        InterleaveList (pss.map Prod.fst) z₁ ∧ InterleaveList (pss.map Prod.snd) z₂ := by
  intro ls z h
  induction h with
  | nil =>
      intro z₁ z₂ hz
      have h₁ : z₁ = [] := by
        rcases List.append_eq_nil_iff.1 hz.symm with ⟨h, -⟩; exact h
      have h₂ : z₂ = [] := by
        rcases List.append_eq_nil_iff.1 hz.symm with ⟨-, h⟩; exact h
      subst h₁; subst h₂
      exact ⟨[], rfl, InterleaveList.nil, InterleaveList.nil⟩
  | @cons as bs cs ls hrec hint ih =>
      intro z₁ z₂ hz
      obtain ⟨a₁, a₂, b₁, b₂, ha, hb, hi₁, hi₂⟩ := hint.split_result hz
      obtain ⟨pss, hls, hp₁, hp₂⟩ := ih hb
      exact ⟨(a₁, a₂) :: pss, by rw [ha, hls]; rfl,
        InterleaveList.cons hp₁ hi₁, InterleaveList.cons hp₂ hi₂⟩

/-- An interleaving of empty lists is empty. -/
lemma eq_nil_of_forall_nil : ∀ {ls : List (List α)} {z : List α}, InterleaveList ls z →
    (∀ l ∈ ls, l = []) → z = [] := by
  intro ls z h
  induction h with
  | nil => intro _; rfl
  | @cons as bs cs ls hrec hint ih =>
      intro hall
      have has : as = [] := hall as (by simp)
      have hbs : bs = [] := ih fun l hl => hall l (by simp [hl])
      subst has; subst hbs
      exact (hint.eq_of_nil_left).symm ▸ rfl

/-- **Two componentwise interleavings assemble into one.** -/
lemma append_pair : ∀ {pss : List (List α × List α)} {z₁ z₂ : List α},
    InterleaveList (pss.map Prod.fst) z₁ → InterleaveList (pss.map Prod.snd) z₂ →
      InterleaveList (pss.map fun x => x.1 ++ x.2) (z₁ ++ z₂) := by
  intro pss
  induction pss with
  | nil =>
      intro z₁ z₂ h₁ h₂
      cases h₁; cases h₂
      exact InterleaveList.nil
  | cons p pss ih =>
      intro z₁ z₂ h₁ h₂
      cases h₁ with
      | @cons _ b₁ _ _ hr₁ hi₁ =>
        cases h₂ with
        | @cons _ b₂ _ _ hr₂ hi₂ =>
          exact InterleaveList.cons (ih hr₁ hr₂) (hi₁.append_append hi₂)

/-- **An interleaving in which all components but one are empty is that component.** -/
lemma eq_getElem_of_others_nil : ∀ {ls : List (List α)} {z : List α}, InterleaveList ls z →
    ∀ {j : ℕ} (hj : j < ls.length),
      (∀ i, ∀ hi : i < ls.length, i ≠ j → ls[i] = []) → z = ls[j] := by
  intro ls z h
  induction h with
  | nil => intro j hj _; simp at hj
  | @cons as bs cs ls hrec hint ih =>
      intro j hj hall
      cases j with
      | zero =>
          have hbs : bs = [] := by
            refine eq_nil_of_forall_nil hrec fun l hl => ?_
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
            exact hall (i + 1) (by simpa using hi) (by omega)
          subst hbs
          simpa using hint.eq_of_nil_right
      | succ j =>
          have has : as = [] := hall 0 (by simp) (by omega)
          subst has
          have hz : cs = bs := hint.eq_of_nil_left
          rw [hz]
          have hj' : j < ls.length := by simpa using hj
          refine ih hj' fun i hi hij => ?_
          have := hall (i + 1) (by simpa using hi) (by omega)
          simpa using this

/-- **Filtering commutes with interleaving.** -/
lemma filter (p : α → Bool) : ∀ {ls : List (List α)} {z : List α}, InterleaveList ls z →
    InterleaveList (ls.map fun l => l.filter p) (z.filter p) := by
  intro ls z h
  induction h with
  | nil => exact InterleaveList.nil
  | cons hrec hint ih => exact InterleaveList.cons ih (hint.filter p)

end InterleaveList

/-- A list whose filter starts with `a` splits at that occurrence of `a`. -/
lemma exists_split_of_filter_eq_cons {p : α → Bool} : ∀ {l : List α} {a : α} {rest : List α},
    l.filter p = a :: rest → ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ l₁.filter p = [] ∧ l₂.filter p = rest := by
  intro l
  induction l with
  | nil => intro a rest h; simp at h
  | cons b l ih =>
      intro a rest h
      by_cases hb : p b
      · rw [List.filter_cons_of_pos hb] at h
        obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨[], l, rfl, rfl, rfl⟩
      · rw [List.filter_cons_of_neg hb] at h
        obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := ih h
        exact ⟨b :: l₁, l₂, rfl, by rw [List.filter_cons_of_neg hb, h₁], h₂⟩

/-! ### The shape of a plan: several components, a tape stream and a head stream -/

/-- **The shape of a plan of the encoding**: `whole` is an interleaving of the components `ls`
(the cell counters), of the stream `T` (the tape) and of the stream `H` (the head counter). -/
def PlanInter (ls : List (List α)) (H T whole : List α) : Prop :=
  ∃ ac bs, InterleaveList ls ac ∧ Interleave ac T bs ∧ Interleave H bs whole

namespace PlanInter

/-- **A plan can be cut at a chosen action of the tape**: the action itself is the first action
of the second piece. -/
lemma cut_at {ls : List (List α)} {H T whole T₁ T₂ : List α} {b : α}
    (h : PlanInter ls H T whole) (hT : T = T₁ ++ b :: T₂) :
    ∃ (pss : List (List α × List α)) (H₁ H₂ w₁ w₂ : List α),
      ls = pss.map (fun x => x.1 ++ x.2) ∧ H = H₁ ++ H₂ ∧ whole = w₁ ++ b :: w₂ ∧
        PlanInter (pss.map Prod.fst) H₁ T₁ w₁ ∧ PlanInter (pss.map Prod.snd) H₂ T₂ w₂ := by
  obtain ⟨ac, bs, hil, hi₁, hi₂⟩ := h
  obtain ⟨a₁, a₂, b₁, b₂, hac, hbs, hj₁, hj₂⟩ := hi₁.split_right_tight hT
  obtain ⟨H₁, H₂, w₁, w₂, hH, hw, hk₁, hk₂⟩ := hi₂.split_right_tight hbs
  obtain ⟨pss, hls, hp₁, hp₂⟩ := hil.split_pair hac
  exact ⟨pss, H₁, H₂, w₁, w₂, hls, hH, hw, ⟨a₁, b₁, hp₁, hj₁, hk₁⟩, ⟨a₂, b₂, hp₂, hj₂, hk₂⟩⟩

/-- **A plan can be cut along any splitting of the tape stream.** -/
lemma cut {ls : List (List α)} {H T whole T₁ T₂ : List α}
    (h : PlanInter ls H T whole) (hT : T = T₁ ++ T₂) :
    ∃ (pss : List (List α × List α)) (H₁ H₂ w₁ w₂ : List α),
      ls = pss.map (fun x => x.1 ++ x.2) ∧ H = H₁ ++ H₂ ∧ whole = w₁ ++ w₂ ∧
        PlanInter (pss.map Prod.fst) H₁ T₁ w₁ ∧ PlanInter (pss.map Prod.snd) H₂ T₂ w₂ := by
  obtain ⟨ac, bs, hil, hi₁, hi₂⟩ := h
  obtain ⟨a₁, a₂, b₁, b₂, hac, hbs, hj₁, hj₂⟩ := hi₁.split_right hT
  obtain ⟨H₁, H₂, w₁, w₂, hH, hw, hk₁, hk₂⟩ := hi₂.split_right hbs
  obtain ⟨pss, hls, hp₁, hp₂⟩ := hil.split_pair hac
  exact ⟨pss, H₁, H₂, w₁, w₂, hls, hH, hw, ⟨a₁, b₁, hp₁, hj₁, hk₁⟩, ⟨a₂, b₂, hp₂, hj₂, hk₂⟩⟩

/-- **Two consecutive pieces of a plan assemble.** -/
lemma append {pss : List (List α × List α)} {H₁ H₂ T₁ T₂ w₁ w₂ : List α}
    (h₁ : PlanInter (pss.map Prod.fst) H₁ T₁ w₁) (h₂ : PlanInter (pss.map Prod.snd) H₂ T₂ w₂) :
    PlanInter (pss.map fun x => x.1 ++ x.2) (H₁ ++ H₂) (T₁ ++ T₂) (w₁ ++ w₂) := by
  obtain ⟨ac₁, bs₁, hil₁, hi₁, hj₁⟩ := h₁
  obtain ⟨ac₂, bs₂, hil₂, hi₂, hj₂⟩ := h₂
  exact ⟨ac₁ ++ ac₂, bs₁ ++ bs₂, InterleaveList.append_pair hil₁ hil₂,
    hi₁.append_append hi₂, hj₁.append_append hj₂⟩

/-- **Filtering commutes with the plan structure.** -/
lemma filter (p : α → Bool) {ls : List (List α)} {H T whole : List α}
    (h : PlanInter ls H T whole) :
    PlanInter (ls.map fun l => l.filter p) (H.filter p) (T.filter p) (whole.filter p) := by
  obtain ⟨ac, bs, hil, hi₁, hi₂⟩ := h
  exact ⟨ac.filter p, bs.filter p, hil.filter p, hi₁.filter p, hi₂.filter p⟩

/-- **Only one component contributes.**  If, after filtering, the tape, the head counter and all
components but the `j`-th are empty, the filtered plan is the filtered `j`-th component. -/
lemma filter_eq_getElem (p : α → Bool) {ls : List (List α)} {H T whole : List α}
    (h : PlanInter ls H T whole) (hH : H.filter p = []) (hT : T.filter p = [])
    {j : ℕ} (hj : j < ls.length)
    (hothers : ∀ i, ∀ hi : i < ls.length, i ≠ j → (ls[i]).filter p = []) :
    whole.filter p = (ls[j]).filter p := by
  obtain ⟨ac, bs, hil, hi₁, hi₂⟩ := h.filter p
  rw [hT] at hi₁
  rw [hH] at hi₂
  have hbs : bs = ac := hi₁.eq_of_nil_right
  have hw : whole.filter p = bs := hi₂.eq_of_nil_left
  rw [hw, hbs]
  have hlen : (ls.map fun l => l.filter p).length = ls.length := by simp
  have hj' : j < (ls.map fun l => l.filter p).length := by omega
  have := hil.eq_getElem_of_others_nil hj' (by
    intro i hi hij
    have hi' : i < ls.length := by simpa using hi
    simpa using hothers i hi' hij)
  simpa using this

end PlanInter

/-- The first components of a componentwise splitting are prefixes. -/
lemma forall₂_prefix_map_fst (pss : List (List α × List α)) :
    List.Forall₂ (· <+: ·) (pss.map Prod.fst) (pss.map fun x => x.1 ++ x.2) := by
  induction pss with
  | nil => exact List.Forall₂.nil
  | cons p pss ih => exact List.Forall₂.cons (List.prefix_append _ _) ih

/-! ### Prefixes of a stream of rounds -/

/-- **A prefix of a stream of rounds is a whole number of rounds**, as soon as the first and the
last element of every round are marked (by `f`, respectively `g`), each round carries exactly one
of either mark, and the prefix carries `n` of either. -/
lemma prefix_roundStream_eq (f g : α → Bool) : ∀ {R : ℕ} {cell : ℕ → List α},
    (∀ r < R, (cell r).countP f = 1) → (∀ r < R, (cell r).countP g = 1) →
    (∀ r < R, ∃ a t, cell r = a :: t ∧ f a) → (∀ r < R, ∃ t a, cell r = t ++ [a] ∧ g a) →
    ∀ {q : List α} {n : ℕ}, q <+: roundStream R cell → n ≤ R →
      q.countP f = n → q.countP g = n → q = roundStream n cell := by
  intro R
  induction R with
  | zero =>
      intro cell _ _ _ _ q n hq hn _ _
      have hn0 : n = 0 := by omega
      subst hn0
      simpa using hq
  | succ R ih =>
      intro cell hf1 hg1 hhead hlast q n hq hn hcf hcg
      obtain ⟨a, t, hcell0, hfa⟩ := hhead 0 (by omega)
      have hsplit : roundStream (R + 1) cell = cell 0 ++ roundStream R fun r => cell (1 + r) := by
        have h := roundStream_add 1 R cell
        rw [show 1 + R = R + 1 by omega] at h
        simpa using h
      rw [hsplit] at hq
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · -- nothing has been marked, so the prefix is empty
        cases q with
        | nil => simp
        | cons b q' =>
            exfalso
            have hb : b = a := by
              have : (b :: q') <+: (a :: (t ++ roundStream R fun r => cell (1 + r))) := by
                simpa [hcell0] using hq
              exact (List.cons_prefix_cons.1 this).1
            subst hb
            rw [List.countP_cons_of_pos hfa] at hcf
            omega
      · -- the first round is contained in the prefix
        have hcell0pre : cell 0 <+: cell 0 ++ roundStream R fun r => cell (1 + r) :=
          List.prefix_append _ _
        have hcomp : cell 0 <+: q := by
          rcases List.prefix_or_prefix_of_prefix hq hcell0pre with hle | hle
          · -- `q` is a prefix of the first round: then it is the whole round
            obtain ⟨t', b, hcellL, hgb⟩ := hlast 0 (by omega)
            have hone : (cell 0).countP g = 1 := hg1 0 (by omega)
            have ht' : t'.countP g = 0 := by
              rw [hcellL, List.countP_append] at hone
              have hb1 : ([b] : List α).countP g = 1 := by
                simp [List.countP_cons_of_pos hgb]
              rw [hb1] at hone
              omega
            rw [hcellL] at hle
            rcases List.prefix_concat_iff.1 hle with heq | hpre
            · rw [← hcellL] at heq; exact heq ▸ List.prefix_refl _
            · exfalso
              have := hpre.sublist.countP_le (p := g)
              omega
          · exact hle
        obtain ⟨q', rfl⟩ := hcomp
        have hq' : q' <+: roundStream R fun r => cell (1 + r) := by
          exact (List.prefix_append_right_inj (cell 0)).1 hq
        have hcf0 : (cell 0).countP f = 1 := hf1 0 (by omega)
        have hcg0 : (cell 0).countP g = 1 := hg1 0 (by omega)
        rw [List.countP_append, hcf0] at hcf
        rw [List.countP_append, hcg0] at hcg
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hres := ih (cell := fun r => cell (1 + r)) (q := q') (n := m)
          (fun r hr => hf1 (1 + r) (by omega)) (fun r hr => hg1 (1 + r) (by omega))
          (fun r hr => hhead (1 + r) (by omega)) (fun r hr => hlast (1 + r) (by omega))
          hq' (by omega) (by omega) (by omega)
        rw [hres]
        have h := roundStream_add 1 m cell
        rw [show 1 + m = m + 1 by omega] at h
        simpa using h.symm

end HTN
