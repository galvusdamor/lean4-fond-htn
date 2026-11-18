import HtnPlanning.Interleave.Sched
/-!
# Schedules of mapped and filtered components

**`HTN.ACHD.sched_filterMap`** — the schedules of the components mapped by `filterMap g` are the
images of the schedules of the components.
-/

namespace HTN

namespace ACHD

variable {α β : Type}

theorem sched_cons_nil {L : List (List α)} {w : List α} (h : Sched L w) : Sched ([] :: L) w := by
  induction h with
  | nil h => exact Sched.nil (by simpa using h)
  | @step pre post a t z _ ih => exact Sched.step (pre := [] :: pre) ih

theorem sched_prefix_comp {pre post : List (List α)} {t w : List α}
    (h : Sched (pre ++ t :: post) w) : ∀ u : List α, Sched (pre ++ (u ++ t) :: post) (u ++ w)
  | [] => h
  | a :: u => Sched.step (sched_prefix_comp h u)

theorem sched_flatten : ∀ (L : List (List α)), Sched L L.flatten
  | [] => Sched.nil (by simp)
  | l :: L => by
    have := sched_prefix_comp (pre := []) (t := []) (sched_cons_nil (sched_flatten L)) l
    simpa using this

theorem map_eq_cons_split {f : List α → List β} :
    ∀ {L : List (List α)} {pre' post' : List (List β)} {m : List β},
      L.map f = pre' ++ m :: post' →
      ∃ preL l postL, L = preL ++ l :: postL ∧ preL.map f = pre' ∧ f l = m ∧ postL.map f = post'
  | [], pre', post', m, h => by cases pre' <;> simp at h
  | l :: L, [], post', m, h => by
    simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
    exact ⟨[], l, L, rfl, rfl, h.1, h.2⟩
  | l :: L, p :: pre', post', m, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨preL, l', postL, rfl, h1, h2, h3⟩ := map_eq_cons_split h.2
    exact ⟨l :: preL, l', postL, rfl, by simp [h.1, h1], h2, h3⟩

theorem filterMap_eq_cons_split (g : α → Option β) :
    ∀ {l : List α} {b : β} {t' : List β}, l.filterMap g = b :: t' →
      ∃ u a t, l = u ++ a :: t ∧ u.filterMap g = [] ∧ g a = some b ∧ t.filterMap g = t'
  | [], b, t', h => by simp at h
  | a :: l, b, t', h => by
    rcases ha : g a with _ | b'
    · rw [List.filterMap_cons_none ha] at h
      obtain ⟨u, a', t, rfl, h1, h2, h3⟩ := filterMap_eq_cons_split g h
      exact ⟨a :: u, a', t, rfl, by simp [ha, h1], h2, h3⟩
    · rw [List.filterMap_cons_some ha, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], a, l, rfl, rfl, ha, rfl⟩

/-- **Schedules of the components mapped by `filterMap`.** -/
theorem sched_filterMap (g : α → Option β) :
    ∀ (n : ℕ) (L : List (List α)) (w' : List β), (L.map List.length).sum ≤ n →
      (Sched (L.map (·.filterMap g)) w' ↔ ∃ w, Sched L w ∧ w.filterMap g = w') := by
  intro n
  induction n with
  | zero =>
    intro L w' hn
    have hL : ∀ l ∈ L, l = [] := fun l hl => List.length_eq_zero_iff.1 (by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hl); omega)
    constructor
    · intro h
      refine ⟨[], Sched.nil hL, ?_⟩
      cases w' with
      | nil => rfl
      | cons b z =>
        obtain ⟨pre, post, t, he, -⟩ := h.exists_of_cons
        obtain ⟨preL, l, postL, rfl, -, hl, -⟩ := map_eq_cons_split he
        rw [hL l (by simp)] at hl; simp at hl
    · rintro ⟨w, h, rfl⟩
      cases w with
      | nil => exact Sched.nil (by intro l hl; obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
                                   rw [hL l' hl']; rfl)
      | cons a z =>
        obtain ⟨pre, post, t, rfl, -⟩ := h.exists_of_cons
        exact absurd (hL (a :: t) (by simp)) (by simp)
  | succ n ih =>
    intro L w' hn
    constructor
    · intro h
      cases w' with
      | nil =>
        refine ⟨L.flatten, sched_flatten L, ?_⟩
        have hall := h.forall_nil
        rw [List.filterMap_flatten]
        simp only [List.flatten_eq_nil_iff, List.mem_map]
        rintro _ ⟨l, hl, rfl⟩
        exact hall _ (List.mem_map_of_mem hl)
      | cons b z =>
        obtain ⟨pre', post', t', he, hs⟩ := h.exists_of_cons
        obtain ⟨preL, l, postL, rfl, h1, h2, h3⟩ := map_eq_cons_split he
        obtain ⟨u, a, t, rfl, hu, ha, ht⟩ := filterMap_eq_cons_split g h2
        have hlen : ((preL ++ t :: postL).map List.length).sum ≤ n := by
          simp at hn ⊢; omega
        have hs' : Sched ((preL ++ t :: postL).map (·.filterMap g)) z := by
          simpa [h1, h3, ht] using hs
        obtain ⟨w₁, hw₁, e⟩ := (ih _ z hlen).1 hs'
        refine ⟨u ++ a :: w₁, sched_prefix_comp (Sched.step hw₁) u, ?_⟩
        simp [List.filterMap_append, hu, ha, e]
    · rintro ⟨w, h, rfl⟩
      induction h with
      | nil h => exact Sched.nil (by intro l hl; obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
                                     rw [h l' hl']; rfl)
      | @step pre post a t z hz ihz =>
        rcases hga : g a with _ | b
        · rw [List.filterMap_cons_none hga]
          have := ihz (by simp at hn ⊢; omega)
          simpa [List.map_append, List.filterMap_cons_none hga] using this
        · rw [List.filterMap_cons_some hga]
          have := ihz (by simp at hn ⊢; omega)
          simp only [List.map_append, List.map_cons, List.filterMap_cons_some hga] at this ⊢
          exact Sched.step this

end ACHD

end HTN
