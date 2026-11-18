import HtnComplexity.AcVerify.Paths
/-!
# Divergence of paths: basic facts

Elementary list lemmas about the divergence `HTN.Syn.AcVer.DivAt` of two paths: it is unique,
symmetric, survives extending both paths, and exists exactly when neither path is a prefix of the
other.
-/

namespace HTN

namespace Syn

namespace AcVer

variable {α : Type*}

/-- Generic divergence on lists (the definition of `DivAt` is about `PStep`, but nothing in it
depends on that). -/
theorem divAt_symm {u v : List PStep} {x y : PStep} (h : DivAt u v x y) : DivAt v u y x := by
  obtain ⟨P, su, sv, hu, hv, hxy⟩ := h
  exact ⟨P, sv, su, hv, hu, Ne.symm hxy⟩

theorem divAt_append {u v : List PStep} {x y : PStep} (h : DivAt u v x y) (a b : List PStep) :
    DivAt (u ++ a) (v ++ b) x y := by
  obtain ⟨P, su, sv, rfl, rfl, hxy⟩ := h
  exact ⟨P, su ++ a, sv ++ b, by simp, by simp, hxy⟩

theorem divAt_append_left {u v : List PStep} {x y : PStep} (h : DivAt u v x y) (a : List PStep) :
    DivAt (u ++ a) v x y := by
  simpa using divAt_append h a []

theorem divAt_append_right {u v : List PStep} {x y : PStep} (h : DivAt u v x y) (b : List PStep) :
    DivAt u (v ++ b) x y := by
  simpa using divAt_append h [] b

theorem divAt_snoc (p : List PStep) {a b : PStep} (h : a ≠ b) (s s' : List PStep) :
    DivAt (p ++ a :: s) (p ++ b :: s') a b := ⟨p, s, s', rfl, rfl, h⟩

/-- Two decompositions `P ++ x :: su = P' ++ x' :: su'`, `P ++ y :: sv = P' ++ y' :: sv'` with
`x ≠ y` have `P = P'`. -/
theorem divAt_unique_aux {P P' su su' sv sv' : List PStep} {x y x' y' : PStep}
    (hu : P ++ x :: su = P' ++ x' :: su') (hv : P ++ y :: sv = P' ++ y' :: sv') (hxy : x ≠ y)
    (hxy' : x' ≠ y') : P = P' := by
  induction P generalizing P' with
  | nil =>
    cases P' with
    | nil => rfl
    | cons z P' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hu hv
      exact absurd (hu.1.trans hv.1.symm) hxy
  | cons z P ih =>
    cases P' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hu hv
      exact absurd (hu.1.symm.trans hv.1) hxy'
    | cons z' P' =>
      simp only [List.cons_append, List.cons.injEq] at hu hv
      rw [hu.1, ih hu.2 hv.2]

/-- **The divergence is unique.** -/
theorem divAt_unique {u v : List PStep} {x y x' y' : PStep} (h : DivAt u v x y)
    (h' : DivAt u v x' y') : x = x' ∧ y = y' := by
  obtain ⟨P, su, sv, hu, hv, hxy⟩ := h
  obtain ⟨P', su', sv', hu', hv', hxy'⟩ := h'
  have hP := divAt_unique_aux (hu.symm.trans hu') (hv.symm.trans hv') hxy hxy'
  subst hP
  rw [hu] at hu'
  rw [hv] at hv'
  simp only [List.append_cancel_left_eq, List.cons.injEq] at hu' hv'
  exact ⟨hu'.1, hv'.1⟩

/-- Diverging paths are not prefixes of one another. -/
theorem not_prefix_of_divAt {u v : List PStep} {x y : PStep} (h : DivAt u v x y) :
    ¬ u <+: v := by
  obtain ⟨P, su, sv, rfl, rfl, hxy⟩ := h
  rintro ⟨r, hr⟩
  simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq,
    List.cons.injEq] at hr
  exact hxy hr.1

/-- Paths neither of which is a prefix of the other diverge. -/
theorem exists_divAt : ∀ {u v : List PStep}, ¬ u <+: v → ¬ v <+: u → ∃ x y, DivAt u v x y
  | [], _, h, _ => absurd List.nil_prefix h
  | _, [], _, h => absurd List.nil_prefix h
  | a :: u, b :: v, h, h' => by
    by_cases hab : a = b
    · subst hab
      have h1 : ¬ u <+: v := fun hp => h (List.cons_prefix_cons.2 ⟨rfl, hp⟩)
      have h2 : ¬ v <+: u := fun hp => h' (List.cons_prefix_cons.2 ⟨rfl, hp⟩)
      obtain ⟨x, y, P, su, sv, hu, hv, hxy⟩ := exists_divAt h1 h2
      exact ⟨x, y, a :: P, su, sv, by simp [hu], by simp [hv], hxy⟩
    · exact ⟨a, b, [], u, v, rfl, rfl, hab⟩

/-- Extending a path at its end does not change its divergence from a path it diverges from. -/
theorem divOrd_append_iff {d : DomDesc} {q : InstDesc} {u v : List PStep} {x y : PStep}
    (h : DivAt u v x y) (a b : List PStep) :
    DivOrd d q (u ++ a) (v ++ b) ↔ DivOrd d q u v := by
  constructor
  · rintro ⟨x', y', h', h1, h2⟩
    obtain ⟨rfl, rfl⟩ := divAt_unique (divAt_append h a b) h'
    exact ⟨x, y, h, h1, h2⟩
  · rintro ⟨x', y', h', h1, h2⟩
    exact ⟨x', y', divAt_append h' a b, h1, h2⟩

end AcVer

end Syn

end HTN
