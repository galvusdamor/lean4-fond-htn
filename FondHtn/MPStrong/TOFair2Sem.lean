import FondHtn.MPStrong.TOFair
/-!
# Fair sequential composition with ranks (path splitting)

Ranked refinements of `FOND.Problem.FairWinT.compL` used by the summary game for fair strong
cyclic planning on totally ordered problems (`doc/notes_to_fair_3.md`):

* `FOND.Problem.projSet X v` — the projection of a set `X` of nodes of `u ; v` to `u`;
* **`FOND.Problem.FAttrT.proj`** — the attractor of `u ; v` (any target) projects to the attractor
  of `u` with the target "states from which `(v, ·)` lies in `X`";
* **`FOND.Problem.FAttrT.split`** — **path splitting**: the attractor of `u ; v` with rank `n`
  yields an exit `e'` of `u` reached with rank `≤ n` (target `{e'}`, for the projected set) and a
  continuation `(v, e') ∈ X` with rank `≤ n`.
-/

namespace FOND

open HTN HTN.TaskNetwork

namespace Problem

variable {F A C I : Type} {P : Problem F A C I} [DecidableEq I]

lemma FAttrT.mono {G : Set (Set F)} {X : NSet F A C I} {n : ℕ} {tn : TaskNetwork I A C}
    {s : Set F} (h : P.FAttrT G X n tn s) : ∀ {n'}, n ≤ n' → P.FAttrT G X n' tn s := by
  induction h with
  | goal h hs => exact fun _ => .goal h hs
  | prim hu hα happ hall hs₀ _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .prim hu hα happ hall hs₀ (ih (by omega))
  | decomp hu hd hX _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .decomp hu hd hX (ih (by omega))

lemma FAttrT.monoG {G G' : Set (Set F)} (hG : ∀ s, s ∈ G → s ∈ G') {X : NSet F A C I} {n : ℕ}
    {tn : TaskNetwork I A C} {s : Set F} (h : P.FAttrT G X n tn s) : P.FAttrT G' X n tn s := by
  induction h with
  | goal h hs => exact .goal h (hG _ hs)
  | prim hu hα happ hall hs₀ _ ih => exact .prim hu hα happ hall hs₀ ih
  | decomp hu hd hX _ ih => exact .decomp hu hd hX ih

lemma FAttrT.of_empty {G : Set (Set F)} {X : NSet F A C I} {n : ℕ} {tn : TaskNetwork I A C}
    {s : Set F} (he : tn.T = ∅) (h : P.FAttrT G X n tn s) : s ∈ G := by
  cases h with
  | goal _ hs => exact hs
  | prim hu => exact absurd hu.1 (by simp [he])
  | decomp hu => exact absurd hu.1 (by simp [he])

/-- The projection of `X` (nodes of `u ; v`) to the first component. -/
def projSet (X : NSet F A C I) (v : TaskNetwork I A C) : NSet F A C I :=
  fun tn s => tn.WF ∧ ∃ (u' : TaskNetwork I A C) (σ : I → I), u'.WF ∧ Disjoint u'.T v.T ∧
    X (seqNet u' v) s ∧ IsoVia σ u' tn

theorem projSet_good {X : NSet F A C I} {v : TaskNetwork I A C} : NGood (projSet X v) := by
  refine ⟨fun _ _ h => h.1, fun tn tn' s σ h hw' hσ => ?_⟩
  obtain ⟨-, u', τ, hw, hdj, hXs, hτ⟩ := h
  exact ⟨hw', u', σ ∘ τ, hw, hdj, hXs, hτ.comp hσ⟩

theorem projSet_mem {X : NSet F A C I} {v u : TaskNetwork I A C} {s : Set F} (hu : u.WF)
    (hd : Disjoint u.T v.T) (h : X (seqNet u v) s) : projSet X v u s :=
  ⟨hu, u, id, hu, hd, h, IsoVia.refl _⟩

/-- **Projection and path splitting.**  If `u ; v` is in `X` and in the attractor of `X` (target
`T`) with rank `n`, then `u` is in the attractor of the projected set with rank `n` for the target
`{x | (v, x) ∈ X}`, and moreover some exit `e'` of `u` is reached with rank `≤ n` while the
continuation `(v, e')` is in `X` and in the attractor with rank `≤ n`. -/
theorem FAttrT.split [Infinite I] {T : Set (Set F)} {X : NSet F A C I} (hX : NGood X)
    {v : TaskNetwork I A C} (hv : v.WF) (n : ℕ) :
    ∀ {u : TaskNetwork I A C} {s : Set F}, u.WF → Disjoint u.T v.T → X (seqNet u v) s →
      P.FAttrT T X n (seqNet u v) s →
        P.FAttrT {x | X v x} (projSet X v) n u s ∧
        ∃ e', P.FAttrT {e'} (projSet X v) n u s ∧ X v e' ∧ P.FAttrT T X n v e' := by
  induction n with
  | zero =>
    intro u s hw hdj hXs h
    by_cases he : u.T = ∅
    · have hXv : X v s := hX.2 _ _ _ _ hXs hv (isoVia_of_agree' (seqNet_empty hw he))
      exact ⟨.goal he hXv, s, .goal he rfl, hXv,
        h.isoVia hX (seqNet_wf hw hv hdj) hv (isoVia_of_agree' (seqNet_empty hw he))⟩
    · cases h with
      | goal h' => exact absurd (Finset.union_eq_empty.1 h').1 he
  | succ k ih =>
    intro u s hw hdj hXs h
    by_cases he : u.T = ∅
    · have hXv : X v s := hX.2 _ _ _ _ hXs hv (isoVia_of_agree' (seqNet_empty hw he))
      exact ⟨.goal he hXv, s, .goal he rfl, hXv,
        h.isoVia hX (seqNet_wf hw hv hdj) hv (isoVia_of_agree' (seqNet_empty hw he))⟩
    have hws := seqNet_wf hw hv hdj
    cases h with
    | goal h' => exact absurd (Finset.union_eq_empty.1 h').1 he
    | @prim _ _ _ t a hu' hα happ hall s₀ hs₀ h₀ =>
      obtain ⟨htu, hut⟩ := unconstrained_seqNet hw hdj he hu'
      have hd' : Disjoint (u.progress t).T v.T :=
        Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdj
      have hwp := progress_wf hw hut
      have hag := progress_seqNet htu hdj hv
      have hX' : ∀ s', X ((seqNet u v).progress t) s' → X (seqNet (u.progress t) v) s' :=
        fun s' h => hX.2 _ _ _ _ h (seqNet_wf hwp hv hd') (isoVia_of_agree' hag)
      have hall' : ∀ s' ∈ (P.δ a).outcomes s, projSet X v (u.progress t) s' :=
        fun s' hs' => projSet_mem hwp hd' (hX' s' (hall s' hs'))
      obtain ⟨h1, e', h2, h3, h4⟩ := ih hwp hd' (hX' s₀ (hall s₀ hs₀))
        (h₀.isoVia hX (progress_wf hws hu') (seqNet_wf hwp hv hd') (isoVia_of_agree' hag))
      have hαu := (seqNet_α htu).symm.trans hα
      exact ⟨.prim hut hαu happ hall' hs₀ h1, e', .prim hut hαu happ hall' hs₀ h2, h3,
        h4.mono (by omega)⟩
    | @decomp _ _ N' _ t m hu' hdN hXN h' =>
      obtain ⟨htu, hut⟩ := unconstrained_seqNet hw hdj he hu'
      obtain ⟨hmM, -, hαt, w, hww, hwiso, hwdisj, rfl⟩ := hdN
      have hwu : Disjoint u.T w.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_left hwdisj
      have hdu : DecompStep P.methods u t m (decomposeWith u t w) :=
        ⟨hmM, htu, (seqNet_α htu).symm.trans hαt, w, hww, hwiso, hwu, rfl⟩
      have hd' : Disjoint (decomposeWith u t w).T v.T := by
        rw [Finset.disjoint_left]
        intro y hy hyv
        rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · exact disj_mem hdj hy hyv
        · exact Finset.disjoint_left.1 hwdisj (Finset.mem_union_right _ hyv) hy
      have hwu' := hdu.wf hw
      have hag := decomposeWith_seqNet htu hdj hv hww hwdisj
      have hwN : (decomposeWith (seqNet u v) t w).WF := decomposeWith_wf hws hww hwdisj
      have hXd := hX.2 _ _ _ _ hXN (seqNet_wf hwu' hv hd') (isoVia_of_agree' hag)
      obtain ⟨h1, e', h2, h3, h4⟩ := ih hwu' hd' hXd
        (h'.isoVia hX hwN (seqNet_wf hwu' hv hd') (isoVia_of_agree' hag))
      have hP := projSet_mem hwu' hd' hXd
      exact ⟨.decomp hut hdu hP h1, e', .decomp hut hdu hP h2, h3, h4.mono (by omega)⟩

/-- The projected set is self-supporting for the target `{x | (v, x) ∈ X}`. -/
theorem projSet_attr [Infinite I] {T : Set (Set F)} {X : NSet F A C I} (hX : NGood X)
    (hXa : ∀ tn s, X tn s → ∃ n, P.FAttrT T X n tn s) {v : TaskNetwork I A C} (hv : v.WF) :
    ∀ tn s, projSet X v tn s → ∃ n, P.FAttrT {x | X v x} (projSet X v) n tn s := by
  intro tn s h
  obtain ⟨hw, u', σ, hw', hdj, hXs, hσ⟩ := h
  obtain ⟨n, hn⟩ := hXa _ _ hXs
  exact ⟨n, (FAttrT.split hX hv n hw' hdj hXs hn).1.isoVia projSet_good hw' hw hσ⟩

end Problem

end FOND
