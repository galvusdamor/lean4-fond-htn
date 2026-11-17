import FondHtn.MPStrong.Game
/-!
# Sequential composition of the progression game (the "rank argument" for total order)

The progression game with a **target**: `FOND.Problem.MPProgTH G n tn s` — the empty network wins
only in a state of `G`.  For `G = univ` this is the progression game `MPProgH`
(`FOND.Problem.mpProgTH_univ_iff`).

* `FOND.Problem.seqNet u v` — the sequential composition of two networks with disjoint ids:
  every task of `u` before every task of `v`.
* **`FOND.Problem.MPProgTH.compL`** — a winning strategy for `u ; v` (height `n`) plays `u` to
  completion first: `u` is won (height `≤ n`) with the target "states from which `v` is won with
  height `≤ n`".
* **`FOND.Problem.MPProgTH.compR`** — conversely, strategies for `u` (target `S'`) and for `v`
  from every state of `S'` compose (heights add).
* **`FOND.Problem.MPProgTH.first_prim`**, **`first_comp`** — for a network whose task `x`
  precedes all other tasks (the head of a totally ordered network): if `x` is primitive the game
  continues on the outcomes; if `x` is compound with name `c`, the game is won iff some method
  of `c` is won with some target `S''` from which the rest is won.
-/

namespace FOND

open HTN HTN.TaskNetwork

namespace Problem

variable {F A C I : Type} (P : Problem F A C I) [DecidableEq I]

/-- **The progression game with target `G`**, graded by the height. -/
inductive MPProgTH (G : Set (Set F)) : ℕ → TaskNetwork I A C → Set F → Prop
  | empty {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) (hs : s ∈ G) :
      MPProgTH G n tn s
  | prim {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, MPProgTH G n (tn.progress t) s') :
      MPProgTH G (n + 1) tn s
  | decomp {n : ℕ} {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}
      (hu : tn.Unconstrained t) (hd : DecompStep P.methods tn t m tn') (h : MPProgTH G n tn' s) :
      MPProgTH G (n + 1) tn s

variable {P}

lemma MPProgTH.mono {G : Set (Set F)} {n : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPProgTH G n tn s) : ∀ {n'}, n ≤ n' → P.MPProgTH G n' tn s := by
  induction h with
  | empty h hs => exact fun _ => .empty h hs
  | prim hu hα happ _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .prim hu hα happ fun s' hs' => ih s' hs' (by omega)
  | decomp hu hd _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .decomp hu hd (ih (by omega))

lemma MPProgTH.monoG {G G' : Set (Set F)} (hG : ∀ s, s ∈ G → s ∈ G') {n : ℕ}
    {tn : TaskNetwork I A C} {s : Set F} (h : P.MPProgTH G n tn s) : P.MPProgTH G' n tn s := by
  induction h with
  | empty h hs => exact .empty h (hG _ hs)
  | prim hu hα happ _ ih => exact .prim hu hα happ ih
  | decomp hu hd _ ih => exact .decomp hu hd ih

theorem MPProgTH.isoVia [Infinite I] {G : Set (Set F)} {n : ℕ} {tn : TaskNetwork I A C}
    {s : Set F} (h : P.MPProgTH G n tn s) :
    ∀ {tn' : TaskNetwork I A C} {σ : I → I}, tn.WF → tn'.WF → IsoVia σ tn tn' →
      P.MPProgTH G n tn' s := by
  induction h with
  | empty he hs => exact fun _ _ hσ => .empty (hσ.empty he) hs
  | prim hu hα happ _ ih =>
    intro tn' σ hw hw' hσ
    exact .prim (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ fun s' hs' =>
      ih s' hs' (progress_wf hw hu) (progress_wf hw' (hσ.unconstrained hu)) (hσ.progress hu.1)
  | decomp hu hd _ ih =>
    intro tn' σ hw hw' hσ
    obtain ⟨u', hd', ρ, hρ⟩ := hd.isoVia hw hw' hσ
    exact .decomp (hσ.unconstrained hu) hd' (ih (hd.wf hw) (hd'.wf hw') hρ)

omit [DecidableEq I] in
theorem wf_of_agree {tn u : TaskNetwork I A C} (h : tn.WF) (hag : tn.Agree u) : u.WF := by
  obtain ⟨hT, ho, -⟩ := hag
  exact ⟨fun hab => hT ▸ h.mem_left (ho ▸ hab), fun hab => hT ▸ h.mem_right (ho ▸ hab),
    fun a hab => h.irrefl a (ho ▸ hab), fun h₁ h₂ => ho ▸ h.trans (ho ▸ h₁) (ho ▸ h₂)⟩

theorem MPProgTH.of_agree [Infinite I] {G : Set (Set F)} {n : ℕ} {tn tn' : TaskNetwork I A C}
    {s : Set F} (h : P.MPProgTH G n tn s) (hw : tn.WF) (hag : tn.Agree tn') :
    P.MPProgTH G n tn' s :=
  h.isoVia hw (wf_of_agree hw hag) (HTN.Article.isoVia_id_of_agree hag)

/-- The target `univ` is the plain progression game. -/
theorem mpProgTH_univ_iff {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} :
    P.MPProgTH Set.univ n tn s ↔ P.MPProgH n tn s := by
  constructor
  · intro h
    induction h with
    | empty h _ => exact .empty h
    | prim hu hα happ _ ih => exact .prim hu hα happ ih
    | decomp hu hd _ ih => exact .decomp hu hd ih
  · intro h
    induction h with
    | empty h => exact .empty h trivial
    | prim hu hα happ _ ih => exact .prim hu hα happ ih
    | decomp hu hd _ ih => exact .decomp hu hd ih

theorem MPProgTH.of_empty {G : Set (Set F)} {n : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (he : tn.T = ∅) (h : P.MPProgTH G n tn s) : s ∈ G := by
  cases h with
  | empty _ hs => exact hs
  | prim hu => exact absurd hu.1 (by simp [he])
  | decomp hu => exact absurd hu.1 (by simp [he])

/-! ## Sequential composition of networks -/

/-- The sequential composition `u ; v`: every task of `u` precedes every task of `v`. -/
def seqNet (u v : TaskNetwork I A C) : TaskNetwork I A C where
  T := u.T ∪ v.T
  ord a b := u.ord a b ∨ v.ord a b ∨ (a ∈ u.T ∧ b ∈ v.T)
  α y := if y ∈ u.T then u.α y else v.α y

section Seq

variable {u v : TaskNetwork I A C}

omit [DecidableEq I] in
theorem disj_mem {u v : TaskNetwork I A C} (hd : Disjoint u.T v.T) {y : I} (hu : y ∈ u.T)
    (hv : y ∈ v.T) : False := Finset.disjoint_left.1 hd hu hv

theorem seqNet_wf (hu : u.WF) (hv : v.WF) (hd : Disjoint u.T v.T) : (seqNet u v).WF := by
  refine ⟨fun h => ?_, fun h => ?_, fun a h => ?_, fun h₁ h₂ => ?_⟩
  · rcases h with h | h | ⟨h, -⟩
    · exact Finset.mem_union_left _ (hu.mem_left h)
    · exact Finset.mem_union_right _ (hv.mem_left h)
    · exact Finset.mem_union_left _ h
  · rcases h with h | h | ⟨-, h⟩
    · exact Finset.mem_union_left _ (hu.mem_right h)
    · exact Finset.mem_union_right _ (hv.mem_right h)
    · exact Finset.mem_union_right _ h
  · rcases h with h | h | ⟨h1, h2⟩
    · exact hu.irrefl a h
    · exact hv.irrefl a h
    · exact disj_mem hd h1 h2
  · rcases h₁ with h₁ | h₁ | ⟨h₁, h₁'⟩ <;> rcases h₂ with h₂ | h₂ | ⟨h₂, h₂'⟩
    · exact Or.inl (hu.trans h₁ h₂)
    · exact absurd (disj_mem hd (hu.mem_right h₁) (hv.mem_left h₂)) id
    · exact Or.inr (Or.inr ⟨hu.mem_left h₁, h₂'⟩)
    · exact absurd (disj_mem hd (hu.mem_left h₂) (hv.mem_right h₁)) id
    · exact Or.inr (Or.inl (hv.trans h₁ h₂))
    · exact absurd (disj_mem hd h₂ (hv.mem_right h₁)) id
    · exact absurd (disj_mem hd (hu.mem_left h₂) h₁') id
    · exact Or.inr (Or.inr ⟨h₁, hv.mem_right h₂⟩)
    · exact absurd (disj_mem hd h₂ h₁') id

theorem seqNet_empty (hu : u.WF) (he : u.T = ∅) : (seqNet u v).Agree v := by
  refine ⟨by simp [seqNet, he], ?_, fun y _ => by simp [seqNet, he]⟩
  funext a b
  simp only [seqNet, he, Finset.notMem_empty, false_and, or_false, eq_iff_iff]
  constructor
  · rintro (h | h)
    · exact absurd (hu.mem_left h) (by simp [he])
    · exact h
  · exact Or.inr

theorem seqNet_α {y : I} (hy : y ∈ u.T) : (seqNet u v).α y = u.α y := by simp [seqNet, hy]

theorem unconstrained_seqNet (_hu : u.WF) (_hd : Disjoint u.T v.T) (hne : u.T ≠ ∅) {t : I}
    (h : (seqNet u v).Unconstrained t) : t ∈ u.T ∧ u.Unconstrained t := by
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have htu : t ∈ u.T := by
    rcases Finset.mem_union.1 h.1 with h' | h'
    · exact h'
    · exact absurd (Or.inr (Or.inr ⟨ha, h'⟩)) (h.2 a (Finset.mem_union_left _ ha))
  exact ⟨htu, htu, fun y hy hyt => h.2 y (Finset.mem_union_left _ hy) (Or.inl hyt)⟩

theorem unconstrained_seqNet_of (hu : u.WF) (hv : v.WF) (hd : Disjoint u.T v.T) {t : I}
    (h : u.Unconstrained t) : (seqNet u v).Unconstrained t := by
  refine ⟨Finset.mem_union_left _ h.1, fun y _ hyt => ?_⟩
  rcases hyt with hyt | hyt | ⟨-, htv⟩
  · exact h.2 y (hu.mem_left hyt) hyt
  · exact disj_mem hd h.1 (hv.mem_right hyt)
  · exact disj_mem hd h.1 htv

theorem progress_seqNet {t : I} (ht : t ∈ u.T) (hd : Disjoint u.T v.T) (hv : v.WF) :
    ((seqNet u v).progress t).Agree (seqNet (u.progress t) v) := by
  have htv : t ∉ v.T := fun h => disj_mem hd ht h
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · ext y
    simp only [progress_T, seqNet, Finset.mem_erase, Finset.mem_union]
    constructor
    · rintro ⟨hyt, hy | hy⟩
      · exact Or.inl ⟨hyt, hy⟩
      · exact Or.inr hy
    · rintro (⟨hyt, hy⟩ | hy)
      · exact ⟨hyt, Or.inl hy⟩
      · exact ⟨fun e => htv (e ▸ hy), Or.inr hy⟩
  · funext a b
    simp only [progress_ord, seqNet, progress_T, Finset.mem_erase, eq_iff_iff]
    constructor
    · rintro ⟨h | h | ⟨ha, hb⟩, hat⟩
      · exact Or.inl ⟨h, hat⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨⟨hat, ha⟩, hb⟩)
    · rintro (⟨h, hat⟩ | h | ⟨⟨hat, ha⟩, hb⟩)
      · exact ⟨Or.inl h, hat⟩
      · exact ⟨Or.inr (Or.inl h), fun e => htv (e ▸ hv.mem_left h)⟩
      · exact ⟨Or.inr (Or.inr ⟨ha, hb⟩), hat⟩
  · simp only [progress_T, Finset.mem_erase] at hy
    simp only [progress_α, seqNet, progress_T, Finset.mem_erase, hy.1, ne_eq, not_false_eq_true,
      true_and]

theorem decomposeWith_seqNet {t : I} {w : TaskNetwork I A C} (ht : t ∈ u.T)
    (hd : Disjoint u.T v.T) (hv : v.WF) (_hw : w.WF) (hdw : Disjoint (u.T ∪ v.T) w.T) :
    (decomposeWith (seqNet u v) t w).Agree (seqNet (decomposeWith u t w) v) := by
  have htv : t ∉ v.T := fun h => disj_mem hd ht h
  have hwv : ∀ y, y ∈ w.T → y ∉ v.T := fun y hy hy' =>
    Finset.disjoint_left.1 hdw (Finset.mem_union_right _ hy') hy
  have hwu : ∀ y, y ∈ w.T → y ∉ u.T := fun y hy hy' =>
    Finset.disjoint_left.1 hdw (Finset.mem_union_left _ hy') hy
  refine ⟨?_, ?_, fun y hyT => ?_⟩
  · ext y
    simp only [decomposeWith_T, seqNet, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (⟨hyt, hy | hy⟩ | hy)
      · exact Or.inl (Or.inl ⟨hyt, hy⟩)
      · exact Or.inr hy
      · exact Or.inl (Or.inr hy)
    · rintro ((⟨hyt, hy⟩ | hy) | hy)
      · exact Or.inl ⟨hyt, Or.inl hy⟩
      · exact Or.inr hy
      · exact Or.inl ⟨fun e => htv (e ▸ hy), Or.inr hy⟩
  · funext a b
    simp only [decomposeWith_ord_iff, seqNet, decomposeWith_T, Finset.mem_union,
      Finset.mem_erase, eq_iff_iff]
    constructor
    · rintro (h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, hat, hbt⟩)
      · exact Or.inl (Or.inl h)
      · rcases h with h | h | ⟨-, h⟩
        · exact Or.inl (Or.inr (Or.inl ⟨h, hb⟩))
        · exact absurd (hv.mem_right h) htv
        · exact absurd h htv
      · rcases h with h | h | ⟨-, h⟩
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨h, ha⟩)))
        · exact absurd (hv.mem_left h) htv
        · exact Or.inr (Or.inr ⟨Or.inr ha, h⟩)
      · rcases h with h | h | ⟨ha, hb⟩
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨h, hat, hbt⟩)))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨Or.inl ⟨hat, ha⟩, hb⟩)
    · rintro ((h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, hat, hbt⟩) | h | ⟨ha | ha, hb⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inl h, hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨Or.inl h, ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inl h, hat, hbt⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl h), fun e => htv (e ▸ hv.mem_left h),
          fun e => htv (e ▸ hv.mem_right h)⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr ⟨ha.2, hb⟩), ha.1,
          fun e => htv (e ▸ hb)⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr ⟨ht, hb⟩), ha⟩))
  · simp only [decomposeWith_α, seqNet, decomposeWith_T, Finset.mem_union, Finset.mem_erase]
    by_cases hyw : y ∈ w.T
    · simp [hyw]
    · have hyt : y ≠ t := by
        rcases mem_decomposeWith_T.1 hyT with ⟨-, h⟩ | h
        · exact h
        · exact absurd h hyw
      by_cases hyu : y ∈ u.T
      · simp [hyw, hyu, hyt]
      · simp [hyw, hyu]

end Seq

/-! ## Composition lemmas -/

/-- **Sequential decomposition of a winning strategy.** -/
theorem MPProgTH.compL [Infinite I] {G : Set (Set F)} (n : ℕ) :
    ∀ {u v : TaskNetwork I A C} {s : Set F}, u.WF → v.WF → Disjoint u.T v.T →
      P.MPProgTH G n (seqNet u v) s → P.MPProgTH {s' | P.MPProgTH G n v s'} n u s := by
  induction n with
  | zero =>
    intro u v s hu hv hd h
    by_cases he : u.T = ∅
    · exact .empty he (h.of_agree (seqNet_wf hu hv hd) (seqNet_empty hu he))
    · cases h with
      | empty h' => exact absurd (Finset.union_eq_empty.1 h').1 he
  | succ k ih =>
    intro u v s hu hv hd h
    by_cases he : u.T = ∅
    · exact .empty he (h.of_agree (seqNet_wf hu hv hd) (seqNet_empty hu he))
    have hw := seqNet_wf hu hv hd
    cases h with
    | empty h' => exact absurd (Finset.union_eq_empty.1 h').1 he
    | @prim _ _ _ t a hu' hα happ hall =>
      obtain ⟨htu, hut⟩ := unconstrained_seqNet hu hd he hu'
      refine .prim hut ((seqNet_α htu).symm.trans hα) happ fun s' hs' => ?_
      have h1 := (hall s' hs').of_agree (progress_wf hw hu') (progress_seqNet htu hd hv)
      have hd' : Disjoint (u.progress t).T v.T :=
        Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd
      exact (ih (progress_wf hu hut) hv hd' h1).monoG fun s'' hs'' => hs''.mono (by omega)
    | @decomp _ _ N' _ t m hu' hdN h' =>
      obtain ⟨htu, hut⟩ := unconstrained_seqNet hu hd he hu'
      obtain ⟨hmM, -, hαt, w, hww, hwiso, hwdisj, rfl⟩ := hdN
      have hwu : Disjoint u.T w.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_left hwdisj
      have hdu : DecompStep P.methods u t m (decomposeWith u t w) :=
        ⟨hmM, htu, (seqNet_α htu).symm.trans hαt, w, hww, hwiso, hwu, rfl⟩
      have h1 := h'.of_agree (decomposeWith_wf hw hww hwdisj)
        (decomposeWith_seqNet htu hd hv hww hwdisj)
      have hd' : Disjoint (decomposeWith u t w).T v.T := by
        rw [Finset.disjoint_left]
        intro y hy hyv
        rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · exact disj_mem hd hy hyv
        · exact Finset.disjoint_left.1 hwdisj (Finset.mem_union_right _ hyv) hy
      exact .decomp hut hdu ((ih (hdu.wf hu) hv hd' h1).monoG fun s'' hs'' =>
        hs''.mono (by omega))

/-- **Sequential composition of winning strategies.** -/
theorem MPProgTH.compR [Infinite I] {G S' : Set (Set F)} {j : ℕ} {v : TaskNetwork I A C}
    (hv : v.WF) (hvS : ∀ s' ∈ S', P.MPProgTH G j v s') (n : ℕ) :
    ∀ {u : TaskNetwork I A C} {s : Set F}, u.WF → Disjoint u.T v.T →
      P.MPProgTH S' n u s → P.MPProgTH G (n + j) (seqNet u v) s := by
  induction n with
  | zero =>
    intro u s hu hd h
    cases h with
    | empty he hs =>
      exact ((hvS s hs).of_agree hv (seqNet_empty hu he).symm).mono (by omega)
  | succ k ih =>
    intro u s hu hd h
    have hw := seqNet_wf hu hv hd
    cases h with
    | empty he hs =>
      exact ((hvS s hs).of_agree hv (seqNet_empty hu he).symm).mono (by omega)
    | @prim _ _ _ t a hu' hα happ hall =>
      rw [show k + 1 + j = (k + j) + 1 by omega]
      refine .prim (unconstrained_seqNet_of hu hv hd hu') ((seqNet_α hu'.1).trans hα) happ
        fun s' hs' => ?_
      have hd' : Disjoint (u.progress t).T v.T :=
        Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd
      have h1 := ih (progress_wf hu hu') hd' (hall s' hs')
      exact h1.of_agree (seqNet_wf (progress_wf hu hu') hv hd')
        (progress_seqNet hu'.1 hd hv).symm
    | @decomp _ _ u' _ t m hu' hdu h' =>
      rw [show k + 1 + j = (k + j) + 1 by omega]
      obtain ⟨hmM, htu, hαt, w, hww, hwiso, hwdisj, rfl⟩ := hdu
      obtain ⟨w₂, hww₂, hw₂iso, hw₂disj⟩ := exists_fresh_iso_copy w hww (u.T ∪ v.T)
      have hw₂u : Disjoint u.T w₂.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_left hw₂disj
      obtain ⟨ρ, hρbij, hρord, hρα⟩ := hw₂iso.symm
      have hiso : (decomposeWith u t w).Iso (decomposeWith u (id t) w₂) :=
        decomposeWith_iso_congr hu hu hww hww₂ hwdisj hw₂u htu (Set.bijOn_id _)
          (by simp) (by simp) hρbij hρord hρα
      obtain ⟨τ, hτ⟩ := hiso
      have hwu₂ : (decomposeWith u t w₂).WF := decomposeWith_wf hu hww₂ hw₂u
      have h₂ : P.MPProgTH S' k (decomposeWith u t w₂) s :=
        h'.isoVia (decomposeWith_wf hu hww hwdisj) hwu₂ hτ
      have hd' : Disjoint (decomposeWith u t w₂).T v.T := by
        rw [Finset.disjoint_left]
        intro y hy hyv
        rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · exact disj_mem hd hy hyv
        · exact Finset.disjoint_left.1 hw₂disj (Finset.mem_union_right _ hyv) hy
      have h1 := ih hwu₂ hd' h₂
      have hseq : Disjoint (seqNet u v).T w₂.T := hw₂disj
      have hdS : DecompStep P.methods (seqNet u v) t m (decomposeWith (seqNet u v) t w₂) :=
        ⟨hmM, Finset.mem_union_left _ htu, (seqNet_α htu).trans hαt, w₂, hww₂,
          hw₂iso.trans hwiso, hseq, rfl⟩
      exact .decomp (unconstrained_seqNet_of hu hv hd hu') hdS
        (h1.of_agree (seqNet_wf hwu₂ hv hd') (decomposeWith_seqNet htu hd hv hww₂ hw₂disj).symm)

/-! ## The first task of a network -/

section First

variable {N : TaskNetwork I A C} {x : I}

/-- `x` precedes every other task of `N`. -/
def IsFirst (N : TaskNetwork I A C) (x : I) : Prop := x ∈ N.T ∧ ∀ b ∈ N.T, b ≠ x → N.ord x b

theorem IsFirst.unconstrained (hN : N.WF) (h : IsFirst N x) : N.Unconstrained x :=
  ⟨h.1, fun b hb hbx => by
    by_cases e : b = x
    · subst e; exact hN.irrefl b hbx
    · exact hN.irrefl x (hN.trans (h.2 b hb e) hbx)⟩

theorem IsFirst.eq (h : IsFirst N x) {t : I} (ht : N.Unconstrained t) : t = x := by
  by_contra e
  exact ht.2 x h.1 (h.2 t ht.1 e)

theorem decomposeWith_first (hN : N.WF) (h : IsFirst N x) {u : TaskNetwork I A C}
    (hd : Disjoint N.T u.T) : (decomposeWith N x u).Agree (seqNet u (N.progress x)) := by
  have hux : ∀ y, y ∈ u.T → y ∉ N.T := fun y hy hy' => Finset.disjoint_left.1 hd hy' hy
  have hunc := h.unconstrained hN
  refine ⟨?_, ?_, fun y _ => ?_⟩
  · ext y; simp only [decomposeWith_T, seqNet, progress_T, Finset.mem_union]; tauto
  · funext a b
    simp only [decomposeWith_ord_iff, seqNet, progress_ord, progress_T, Finset.mem_erase,
      eq_iff_iff]
    constructor
    · rintro (h' | ⟨h', -⟩ | ⟨h', ha⟩ | ⟨h', hax, -⟩)
      · exact Or.inl h'
      · exact absurd h' (hunc.2 a (hN.mem_left h'))
      · exact Or.inr (Or.inr ⟨ha, fun e => hN.irrefl x (e ▸ h'), hN.mem_right h'⟩)
      · exact Or.inr (Or.inl ⟨h', hax⟩)
    · rintro (h' | ⟨h', hax⟩ | ⟨ha, hbx, hb⟩)
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inr ⟨h', hax, fun e => hunc.2 a (hN.mem_left h') (e ▸ h')⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h.2 b hb hbx, ha⟩))
  · simp only [decomposeWith_α, seqNet, progress_α]

/-- **The first task is primitive.** -/
theorem MPProgTH.first_prim {G : Set (Set F)} {n : ℕ} {s : Set F} {a : A} (_hN : N.WF)
    (h : IsFirst N x) (hα : N.α x = Sum.inl a) (hw : P.MPProgTH G n N s) :
    ∃ k, n = k + 1 ∧ (P.δ a).Applicable s ∧
      ∀ s' ∈ (P.δ a).outcomes s, P.MPProgTH G k (N.progress x) s' := by
  cases hw with
  | empty he => exact absurd h.1 (by simp [he])
  | @prim k _ _ t a' hu hα' happ hall =>
    obtain rfl := h.eq hu
    obtain rfl : a' = a := Sum.inl_injective (hα'.symm.trans hα)
    exact ⟨k, rfl, happ, hall⟩
  | decomp hu hd =>
    obtain rfl := h.eq hu
    rw [hd.2.2.1] at hα
    cases hα

/-- **The first task is compound** (decomposition of a strategy). -/
theorem MPProgTH.first_comp [Infinite I] (hM : ∀ m ∈ P.methods, m.subtasks.WF)
    {G : Set (Set F)} {n : ℕ} {s : Set F} {c : C} (hN : N.WF) (h : IsFirst N x)
    (hα : N.α x = Sum.inr c) (hw : P.MPProgTH G n N s) :
    ∃ k, n = k + 1 ∧ ∃ m ∈ P.methods, m.abstractTask = c ∧
      P.MPProgTH {s' | P.MPProgTH G k (N.progress x) s'} k m.subtasks s := by
  cases hw with
  | empty he => exact absurd h.1 (by simp [he])
  | prim hu hα' =>
    obtain rfl := h.eq hu
    rw [hα] at hα'
    cases hα'
  | @decomp k _ N' _ t m hu hd h' =>
    obtain rfl : x = t := (h.eq hu).symm
    obtain ⟨hmM, -, hαm, w, hww, hwiso, hwdisj, rfl⟩ := hd
    have hc : m.abstractTask = c := Sum.inr_injective (hαm.symm.trans hα)
    have hun := h.unconstrained hN
    have hwp : (N.progress x).WF := progress_wf hN hun
    have hdisj : Disjoint w.T (N.progress x).T := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      exact Finset.disjoint_left.1 hwdisj (Finset.mem_of_mem_erase hy') hy
    have h1 := h'.of_agree (decomposeWith_wf hN hww hwdisj) (decomposeWith_first hN h hwdisj)
    have h2 := MPProgTH.compL k hww hwp hdisj h1
    obtain ⟨σ, hσ⟩ := hwiso
    exact ⟨k, rfl, m, hmM, hc, h2.isoVia hww (hM m hmM) hσ⟩

/-- **The first task is compound** (composition of strategies). -/
theorem MPProgTH.first_comp_of [Infinite I] {G S'' : Set (Set F)} {k j : ℕ} {s : Set F} {c : C}
    (hN : N.WF) (h : IsFirst N x) (hα : N.α x = Sum.inr c) {m : Method I A C}
    (hm : m ∈ P.methods) (hc : m.abstractTask = c) (hmw : m.subtasks.WF)
    (hk : P.MPProgTH S'' k m.subtasks s) (hrest : ∀ s' ∈ S'', P.MPProgTH G j (N.progress x) s') :
    P.MPProgTH G (k + j + 1) N s := by
  obtain ⟨w, hww, hwiso, hwdisj⟩ := exists_fresh_iso_copy m.subtasks hmw N.T
  have hun := h.unconstrained hN
  have hwp : (N.progress x).WF := progress_wf hN hun
  have hdisj : Disjoint w.T (N.progress x).T := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    exact Finset.disjoint_left.1 hwdisj (Finset.mem_of_mem_erase hy') hy
  obtain ⟨τ, hτ⟩ := hwiso.symm
  have h1 := MPProgTH.compR hwp hrest k hww hdisj (hk.isoVia hmw hww hτ)
  have hd : DecompStep P.methods N x m (decomposeWith N x w) :=
    ⟨hm, h.1, hα.trans (by rw [hc]), w, hww, hwiso, hwdisj, rfl⟩
  exact .decomp hun hd (h1.of_agree (seqNet_wf hww hwp hdisj)
    (decomposeWith_first hN h hwdisj).symm)

end First

end Problem

end FOND
