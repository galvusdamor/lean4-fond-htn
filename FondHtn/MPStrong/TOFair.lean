import FondHtn.MPStrong.TOGame
import FondHtn.MPStrong.CyclicGame
/-!
# Sequential composition of the fair game

The progression fair game of `FondHtn/MPStrong/CyclicGame.lean` with a **target**: the empty
network is a goal only in a state of `G` (`FOND.Problem.FAttrT`, `FOND.Problem.FairWinT`).  For
`G = univ` it is `FairWin true` (`FOND.Problem.fairWinT_univ_iff`).

* **`FOND.Problem.FairWinT.compL`** — a fair solution of `u ; v` (`FOND.Problem.seqNet`) restricts
  to a fair solution of `u` with the target "states from which `v` is fairly won";
* **`FOND.Problem.FairWinT.compR`** — fair solutions of `u` (target `S'`) and of `v` from every
  state of `S'` compose to a fair solution of `u ; v`.

So `FairWinT G (u ; v) s ↔ ∃ S', FairWinT S' u s ∧ ∀ s' ∈ S', FairWinT G v s'` exactly as for the
strong game (`FOND.Problem.MPProgTH.compL/compR`).  Positional sets compose because the attractor
is existential (a node needs *some* witness move).  See `doc/notes_to_fair_2.md` for why this does
not yet give a finite summary fixpoint for totally ordered problems.
-/

namespace FOND

open HTN HTN.TaskNetwork

namespace Problem

variable {F A C I : Type} (P : Problem F A C I) [DecidableEq I]

/-- **The attractor with target `G`** (progression moves only). -/
inductive FAttrT (G : Set (Set F)) (X : NSet F A C I) : ℕ → TaskNetwork I A C → Set F → Prop
  | goal {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) (hs : s ∈ G) :
      FAttrT G X n tn s
  | prim {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A}
      (hu : tn.Unconstrained t) (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, X (tn.progress t) s') {s₀ : Set F}
      (hs₀ : s₀ ∈ (P.δ a).outcomes s) (h : FAttrT G X n (tn.progress t) s₀) :
      FAttrT G X (n + 1) tn s
  | decomp {n : ℕ} {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}
      (hu : tn.Unconstrained t) (hd : DecompStep P.methods tn t m tn') (hX : X tn' s)
      (h : FAttrT G X n tn' s) : FAttrT G X (n + 1) tn s

/-- **The fair game with target `G`.** -/
def FairWinT (G : Set (Set F)) (tn : TaskNetwork I A C) (s : Set F) : Prop :=
  ∃ X : NSet F A C I, NGood X ∧ X tn s ∧ ∀ tn s, X tn s → ∃ n, P.FAttrT G X n tn s

variable {P}

lemma FAttrT.monoX {G : Set (Set F)} {X Y : NSet F A C I} (hXY : ∀ tn s, X tn s → Y tn s)
    {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : P.FAttrT G X n tn s) :
    P.FAttrT G Y n tn s := by
  induction h with
  | goal h hs => exact .goal h hs
  | prim hu hα happ hall hs₀ _ ih =>
    exact .prim hu hα happ (fun s' hs' => hXY _ _ (hall s' hs')) hs₀ ih
  | decomp hu hd hX _ ih => exact .decomp hu hd (hXY _ _ hX) ih

theorem FAttrT.isoVia [Infinite I] {G : Set (Set F)} {X : NSet F A C I} (hX : NGood X) {n : ℕ}
    {tn : TaskNetwork I A C} {s : Set F} (h : P.FAttrT G X n tn s) :
    ∀ {tn' : TaskNetwork I A C} {σ : I → I}, tn.WF → tn'.WF → IsoVia σ tn tn' →
      P.FAttrT G X n tn' s := by
  induction h with
  | goal he hs => exact fun _ _ hσ => .goal (hσ.empty he) hs
  | prim hu hα happ hall hs₀ _ ih =>
    intro tn' σ hw hw' hσ
    have hw₁ := progress_wf hw hu
    have hw₁' := progress_wf hw' (hσ.unconstrained hu)
    exact .prim (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ
      (fun s' hs' => hX.2 _ _ _ _ (hall s' hs') hw₁' (hσ.progress hu.1)) hs₀
      (ih hw₁ hw₁' (hσ.progress hu.1))
  | decomp hu hd hXt _ ih =>
    intro tn' σ hw hw' hσ
    obtain ⟨u', hd', ρ, hρ⟩ := hd.isoVia hw hw' hσ
    exact .decomp (hσ.unconstrained hu) hd' (hX.2 _ _ _ _ hXt (hd'.wf hw') hρ)
      (ih (hd.wf hw) (hd'.wf hw') hρ)

/-- The target `univ` is the progression fair game. -/
theorem fairWinT_univ_iff {tn : TaskNetwork I A C} {s : Set F} :
    P.FairWinT Set.univ tn s ↔ P.FairWin true tn s := by
  have h1 : ∀ {X : NSet F A C I} {n tn s}, P.FAttrT Set.univ X n tn s → P.FAttrH true X n tn s := by
    intro X n tn s h
    induction h with
    | goal h _ => exact .goal h
    | prim hu hα happ hall hs₀ _ ih => exact .prim hu hα happ hall hs₀ ih
    | decomp hu hd hX _ ih => exact .decomp (fun _ => hu) hd hX ih
  have h2 : ∀ {X : NSet F A C I} {n tn s}, P.FAttrH true X n tn s → P.FAttrT Set.univ X n tn s := by
    intro X n tn s h
    induction h with
    | goal h => exact .goal h trivial
    | prim hu hα happ hall hs₀ _ ih => exact .prim hu hα happ hall hs₀ ih
    | decomp hu hd hX _ ih => exact .decomp (hu rfl) hd hX ih
  constructor
  · rintro ⟨X, hX, hX₀, hXa⟩
    exact ⟨X, hX, hX₀, fun tn s h => let ⟨n, hn⟩ := hXa tn s h; ⟨n, h1 hn⟩⟩
  · rintro ⟨X, hX, hX₀, hXa⟩
    exact ⟨X, hX, hX₀, fun tn s h => let ⟨n, hn⟩ := hXa tn s h; ⟨n, h2 hn⟩⟩

/-! ## Composition -/

theorem isoVia_of_agree' {tn tn' : TaskNetwork I A C} (h : tn.Agree tn') : IsoVia id tn tn' :=
  HTN.Article.isoVia_id_of_agree h

/-- **Restriction of a fair solution of `u ; v` to `u`.** -/
theorem FairWinT.compL [Infinite I] {G : Set (Set F)} {u v : TaskNetwork I A C} {s : Set F}
    (hu : u.WF) (hv : v.WF) (hd : Disjoint u.T v.T) (h : P.FairWinT G (seqNet u v) s) :
    P.FairWinT {s' | P.FairWinT G v s'} u s := by
  obtain ⟨X, hX, hX₀, hXa⟩ := h
  -- the networks `u'` with `u' ; v` (up to isomorphism) in `X`
  let Xu : NSet F A C I := fun tn s => tn.WF ∧ ∃ (u' : TaskNetwork I A C) (σ : I → I), u'.WF ∧
    Disjoint u'.T v.T ∧ X (seqNet u' v) s ∧ IsoVia σ u' tn
  have hXu : NGood Xu := by
    refine ⟨fun _ _ h => h.1, fun tn tn' s σ h hw' hσ => ?_⟩
    obtain ⟨-, u', τ, hw, hdj, hXs, hτ⟩ := h
    exact ⟨hw', u', σ ∘ τ, hw, hdj, hXs, hτ.comp hσ⟩
  have hmem : ∀ {u' : TaskNetwork I A C} {s}, u'.WF → Disjoint u'.T v.T → X (seqNet u' v) s →
      Xu u' s := fun hw hdj hXs => ⟨hw, _, id, hw, hdj, hXs, IsoVia.refl _⟩
  -- the attractor of `u' ; v` restricts to `u'`
  have key : ∀ n {u' : TaskNetwork I A C} {s}, u'.WF → Disjoint u'.T v.T → X (seqNet u' v) s →
      P.FAttrT G X n (seqNet u' v) s → P.FAttrT {s' | P.FairWinT G v s'} Xu n u' s := by
    intro n
    induction n with
    | zero =>
      intro u' s hw hdj hXs h
      by_cases he : u'.T = ∅
      · refine .goal he ⟨X, hX, ?_, hXa⟩
        exact hX.2 _ _ _ _ hXs hv (isoVia_of_agree' (seqNet_empty hw he))
      · cases h with
        | goal h' => exact absurd (Finset.union_eq_empty.1 h').1 he
    | succ k ih =>
      intro u' s hw hdj hXs h
      by_cases he : u'.T = ∅
      · refine .goal he ⟨X, hX, ?_, hXa⟩
        exact hX.2 _ _ _ _ hXs hv (isoVia_of_agree' (seqNet_empty hw he))
      have hws := seqNet_wf hw hv hdj
      cases h with
      | goal h' => exact absurd (Finset.union_eq_empty.1 h').1 he
      | @prim _ _ _ t a hu' hα happ hall s₀ hs₀ h₀ =>
        obtain ⟨htu, hut⟩ := unconstrained_seqNet hw hdj he hu'
        have hd' : Disjoint (u'.progress t).T v.T :=
          Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdj
        have hwp := progress_wf hw hut
        have hag := progress_seqNet htu hdj hv
        have hX' : ∀ s', X ((seqNet u' v).progress t) s' → X (seqNet (u'.progress t) v) s' :=
          fun s' h => hX.2 _ _ _ _ h (seqNet_wf hwp hv hd') (isoVia_of_agree' hag)
        refine .prim hut ((seqNet_α htu).symm.trans hα) happ
          (fun s' hs' => hmem hwp hd' (hX' s' (hall s' hs'))) hs₀ ?_
        exact ih hwp hd' (hX' s₀ (hall s₀ hs₀)) (h₀.isoVia hX (progress_wf hws hu')
          (seqNet_wf hwp hv hd') (isoVia_of_agree' hag))
      | @decomp _ _ N' _ t m hu' hdN hXN h' =>
        obtain ⟨htu, hut⟩ := unconstrained_seqNet hw hdj he hu'
        obtain ⟨hmM, -, hαt, w, hww, hwiso, hwdisj, rfl⟩ := hdN
        have hwu : Disjoint u'.T w.T :=
          Finset.disjoint_of_subset_left Finset.subset_union_left hwdisj
        have hdu : DecompStep P.methods u' t m (decomposeWith u' t w) :=
          ⟨hmM, htu, (seqNet_α htu).symm.trans hαt, w, hww, hwiso, hwu, rfl⟩
        have hd' : Disjoint (decomposeWith u' t w).T v.T := by
          rw [Finset.disjoint_left]
          intro y hy hyv
          rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
          · exact disj_mem hdj hy hyv
          · exact Finset.disjoint_left.1 hwdisj (Finset.mem_union_right _ hyv) hy
        have hwu' := hdu.wf hw
        have hag := decomposeWith_seqNet htu hdj hv hww hwdisj
        have hwN : (decomposeWith (seqNet u' v) t w).WF := decomposeWith_wf hws hww hwdisj
        have hXd := hX.2 _ _ _ _ hXN (seqNet_wf hwu' hv hd') (isoVia_of_agree' hag)
        exact .decomp hut hdu (hmem hwu' hd' hXd)
          (ih hwu' hd' hXd (h'.isoVia hX hwN (seqNet_wf hwu' hv hd') (isoVia_of_agree' hag)))
  refine ⟨Xu, hXu, hmem hu hd hX₀, fun tn s hXt => ?_⟩
  obtain ⟨hw, u', σ, hw', hdj, hXs, hσ⟩ := hXt
  obtain ⟨n, hn⟩ := hXa _ _ hXs
  exact ⟨n, (key n hw' hdj hXs hn).isoVia hXu hw' hw hσ⟩

/-- **Composition of fair solutions.** -/
theorem FairWinT.compR [Infinite I] {G S' : Set (Set F)} {u v : TaskNetwork I A C} {s : Set F}
    (hu : u.WF) (hv : v.WF) (hd : Disjoint u.T v.T) (h : P.FairWinT S' u s)
    (hv' : ∀ s' ∈ S', P.FairWinT G v s') : P.FairWinT G (seqNet u v) s := by
  classical
  obtain ⟨Xu, hXu, hXu₀, hXua⟩ := h
  -- the chosen solutions for `v`
  let Xv : Set F → NSet F A C I := fun s' => if h : s' ∈ S' then (hv' s' h).choose else fun _ _ => False
  have hXv : ∀ s' ∈ S', NGood (Xv s') ∧ Xv s' v s' ∧
      ∀ tn s, Xv s' tn s → ∃ n, P.FAttrT G (Xv s') n tn s := by
    intro s' hs'
    simp only [Xv, dif_pos hs']
    exact (hv' s' hs').choose_spec
  let Y : NSet F A C I := fun tn s => ∃ s' ∈ S', Xv s' tn s
  let A₁ : NSet F A C I := fun tn s => tn.WF ∧ ∃ (u' : TaskNetwork I A C) (σ : I → I), u'.WF ∧
    Disjoint u'.T v.T ∧ Xu u' s ∧ IsoVia σ (seqNet u' v) tn
  let X : NSet F A C I := fun tn s => A₁ tn s ∨ Y tn s
  have hX : NGood X := by
    refine ⟨fun tn s h => ?_, fun tn tn' s σ h hw' hσ => ?_⟩
    · rcases h with h | ⟨s', hs', h⟩
      · exact h.1
      · exact (hXv s' hs').1.1 _ _ h
    · rcases h with ⟨-, u', τ, hw, hdj, hXs, hτ⟩ | ⟨s', hs', h⟩
      · exact Or.inl ⟨hw', u', σ ∘ τ, hw, hdj, hXs, hτ.comp hσ⟩
      · exact Or.inr ⟨s', hs', (hXv s' hs').1.2 _ _ _ _ h hw' hσ⟩
  have hYX : ∀ s' ∈ S', ∀ tn s, Xv s' tn s → X tn s := fun s' hs' tn s h => Or.inr ⟨s', hs', h⟩
  have hmem : ∀ {u' : TaskNetwork I A C} {s}, u'.WF → Disjoint u'.T v.T → Xu u' s →
      X (seqNet u' v) s := fun hw hdj hX' =>
    Or.inl ⟨seqNet_wf hw hv hdj, _, id, hw, hdj, hX', IsoVia.refl _⟩
  -- the attractor of `u'` lifts to `u' ; v`
  have key : ∀ n {u' : TaskNetwork I A C} {s}, u'.WF → Disjoint u'.T v.T →
      P.FAttrT S' Xu n u' s → ∃ k, P.FAttrT G X k (seqNet u' v) s := by
    intro n
    induction n with
    | zero =>
      intro u' s hw hdj h
      cases h with
      | goal he hs =>
        obtain ⟨hg, hv₀, hva⟩ := hXv s hs
        obtain ⟨k, hk⟩ := hva _ _ hv₀
        exact ⟨k, (hk.monoX (hYX s hs)).isoVia hX hv (seqNet_wf hw hv hdj)
          (isoVia_of_agree' (seqNet_empty hw he).symm)⟩
    | succ k ih =>
      intro u' s hw hdj h
      have hws := seqNet_wf hw hv hdj
      cases h with
      | goal he hs =>
        obtain ⟨hg, hv₀, hva⟩ := hXv s hs
        obtain ⟨k, hk⟩ := hva _ _ hv₀
        exact ⟨k, (hk.monoX (hYX s hs)).isoVia hX hv hws
          (isoVia_of_agree' (seqNet_empty hw he).symm)⟩
      | @prim _ _ _ t a hu' hα happ hall s₀ hs₀ h₀ =>
        have hd' : Disjoint (u'.progress t).T v.T :=
          Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdj
        have hwp := progress_wf hw hu'
        have hag := (progress_seqNet hu'.1 hdj hv).symm
        have hwsp := progress_wf hws (unconstrained_seqNet_of hw hv hdj hu')
        obtain ⟨j, hj⟩ := ih hwp hd' h₀
        exact ⟨j + 1, .prim (unconstrained_seqNet_of hw hv hdj hu') ((seqNet_α hu'.1).trans hα)
          happ (fun s' hs' => hX.2 _ _ _ _ (hmem hwp hd' (hall s' hs')) hwsp
            (isoVia_of_agree' hag)) hs₀
          (hj.isoVia hX (seqNet_wf hwp hv hd') hwsp (isoVia_of_agree' hag))⟩
      | @decomp _ _ u'' _ t m hu' hdu hXu'' h' =>
        obtain ⟨hmM, htu, hαt, w, hww, hwiso, hwdisj, rfl⟩ := hdu
        obtain ⟨w₂, hww₂, hw₂iso, hw₂disj⟩ := exists_fresh_iso_copy w hww (u'.T ∪ v.T)
        have hw₂u : Disjoint u'.T w₂.T :=
          Finset.disjoint_of_subset_left Finset.subset_union_left hw₂disj
        obtain ⟨ρ, hρbij, hρord, hρα⟩ := hw₂iso.symm
        have hiso : (decomposeWith u' t w).Iso (decomposeWith u' (id t) w₂) :=
          decomposeWith_iso_congr hw hw hww hww₂ hwdisj hw₂u htu (Set.bijOn_id _)
            (by simp) (by simp) hρbij hρord hρα
        obtain ⟨τ, hτ⟩ := hiso
        have hwu₂ : (decomposeWith u' t w₂).WF := decomposeWith_wf hw hww₂ hw₂u
        have hwu₁ : (decomposeWith u' t w).WF := decomposeWith_wf hw hww hwdisj
        have hd' : Disjoint (decomposeWith u' t w₂).T v.T := by
          rw [Finset.disjoint_left]
          intro y hy hyv
          rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
          · exact disj_mem hdj hy hyv
          · exact Finset.disjoint_left.1 hw₂disj (Finset.mem_union_right _ hyv) hy
        have hX₂ : Xu (decomposeWith u' t w₂) s := hXu.2 _ _ _ _ hXu'' hwu₂ hτ
        obtain ⟨j, hj⟩ := ih hwu₂ hd' (h'.isoVia hXu hwu₁ hwu₂ hτ)
        have hdS : DecompStep P.methods (seqNet u' v) t m (decomposeWith (seqNet u' v) t w₂) :=
          ⟨hmM, Finset.mem_union_left _ htu, (seqNet_α htu).trans hαt, w₂, hww₂,
            hw₂iso.trans hwiso, hw₂disj, rfl⟩
        have hag := (decomposeWith_seqNet htu hdj hv hww₂ hw₂disj).symm
        have hwN := hdS.wf hws
        exact ⟨j + 1, .decomp (unconstrained_seqNet_of hw hv hdj hu') hdS
          (hX.2 _ _ _ _ (hmem hwu₂ hd' hX₂) hwN (isoVia_of_agree' hag))
          (hj.isoVia hX (seqNet_wf hwu₂ hv hd') hwN (isoVia_of_agree' hag))⟩
  refine ⟨X, hX, hmem hu hd hXu₀, fun tn s hXt => ?_⟩
  rcases hXt with ⟨hw, u', σ, hw', hdj, hXs, hσ⟩ | ⟨s', hs', h⟩
  · obtain ⟨n, hn⟩ := hXua _ _ hXs
    obtain ⟨k, hk⟩ := key n hw' hdj hn
    exact ⟨k, hk.isoVia hX (seqNet_wf hw' hv hdj) hw hσ⟩
  · obtain ⟨-, -, hva⟩ := hXv s' hs'
    obtain ⟨k, hk⟩ := hva _ _ h
    exact ⟨k, hk.monoX (hYX s' hs')⟩

/-- **Fair sequential composition.** -/
theorem fairWinT_seqNet_iff [Infinite I] {G : Set (Set F)} {u v : TaskNetwork I A C} {s : Set F}
    (hu : u.WF) (hv : v.WF) (hd : Disjoint u.T v.T) :
    P.FairWinT G (seqNet u v) s ↔ ∃ S', P.FairWinT S' u s ∧ ∀ s' ∈ S', P.FairWinT G v s' :=
  ⟨fun h => ⟨_, h.compL hu hv hd, fun _ h' => h'⟩,
    fun ⟨_, h₁, h₂⟩ => FairWinT.compR hu hv hd h₁ h₂⟩

end Problem

end FOND
