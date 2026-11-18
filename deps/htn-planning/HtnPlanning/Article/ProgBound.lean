import HtnPlanning.Article.AbsProgression
import HtnPlanning.Article.Classes
/-!
# Progression bounds (Lemmas 4.2.15, 4.2.19, 4.2.21)

Bounds on the size of the task networks reachable from `tn_I` by abstract progression
(`HTN.AbsReachN`), i.e. by progression of the abstraction of Prop. 4.2.14:

* `HTN.Problem.progBound_tailRec` — **Lemma 4.2.15**: for a `≤_r`-stratification of height `h` and
  at most `m ≥ 1` tasks per reachable method, `|tn_I| · m^h`;
* `HTN.Problem.progBound_TO` — **Lemma 4.2.19**: if moreover `tn_I` and the methods are totally
  ordered, `|tn_I| + (m - 1) · h`;
* `HTN.Problem.progBound_TOM` — **Lemma 4.2.21 (corrected)**: if the methods are totally ordered,
  `|tn_I| · (1 + (m - 1) · h)`.  The article states `|tn_I| · m · h`, which is wrong for `h = 0`
  (no compound tasks: the bound would be `0`) and for `m = 0`; for `m, h ≥ 1` it follows from the
  corrected bound.

All three are proved from the splitting lemma `HTN.AbsReachN.split` by induction on the rank of a
task (its stratum), with an inner induction on the number of steps for the tail-recursive last
tasks, which stay in the stratum.  This is the article's proof made precise: the bound of a
compound task is computed from those of the tasks of its method, and a last task is only
progressed once all other tasks of the method are gone.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

open TaskNetwork

namespace TaskNetwork

theorem restrict_eq_T {tn : TaskNetwork I A C} {x : I} (hx : x ∈ tn.T) :
    (tn.restrict (· = x)).T = {x} := by
  ext y; simp only [restrict, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro rfl; exact ⟨hx, rfl⟩

/-- An isomorphism maps last tasks to last tasks. -/
theorem Iso.isLastId_iff {tn tn' : TaskNetwork I A C} {σ : I → I}
    (hbij : Set.BijOn σ (tn.T : Set I) (tn'.T : Set I))
    (hord : ∀ t ∈ tn.T, ∀ t' ∈ tn.T, (tn.ord t t' ↔ tn'.ord (σ t) (σ t'))) {u : I}
    (hu : u ∈ tn.T) : tn.IsLastId u ↔ tn'.IsLastId (σ u) := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hbij.mapsTo hu, fun t' ht' hne => ?_⟩
    obtain ⟨v, hv, rfl⟩ := hbij.surjOn ht'
    have hvu : v ≠ u := fun e => hne (e ▸ rfl)
    exact (hord v hv u hu).1 (h v hv hvu)
  · rintro ⟨-, h⟩
    refine ⟨hu, fun v hv hne => ?_⟩
    have : σ v ≠ σ u := fun e => hne (hbij.injOn hv hu e)
    exact (hord v hv u hu).2 (h (σ v) (hbij.mapsTo hv) this)

/-- A well-formed network has at most one last task, unless it has a single task. -/
theorem IsLastId.unique {tn : TaskNetwork I A C} (hwf : tn.WF) {u v : I} (hu : tn.IsLastId u)
    (hv : tn.IsLastId v) : u = v := by
  by_contra hne
  exact hwf.irrefl u (hwf.trans (hv.2 u hu.1 hne) (hu.2 v hv.1 (Ne.symm hne)))

end TaskNetwork

/-! ### Basic facts on abstract progression from a single task -/

section Single

variable {M : Set (Method I A C)}

/-- The first step from a one-task network: the task is progressed or decomposed. -/
theorem AbsReachN.first_step {n : ℕ} {N N' : TaskNetwork I A C} {x : I} (hT : N.T = {x})
    (h : AbsReachN M (n + 1) N N') :
    ((∃ a, N.α x = Sum.inl a) ∧ N'.T = ∅) ∨
      ∃ m tn'', DecompStep M N x m (decomposeWith N x tn'') ∧ AbsReachN M n (decomposeWith N x tn'') N' := by
  cases h with
  | head hs hr =>
    cases hs with
    | @prog t hu hp =>
      have ht : t = x := by have := hu.1; rw [hT] at this; simpa using this
      subst ht
      refine Or.inl ⟨hp, hr.T_empty ?_⟩
      simp [TaskNetwork.progress, hT]
    | @decomp _ t m hu hd =>
      have ht : t = x := by have := hu.1; rw [hT] at this; simpa using this
      subst ht
      have hd' := hd
      obtain ⟨-, -, -, tn'', -, -, -, rfl⟩ := hd
      exact Or.inr ⟨m, tn'', hd', hr⟩

/-- From a primitive task, at most one task remains. -/
theorem AbsReachN.card_le_one_of_prim {n : ℕ} {N N' : TaskNetwork I A C} {x : I} (hT : N.T = {x})
    {a : A} (ha : N.α x = Sum.inl a) (h : AbsReachN M n N N') : N'.T.card ≤ 1 := by
  cases n with
  | zero => cases h; simp [hT]
  | succ n =>
    rcases h.first_step hT with ⟨-, he⟩ | ⟨m, tn'', hd, -⟩
    · simp [he]
    · rw [hd.2.2.1] at ha; cases ha

theorem decomposeWith_single_T {N tn'' : TaskNetwork I A C} {x : I} (hT : N.T = {x}) :
    (decomposeWith N x tn'').T = tn''.T := by
  simp [decomposeWith, hT]

end Single

namespace Problem

variable (P : Problem F A C I)

theorem AbsStep.namesReachable {tn tn' : TaskNetwork I A C} (h : AbsStep P.methods tn tn')
    (hn : P.NamesReachable tn) : P.NamesReachable tn' := by
  cases h with
  | prog hu _ => exact fun t ht c hc => hn t (Finset.mem_of_mem_erase ht) c hc
  | decomp _ h => exact namesReachable_of_decompStep h hn

theorem namesReachable_restrict {tn : TaskNetwork I A C} (hn : P.NamesReachable tn)
    (S : I → Prop) [DecidablePred S] : P.NamesReachable (tn.restrict S) :=
  fun t ht c hc => hn t (Finset.mem_filter.1 ht).1 c hc

/-- The size of a network reached by splitting is the sum of the sizes of the parts. -/
theorem card_eq_sum_parts {tn tn' : TaskNetwork I A C} {o : I → I}
    (hA : ∀ y ∈ tn'.T, o y ∈ tn.T) :
    tn'.T.card = ∑ x ∈ tn.T, (tn'.restrict (fun y => o y = x)).T.card :=
  Finset.card_eq_sum_card_fiberwise hA

/-! ### Tail-recursive problems -/

section TailRec

variable {le : C → C → Prop} (hs : P.IsStratR le) {f : C → ℕ}
  (hf : ∀ c c', P.ReachableName c → P.ReachableName c' → (le c c' ↔ f c ≤ f c'))
  {mm : ℕ} (hmm1 : 1 ≤ mm) (hmm : ∀ m, P.ReachableMethod m → m.subtasks.T.card ≤ mm)
include hs hf hmm1 hmm

/-- **The bound for a single task** in a tail-recursive problem: from a compound task of rank at
most `j`, at most `mm^(j+1)` tasks. -/
theorem single_bound_tailRec : ∀ (j n : ℕ) (N N' : TaskNetwork I A C) (x : I), N.WF → N.T = {x} →
    P.NamesReachable N → (∀ c, N.α x = Sum.inr c → f c ≤ j) →
    AbsReachN P.methods n N N' → N'.T.card ≤ mm ^ (j + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ihj =>
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro N N' x hwf hT hnr hrank hr
  have hpow : ∀ i, 1 ≤ mm ^ i := fun i => Nat.one_le_pow _ _ hmm1
  cases n with
  | zero => cases hr; rw [hT]; simpa using hpow (j + 1)
  | succ n =>
  rcases hr.first_step hT with ⟨-, he⟩ | ⟨m, tn'', hstep, hr'⟩
  · rw [he]; simp
  have hstep' := hstep
  obtain ⟨hm, -, hα, tn₀, hwf'', ⟨σ, hbij, hord, hlab⟩, hdisj, heq⟩ := hstep'
  have htn₀ : decomposeWith N x tn'' = decomposeWith N x tn₀ := heq
  set N₁ := decomposeWith N x tn''
  have hT₁ : N₁.T = tn''.T := decomposeWith_single_T hT
  have hT₀ : N₁.T = tn₀.T := by rw [htn₀]; exact decomposeWith_single_T hT
  have hrm : P.ReachableMethod m := reachableMethod_of_decompStep hstep hnr
  have hnr₁ : P.NamesReachable N₁ := namesReachable_of_decompStep hstep hnr
  have hwf₁ : N₁.WF := hstep.wf hwf
  have hc : f m.abstractTask ≤ j := hrank _ hα
  obtain ⟨o, cnt, hA, hB, hC, hD⟩ := hr'.split hwf₁
  -- the facts about the tasks of `N₁`, transported from the method through `σ`
  have hmem₀ : ∀ u ∈ N₁.T, u ∈ tn₀.T := fun u hu => hT₀ ▸ hu
  have hα₁ : ∀ u ∈ N₁.T, N₁.α u = m.subtasks.α (σ u) := fun u hu => by
    rw [htn₀]
    simp only [decomposeWith, hmem₀ u hu, if_true]
    exact hlab u (hmem₀ u hu)
  have hord₁ : ∀ u ∈ N₁.T, ∀ v ∈ N₁.T, tn₀.ord u v → N₁.ord u v := fun u _ v _ h => by
    rw [htn₀]; exact Or.inl h
  -- the bound of each part
  have hpart : ∀ u ∈ N₁.T, ∃ N_u, AbsReachN P.methods (cnt u) (N₁.restrict (· = u)) N_u ∧
      (N'.restrict (fun y => o y = u)).T.card = N_u.T.card := fun u hu => by
    obtain ⟨-, N_u, h1, h2⟩ := hC u hu
    exact ⟨N_u, h1, by rw [h2.1]⟩
  have hsingle : ∀ u ∈ N₁.T, (N₁.restrict (· = u)).WF ∧ (N₁.restrict (· = u)).T = {u} ∧
      P.NamesReachable (N₁.restrict (· = u)) := fun u hu =>
    ⟨restrict_wf hwf₁ _, restrict_eq_T hu, namesReachable_restrict P hnr₁ _⟩
  have hcard := card_eq_sum_parts hA
  by_cases hlast : ∃ u ∈ N₁.T, m.subtasks.IsLastId (σ u) ∧ 0 < cnt u
  · obtain ⟨uL, huL, hL, hpos⟩ := hlast
    have hL₀ : tn₀.IsLastId uL := (Iso.isLastId_iff hbij hord (hmem₀ uL huL)).2 hL
    have hempty : ∀ u ∈ N₁.T, u ≠ uL → (N'.restrict (fun y => o y = u)).T.card = 0 := by
      intro u hu hne
      have hz := hD uL huL u hu (hord₁ u hu uL huL (hL₀.2 u (hmem₀ u hu) hne)) hpos
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro y hy
      exact hz y (Finset.mem_filter.1 hy).1 (Finset.mem_filter.1 hy).2
    rw [hcard, Finset.sum_eq_single uL (fun u hu hne => hempty u hu hne) (fun h => absurd huL h)]
    obtain ⟨N_u, h1, h2⟩ := hpart uL huL
    rw [h2]
    obtain ⟨hw, hTu, hnu⟩ := hsingle uL huL
    refine ihn (cnt uL) (by have := (hC uL huL).1; omega) _ _ uL hw hTu hnu (fun d hd => ?_) h1
    have hd' : m.subtasks.α (σ uL) = Sum.inr d := by rw [← hα₁ uL huL]; exact hd
    have h1 := hs.last m hrm (σ uL) (hbij.mapsTo (hmem₀ uL huL)) hL d hd'
    have hrd : P.ReachableName d := ReachableName.method hm hrm.2 (hbij.mapsTo (hmem₀ uL huL)) hd'
    rw [hf d _ hrd hrm.2] at h1
    omega
  · push_neg at hlast
    -- every part is bounded by `1` (last tasks, untouched) or `mm^j` (other tasks)
    classical
    let L := N₁.T.filter fun u => m.subtasks.IsLastId (σ u)
    have hb : ∀ u ∈ N₁.T, (N'.restrict (fun y => o y = u)).T.card ≤
        if u ∈ L then 1 else mm ^ j := by
      intro u hu
      obtain ⟨N_u, h1, h2⟩ := hpart u hu
      rw [h2]
      obtain ⟨hw, hTu, hnu⟩ := hsingle u hu
      by_cases huL : u ∈ L
      · rw [if_pos huL]
        have h0 : cnt u = 0 := by
          have := hlast u hu (Finset.mem_filter.1 huL).2; omega
        rw [h0] at h1
        cases h1
        rw [hTu]; simp
      · rw [if_neg huL]
        have hnl : ¬ m.subtasks.IsLastId (σ u) := fun h => huL (Finset.mem_filter.2 ⟨hu, h⟩)
        cases hαu : N₁.α u with
        | inl a =>
          have := AbsReachN.card_le_one_of_prim hTu (by simpa [TaskNetwork.restrict] using hαu) h1
          exact this.trans (hpow j)
        | inr d =>
          have hd' : m.subtasks.α (σ u) = Sum.inr d := by rw [← hα₁ u hu]; exact hαu
          have hu' := hbij.mapsTo (hmem₀ u hu)
          obtain ⟨h1', h2'⟩ := hs.nonlast m hrm (σ u) hu' hnl d hd'
          have hrd : P.ReachableName d := ReachableName.method hm hrm.2 hu' hd'
          rw [hf d _ hrd hrm.2] at h1'
          rw [hf _ d hrm.2 hrd] at h2'
          have hlt : f d < j := by omega
          have := ihj (f d) hlt _ _ _ u hw hTu hnu (fun d' hd'' => by
            have : (N₁.restrict (· = u)).α u = N₁.α u := rfl
            rw [this, hαu] at hd''; cases hd''; exact le_rfl) h1
          exact this.trans (Nat.pow_le_pow_right hmm1 (by omega))
    have hLcard : L.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' := (Iso.isLastId_iff hbij hord (hmem₀ a (Finset.mem_filter.1 ha).1)).2
        (Finset.mem_filter.1 ha).2
      have hb' := (Iso.isLastId_iff hbij hord (hmem₀ b (Finset.mem_filter.1 hb).1)).2
        (Finset.mem_filter.1 hb).2
      exact IsLastId.unique hwf'' ha' hb'
    have hTcard : N₁.T.card ≤ mm := by
      have : N₁.T.card = m.subtasks.T.card := by
        rw [hT₀]; exact Finset.card_nbij σ (fun x hx => hbij.mapsTo hx) hbij.injOn hbij.surjOn
      rw [this]; exact hmm m hrm
    rw [hcard]
    calc ∑ u ∈ N₁.T, (N'.restrict (fun y => o y = u)).T.card
        ≤ ∑ u ∈ N₁.T, (if u ∈ L then 1 else mm ^ j) := Finset.sum_le_sum hb
      _ = L.card + (N₁.T.card - L.card) * mm ^ j := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
            mul_one]
          have hfL : N₁.T.filter (fun u => u ∈ L) = L := by
            ext u; simp only [Finset.mem_filter, L]; tauto
          have hfL' : (N₁.T.filter (fun u => u ∉ L)).card = N₁.T.card - L.card := by
            have := Finset.filter_card_add_filter_neg_card_eq_card (s := N₁.T)
              (p := fun u => u ∈ L)
            rw [hfL] at this
            omega
          rw [hfL, hfL']
      _ ≤ mm ^ (j + 1) := by
          have hLT : L.card ≤ N₁.T.card := Finset.card_filter_le _ _
          rw [pow_succ]
          rcases Nat.lt_or_ge L.card 1 with h0 | h1
          · have : L.card = 0 := by omega
            rw [this]; simp; nlinarith [hpow j]
          · have : L.card = 1 := by omega
            rw [this]
            have h2 : N₁.T.card - 1 ≤ mm - 1 := by omega
            have h3 := Nat.mul_le_mul_right (mm ^ j) h2
            have h4 : (mm - 1) * mm ^ j + mm ^ j = mm ^ j * mm := by
              rw [mul_comm (mm ^ j) mm, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hmm1]
            have := hpow j
            omega

end TailRec

/-- An untouched part has one task. -/
theorem part_card_of_cnt_zero {n : ℕ} {tn tn' : TaskNetwork I A C} {o : I → I} {cnt : I → ℕ}
    {x : I} (hx : x ∈ tn.T) (hC : cnt x ≤ n ∧ ∃ N, AbsReachN P.methods (cnt x)
      (tn.restrict (· = x)) N ∧ N.Agree (tn'.restrict (fun y => o y = x))) (h0 : cnt x = 0) :
    (tn'.restrict (fun y => o y = x)).T.card = 1 := by
  obtain ⟨-, N, h1, h2⟩ := hC
  rw [h0] at h1
  cases h1
  rw [← h2.1, restrict_eq_T hx]; simp

/-- **Lemma 4.2.15.** In a tail-recursive problem with a `≤_r`-stratification of height at most
`h` and at most `mm ≥ 1` tasks in every reachable method, every network reachable from `tn_I` by
abstract progression has at most `|tn_I| · mm^h` tasks. -/
theorem progBound_tailRec {le : C → C → Prop} (hs : P.IsStratR le) {h : ℕ}
    (hh : P.HasHeightLE le h) {mm : ℕ} (hmm1 : 1 ≤ mm)
    (hmm : ∀ m, P.ReachableMethod m → m.subtasks.T.card ≤ mm) (hwf : P.tnI.WF) {n : ℕ}
    {tn' : TaskNetwork I A C} (hr : AbsReachN P.methods n P.tnI tn') :
    tn'.T.card ≤ P.tnI.T.card * mm ^ h := by
  obtain ⟨f, hfh, hf⟩ := hh
  obtain ⟨o, cnt, hA, -, hC, -⟩ := hr.split hwf
  rw [card_eq_sum_parts hA]
  calc ∑ x ∈ P.tnI.T, (tn'.restrict (fun y => o y = x)).T.card
      ≤ ∑ x ∈ P.tnI.T, mm ^ h := Finset.sum_le_sum fun x hx => by
        obtain ⟨-, N, h1, h2⟩ := hC x hx
        rw [← h2.1]
        cases hαx : P.tnI.α x with
        | inl a =>
          exact (AbsReachN.card_le_one_of_prim (restrict_eq_T hx) hαx h1).trans
            (Nat.one_le_pow _ _ hmm1)
        | inr c =>
          have hrc : P.ReachableName c := ReachableName.tnI hx hαx
          have := single_bound_tailRec P hs hf hmm1 hmm (f c) _ _ _ x (restrict_wf hwf _)
            (restrict_eq_T hx) (namesReachable_restrict P P.namesReachable_tnI _)
            (fun c' hc' => by
              have : (P.tnI.restrict (· = x)).α x = P.tnI.α x := rfl
              rw [this, hαx] at hc'; cases hc'; exact le_rfl) h1
          exact this.trans (Nat.pow_le_pow_right hmm1 (hfh c hrc))
    _ = P.tnI.T.card * mm ^ h := by rw [Finset.sum_const, smul_eq_mul]

/-! ### Totally ordered methods -/

section TO

variable {le : C → C → Prop} (hs : P.IsStratR le) {f : C → ℕ}
  (hf : ∀ c c', P.ReachableName c → P.ReachableName c' → (le c c' ↔ f c ≤ f c'))
  {mm : ℕ} (hmm : ∀ m, P.ReachableMethod m → m.subtasks.T.card ≤ mm)
  (hTO : ∀ m, P.ReachableMethod m → m.subtasks.IsTotallyOrdered)
include hs hf hmm hTO

/-- In a totally ordered network, at most one part is touched and nonempty; the parts before it
are empty, the others untouched. -/
theorem touched_parts {n : ℕ} {tn tn' : TaskNetwork I A C} (hto : tn.IsTotallyOrdered)
    {o : I → I} {cnt : I → ℕ}
    (hC : ∀ x ∈ tn.T, cnt x ≤ n ∧ ∃ N, AbsReachN P.methods (cnt x) (tn.restrict (· = x)) N ∧
          N.Agree (tn'.restrict (fun y => o y = x)))
    (hD : ∀ x ∈ tn.T, ∀ z ∈ tn.T, tn.ord z x → 0 < cnt x → ∀ y ∈ tn'.T, o y ≠ z)
    {u : I} (hu : u ∈ tn.T) (hpos : 0 < cnt u)
    (hne : 0 < (tn'.restrict (fun y => o y = u)).T.card) :
    ∀ v ∈ tn.T, v ≠ u → (tn'.restrict (fun y => o y = v)).T.card ≤ 1 ∧
      (tn.ord v u → (tn'.restrict (fun y => o y = v)).T.card = 0) := by
  have hempty : ∀ x ∈ tn.T, ∀ z ∈ tn.T, tn.ord z x → 0 < cnt x →
      (tn'.restrict (fun y => o y = z)).T.card = 0 := fun x hx z hz hzx hp => by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro y hy
    exact hD x hx z hz hzx hp y (Finset.mem_filter.1 hy).1 (Finset.mem_filter.1 hy).2
  intro v hv hvu
  have h2 : tn.ord v u → (tn'.restrict (fun y => o y = v)).T.card = 0 :=
    fun h => hempty u hu v hv h hpos
  refine ⟨?_, h2⟩
  rcases hto v hv u hu hvu with h | h
  · rw [h2 h]; exact Nat.zero_le _
  · rcases Nat.eq_zero_or_pos (cnt v) with h0 | h0
    · rw [part_card_of_cnt_zero P hv (hC v hv) h0]
    · have := hempty v hv u hu h h0; omega

/-- **The bound for a single task** with totally ordered methods: from a compound task of rank
at most `j`, at most `1 + (mm - 1) · (j + 1)` tasks. -/
theorem single_bound_TO : ∀ (j n : ℕ) (N N' : TaskNetwork I A C) (x : I), N.WF → N.T = {x} →
    P.NamesReachable N → (∀ c, N.α x = Sum.inr c → f c ≤ j) →
    AbsReachN P.methods n N N' → N'.T.card ≤ 1 + (mm - 1) * (j + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ihj =>
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro N N' x hwf hT hnr hrank hr
  cases n with
  | zero => cases hr; rw [hT]; simp
  | succ n =>
  rcases hr.first_step hT with ⟨-, he⟩ | ⟨m, tn'', hstep, hr'⟩
  · rw [he]; simp
  have hstep' := hstep
  obtain ⟨hm, -, hα, tn₀, hwf'', ⟨σ, hbij, hord, hlab⟩, hdisj, heq⟩ := hstep'
  have htn₀ : decomposeWith N x tn'' = decomposeWith N x tn₀ := heq
  set N₁ := decomposeWith N x tn''
  have hT₀ : N₁.T = tn₀.T := by rw [htn₀]; exact decomposeWith_single_T hT
  have hrm : P.ReachableMethod m := reachableMethod_of_decompStep hstep hnr
  have hnr₁ : P.NamesReachable N₁ := namesReachable_of_decompStep hstep hnr
  have hwf₁ : N₁.WF := hstep.wf hwf
  have hc : f m.abstractTask ≤ j := hrank _ hα
  obtain ⟨o, cnt, hA, hB, hC, hD⟩ := hr'.split hwf₁
  have hmem₀ : ∀ u ∈ N₁.T, u ∈ tn₀.T := fun u hu => hT₀ ▸ hu
  have hα₁ : ∀ u ∈ N₁.T, N₁.α u = m.subtasks.α (σ u) := fun u hu => by
    rw [htn₀]
    simp only [decomposeWith, hmem₀ u hu, if_true]
    exact hlab u (hmem₀ u hu)
  have hord₁ : ∀ u ∈ N₁.T, ∀ v ∈ N₁.T, tn₀.ord u v → N₁.ord u v := fun u _ v _ h => by
    rw [htn₀]; exact Or.inl h
  have hto₁ : N₁.IsTotallyOrdered := by
    intro u hu v hv huv
    have h := hTO m hrm (σ u) (hbij.mapsTo (hmem₀ u hu)) (σ v) (hbij.mapsTo (hmem₀ v hv))
      (fun e => huv (hbij.injOn (hmem₀ u hu) (hmem₀ v hv) e))
    rcases h with h | h
    · exact Or.inl (hord₁ u hu v hv ((hord u (hmem₀ u hu) v (hmem₀ v hv)).2 h))
    · exact Or.inr (hord₁ v hv u hu ((hord v (hmem₀ v hv) u (hmem₀ u hu)).2 h))
  have hTcard : N₁.T.card ≤ mm := by
    have : N₁.T.card = m.subtasks.T.card := by
      rw [hT₀]; exact Finset.card_nbij σ (fun x hx => hbij.mapsTo hx) hbij.injOn hbij.surjOn
    rw [this]; exact hmm m hrm
  have hcard := card_eq_sum_parts hA
  by_cases hK : ∃ u ∈ N₁.T, 0 < cnt u ∧ 0 < (N'.restrict (fun y => o y = u)).T.card
  · obtain ⟨u, hu, hpos, hne⟩ := hK
    have hoth := touched_parts P hs hf hmm hTO hto₁ hC hD hu hpos hne
    obtain ⟨-, N_u, h1, h2⟩ := hC u hu
    have hcu : cnt u ≤ n := (hC u hu).1
    have hw := restrict_wf hwf₁ (· = u)
    have hTu := restrict_eq_T hu
    have hnu := namesReachable_restrict P hnr₁ (· = u)
    have hαu' : (N₁.restrict (· = u)).α u = N₁.α u := rfl
    rw [hcard, ← Finset.add_sum_erase _ _ hu, ← h2.1]
    by_cases hL : m.subtasks.IsLastId (σ u)
    · -- the last task: all other parts precede it and are empty
      have hL₀ : tn₀.IsLastId u := (Iso.isLastId_iff hbij hord (hmem₀ u hu)).2 hL
      have hz : ∑ v ∈ N₁.T.erase u, (N'.restrict (fun y => o y = v)).T.card = 0 :=
        Finset.sum_eq_zero fun v hv => (hoth v (Finset.mem_of_mem_erase hv)
          (Finset.ne_of_mem_erase hv)).2 (hord₁ v (Finset.mem_of_mem_erase hv) u hu
            (hL₀.2 v (hmem₀ v (Finset.mem_of_mem_erase hv)) (Finset.ne_of_mem_erase hv)))
      rw [hz, add_zero]
      refine ihn (cnt u) (by omega) _ _ u hw hTu hnu (fun d hd => ?_) h1
      rw [hαu'] at hd
      have hd' : m.subtasks.α (σ u) = Sum.inr d := by rw [← hα₁ u hu]; exact hd
      have h1 := hs.last m hrm (σ u) (hbij.mapsTo (hmem₀ u hu)) hL d hd'
      have hrd : P.ReachableName d := ReachableName.method hm hrm.2 (hbij.mapsTo (hmem₀ u hu)) hd'
      rw [hf d _ hrd hrm.2] at h1
      omega
    · -- a non-last task: of lower rank; the others contribute at most one each
      have hpu : N_u.T.card ≤ 1 + (mm - 1) * j := by
        cases hαu : N₁.α u with
        | inl a =>
          have := AbsReachN.card_le_one_of_prim hTu (by rw [hαu']; exact hαu) h1
          omega
        | inr d =>
          have hd' : m.subtasks.α (σ u) = Sum.inr d := by rw [← hα₁ u hu]; exact hαu
          have hu' := hbij.mapsTo (hmem₀ u hu)
          obtain ⟨h1', h2'⟩ := hs.nonlast m hrm (σ u) hu' hL d hd'
          have hrd : P.ReachableName d := ReachableName.method hm hrm.2 hu' hd'
          rw [hf d _ hrd hrm.2] at h1'
          rw [hf _ d hrm.2 hrd] at h2'
          have hlt : f d < j := by omega
          have := ihj (f d) hlt _ _ _ u hw hTu hnu (fun d' hd'' => by
            rw [hαu', hαu] at hd''; cases hd''; exact le_rfl) h1
          have : (mm - 1) * (f d + 1) ≤ (mm - 1) * j := Nat.mul_le_mul_left _ (by omega)
          omega
      have hrest : ∑ v ∈ N₁.T.erase u, (N'.restrict (fun y => o y = v)).T.card ≤
          (N₁.T.erase u).card := by
        have := Finset.sum_le_card_nsmul (N₁.T.erase u)
          (fun v => (N'.restrict (fun y => o y = v)).T.card) 1 fun v hv =>
            (hoth v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv)).1
        simpa using this
      have hce : (N₁.T.erase u).card = N₁.T.card - 1 := Finset.card_erase_of_mem hu
      have : (mm - 1) * (j + 1) = (mm - 1) * j + (mm - 1) := by ring
      omega
  · push_neg at hK
    have hb : ∀ u ∈ N₁.T, (N'.restrict (fun y => o y = u)).T.card ≤ 1 := by
      intro u hu
      rcases Nat.eq_zero_or_pos (cnt u) with h0 | h0
      · rw [part_card_of_cnt_zero P hu (hC u hu) h0]
      · have := hK u hu h0; omega
    rw [hcard]
    have := Finset.sum_le_card_nsmul N₁.T _ 1 hb
    simp only [smul_eq_mul, mul_one] at this
    have h3 : mm ≤ 1 + (mm - 1) * (j + 1) := by
      have : mm - 1 ≤ (mm - 1) * (j + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    omega

/-- The bound of a part of `tn_I` with totally ordered methods. -/
theorem part_bound_TO {h : ℕ} (hfh : ∀ c, P.ReachableName c → f c < h) (hwf : P.tnI.WF)
    {n : ℕ} {tn' : TaskNetwork I A C} {o : I → I} {cnt : I → ℕ} {x : I} (hx : x ∈ P.tnI.T)
    (hC : cnt x ≤ n ∧ ∃ N, AbsReachN P.methods (cnt x) (P.tnI.restrict (· = x)) N ∧
      N.Agree (tn'.restrict (fun y => o y = x))) :
    (tn'.restrict (fun y => o y = x)).T.card ≤ 1 + (mm - 1) * h := by
  obtain ⟨-, N, h1, h2⟩ := hC
  rw [← h2.1]
  cases hαx : P.tnI.α x with
  | inl a =>
    have := AbsReachN.card_le_one_of_prim (restrict_eq_T hx) hαx h1
    omega
  | inr c =>
    have hrc : P.ReachableName c := ReachableName.tnI hx hαx
    have := single_bound_TO P hs hf hmm hTO (f c) _ _ _ x (restrict_wf hwf _)
      (restrict_eq_T hx) (namesReachable_restrict P P.namesReachable_tnI _)
      (fun c' hc' => by
        have : (P.tnI.restrict (· = x)).α x = P.tnI.α x := rfl
        rw [this, hαx] at hc'; cases hc'; exact le_rfl) h1
    have : (mm - 1) * (f c + 1) ≤ (mm - 1) * h :=
      Nat.mul_le_mul_left _ (hfh c hrc)
    omega

/-- **Lemma 4.2.21 (corrected).** With totally ordered methods (`TO-M`), every network
reachable from `tn_I` by abstract progression has at most `|tn_I| · (1 + (mm - 1) · h)`
tasks. -/
theorem progBound_TOM {h : ℕ} (hfh : ∀ c, P.ReachableName c → f c < h) (hwf : P.tnI.WF)
    {n : ℕ} {tn' : TaskNetwork I A C} (hr : AbsReachN P.methods n P.tnI tn') :
    tn'.T.card ≤ P.tnI.T.card * (1 + (mm - 1) * h) := by
  obtain ⟨o, cnt, hA, -, hC, -⟩ := hr.split hwf
  rw [card_eq_sum_parts hA]
  have := Finset.sum_le_card_nsmul P.tnI.T _ _ fun x hx =>
    part_bound_TO P hs hf hmm hTO hfh hwf hx (hC x hx)
  simpa using this

/-- **Lemma 4.2.19.** If moreover `tn_I` is totally ordered, every network reachable from `tn_I`
by abstract progression has at most `|tn_I| + (mm - 1) · h` tasks. -/
theorem progBound_TO {h : ℕ} (hfh : ∀ c, P.ReachableName c → f c < h) (hwf : P.tnI.WF)
    (htoI : P.tnI.IsTotallyOrdered) {n : ℕ} {tn' : TaskNetwork I A C}
    (hr : AbsReachN P.methods n P.tnI tn') :
    tn'.T.card ≤ P.tnI.T.card + (mm - 1) * h := by
  obtain ⟨o, cnt, hA, -, hC, hD⟩ := hr.split hwf
  rw [card_eq_sum_parts hA]
  by_cases hK : ∃ u ∈ P.tnI.T, 0 < cnt u ∧ 0 < (tn'.restrict (fun y => o y = u)).T.card
  · obtain ⟨u, hu, hpos, hne⟩ := hK
    have hoth := touched_parts P hs hf hmm hTO htoI hC hD hu hpos hne
    rw [← Finset.add_sum_erase _ _ hu]
    have h1 := part_bound_TO P hs hf hmm hTO hfh hwf hu (hC u hu)
    have hrest : ∑ v ∈ P.tnI.T.erase u, (tn'.restrict (fun y => o y = v)).T.card ≤
        (P.tnI.T.erase u).card := by
      have := Finset.sum_le_card_nsmul (P.tnI.T.erase u)
        (fun v => (tn'.restrict (fun y => o y = v)).T.card) 1 fun v hv =>
          (hoth v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv)).1
      simpa using this
    have hce : (P.tnI.T.erase u).card = P.tnI.T.card - 1 := Finset.card_erase_of_mem hu
    have : 0 < P.tnI.T.card := Finset.card_pos.2 ⟨u, hu⟩
    omega
  · push_neg at hK
    have hb : ∀ u ∈ P.tnI.T, (tn'.restrict (fun y => o y = u)).T.card ≤ 1 := by
      intro u hu
      rcases Nat.eq_zero_or_pos (cnt u) with h0 | h0
      · rw [part_card_of_cnt_zero P hu (hC u hu) h0]
      · have := hK u hu h0; omega
    have := Finset.sum_le_card_nsmul P.tnI.T _ 1 hb
    simp only [smul_eq_mul, mul_one] at this
    omega

end TO

end Problem

end HTN
