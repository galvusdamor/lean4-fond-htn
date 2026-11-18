import HtnComplexity.Regular.RegularBound
import HtnPlanning.Core.ListsUpTo
/-!
# Tail-recursive problems have boundedly many open tasks

A *tail-recursive* hierarchy (Def. 3.4/3.6) comes with a rank on the compound task names such
that a method for a task of rank `r` may only introduce compound subtasks of rank `< r`, except
for a **last** one, which may keep the rank `r`.  Since that last subtask is ordered after every
other subtask of the method, it cannot be refined before the rest of its body is gone: a
compound task behaves like a process that either runs the children it has spawned or its own
continuation, and a child has a strictly smaller rank.  The live task network is therefore a
*forest of processes* of depth at most the maximal rank, with a bounded branching, hence
bounded.

This file makes that precise for an arbitrary (partially ordered) task network, generalising the
slot invariant of `HtnComplexity/Regular/RegularBound.lean` from a flat set of slots to a tree of
**addresses**:

* `HTN.TaskNetwork.AddrBound tn own rk K R m` — the ownership map `own` assigns every task an
  address, a list of length at most `R` over `{0, …, K - 1}`; at most `m` tasks share an
  address; a compound task is ordered after every other task of its address; a task whose
  address is a proper extension of the address of a compound task is ordered before that
  compound task; and the length of the address of a compound task plus the rank of its name
  stays below `R`;
* `HTN.TaskNetwork.AddrBounded.card_le` — such a network has at most `m * (K + 1) ^ R` tasks;
* `HTN.TaskNetwork.AddrBounded.progress` and `HTN.TaskNetwork.AddrBounded.decompose` — the
  invariant is preserved by the two operations of the progression search, the second one for a
  body all of whose compound subtasks obey the tail-recursion condition.
-/

namespace HTN

universe u v w x

variable {I : Type x} {A : Type v} {C : Type w}

namespace TaskNetwork

variable [DecidableEq I]

omit [DecidableEq I] in
/-- Being a *last* task is transported along an isomorphism. -/
theorem Iso.isLastId {tn tn' : TaskNetwork I A C} {σ : I → I}
    (hbij : Set.BijOn σ (tn.T : Set I) (tn'.T : Set I))
    (hord : ∀ t ∈ tn.T, ∀ t' ∈ tn.T, (tn.ord t t' ↔ tn'.ord (σ t) (σ t'))) {x : I}
    (hx : x ∈ tn.T) : tn.IsLastId x ↔ tn'.IsLastId (σ x) := by
  have hmem : ∀ t ∈ tn.T, σ t ∈ tn'.T := fun t ht => by simpa using hbij.mapsTo (by simpa using ht)
  constructor
  · rintro ⟨-, hall⟩
    refine ⟨hmem x hx, fun y' hy' hne => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hbij.surjOn (by simpa using hy')
    have hyT : y ∈ tn.T := by simpa using hy
    have hyx : y ≠ x := fun hc => hne (by rw [hc])
    exact (hord y hyT x hx).1 (hall y hyT hyx)
  · rintro ⟨-, hall⟩
    refine ⟨hx, fun y hy hne => ?_⟩
    have hne' : σ y ≠ σ x := fun hc =>
      hne (hbij.injOn (by simpa using hy) (by simpa using hx) hc)
    exact (hord y hy x hx).2 (hall (σ y) (hmem y hy) hne')

omit [DecidableEq I] in
/-- The tail-recursion condition on the body of a method is transported along an
isomorphism. -/
theorem Iso.tailRecBody {tn tn' : TaskNetwork I A C} {rk : C → ℕ} {r : ℕ} (h : tn.Iso tn')
    (h' : ∀ x ∈ tn'.T, ∀ n : C, tn'.α x = Sum.inr n →
      (tn'.IsLastId x → rk n ≤ r) ∧ (¬ tn'.IsLastId x → rk n < r)) :
    ∀ x ∈ tn.T, ∀ n : C, tn.α x = Sum.inr n →
      (tn.IsLastId x → rk n ≤ r) ∧ (¬ tn.IsLastId x → rk n < r) := by
  obtain ⟨σ, hbij, hord, hα⟩ := h
  intro x hx n hn
  have hmem : σ x ∈ tn'.T := by simpa using hbij.mapsTo (by simpa using hx)
  have hn' : tn'.α (σ x) = Sum.inr n := by rw [← hα x hx]; exact hn
  have hlast := Iso.isLastId hbij hord hx
  refine ⟨fun hl => (h' (σ x) hmem n hn').1 (hlast.1 hl), fun hl => ?_⟩
  exact (h' (σ x) hmem n hn').2 fun hc => hl (hlast.2 hc)

/-- **The address invariant** of a tail-recursive hierarchy. -/
structure AddrBound (tn : TaskNetwork I A C) (own : I → List ℕ) (rk : C → ℕ) (K R m : ℕ) :
    Prop where
  /-- Addresses are short. -/
  len : ∀ t ∈ tn.T, (own t).length ≤ R
  /-- Addresses use only the first `K` numbers. -/
  entries : ∀ t ∈ tn.T, ∀ i ∈ own t, i < K
  /-- At most `m` tasks share an address. -/
  fiber : ∀ a : List ℕ, (tn.T.filter (fun t => own t = a)).card ≤ m
  /-- A compound task is ordered after every other task of its own address. -/
  last : ∀ c ∈ tn.T, tn.IsAbstractId c → ∀ y ∈ tn.T, y ≠ c → own y = own c → tn.ord y c
  /-- A task of a strictly deeper address is ordered before a compound task above it. -/
  below : ∀ c ∈ tn.T, tn.IsAbstractId c → ∀ y ∈ tn.T, own c <+: own y → own y ≠ own c →
    tn.ord y c
  /-- The depth of a compound task plus the rank of its name stays below `R`. -/
  depth : ∀ c ∈ tn.T, ∀ n : C, tn.α c = Sum.inr n → (own c).length + rk n ≤ R

/-- A task network is *address bounded* iff some ownership map satisfies the address
invariant. -/
def AddrBounded (tn : TaskNetwork I A C) (rk : C → ℕ) (K R m : ℕ) : Prop :=
  ∃ own, AddrBound tn own rk K R m

omit [DecidableEq I] in
/-- **An address bounded task network has at most `m * (K + 1) ^ R` tasks.** -/
theorem AddrBounded.card_le {tn : TaskNetwork I A C} {rk : C → ℕ} {K R m : ℕ}
    (h : AddrBounded tn rk K R m) : tn.T.card ≤ m * (K + 1) ^ R := by
  classical
  obtain ⟨own, h⟩ := h
  have h₁ : tn.T.card ≤ m * (tn.T.image own).card :=
    Finset.card_le_mul_card_image _ _ (fun a _ => h.fiber a)
  have h₂ : (tn.T.image own).card ≤ (K + 1) ^ R := by
    refine le_trans (card_image_le_of_short tn.T own (List.range K) R h.len
      (fun a ha x hx => List.mem_range.2 (h.entries a ha x hx))) ?_
    simp
  exact h₁.trans (Nat.mul_le_mul_left m h₂)

/-- **The address invariant is preserved by progression.** -/
theorem AddrBound.progress {tn : TaskNetwork I A C} {own : I → List ℕ} {rk : C → ℕ} {K R m : ℕ}
    (h : AddrBound tn own rk K R m) (t : I) : AddrBound (tn.progress t) own rk K R m where
  len := fun x hx => h.len x (Finset.mem_of_mem_erase hx)
  entries := fun x hx => h.entries x (Finset.mem_of_mem_erase hx)
  fiber := by
    intro a
    refine le_trans (Finset.card_le_card ?_) (h.fiber a)
    intro x hx
    simp only [Finset.mem_filter, progress_T] at hx ⊢
    exact ⟨Finset.mem_of_mem_erase hx.1, hx.2⟩
  last := by
    intro c hc habs y hy hyc hown
    exact ⟨h.last c (Finset.mem_of_mem_erase hc) habs y (Finset.mem_of_mem_erase hy) hyc hown,
      Finset.ne_of_mem_erase hy⟩
  below := by
    intro c hc habs y hy hpre hne
    exact ⟨h.below c (Finset.mem_of_mem_erase hc) habs y (Finset.mem_of_mem_erase hy) hpre hne,
      Finset.ne_of_mem_erase hy⟩
  depth := fun c hc n hn => h.depth c (Finset.mem_of_mem_erase hc) n hn

/-- **The address invariant is preserved by decomposition** of an unconstrained compound task
`t` of rank `rk n` by a body `u` of at most `m` tasks all of whose compound subtasks obey the
tail-recursion condition: the body stays at the address of `t`, except for its compound
subtasks that are *not* last, which — having a strictly smaller rank — open a new address one
level deeper. -/
theorem AddrBounded.decompose {tn u : TaskNetwork I A C} {rk : C → ℕ} {K R m : ℕ} {t : I}
    {n : C} (h : AddrBounded tn rk K R m) (hu : tn.Unconstrained t)
    (hα : tn.α t = Sum.inr n) (hdisj : Disjoint tn.T u.T) (hcard : u.T.card ≤ m) (hm : 1 ≤ m)
    (hmK : m ≤ K)
    (htr : ∀ x ∈ u.T, ∀ n' : C, u.α x = Sum.inr n' →
      (u.IsLastId x → rk n' ≤ rk n) ∧ (¬ u.IsLastId x → rk n' < rk n)) :
    AddrBounded (HTN.decomposeWith tn t u) rk K R m := by
  classical
  obtain ⟨own, h⟩ := h
  have htT : t ∈ tn.T := hu.1
  have habs_t : tn.IsAbstractId t := ⟨n, hα⟩
  have hdepth_t : (own t).length + rk n ≤ R := h.depth t htT n hα
  -- nothing else sits at the address of `t`, and nothing sits strictly below it
  have hfree : ∀ y ∈ tn.T, y ≠ t → own y ≠ own t := fun y hy hyt hown =>
    hu.2 y hy (h.last t htT habs_t y hy hyt hown)
  have hnobelow : ∀ y ∈ tn.T, (own t).IsPrefix (own y) → own y ≠ own t → False :=
    fun y hy hpre hne => hu.2 y hy (h.below t htT habs_t y hy hpre hne)
  -- the index of a task of the body
  set idx : I → ℕ := fun x => u.T.toList.idxOf x with hidx
  have hidx_lt : ∀ x ∈ u.T, idx x < m := by
    intro x hx
    have h1 : idx x < u.T.toList.length :=
      List.idxOf_lt_length_of_mem (Finset.mem_toList.2 hx)
    rw [Finset.length_toList] at h1
    omega
  have hidx_inj : ∀ x ∈ u.T, ∀ y ∈ u.T, idx x = idx y → x = y := by
    intro x hx y _ hxy
    exact (List.idxOf_inj (Finset.mem_toList.2 hx)).1 hxy
  -- the new ownership map
  set own' : I → List ℕ := fun x =>
    if x ∈ u.T then
      (if u.IsAbstractId x ∧ ¬ u.IsLastId x then own t ++ [idx x] else own t)
    else own x with hown'
  have hold : ∀ x, x ∉ u.T → own' x = own x := by
    intro x hx
    simp [hown', hx]
  have hnew_stay : ∀ x ∈ u.T, ¬ (u.IsAbstractId x ∧ ¬ u.IsLastId x) → own' x = own t := by
    intro x hx hnl
    simp [hown', hx, hnl]
  have hnew_deep : ∀ x ∈ u.T, u.IsAbstractId x → ¬ u.IsLastId x →
      own' x = own t ++ [idx x] := by
    intro x hx habs hnl
    simp [hown', hx, habs, hnl]
  have hdisj' : ∀ x ∈ u.T, x ∉ tn.T := fun x hx hc => (Finset.disjoint_left.1 hdisj hc) hx
  have hdisjT : ∀ x ∈ tn.T, x ∉ u.T := fun x hx => Finset.disjoint_left.1 hdisj hx
  -- the four shapes of the new ordering
  have ord_nn : ∀ x y, u.ord x y → (HTN.decomposeWith tn t u).ord x y := fun x y hxy => Or.inl hxy
  have ord_no : ∀ x y, x ∈ u.T → tn.ord t y → (HTN.decomposeWith tn t u).ord x y :=
    fun x y hx hty => Or.inr (Or.inr (Or.inl ⟨hty, hx⟩))
  have ord_oo : ∀ x y, tn.ord x y → x ≠ t → y ≠ t → (HTN.decomposeWith tn t u).ord x y :=
    fun x y hxy hx hy => Or.inr (Or.inr (Or.inr ⟨hxy, hx, hy⟩))
  -- the rank of a compound subtask of the body
  have hrank_last : ∀ x ∈ u.T, ∀ n' : C, u.α x = Sum.inr n' → u.IsLastId x → rk n' ≤ rk n :=
    fun x hx n' hn' hl => (htr x hx n' hn').1 hl
  have hrank_nl : ∀ x ∈ u.T, ∀ n' : C, u.α x = Sum.inr n' → ¬ u.IsLastId x → rk n' < rk n :=
    fun x hx n' hn' hl => (htr x hx n' hn').2 hl
  refine ⟨own', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- len
    intro x hx
    rcases mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx₂
    · rw [hold x (hdisjT x hx₁)]
      exact h.len x hx₁
    · by_cases hnl : u.IsAbstractId x ∧ ¬ u.IsLastId x
      · obtain ⟨n', hn'⟩ := hnl.1
        have hlt : rk n' < rk n := hrank_nl x hx₂ n' hn' hnl.2
        rw [hnew_deep x hx₂ hnl.1 hnl.2]
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [hnew_stay x hx₂ hnl]
        exact h.len t htT
  · -- entries
    intro x hx i hi
    rcases mem_decomposeWith_T.1 hx with ⟨hx₁, hxt⟩ | hx₂
    · rw [hold x (hdisjT x hx₁)] at hi
      exact h.entries x hx₁ i hi
    · by_cases hnl : u.IsAbstractId x ∧ ¬ u.IsLastId x
      · rw [hnew_deep x hx₂ hnl.1 hnl.2] at hi
        rcases List.mem_append.1 hi with hi' | hi'
        · exact h.entries t htT i hi'
        · have : i = idx x := by simpa using hi'
          exact lt_of_lt_of_le (this ▸ hidx_lt x hx₂) hmK
      · rw [hnew_stay x hx₂ hnl] at hi
        exact h.entries t htT i hi
  · -- fiber
    intro a
    by_cases ha : a = own t
    · subst ha
      refine le_trans (Finset.card_le_card ?_) hcard
      intro x hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨hxT, hxa⟩ := hx
      rcases mem_decomposeWith_T.1 hxT with ⟨hx₁, hxt⟩ | hx₂
      · rw [hold x (hdisjT x hx₁)] at hxa
        exact absurd hxa (hfree x hx₁ hxt)
      · exact hx₂
    · by_cases hb : (own t).IsPrefix a
      · refine le_trans (Finset.card_le_one.2 ?_) hm
        intro x hx y hy
        simp only [Finset.mem_filter] at hx hy
        have key : ∀ z, z ∈ (HTN.decomposeWith tn t u).T → own' z = a →
            z ∈ u.T ∧ own' z = own t ++ [idx z] := by
          intro z hzT hza
          rcases mem_decomposeWith_T.1 hzT with ⟨hz₁, hzt⟩ | hz₂
          · exfalso
            rw [hold z (hdisjT z hz₁)] at hza
            exact hnobelow z hz₁ (hza ▸ hb) (by rw [hza]; exact ha)
          · refine ⟨hz₂, ?_⟩
            by_cases hnl : u.IsAbstractId z ∧ ¬ u.IsLastId z
            · exact hnew_deep z hz₂ hnl.1 hnl.2
            · exfalso
              rw [hnew_stay z hz₂ hnl] at hza
              exact ha hza.symm
        obtain ⟨hxu, hxe⟩ := key x hx.1 hx.2
        obtain ⟨hyu, hye⟩ := key y hy.1 hy.2
        have : own t ++ [idx x] = own t ++ [idx y] := by
          rw [← hxe, ← hye, hx.2, hy.2]
        have hidxeq : idx x = idx y := by simpa using this
        exact hidx_inj x hxu y hyu hidxeq
      · refine le_trans (Finset.card_le_card ?_) (h.fiber a)
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        obtain ⟨hxT, hxa⟩ := hx
        rcases mem_decomposeWith_T.1 hxT with ⟨hx₁, hxt⟩ | hx₂
        · rw [hold x (hdisjT x hx₁)] at hxa
          exact ⟨hx₁, hxa⟩
        · exfalso
          by_cases hnl : u.IsAbstractId x ∧ ¬ u.IsLastId x
          · rw [hnew_deep x hx₂ hnl.1 hnl.2] at hxa
            exact hb (hxa ▸ List.prefix_append _ _)
          · rw [hnew_stay x hx₂ hnl] at hxa
            exact ha hxa.symm
  · -- last
    intro c hc habsc y hy hyc hown
    by_cases hcu : c ∈ u.T
    · have habsu : u.IsAbstractId c := by
        obtain ⟨n', hn'⟩ := habsc
        exact ⟨n', by simpa [hcu] using hn'⟩
      by_cases hnl : ¬ u.IsLastId c
      · -- `c` opened its own address, so nothing else shares it
        exfalso
        have hce : own' c = own t ++ [idx c] := hnew_deep c hcu habsu hnl
        rcases mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy₂
        · rw [hold y (hdisjT y hy₁)] at hown
          refine hnobelow y hy₁ ?_ ?_
          · rw [hown, hce]
            exact List.prefix_append _ _
          · rw [hown, hce]
            intro hcon
            have := congrArg List.length hcon
            simp at this
        · by_cases hnl' : u.IsAbstractId y ∧ ¬ u.IsLastId y
          · rw [hnew_deep y hy₂ hnl'.1 hnl'.2, hce] at hown
            exact hyc (hidx_inj y hy₂ c hcu (by simpa using hown))
          · rw [hnew_stay y hy₂ hnl', hce] at hown
            have := congrArg List.length hown
            simp at this
      · -- `c` is the last task of the body and stays at the address of `t`
        push_neg at hnl
        have hce : own' c = own t := hnew_stay c hcu (by tauto)
        rcases mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy₂
        · exfalso
          rw [hold y (hdisjT y hy₁), hce] at hown
          exact hfree y hy₁ hyt hown
        · exact ord_nn y c (hnl.2 y hy₂ hyc)
    · -- `c` is an old task
      have hc₁ : c ∈ tn.T ∧ c ≠ t := by
        rcases mem_decomposeWith_T.1 hc with h' | h'
        · exact h'
        · exact absurd h' hcu
      have habsc' : tn.IsAbstractId c := by
        obtain ⟨n', hn'⟩ := habsc
        exact ⟨n', by simpa [hcu] using hn'⟩
      have hce : own' c = own c := hold c hcu
      rcases mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy₂
      · rw [hold y (hdisjT y hy₁), hce] at hown
        exact ord_oo y c (h.last c hc₁.1 habsc' y hy₁ hyc hown) hyt hc₁.2
      · exfalso
        rw [hce] at hown
        by_cases hnl : u.IsAbstractId y ∧ ¬ u.IsLastId y
        · rw [hnew_deep y hy₂ hnl.1 hnl.2] at hown
          refine hnobelow c hc₁.1 ?_ ?_
          · rw [← hown]
            exact List.prefix_append _ _
          · rw [← hown]
            intro hcon
            have := congrArg List.length hcon
            simp at this
        · rw [hnew_stay y hy₂ hnl] at hown
          exact hfree c hc₁.1 hc₁.2 hown.symm
  · -- below
    intro c hc habsc y hy hpre hne
    by_cases hcu : c ∈ u.T
    · have habsu : u.IsAbstractId c := by
        obtain ⟨n', hn'⟩ := habsc
        exact ⟨n', by simpa [hcu] using hn'⟩
      by_cases hnl : ¬ u.IsLastId c
      · exfalso
        have hce : own' c = own t ++ [idx c] := hnew_deep c hcu habsu hnl
        rw [hce] at hpre hne
        rcases mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy₂
        · rw [hold y (hdisjT y hy₁)] at hpre hne
          refine hnobelow y hy₁ (List.IsPrefix.trans (List.prefix_append _ _) hpre) ?_
          intro hcon
          rw [hcon] at hpre
          have := hpre.length_le
          simp at this
        · by_cases hnl' : u.IsAbstractId y ∧ ¬ u.IsLastId y
          · rw [hnew_deep y hy₂ hnl'.1 hnl'.2] at hpre hne
            exact hne (hpre.eq_of_length (by simp)).symm
          · rw [hnew_stay y hy₂ hnl'] at hpre
            have := hpre.length_le
            simp at this
      · push_neg at hnl
        have hce : own' c = own t := hnew_stay c hcu (by tauto)
        rw [hce] at hpre hne
        rcases mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy₂
        · exfalso
          rw [hold y (hdisjT y hy₁)] at hpre hne
          exact hnobelow y hy₁ hpre hne
        · refine ord_nn y c (hnl.2 y hy₂ ?_)
          intro hyc
          subst hyc
          exact hne (hnew_stay y hy₂ (by tauto))
    · have hc₁ : c ∈ tn.T ∧ c ≠ t := by
        rcases mem_decomposeWith_T.1 hc with h' | h'
        · exact h'
        · exact absurd h' hcu
      have habsc' : tn.IsAbstractId c := by
        obtain ⟨n', hn'⟩ := habsc
        exact ⟨n', by simpa [hcu] using hn'⟩
      have hce : own' c = own c := hold c hcu
      rw [hce] at hpre hne
      rcases mem_decomposeWith_T.1 hy with ⟨hy₁, hyt⟩ | hy₂
      · rw [hold y (hdisjT y hy₁)] at hpre hne
        exact ord_oo y c (h.below c hc₁.1 habsc' y hy₁ hpre hne) hyt hc₁.2
      · -- a new task: it suffices that `t` was already below `c`
        refine ord_no y c hy₂ ?_
        have hpre' : (own c).IsPrefix (own t) := by
          by_cases hnl : u.IsAbstractId y ∧ ¬ u.IsLastId y
          · rw [hnew_deep y hy₂ hnl.1 hnl.2] at hpre
            by_cases hlen : (own c).length ≤ (own t).length
            · exact List.prefix_of_prefix_length_le hpre (List.prefix_append _ _) hlen
            · exfalso
              have hle := hpre.length_le
              simp only [List.length_append, List.length_singleton] at hle
              have hEq : own c = own t ++ [idx y] := hpre.eq_of_length (by
                simp only [List.length_append, List.length_singleton]
                omega)
              rw [hnew_deep y hy₂ hnl.1 hnl.2] at hne
              exact hne hEq.symm
          · rw [hnew_stay y hy₂ hnl] at hpre
            exact hpre
        have hne' : own t ≠ own c := fun hcon => hfree c hc₁.1 hc₁.2 hcon.symm
        exact h.below c hc₁.1 habsc' t htT hpre' hne'
  · -- depth
    intro c hc n' hn'
    by_cases hcu : c ∈ u.T
    · have hn'u : u.α c = Sum.inr n' := by simpa [hcu] using hn'
      by_cases hnl : u.IsAbstractId c ∧ ¬ u.IsLastId c
      · have hlt : rk n' < rk n := hrank_nl c hcu n' hn'u hnl.2
        rw [hnew_deep c hcu hnl.1 hnl.2]
        simp only [List.length_append, List.length_singleton]
        omega
      · have hlast : u.IsLastId c := by
          by_contra hcon
          exact hnl ⟨⟨n', hn'u⟩, hcon⟩
        have hle : rk n' ≤ rk n := hrank_last c hcu n' hn'u hlast
        rw [hnew_stay c hcu hnl]
        omega
    · have hc₁ : c ∈ tn.T ∧ c ≠ t := by
        rcases mem_decomposeWith_T.1 hc with h' | h'
        · exact h'
        · exact absurd h' hcu
      rw [hold c hcu]
      exact h.depth c hc₁.1 n' (by simpa [hcu] using hn')

end TaskNetwork

end HTN
