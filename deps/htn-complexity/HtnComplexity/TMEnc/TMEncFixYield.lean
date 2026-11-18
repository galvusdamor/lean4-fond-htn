import HtnComplexity.TMEnc.TMEncWitness
import HtnPlanning.Interleave.GridYield
import HtnPlanning.Interleave.InterleaveList
/-!
# The counting tasks of the repaired encoding refine into the expected copies

Plans of the encoded problem are described syntactically by the relations
`HTN.Domain.ChainYield` / `HTN.Domain.GridYield` of `HtnPlanning/Interleave/GridYield.lean`, which
agree with the semantic refinement relation for every domain all of whose methods have **grid**
bodies.  The repaired domain `HTN.TMEnc.domainFix` has one method that is not a grid — the one
of the fresh initial task `sI`, whose body is the `gridTail` network `initNet K` — so the theory
is developed here for the auxiliary domain `HTN.TMEnc.domainBod`, which has exactly the grid
methods of `HTN.TMEnc.bodiesFix`; its methods are a subset of those of `domainFix`, so every
refinement it admits is one of `domainFix` (`HTN.TMEnc.netYield_fix_of_bod`).

The results are the two counting tasks of the construction, which generate the exponentially
many tape cells, waiting cycles and counters out of logarithmically many methods:

* `HTN.TMEnc.chainYield_cSeq_iff` — **`C^k_t` refines exactly into `k` refinements of `t`,
  concatenated**;
* `HTN.TMEnc.chainYield_cPar_iff` — **`C_k^t` refines exactly into `k` refinements of `t`,
  interleaved**;
* `HTN.TMEnc.chainYield_waitN_iff` — `wait^i` refines into `i` waiting cycles.

They are the first step of both plan-level halves of the simulation argument; see `NOTES.md`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Splitting an interleaving of many components

The counterpart of `HTN.InterleaveList.append`; it belongs to
`HtnPlanning/Interleave/InterleaveList.lean` and is kept here only to avoid rebuilding the whole
library. -/

/-- **An interleaving of two groups of components splits into an interleaving of each group.** -/
lemma interleaveList_split {α : Type} : ∀ {ls₁ ls₂ : List (List α)} {z : List α},
    InterleaveList (ls₁ ++ ls₂) z →
      ∃ z₁ z₂, InterleaveList ls₁ z₁ ∧ InterleaveList ls₂ z₂ ∧ Interleave z₁ z₂ z := by
  intro ls₁
  induction ls₁ with
  | nil => intro ls₂ z h; exact ⟨[], z, InterleaveList.nil, h, Interleave.nil_left z⟩
  | cons a ls ih =>
      intro ls₂ z h
      rw [List.cons_append] at h
      cases h with
      | @cons as bs cs ls' hrec hint =>
          obtain ⟨z₁, z₂, h₁, h₂, hsplit⟩ := ih hrec
          obtain ⟨y, hy₁, hy₂⟩ := Interleave.assoc' hsplit hint
          exact ⟨y, z₂, InterleaveList.cons h₁ hy₁, h₂, hy₂⟩

/-- **Interleaving the components pointwise.**  If `z₁` is an interleaving of `xs` and `z₂` one
of `ys`, then `z₁ ++ z₂` is an interleaving of the componentwise concatenations. -/
lemma interleaveList_append_pointwise {α : Type} :
    ∀ {xs ys : List (List α)} {z₁ z₂ : List α}, InterleaveList xs z₁ → InterleaveList ys z₂ →
      xs.length = ys.length → InterleaveList (List.zipWith (· ++ ·) xs ys) (z₁ ++ z₂) := by
  intro xs
  induction xs with
  | nil =>
      intro ys z₁ z₂ h₁ h₂ hlen
      cases h₁
      have hys : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst hys
      cases h₂
      simpa using InterleaveList.nil
  | cons a xs ih =>
      intro ys z₁ z₂ h₁ h₂ hlen
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          cases h₁ with
          | @cons _ bs _ _ hrec₁ hint₁ =>
              cases h₂ with
              | @cons _ cs _ _ hrec₂ hint₂ =>
                  have hlen' : xs.length = ys.length := by simpa using hlen
                  refine InterleaveList.cons (ih hrec₁ hrec₂ hlen') ?_
                  exact hint₁.append_append hint₂

/-- **Interleaving does not depend on the order of the components.** -/
lemma interleaveList_perm {α : Type} {xs ys : List (List α)} {z : List α} (hp : xs.Perm ys)
    (h : InterleaveList xs z) : InterleaveList ys z := by
  induction hp generalizing z with
  | nil => exact h
  | cons a _ ih =>
      cases h with
      | cons hrec hint => exact InterleaveList.cons (ih hrec) hint
  | swap a b l =>
      cases h with
      | @cons _ bs _ _ hrec hint =>
          cases hrec with
          | @cons _ cs _ _ hrec' hint' =>
              obtain ⟨y, hy₁, hy₂⟩ := Interleave.assoc' hint' hint
              obtain ⟨y', hy₁', hy₂'⟩ := Interleave.assoc hy₁.symm hy₂
              exact InterleaveList.cons (InterleaveList.cons hrec' hy₁') hy₂'
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)

/-! ### The domain of the grid bodies -/

/-- The repaired domain without the single method of the fresh initial task `sI`: all of its
methods have grid bodies, so the syntactic refinement relations apply to it. -/
def domainBod (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    Domain (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  toActionModel := actionModel
  methods := {m | ∃ ls ∈ bodiesFix N w K m.abstractTask, m.subtasks = TaskNetwork.grid ls}

lemma methods_grid_bod :
    ∀ m ∈ (domainBod N w K).methods, ∃ ls, m.subtasks = TaskNetwork.grid ls := by
  rintro ⟨c, tn⟩ ⟨ls, -, rfl⟩
  exact ⟨ls, rfl⟩

lemma methods_bod_subset : (domainBod N w K).methods ⊆ (domainFix N w K).methods :=
  fun _ hm => Set.mem_union_left _ hm

/-- Two presentations of the same grid have the same refinements. -/
lemma gridYield_congr_bod {ls ls' : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    {as : List (TMAct Q Γ)} (h : TaskNetwork.grid ls = TaskNetwork.grid ls') :
    (domainBod N w K).GridYield ls as ↔ (domainBod N w K).GridYield ls' as := by
  rw [← netYield_grid_iff methods_grid_bod, ← netYield_grid_iff methods_grid_bod, h]

/-- **A single compound task refines exactly like the grid bodies of its methods.** -/
lemma chainYield_singleton_bod_iff {c : TMTask Q Γ} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr c] as ↔
      ∃ ls ∈ bodiesFix N w K c, (domainBod N w K).GridYield ls as := by
  rw [chainYield_singleton_inr_iff]
  constructor
  · rintro ⟨ls, ⟨m, hm, rfl, hsub⟩, hy⟩
    obtain ⟨ls', hls', hsub'⟩ := hm
    exact ⟨ls', hls', (gridYield_congr_bod (by rw [← hsub', hsub])).1 hy⟩
  · rintro ⟨ls, hls, hy⟩
    exact ⟨ls, ⟨⟨c, TaskNetwork.grid ls⟩, ⟨ls, hls, rfl⟩, rfl, rfl⟩, hy⟩

/-! ### The bodies of the two counting tasks -/

lemma bodiesFix_cSeq_zero {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.cSeq t 0) ↔ ls = [] := by
  simp [bodiesFix, bodies]

lemma bodiesFix_cSeq_one {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.cSeq t 1) ↔ ls = [[Sum.inr t]] := by
  simp [bodiesFix, bodies]

lemma bodiesFix_cSeq_even {t : TMTask Q Γ} {k : ℕ} (hk : 2 ≤ k) (he : k % 2 = 0)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.cSeq t k) ↔
      ls = [[Sum.inr (TMTask.cSeq t (k / 2)), Sum.inr (TMTask.cSeq t (k / 2))]] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  simp [bodiesFix, bodies, h0, h1, he]

lemma bodiesFix_cSeq_odd {t : TMTask Q Γ} {k : ℕ} (hk : 2 ≤ k) (ho : k % 2 = 1)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.cSeq t k) ↔
      ls = [[Sum.inr t, Sum.inr (TMTask.cSeq t (k - 1))]] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  have he : ¬ (k % 2 = 0) := by omega
  simp [bodiesFix, bodies, h0, h1, he]

lemma bodiesFix_cPar_zero {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.cPar t 0) ↔ ls = [] := by
  simp [bodiesFix, bodies]

lemma bodiesFix_cPar_one {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.cPar t 1) ↔ ls = [[Sum.inr t]] := by
  simp [bodiesFix, bodies]

lemma bodiesFix_cPar_even {t : TMTask Q Γ} {k : ℕ} (hk : 2 ≤ k) (he : k % 2 = 0)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.cPar t k) ↔
      ls = [[Sum.inr (TMTask.cPar t (k / 2))], [Sum.inr (TMTask.cPar t (k / 2))]] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  simp [bodiesFix, bodies, h0, h1, he]

lemma bodiesFix_cPar_odd {t : TMTask Q Γ} {k : ℕ} (hk : 2 ≤ k) (ho : k % 2 = 1)
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} :
    ls ∈ bodiesFix N w K (TMTask.cPar t k) ↔
      ls = [[Sum.inr t], [Sum.inr (TMTask.cPar t (k - 1))]] := by
  have h0 : ¬ (k = 0) := by omega
  have h1 : ¬ (k = 1) := by omega
  have he : ¬ (k % 2 = 0) := by omega
  simp [bodiesFix, bodies, h0, h1, he]

/-! ### Refinements of the two counting tasks -/

/-- **The totally ordered counting task `C^k_t` refines exactly into `k` refinements of `t`,
concatenated.** -/
theorem chainYield_cSeq_iff : ∀ (k : ℕ) {t : TMTask Q Γ} {as : List (TMAct Q Γ)},
    (domainBod N w K).ChainYield [Sum.inr (TMTask.cSeq t k)] as ↔
      ∃ ass : List (List (TMAct Q Γ)), ass.length = k ∧
        (∀ l ∈ ass, (domainBod N w K).ChainYield [Sum.inr t] l) ∧ as = ass.flatten := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t as
  rw [chainYield_singleton_bod_iff]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodiesFix_cSeq_zero] at hls
        subst hls
        exact ⟨[], rfl, by simp, by simpa using hy⟩
      · rintro ⟨ass, hlen, -, rfl⟩
        have hass : ass = [] := List.eq_nil_of_length_eq_zero hlen
        subst hass
        exact ⟨[], bodiesFix_cSeq_zero.2 rfl, by simp⟩
    · constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodiesFix_cSeq_one] at hls
        subst hls
        refine ⟨[as], rfl, ?_, by simp⟩
        intro l hl
        rw [List.mem_singleton] at hl
        subst hl
        exact gridYield_singleton_iff.1 hy
      · rintro ⟨ass, hlen, hall, rfl⟩
        obtain ⟨l, rfl⟩ : ∃ l, ass = [l] := by
          cases ass with
          | nil => simp at hlen
          | cons l tl =>
              cases tl with
              | nil => exact ⟨l, rfl⟩
              | cons _ _ => simp at hlen
        exact ⟨[[Sum.inr t]], bodiesFix_cSeq_one.2 rfl,
          gridYield_singleton_iff.2 (by simpa using hall l (by simp))⟩
  · have hhalf : k / 2 < k := Nat.div_lt_self (by omega) (by omega)
    have hpred : k - 1 < k := by omega
    rcases Nat.even_or_odd k with hev | hod
    · have he : k % 2 = 0 := Nat.even_iff.1 hev
      constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodiesFix_cSeq_even hk he] at hls
        subst hls
        rw [gridYield_singleton_iff,
          show [Sum.inr (TMTask.cSeq t (k / 2)), Sum.inr (TMTask.cSeq t (k / 2))] =
            [Sum.inr (TMTask.cSeq t (k / 2))] ++ [Sum.inr (TMTask.cSeq t (k / 2))] from rfl,
          chainYield_append_iff] at hy
        obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := hy
        obtain ⟨ass₁, hlen₁, hall₁, rfl⟩ := (ih _ hhalf).1 h₁
        obtain ⟨ass₂, hlen₂, hall₂, rfl⟩ := (ih _ hhalf).1 h₂
        refine ⟨ass₁ ++ ass₂, by simp [hlen₁, hlen₂]; omega, ?_, by simp⟩
        intro l hl
        rcases List.mem_append.1 hl with hl | hl
        · exact hall₁ l hl
        · exact hall₂ l hl
      · rintro ⟨ass, hlen, hall, rfl⟩
        refine ⟨_, (bodiesFix_cSeq_even hk he).2 rfl, ?_⟩
        rw [gridYield_singleton_iff,
          show [Sum.inr (TMTask.cSeq t (k / 2)), Sum.inr (TMTask.cSeq t (k / 2))] =
            [Sum.inr (TMTask.cSeq t (k / 2))] ++ [Sum.inr (TMTask.cSeq t (k / 2))] from rfl,
          chainYield_append_iff]
        refine ⟨(ass.take (k / 2)).flatten, (ass.drop (k / 2)).flatten, ?_,
          (ih _ hhalf).2 ⟨ass.take (k / 2), by simp [hlen]; omega,
            fun l hl => hall l (List.mem_of_mem_take hl), rfl⟩,
          (ih _ hhalf).2 ⟨ass.drop (k / 2), by simp [hlen]; omega,
            fun l hl => hall l (List.mem_of_mem_drop hl), rfl⟩⟩
        rw [← List.flatten_append, List.take_append_drop]
    · have ho : k % 2 = 1 := Nat.odd_iff.1 hod
      constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodiesFix_cSeq_odd hk ho] at hls
        subst hls
        rw [gridYield_singleton_iff,
          show [Sum.inr t, Sum.inr (TMTask.cSeq t (k - 1))] =
            [Sum.inr t] ++ [Sum.inr (TMTask.cSeq t (k - 1))] from rfl,
          chainYield_append_iff] at hy
        obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := hy
        obtain ⟨ass₂, hlen₂, hall₂, rfl⟩ := (ih _ hpred).1 h₂
        refine ⟨as₁ :: ass₂, by simp [hlen₂]; omega, ?_, by simp⟩
        intro l hl
        rcases List.mem_cons.1 hl with rfl | hl
        · exact h₁
        · exact hall₂ l hl
      · rintro ⟨ass, hlen, hall, rfl⟩
        obtain ⟨l, ass', rfl⟩ : ∃ l ass', ass = l :: ass' := by
          cases ass with
          | nil => simp at hlen; omega
          | cons l ass' => exact ⟨l, ass', rfl⟩
        refine ⟨_, (bodiesFix_cSeq_odd hk ho).2 rfl, ?_⟩
        rw [gridYield_singleton_iff,
          show [Sum.inr t, Sum.inr (TMTask.cSeq t (k - 1))] =
            [Sum.inr t] ++ [Sum.inr (TMTask.cSeq t (k - 1))] from rfl,
          chainYield_append_iff]
        refine ⟨l, ass'.flatten, by simp, hall l (by simp), ?_⟩
        have hlen' : ass'.length = k - 1 := by simp at hlen; omega
        exact (ih _ hpred).2 ⟨ass', hlen', fun x hx => hall x (by simp [hx]), rfl⟩

/-- **The parallel counting task `C_k^t` refines exactly into `k` refinements of `t`,
interleaved.** -/
theorem chainYield_cPar_iff : ∀ (k : ℕ) {t : TMTask Q Γ} {as : List (TMAct Q Γ)},
    (domainBod N w K).ChainYield [Sum.inr (TMTask.cPar t k)] as ↔
      ∃ ass : List (List (TMAct Q Γ)), ass.length = k ∧
        (∀ l ∈ ass, (domainBod N w K).ChainYield [Sum.inr t] l) ∧ InterleaveList ass as := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t as
  rw [chainYield_singleton_bod_iff]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodiesFix_cPar_zero] at hls
        subst hls
        rw [gridYield_nil_iff] at hy
        subst hy
        exact ⟨[], rfl, by simp, InterleaveList.nil⟩
      · rintro ⟨ass, hlen, -, hint⟩
        have hass : ass = [] := List.eq_nil_of_length_eq_zero hlen
        subst hass
        cases hint
        exact ⟨[], bodiesFix_cPar_zero.2 rfl, by simp⟩
    · constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodiesFix_cPar_one] at hls
        subst hls
        refine ⟨[as], rfl, ?_, InterleaveList.cons InterleaveList.nil (Interleave.nil_right as)⟩
        intro l hl
        rw [List.mem_singleton] at hl
        subst hl
        exact gridYield_singleton_iff.1 hy
      · rintro ⟨ass, hlen, hall, hint⟩
        obtain ⟨l, rfl⟩ : ∃ l, ass = [l] := by
          cases ass with
          | nil => simp at hlen
          | cons l tl =>
              cases tl with
              | nil => exact ⟨l, rfl⟩
              | cons _ _ => simp at hlen
        refine ⟨[[Sum.inr t]], bodiesFix_cPar_one.2 rfl, gridYield_singleton_iff.2 ?_⟩
        cases hint with
        | cons hrec hi =>
            cases hrec
            rw [hi.eq_of_nil_right]
            exact hall l (by simp)
  · have hhalf : k / 2 < k := Nat.div_lt_self (by omega) (by omega)
    have hpred : k - 1 < k := by omega
    rcases Nat.even_or_odd k with hev | hod
    · have he : k % 2 = 0 := Nat.even_iff.1 hev
      constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodiesFix_cPar_even hk he] at hls
        subst hls
        rw [gridYield_cons_iff] at hy
        obtain ⟨as₁, as₂, h₁, h₂, hint⟩ := hy
        rw [gridYield_singleton_iff] at h₂
        obtain ⟨ass₁, hlen₁, hall₁, hint₁⟩ := (ih _ hhalf).1 h₁
        obtain ⟨ass₂, hlen₂, hall₂, hint₂⟩ := (ih _ hhalf).1 h₂
        refine ⟨ass₁ ++ ass₂, by simp [hlen₁, hlen₂]; omega, ?_,
          InterleaveList.append hint₁ hint₂ hint⟩
        intro l hl
        rcases List.mem_append.1 hl with hl | hl
        · exact hall₁ l hl
        · exact hall₂ l hl
      · rintro ⟨ass, hlen, hall, hint⟩
        refine ⟨_, (bodiesFix_cPar_even hk he).2 rfl, ?_⟩
        rw [← List.take_append_drop (k / 2) ass] at hint
        obtain ⟨z₁, z₂, h₁, h₂, hsplit⟩ := interleaveList_split hint
        rw [gridYield_cons_iff]
        refine ⟨z₁, z₂, (ih _ hhalf).2 ⟨ass.take (k / 2), by simp [hlen]; omega,
            fun l hl => hall l (List.mem_of_mem_take hl), h₁⟩,
          gridYield_singleton_iff.2 ((ih _ hhalf).2 ⟨ass.drop (k / 2), by simp [hlen]; omega,
            fun l hl => hall l (List.mem_of_mem_drop hl), h₂⟩), hsplit⟩
    · have ho : k % 2 = 1 := Nat.odd_iff.1 hod
      constructor
      · rintro ⟨ls, hls, hy⟩
        rw [bodiesFix_cPar_odd hk ho] at hls
        subst hls
        rw [gridYield_cons_iff] at hy
        obtain ⟨as₁, as₂, h₁, h₂, hint⟩ := hy
        rw [gridYield_singleton_iff] at h₂
        obtain ⟨ass₂, hlen₂, hall₂, hint₂⟩ := (ih _ hpred).1 h₂
        refine ⟨as₁ :: ass₂, by simp [hlen₂]; omega, ?_, InterleaveList.cons hint₂ hint⟩
        intro l hl
        rcases List.mem_cons.1 hl with rfl | hl
        · exact h₁
        · exact hall₂ l hl
      · rintro ⟨ass, hlen, hall, hint⟩
        obtain ⟨l, ass', rfl⟩ : ∃ l ass', ass = l :: ass' := by
          cases ass with
          | nil => simp at hlen; omega
          | cons l ass' => exact ⟨l, ass', rfl⟩
        refine ⟨_, (bodiesFix_cPar_odd hk ho).2 rfl, ?_⟩
        rw [gridYield_cons_iff]
        cases hint with
        | @cons _ bs _ _ hrec hi =>
            have hlen' : ass'.length = k - 1 := by simp at hlen; omega
            exact ⟨l, bs, hall l (by simp), gridYield_singleton_iff.2
              ((ih _ hpred).2 ⟨ass', hlen', fun x hx => hall x (by simp [hx]), hrec⟩), hi⟩

/-- **`wait^i` refines into `i` waiting cycles.** -/
theorem chainYield_waitN_iff {i : ℕ} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN i)] as ↔
      ∃ ass : List (List (TMAct Q Γ)), ass.length = i ∧
        (∀ l ∈ ass, (domainBod N w K).ChainYield [Sum.inr TMTask.waitCell] l) ∧
          as = ass.flatten := by
  rw [chainYield_singleton_bod_iff]
  constructor
  · rintro ⟨ls, hls, hy⟩
    have hls' : ls = [[Sum.inr (TMTask.cSeq TMTask.waitCell i)]] := by
      simpa [bodiesFix, bodies] using hls
    subst hls'
    rw [gridYield_singleton_iff] at hy
    exact (chainYield_cSeq_iff i).1 hy
  · intro h
    refine ⟨[[Sum.inr (TMTask.cSeq TMTask.waitCell i)]], by simp [bodiesFix, bodies], ?_⟩
    exact gridYield_singleton_iff.2 ((chainYield_cSeq_iff i).2 h)

/-! ### The cell counters

`checkers i` starts `i` cell counters, staggered: counter `j` waits `j` cycles before it starts
and `i - 1 - j` cycles after it has finished, so that all of them answer exactly one
synchronisation request per produced tape cell. -/

/-- The chain of one cell counter: a leading delay of `d` waiting cycles, the counter itself,
and a trailing delay of `e` waiting cycles. -/
def counterChain (Q Γ : Type) (d e : ℕ) : List (TMAct Q Γ ⊕ TMTask Q Γ) :=
  [Sum.inr (TMTask.waitN d), Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN e)]

lemma chainYield_waitN_zero : (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN 0)]
    ([] : List (TMAct Q Γ)) :=
  chainYield_waitN_iff.2 ⟨[], rfl, by simp, by simp⟩

lemma chainYield_waitN_add {c d : ℕ} {u v : List (TMAct Q Γ)}
    (hu : (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN c)] u)
    (hv : (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN d)] v) :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN (c + d))] (u ++ v) := by
  obtain ⟨ass₁, hlen₁, hall₁, rfl⟩ := chainYield_waitN_iff.1 hu
  obtain ⟨ass₂, hlen₂, hall₂, rfl⟩ := chainYield_waitN_iff.1 hv
  refine chainYield_waitN_iff.2 ⟨ass₁ ++ ass₂, by simp [hlen₁, hlen₂], ?_, by simp⟩
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · exact hall₁ l hl
  · exact hall₂ l hl

/-- A counter can be delayed further at the front. -/
lemma chainYield_counterChain_lead {c d e : ℕ} {l x : List (TMAct Q Γ)}
    (hl : (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN c)] l)
    (hx : (domainBod N w K).ChainYield (counterChain Q Γ d e) x) :
    (domainBod N w K).ChainYield (counterChain Q Γ (c + d) e) (l ++ x) := by
  rw [counterChain, show [Sum.inr (TMTask.waitN d), Sum.inr (TMTask.checkers 1),
    Sum.inr (TMTask.waitN e)] = [(Sum.inr (TMTask.waitN d) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN e)] from rfl,
    chainYield_append_iff] at hx
  obtain ⟨x₁, x₂, rfl, h₁, h₂⟩ := hx
  rw [counterChain, show [Sum.inr (TMTask.waitN (c + d)), Sum.inr (TMTask.checkers 1),
    Sum.inr (TMTask.waitN e)] = [(Sum.inr (TMTask.waitN (c + d)) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN e)] from rfl,
    chainYield_append_iff]
  exact ⟨l ++ x₁, x₂, by simp, chainYield_waitN_add hl h₁, h₂⟩

/-- A counter can be delayed further at the end. -/
lemma chainYield_counterChain_trail {c d e : ℕ} {l x : List (TMAct Q Γ)}
    (hx : (domainBod N w K).ChainYield (counterChain Q Γ d e) x)
    (hl : (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN c)] l) :
    (domainBod N w K).ChainYield (counterChain Q Γ d (e + c)) (x ++ l) := by
  rw [counterChain, show [Sum.inr (TMTask.waitN d), Sum.inr (TMTask.checkers 1),
    Sum.inr (TMTask.waitN e)] = [(Sum.inr (TMTask.waitN d) : TMAct Q Γ ⊕ TMTask Q Γ),
      Sum.inr (TMTask.checkers 1)] ++ [Sum.inr (TMTask.waitN e)] from rfl,
    chainYield_append_iff] at hx
  obtain ⟨x₁, x₂, rfl, h₁, h₂⟩ := hx
  rw [counterChain, show [Sum.inr (TMTask.waitN d), Sum.inr (TMTask.checkers 1),
    Sum.inr (TMTask.waitN (e + c))] = [(Sum.inr (TMTask.waitN d) : TMAct Q Γ ⊕ TMTask Q Γ),
      Sum.inr (TMTask.checkers 1)] ++ [Sum.inr (TMTask.waitN (e + c))] from rfl,
    chainYield_append_iff]
  exact ⟨x₁, x₂ ++ l, by simp, h₁, chainYield_waitN_add h₂ hl⟩

/-- The predicate that a list of runs realises a list of (lead, trail) pairs. -/
def CounterRuns (N : NTM Q Γ) (w : List Γ) (K : ℕ) (ps : List (ℕ × ℕ))
    (ass : List (List (TMAct Q Γ))) : Prop :=
  List.Forall₂ (fun p l => (domainBod N w K).ChainYield (counterChain Q Γ p.1 p.2) l) ps ass

lemma counterRuns_lead {c : ℕ} {ps : List (ℕ × ℕ)} {ass lss : List (List (TMAct Q Γ))}
    (hF : CounterRuns N w K ps ass) (hlen : lss.length = ass.length)
    (hall : ∀ l ∈ lss, (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN c)] l) :
    CounterRuns N w K (ps.map fun p => (c + p.1, p.2)) (List.zipWith (· ++ ·) lss ass) := by
  induction hF generalizing lss with
  | nil =>
      have : lss = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this
      exact List.Forall₂.nil
  | @cons p l ps' ass' hp hrec ih =>
      cases lss with
      | nil => simp at hlen
      | cons u lss' =>
          refine List.Forall₂.cons ?_ (ih (by simpa using hlen)
            (fun x hx => hall x (by simp [hx])))
          exact chainYield_counterChain_lead (hall u (by simp)) hp

lemma counterRuns_trail {c : ℕ} {ps : List (ℕ × ℕ)} {ass lss : List (List (TMAct Q Γ))}
    (hF : CounterRuns N w K ps ass) (hlen : lss.length = ass.length)
    (hall : ∀ l ∈ lss, (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN c)] l) :
    CounterRuns N w K (ps.map fun p => (p.1, p.2 + c)) (List.zipWith (· ++ ·) ass lss) := by
  induction hF generalizing lss with
  | nil =>
      have : lss = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this
      exact List.Forall₂.nil
  | @cons p l ps' ass' hp hrec ih =>
      cases lss with
      | nil => simp at hlen
      | cons u lss' =>
          refine List.Forall₂.cons ?_ (ih (by simpa using hlen)
            (fun x hx => hall x (by simp [hx])))
          exact chainYield_counterChain_trail hp (hall u (by simp))

lemma CounterRuns.length_eq {ps : List (ℕ × ℕ)} {ass : List (List (TMAct Q Γ))}
    (h : CounterRuns N w K ps ass) : ps.length = ass.length := List.Forall₂.length_eq h

lemma counterRuns_append {ps ps' : List (ℕ × ℕ)} {ass ass' : List (List (TMAct Q Γ))}
    (h : CounterRuns N w K ps ass) (h' : CounterRuns N w K ps' ass') :
    CounterRuns N w K (ps ++ ps') (ass ++ ass') := List.rel_append h h'

/-- **Every refinement of `checkers i` is an interleaving of `i` staggered cell counters**: the
`i` counters have leading and trailing delays `(j, i - 1 - j)` for `j = 0, …, i - 1`. -/
theorem chainYield_checkers_forward : ∀ (i : ℕ) {as : List (TMAct Q Γ)},
    (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers i)] as →
      ∃ (ps : List (ℕ × ℕ)) (ass : List (List (TMAct Q Γ))),
        ps.Perm ((List.range i).map fun j => (j, i - 1 - j)) ∧
          CounterRuns N w K ps ass ∧ InterleaveList ass as := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro as h
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · rw [chainYield_singleton_bod_iff] at h
      obtain ⟨ls, hls, hy⟩ := h
      have hls' : ls = [] := by simpa [bodiesFix, bodies] using hls
      subst hls'
      rw [gridYield_nil_iff] at hy
      subst hy
      exact ⟨[], [], by simp, List.Forall₂.nil, InterleaveList.nil⟩
    · refine ⟨[(0, 0)], [as], by simp, List.Forall₂.cons ?_ List.Forall₂.nil,
        InterleaveList.cons InterleaveList.nil (Interleave.nil_right as)⟩
      rw [counterChain, show [Sum.inr (TMTask.waitN 0), Sum.inr (TMTask.checkers 1),
        Sum.inr (TMTask.waitN 0)] = [(Sum.inr (TMTask.waitN 0) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
          ([Sum.inr (TMTask.checkers 1)] ++ [Sum.inr (TMTask.waitN 0)]) from rfl,
        chainYield_append_iff]
      exact ⟨[], as, by simp, chainYield_waitN_zero, chainYield_append_iff.2
        ⟨as, [], by simp, h, chainYield_waitN_zero⟩⟩
  · have hhalf : i / 2 < i := Nat.div_lt_self (by omega) (by omega)
    have hpred : i - 1 < i := by omega
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    rcases Nat.even_or_odd i with hev | hod
    · have he : i % 2 = 0 := Nat.even_iff.1 hev
      have hls' : ls = [[Sum.inr (TMTask.cPar (TMTask.waitN (i / 2)) (i / 2)),
          Sum.inr (TMTask.checkers (i / 2))],
        [Sum.inr (TMTask.checkers (i / 2)),
          Sum.inr (TMTask.cPar (TMTask.waitN (i / 2)) (i / 2))]] := by
        have h0 : ¬ (i = 0) := by omega
        have h1 : ¬ (i = 1) := by omega
        simpa [bodiesFix, bodies, h0, h1, he] using hls
      subst hls'
      rw [gridYield_cons_iff] at hy
      obtain ⟨asA, asB, hA, hB, hint⟩ := hy
      rw [gridYield_singleton_iff] at hB
      -- the group whose counters are delayed at the front
      rw [show [Sum.inr (TMTask.cPar (TMTask.waitN (i / 2)) (i / 2)),
          Sum.inr (TMTask.checkers (i / 2))] =
        [(Sum.inr (TMTask.cPar (TMTask.waitN (i / 2)) (i / 2)) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
          [Sum.inr (TMTask.checkers (i / 2))] from rfl, chainYield_append_iff] at hA
      obtain ⟨u, v, rfl, hu, hv⟩ := hA
      obtain ⟨lss, hlenl, halll, hintl⟩ := (chainYield_cPar_iff (i / 2)).1 hu
      obtain ⟨ps', ass', hperm', hruns', hint'⟩ := ih _ hhalf hv
      -- the group whose counters are delayed at the end
      rw [show [Sum.inr (TMTask.checkers (i / 2)),
          Sum.inr (TMTask.cPar (TMTask.waitN (i / 2)) (i / 2))] =
        [(Sum.inr (TMTask.checkers (i / 2)) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
          [Sum.inr (TMTask.cPar (TMTask.waitN (i / 2)) (i / 2))] from rfl,
        chainYield_append_iff] at hB
      obtain ⟨v', u', rfl, hv', hu'⟩ := hB
      obtain ⟨lss', hlenl', halll', hintl'⟩ := (chainYield_cPar_iff (i / 2)).1 hu'
      obtain ⟨ps'', ass'', hperm'', hruns'', hint''⟩ := ih _ hhalf hv'
      have hlenA : lss.length = ass'.length := by
        rw [hlenl, ← hruns'.length_eq, hperm'.length_eq]; simp
      have hlenB : lss'.length = ass''.length := by
        rw [hlenl', ← hruns''.length_eq, hperm''.length_eq]; simp
      refine ⟨(ps''.map fun p => (p.1, p.2 + i / 2)) ++ (ps'.map fun p => (i / 2 + p.1, p.2)),
        List.zipWith (· ++ ·) ass'' lss' ++ List.zipWith (· ++ ·) lss ass', ?_, ?_, ?_⟩
      · -- the (lead, trail) pairs are the expected ones
        have hrange : List.range i =
            List.range (i / 2) ++ (List.range (i / 2)).map (i / 2 + ·) := by
          rw [← List.range_add]
          congr 1
          omega
        have hsplit : ((List.range i).map fun j => (j, i - 1 - j)) =
            ((List.range (i / 2)).map fun j => (j, i - 1 - j)) ++
              ((List.range (i / 2)).map fun j => (i / 2 + j, i - 1 - (i / 2 + j))) := by
          rw [hrange, List.map_append, List.map_map]
          rfl
        rw [hsplit]
        refine List.Perm.append ?_ ?_
        · refine ((hperm''.map _).trans ?_)
          rw [List.map_map]
          refine List.Perm.of_eq (List.map_congr_left ?_)
          intro j hj
          rw [List.mem_range] at hj
          have : i / 2 - 1 - j + i / 2 = i - 1 - j := by omega
          simp [this]
        · refine ((hperm'.map _).trans ?_)
          rw [List.map_map]
          refine List.Perm.of_eq (List.map_congr_left ?_)
          intro j hj
          rw [List.mem_range] at hj
          have : i / 2 - 1 - j = i - 1 - (i / 2 + j) := by omega
          simp [this]
      · exact counterRuns_append (counterRuns_trail hruns'' hlenB halll')
          (counterRuns_lead hruns' hlenA halll)
      · exact InterleaveList.append
          (interleaveList_append_pointwise hint'' hintl' hlenB.symm)
          (interleaveList_append_pointwise hintl hint' hlenA) hint.symm
    · have ho : i % 2 = 1 := Nat.odd_iff.1 hod
      have hls' : ls = [[Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)),
          Sum.inr (TMTask.checkers (i - 1))],
        [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN (i - 1))]] := by
        have h0 : ¬ (i = 0) := by omega
        have h1 : ¬ (i = 1) := by omega
        have he : ¬ (i % 2 = 0) := by omega
        simpa [bodiesFix, bodies, h0, h1, he] using hls
      subst hls'
      rw [gridYield_cons_iff] at hy
      obtain ⟨asA, asB, hA, hB, hint⟩ := hy
      rw [gridYield_singleton_iff] at hB
      rw [show [Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)),
          Sum.inr (TMTask.checkers (i - 1))] =
        [(Sum.inr (TMTask.cPar (TMTask.waitN 1) (i - 1)) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
          [Sum.inr (TMTask.checkers (i - 1))] from rfl, chainYield_append_iff] at hA
      obtain ⟨u, v, rfl, hu, hv⟩ := hA
      obtain ⟨lss, hlenl, halll, hintl⟩ := (chainYield_cPar_iff (i - 1)).1 hu
      obtain ⟨ps', ass', hperm', hruns', hint'⟩ := ih _ hpred hv
      rw [show [Sum.inr (TMTask.checkers 1), Sum.inr (TMTask.waitN (i - 1))] =
        [(Sum.inr (TMTask.checkers 1) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
          [Sum.inr (TMTask.waitN (i - 1))] from rfl, chainYield_append_iff] at hB
      obtain ⟨x, l, rfl, hx, hlast⟩ := hB
      have hlenA : lss.length = ass'.length := by
        rw [hlenl, ← hruns'.length_eq, hperm'.length_eq]; simp
      have hlast' : (domainBod N w K).ChainYield (counterChain Q Γ 0 (i - 1)) (x ++ l) := by
        rw [counterChain, show [Sum.inr (TMTask.waitN 0), Sum.inr (TMTask.checkers 1),
          Sum.inr (TMTask.waitN (i - 1))] =
            [(Sum.inr (TMTask.waitN 0) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
              ([Sum.inr (TMTask.checkers 1)] ++ [Sum.inr (TMTask.waitN (i - 1))]) from rfl,
          chainYield_append_iff]
        exact ⟨[], x ++ l, by simp, chainYield_waitN_zero,
          chainYield_append_iff.2 ⟨x, l, rfl, hx, hlast⟩⟩
      refine ⟨(0, i - 1) :: (ps'.map fun p => (1 + p.1, p.2)),
        (x ++ l) :: List.zipWith (· ++ ·) lss ass', ?_,
        List.Forall₂.cons hlast' (counterRuns_lead hruns' hlenA halll), ?_⟩
      · have hsplit : ((List.range i).map fun j => (j, i - 1 - j)) =
            (0, i - 1) :: ((List.range (i - 1)).map fun j => (1 + j, i - 1 - (1 + j))) := by
          rw [show i = 1 + (i - 1) by omega, List.range_add]
          simp [Function.comp_def]
        rw [hsplit]
        refine List.Perm.cons _ (((hperm'.map _).trans ?_))
        rw [List.map_map]
        refine List.Perm.of_eq (List.map_congr_left ?_)
        intro j hj
        rw [List.mem_range] at hj
        have : i - 1 - 1 - j = i - 1 - (1 + j) := by omega
        simp [this]
      · refine InterleaveList.append (InterleaveList.cons InterleaveList.nil
          (Interleave.nil_right (x ++ l))) ?_ hint.symm
        exact interleaveList_append_pointwise hintl hint' hlenA

/-! ### Transfer to the repaired domain -/

/-- Adding methods can only add derivations. -/
lemma stepsN_mono {M M' : Set (Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ))} (hsub : M ⊆ M')
    {n : ℕ} {tn tn' : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)} (h : StepsN M n tn tn') :
    StepsN M' n tn tn' := by
  induction h with
  | refl tn => exact StepsN.refl tn
  | tail _ hs ih =>
      obtain ⟨t, m, hm, ht, hα, rest⟩ := hs
      exact StepsN.tail ih ⟨t, m, hsub hm, ht, hα, rest⟩

/-- Adding methods can only add refinements. -/
lemma netYieldN_mono {D D' : Domain (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)}
    (hsub : D.methods ⊆ D'.methods) {n : ℕ} {tn : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)}
    {as : List (TMAct Q Γ)} (h : D.NetYieldN n tn as) : D'.NetYieldN n tn as := by
  obtain ⟨tn', hsteps, hprim, l, hlin, has⟩ := h
  exact ⟨tn', stepsN_mono hsub hsteps, hprim, l, hlin, has⟩

/-- **Every refinement of the auxiliary domain is one of the repaired domain.** -/
theorem netYield_fix_of_bod {tn : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)}
    {as : List (TMAct Q Γ)} (h : (domainBod N w K).NetYield tn as) :
    (domainFix N w K).NetYield tn as := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, netYieldN_mono methods_bod_subset hn⟩

/-- **A chain refinement of the auxiliary domain is a refinement of the task sequence in the
repaired domain.** -/
theorem netYield_seq_fix_of_chainYield_bod {xs : List (TMAct Q Γ ⊕ TMTask Q Γ)}
    {as : List (TMAct Q Γ)} (h : (domainBod N w K).ChainYield xs as) :
    (domainFix N w K).NetYield (TaskNetwork.seq xs) as :=
  netYield_fix_of_bod ((netYield_seq_iff methods_grid_bod).2 h)

end TMEnc

end HTN
