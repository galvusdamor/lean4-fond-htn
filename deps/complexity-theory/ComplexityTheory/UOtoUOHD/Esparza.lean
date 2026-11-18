import Mathlib

/-!
# Reordering decompositions of an unordered (commutative) grammar

A finite multiset `P` of *productions* `i` (each with a head `h i` and a multiset `B i` of
nonterminals in its body) can be fired, in some order, starting from the multiset `S` of
nonterminals, consuming every production exactly once, as soon as

* **balance** (`Bal`): every nonterminal is consumed as often as it is available,
  `P.map h = S + Σ_{i ∈ P} B i`, and
* **connectivity** (`Conn`): the head of every production of `P` is reachable from `S` in the
  graph whose edges are the productions of `P` (`h i → b` for `b ∈ B i`).

This is the characterisation of the Parikh images of commutative context-free derivations
(Esparza's theorem on communication-free Petri nets), in the special form needed here:
`HTN.Esparza.exists_fire`.
-/

namespace HTN

namespace Esparza

variable {ι : Type*} (h : ι → ℕ) (B : ι → Multiset ℕ)

/-- Reachability from the multiset `S` along the productions of `P`. -/
inductive Reach (S : Multiset ℕ) (P : Multiset ι) : ℕ → Prop
  | base {c : ℕ} : c ∈ S → Reach S P c
  | step {j : ι} {c : ℕ} : j ∈ P → Reach S P (h j) → c ∈ B j → Reach S P c

/-- Connectivity: every head of `P` is reachable from `S`. -/
def Conn (S : Multiset ℕ) (P : Multiset ι) : Prop := ∀ j ∈ P, Reach h B S P (h j)

/-- Balance: the heads of `P` are exactly the available nonterminals. -/
def Bal (S : Multiset ℕ) (P : Multiset ι) : Prop := P.map h = S + (P.map B).sum

/-- A valid firing sequence from `S`. -/
inductive Fire : Multiset ℕ → List ι → Prop
  | nil (S : Multiset ℕ) : Fire S []
  | cons {S : Multiset ℕ} {i : ι} {l : List ι} :
      h i ∈ S → Fire (S.erase (h i) + B i) l → Fire S (i :: l)

variable {h B}

theorem Reach.induct {S : Multiset ℕ} {P : Multiset ι} (Q : ℕ → Prop) (hS : ∀ x ∈ S, Q x)
    (hP : ∀ j ∈ P, Q (h j) → ∀ b ∈ B j, Q b) {c : ℕ} (hc : Reach h B S P c) : Q c := by
  induction hc with
  | base hx => exact hS _ hx
  | step hj _ hb ih => exact hP _ hj ih _ hb

theorem Reach.mono {S S' : Multiset ℕ} {P P' : Multiset ι} (hS : ∀ x ∈ S, x ∈ S')
    (hP : ∀ j ∈ P, j ∈ P') {c : ℕ} (hc : Reach h B S P c) : Reach h B S' P' c :=
  hc.induct _ (fun x hx => Reach.base (hS x hx))
    (fun j hj hr _ hb => Reach.step (hP j hj) hr hb)

theorem Reach.exists_root {S : Multiset ℕ} {P : Multiset ι} {c : ℕ} (hc : Reach h B S P c) :
    (∃ j ∈ P, h j = c) → ∃ j ∈ P, h j ∈ S := by
  induction hc with
  | base hx => rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, hx⟩
  | @step j' c hj' _ _ ih => intro _; exact ih ⟨j', hj', rfl⟩

/-- Splitting a path at its last visit of `c₀`. -/
theorem Reach.split {S : Multiset ℕ} {P : Multiset ι} (c₀ : ℕ) {c : ℕ}
    (hc : Reach h B S P c) :
    c = c₀ ∨ Reach h B (S.filter (· ≠ c₀)) (P.filter (fun j => h j ≠ c₀)) c ∨
      ∃ i ∈ P, h i = c₀ ∧ ∃ b ∈ B i, Reach h B {b} (P.filter (fun j => h j ≠ c₀)) c := by
  induction hc with
  | @base c hx =>
    by_cases hcc : c = c₀
    · exact Or.inl hcc
    · exact Or.inr (Or.inl (Reach.base (Multiset.mem_filter.2 ⟨hx, hcc⟩)))
  | @step j c hj _ hb ih =>
    by_cases hjc : h j = c₀
    · exact Or.inr (Or.inr ⟨j, hj, hjc, c, hb, Reach.base (Multiset.mem_singleton_self _)⟩)
    · have hjP : j ∈ P.filter (fun j => h j ≠ c₀) := Multiset.mem_filter.2 ⟨hj, hjc⟩
      rcases ih with h1 | h1 | ⟨i, hi, hic, b, hb', h1⟩
      · exact absurd h1 hjc
      · exact Or.inr (Or.inl (Reach.step hjP h1 hb))
      · exact Or.inr (Or.inr ⟨i, hi, hic, b, hb', Reach.step hjP h1 hb⟩)

variable [DecidableEq ι]

theorem mem_of_not_mem_erase {P : Multiset ι} {i j : ι} (hj : j ∈ P) (hj' : j ∉ P.erase i) :
    j = i := by
  by_contra hne
  exact hj' ((Multiset.mem_erase_of_ne hne).2 hj)

/-- Connectivity after firing `i` (with head `c₀`), once `c₀` is still reachable. -/
theorem conn_erase {S S' : Multiset ℕ} {P : Multiset ι} {i : ι} {c₀ : ℕ}
    (hc0 : Reach h B S' (P.erase i) c₀) (hS : ∀ x ∈ S, x ≠ c₀ → x ∈ S')
    (hB : ∀ b ∈ B i, b ∈ S') (hconn : Conn h B S P) : Conn h B S' (P.erase i) := by
  intro j hj
  refine (hconn j (Multiset.mem_of_mem_erase hj)).induct (Reach h B S' (P.erase i)) ?_ ?_
  · intro x hx
    by_cases hxc : x = c₀
    · rw [hxc]; exact hc0
    · exact Reach.base (hS x hx hxc)
  · intro j' hj' hr b hb
    by_cases hj'P : j' ∈ P.erase i
    · exact Reach.step hj'P hr hb
    · rw [mem_of_not_mem_erase hj' hj'P] at hb
      exact Reach.base (hB b hb)

theorem bal_erase {S : Multiset ℕ} {P : Multiset ι} {i : ι} (hb : Bal h B S P) (hi : i ∈ P)
    (hS : h i ∈ S) : Bal h B (S.erase (h i) + B i) (P.erase i) := by
  unfold Bal at hb ⊢
  rw [← Multiset.cons_erase hi, Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons] at hb
  conv_rhs at hb => rw [← Multiset.cons_erase hS]
  rw [Multiset.cons_add, ← add_assoc] at hb
  exact (Multiset.cons_inj_right _).1 hb

/-- **The key step**: some production whose head is available can be fired so that
connectivity is kept. -/
theorem exists_step {S : Multiset ℕ} {P : Multiset ι} (hP : P ≠ 0) (hb : Bal h B S P)
    (hconn : Conn h B S P) :
    ∃ i ∈ P, h i ∈ S ∧ Conn h B (S.erase (h i) + B i) (P.erase i) := by
  obtain ⟨i₀, hi₀⟩ := Multiset.exists_mem_of_ne_zero hP
  obtain ⟨j₀, hj₀, hc0S⟩ := (hconn i₀ hi₀).exists_root ⟨i₀, hi₀, rfl⟩
  set c₀ := h j₀ with hc₀
  by_cases hcase : ∃ i ∈ P, h i = c₀ ∧
      (c₀ ∈ S.erase c₀ + B i ∨ ∀ j ∈ P.erase i, h j ≠ c₀)
  · obtain ⟨i, hi, hic, hor⟩ := hcase
    refine ⟨i, hi, by rw [hic]; exact hc0S, ?_⟩
    rw [hic]
    have hS : ∀ x ∈ S, x ≠ c₀ → x ∈ S.erase c₀ + B i := fun x hx hxc =>
      Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne hxc).2 hx))
    have hB : ∀ b ∈ B i, b ∈ S.erase c₀ + B i := fun b hb' => Multiset.mem_add.2 (Or.inr hb')
    rcases hor with hmem | hnone
    · exact conn_erase (Reach.base hmem) hS hB hconn
    · intro j hj
      have hQ := (hconn j (Multiset.mem_of_mem_erase hj)).induct
        (fun x => Reach h B (S.erase c₀ + B i) (P.erase i) x ∨ x = c₀) ?_ ?_
      · rcases hQ with hQ | hQ
        · exact hQ
        · exact absurd hQ (hnone j hj)
      · intro x hx
        by_cases hxc : x = c₀
        · exact Or.inr hxc
        · exact Or.inl (Reach.base (hS x hx hxc))
      · intro j' hj' hr b hb'
        by_cases hj'P : j' ∈ P.erase i
        · rcases hr with hr | hr
          · exact Or.inl (Reach.step hj'P hr hb')
          · exact absurd hr (hnone j' hj'P)
        · rw [mem_of_not_mem_erase hj' hj'P] at hb'
          exact Or.inl (Reach.base (hB b hb'))
  · push_neg at hcase
    obtain ⟨hn0, j₁, hj₁, hj₁c⟩ := hcase j₀ hj₀ rfl
    have hnS : c₀ ∉ S.erase c₀ := fun h' => hn0 (Multiset.mem_add.2 (Or.inl h'))
    have hcS : S.count c₀ = 1 := by
      have h1 := Multiset.count_pos.2 hc0S
      have h2 : (S.erase c₀).count c₀ = 0 := Multiset.count_eq_zero.2 hnS
      rw [Multiset.count_erase_self] at h2
      omega
    have hcP : 2 ≤ (P.map h).count c₀ := by
      rw [← Multiset.cons_erase hj₀, ← Multiset.cons_erase hj₁, Multiset.map_cons,
        Multiset.map_cons, hj₁c, ← hc₀, Multiset.count_cons_self, Multiset.count_cons_self]
      omega
    have hcB : c₀ ∈ (P.map B).sum := by
      have := congrArg (Multiset.count c₀) hb
      rw [Multiset.count_add, hcS] at this
      exact Multiset.count_pos.1 (by omega)
    rw [← Multiset.join, Multiset.mem_join] at hcB
    obtain ⟨Br, hBr, hc0r⟩ := hcB
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hBr
    have hrc : h r ≠ c₀ := by
      intro hrc
      exact (hcase r hr hrc).1 (Multiset.mem_add.2 (Or.inr hc0r))
    have key : ∀ i ∈ P, h i = c₀ → ∀ T : Multiset ℕ, (∀ x ∈ T, x ∈ S.erase c₀ + B i) →
        Reach h B T (P.filter (fun j => h j ≠ c₀)) (h r) →
        Conn h B (S.erase c₀ + B i) (P.erase i) := by
      intro i hi hic T hT hR
      have hne : ∀ j, h j ≠ c₀ → j ≠ i := fun j hj hji => hj (by rw [hji, hic])
      have hR' : Reach h B (S.erase c₀ + B i) (P.erase i) (h r) :=
        hR.mono hT (fun j hj => by
          obtain ⟨hjP, hjc⟩ := Multiset.mem_filter.1 hj
          exact (Multiset.mem_erase_of_ne (hne j hjc)).2 hjP)
      have hc0 : Reach h B (S.erase c₀ + B i) (P.erase i) c₀ :=
        Reach.step ((Multiset.mem_erase_of_ne (hne r hrc)).2 hr) hR' hc0r
      exact conn_erase hc0
        (fun x hx hxc => Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne hxc).2 hx)))
        (fun b hb' => Multiset.mem_add.2 (Or.inr hb')) hconn
    rcases (hconn r hr).split c₀ with h1 | h1 | ⟨i, hi, hic, b, hb', h1⟩
    · exact absurd h1 hrc
    · refine ⟨j₀, hj₀, hc0S, ?_⟩
      refine key j₀ hj₀ rfl _ (fun x hx => ?_) h1
      obtain ⟨hxS, hxc⟩ := Multiset.mem_filter.1 hx
      exact Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne hxc).2 hxS))
    · refine ⟨i, hi, by rw [hic]; exact hc0S, ?_⟩
      rw [hic]
      refine key i hi hic _ (fun x hx => ?_) h1
      rw [Multiset.mem_singleton] at hx
      subst hx
      exact Multiset.mem_add.2 (Or.inr hb')

/-- **Esparza's reordering**: under balance and connectivity, all productions of `P` can be
fired from `S` in some order. -/
theorem exists_fire : ∀ (n : ℕ) (P : Multiset ι) (S : Multiset ℕ), Multiset.card P = n →
    Bal h B S P → Conn h B S P → ∃ l : List ι, (l : Multiset ι) = P ∧ Fire h B S l
  | 0, P, S, hn, _, _ => ⟨[], by rw [Multiset.card_eq_zero.1 hn]; rfl, Fire.nil S⟩
  | n + 1, P, S, hn, hb, hconn => by
    have hP : P ≠ 0 := fun h0 => by rw [h0] at hn; simp at hn
    obtain ⟨i, hi, hS, hconn'⟩ := exists_step hP hb hconn
    have hn' : Multiset.card (P.erase i) = n := by
      rw [Multiset.card_erase_of_mem hi, hn]; rfl
    obtain ⟨l, hl, hf⟩ := exists_fire n (P.erase i) _ hn' (bal_erase hb hi hS) hconn'
    exact ⟨i :: l, by rw [← Multiset.cons_coe, hl, Multiset.cons_erase hi], Fire.cons hS hf⟩

end Esparza

end HTN
