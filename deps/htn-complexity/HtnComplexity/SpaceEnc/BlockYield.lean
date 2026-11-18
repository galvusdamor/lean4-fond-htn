import HtnComplexity.SpaceEnc.Yield
/-!
# The refinements of the encoding, with the block structure

`HtnComplexity/SpaceEnc/Yield.lean` flattens the refinement of a loop into one interleaving
of words.  The soundness proof needs more: the iterations of a loop are *sequential*, so the
words of one block are all finished before the next block starts.  This file keeps that
structure:

* `HTN.SpaceEnc.IsHActP p h` — a head move action of parity `p`;
* `HTN.SpaceEnc.FreshBlock m n' N p bl` — the words of one iteration of the loop `p`: `2 ^ m`
  chain words of parity `p` (in some order) and one head move word of parity `p`;
* `HTN.SpaceEnc.netYield_prob_gen` — **every refinement of the initial task network** is `boot`
  followed by a word `z'` with `Gen bA bB φ z'`, the blocks of `bA` (resp. `bB`) fresh blocks of
  parity `true` (resp. `false`) and `φ` a finish word.
-/

namespace HTN

namespace SpaceEnc

open TM Domain

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] {m n' : ℕ} {N : NTM Q Γ}

/-- A head move action of parity `p`. -/
def IsHActP (p : Bool) (h : Act Q Γ) : Prop :=
  (∃ k, h = .hinc p k) ∨ (∃ k, h = .hdec p k) ∨ h = .hdec0 p ∨ h = .hstay p

variable (m n' N) in
/-- **A fresh block of parity `p`**: `2 ^ m` chain words of parity `p` followed by one head move
word of parity `p` (the order of the list is irrelevant, the words are interleaved). -/
def FreshBlock (p : Bool) (bl : List (List (Act Q Γ))) : Prop :=
  ∃ (cds : List (CD Q Γ)) (h : Act Q Γ), (∀ cd ∈ cds, ValidCD m n' N p cd) ∧
    cds.length = 2 ^ m ∧ IsHActP p h ∧ bl = cds.map (chainW m p) ++ [[h]]

theorem bodies_reT' {b : Cmp × List (List (Act Q Γ ⊕ Cmp))} (hb : b ∈ bodies m n' N) {p : Bool}
    (h1 : b.1 = .reT p) : ∃ h, IsHActP p h ∧ b.2 = [[aT h]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop (add norm unfold IsHActP)

section Domain

variable {F : Type} {D : Domain F (Act Q Γ) Cmp (ℕ × ℕ)} (hD : D.methods = methodsOf m n' N)
include hD

theorem yield_tree' {p : Bool} : ∀ k : ℕ, ∀ z : List (Act Q Γ),
    D.ChainYield [cT (.tree p k)] z →
    ∃ cds : List (CD Q Γ), (∀ cd ∈ cds, ValidCD m n' N p cd) ∧ cds.length = 2 ^ k ∧
      InterleaveList (cds.map (chainW m p)) z := by
  intro k
  induction k with
  | zero =>
    intro z h
    obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
    rw [bodies_tree0 hb h1] at hy
    obtain ⟨z', rfl, h3⟩ := chain_cons_act (gridYield_singleton_iff.1 hy)
    obtain ⟨cd, hv, rfl⟩ := yield_bit hD m 0 (by omega) z' h3
    refine ⟨[cd], by simpa using hv, rfl, ?_⟩
    exact InterleaveList.cons InterleaveList.nil (Interleave.nil_right _)
  | succ k ih =>
    intro z h
    obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
    rw [bodies_treeS hb h1] at hy
    obtain ⟨z₁, z₂, h₁, h₂, hi⟩ := grid_two hy
    obtain ⟨c₁, hv₁, hn₁, hl₁⟩ := ih z₁ h₁
    obtain ⟨c₂, hv₂, hn₂, hl₂⟩ := ih z₂ h₂
    refine ⟨c₁ ++ c₂, ?_, by simp [hn₁, hn₂, pow_succ]; ring, ?_⟩
    · intro cd hcd
      rcases List.mem_append.1 hcd with h' | h'
      · exact hv₁ cd h'
      · exact hv₂ cd h'
    · rw [List.map_append]
      exact hl₁.append hl₂ hi

theorem yield_block' {p : Bool} {z : List (Act Q Γ)} (h : D.ChainYield [cT (.block p)] z) :
    ∃ bl, FreshBlock m n' N p bl ∧ InterleaveList bl z := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  rw [bodies_block hb h1] at hy
  obtain ⟨z₁, z₂, h₁, h₂, hi⟩ := grid_two hy
  obtain ⟨cds, hv, hn, hl⟩ := yield_tree' hD m z₁ h₁
  obtain ⟨b', hb', h1', hy'⟩ := body_of_chain hD h₂
  obtain ⟨a, ha, h3⟩ := bodies_reT' hb' h1'
  rw [h3] at hy'
  have h4 := chain_act (gridYield_singleton_iff.1 hy')
  subst h4
  exact ⟨_, ⟨cds, a, hv, hn, ha, rfl⟩,
    hl.append (InterleaveList.cons InterleaveList.nil (Interleave.nil_right _)) hi⟩

theorem yield_loop' {p : Bool} : ∀ n : ℕ, ∀ z : List (Act Q Γ),
    D.ChainYieldN n [cT (.loop p)] z →
    ∃ bls : List (List (List (Act Q Γ))), (∀ bl ∈ bls, FreshBlock m n' N p bl) ∧ CS bls z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z h
    obtain ⟨b, hb, h1, k, hk, hy⟩ := body_of_chainN hD h
    rcases bodies_loop hb h1 with h2 | h2 <;> rw [h2] at hy
    · obtain ⟨n₁, n₂, as, bs, rfl, hc, hg, hi⟩ := gridYieldN_cons_iff.1 hy
      obtain ⟨rfl, rfl⟩ := gridYieldN_nil_iff.1 hg
      rw [hi.eq_of_nil_right]
      obtain ⟨k', n'', ls, bs', as', rfl, hm, hb', ht, rfl⟩ := chainYieldN_cons_inr_iff.1 hc
      obtain ⟨bl, hbl, hl⟩ := yield_block' hD (chainYield_singleton_inr_iff.2 ⟨ls, hm, k', hb'⟩)
      obtain ⟨bls, hv, hcs⟩ := ih n'' (by omega) as' ht
      refine ⟨bl :: bls, ?_, bs', as', hl, hcs, rfl⟩
      intro b' hb''
      rcases List.mem_cons.1 hb'' with rfl | h'
      · exact hbl
      · exact hv b' h'
    · obtain ⟨-, rfl⟩ := gridYieldN_nil_iff.1 hy
      exact ⟨[], by simp, rfl⟩

/-- **The refinements of the root task, with the block structure.** -/
theorem yield_root_gen {z : List (Act Q Γ)} (h : D.ChainYield [cT .root] z) :
    ∃ z' bA bB φ, z = .boot :: z' ∧ Gen bA bB φ z' ∧ (∀ bl ∈ bA, FreshBlock m n' N true bl) ∧
      (∀ bl ∈ bB, FreshBlock m n' N false bl) ∧ FinW N φ := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  rw [bodies_root hb h1] at hy
  obtain ⟨z', rfl, h3⟩ := chain_cons_act (gridYield_singleton_iff.1 hy)
  obtain ⟨b', hb', h1', hy'⟩ := body_of_chain hD h3
  rw [bodies_main hb' h1'] at hy'
  obtain ⟨zA, zBF, hA, hBF, hi⟩ := gridYield_cons_iff.1 hy'
  obtain ⟨zB, zF, hB, hF, hi'⟩ := grid_two hBF
  obtain ⟨nA, hA⟩ := hA
  obtain ⟨nB, hB⟩ := hB
  obtain ⟨bA, hvA, hcA⟩ := yield_loop' hD nA zA hA
  obtain ⟨bB, hvB, hcB⟩ := yield_loop' hD nB zB hB
  exact ⟨z', bA, bB, zF, rfl, ⟨zA, zB, zBF, hcA, hcB, hi', hi⟩, hvA, hvB, yield_finish hD hF⟩

end Domain

/-- **Every refinement of the initial task network of the encoding**, with the block
structure of the two loops. -/
theorem netYield_prob_gen (ι : Bool → Γ) (w : List Bool) {z : List (Act Q Γ)}
    (h : (prob m n' ι N w).domain.NetYield (prob m n' ι N w).tnI z) :
    ∃ z' bA bB φ, z = .boot :: z' ∧ Gen bA bB φ z' ∧ (∀ bl ∈ bA, FreshBlock m n' N true bl) ∧
      (∀ bl ∈ bB, FreshBlock m n' N false bl) ∧ FinW N φ := by
  have hD : (prob m n' ι N w).domain.methods = methodsOf m n' N := rfl
  have h' := (netYield_grid_iff (grid_of_methodsOf hD)).1 h
  exact yield_root_gen hD (gridYield_singleton_iff.1 h')

end SpaceEnc

end HTN
