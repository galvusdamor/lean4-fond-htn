import HtnComplexity.SpaceEnc.CompPlan
import HtnComplexity.SpaceEnc.Yield
import HtnPlanning.Interleave.InterleaveSplit
/-!
# Completeness of the encoding: the planned words are refinements

The converse of `HtnComplexity/SpaceEnc/Yield.lean`: chain words with valid chain data,
blocks of `2 ^ m` chain words and a head move, loops of such blocks and finish words are
refinements of the corresponding compound tasks; hence `boot` followed by a three-process
interleaving (`HTN.SpaceEnc.Gen`) of good blocks and a finish word refines the root
(`HTN.SpaceEnc.chain_root_of_gen`).
-/

namespace HTN

namespace SpaceEnc

open TM Domain

variable {α : Type*}

theorem interleaveList_append_inv : ∀ {L₁ L₂ : List (List α)} {z : List α},
    InterleaveList (L₁ ++ L₂) z →
      ∃ z₁ z₂, InterleaveList L₁ z₁ ∧ InterleaveList L₂ z₂ ∧ Interleave z₁ z₂ z
  | [], _, z, h => ⟨[], z, InterleaveList.nil, h, Interleave.nil_left z⟩
  | a :: L₁, L₂, z, h => by
    obtain ⟨bs, hrest, hint⟩ := InterleaveList.cons_inv h
    obtain ⟨z₁, z₂, h₁, h₂, h₃⟩ := interleaveList_append_inv hrest
    obtain ⟨x, hx₁, hx₂⟩ := Interleave.assoc' h₃ hint
    exact ⟨x, z₂, InterleaveList.cons h₁ hx₁, h₂, hx₂⟩

theorem interleaveList_singleton_inv {v z : List α} (h : InterleaveList [v] z) : z = v := by
  obtain ⟨bs, hrest, hint⟩ := InterleaveList.cons_inv h
  rw [InterleaveList.eq_nil_of_nil_components hrest] at hint
  exact hint.eq_of_nil_right

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] {m n' : ℕ} {N : NTM Q Γ}

section Domain

variable {F : Type} {D : Domain F (Act Q Γ) Cmp (ℕ × ℕ)} (hD : D.methods = methodsOf m n' N)
include hD

theorem chain_of_body {c : Cmp} {ls : List (List (Act Q Γ ⊕ Cmp))} (hb : (c, ls) ∈ bodies m n' N)
    {z : List (Act Q Γ)} (hy : D.GridYield ls z) : D.ChainYield [cT c] z :=
  chainYield_singleton_inr_iff.2 ⟨ls, ⟨⟨c, TaskNetwork.grid ls⟩, by rw [hD]; exact ⟨_, hb, rfl⟩,
    rfl, rfl⟩, hy⟩

theorem chain_of_body1 {c : Cmp} {l : List (Act Q Γ ⊕ Cmp)} (hb : (c, [l]) ∈ bodies m n' N)
    {z : List (Act Q Γ)} (hy : D.ChainYield l z) : D.ChainYield [cT c] z :=
  chain_of_body hD hb (gridYield_singleton_iff.2 hy)

omit hD [Fintype Q] [Fintype Γ] in
theorem chain_acts : ∀ (as : List (Act Q Γ)), D.ChainYield (as.map aT) as
  | [] => chainYield_nil_iff.2 rfl
  | _ :: as => chainYield_cons_inl_iff.2 ⟨as, rfl, chain_acts as⟩

theorem yield_incT_of {p : Bool} {a : Act Q Γ} (ha : (∃ k < m, a = .inc p k) ∨ a = .wrap p) :
    D.ChainYield [cT (.incT p)] [a] := by
  refine chain_of_body1 hD (l := [aT a]) ?_ (chain_acts [a])
  rcases ha with ⟨k, hk, rfl⟩ | rfl
  · simp [bodies, bodiesP, hk]
  · simp [bodies, bodiesP]

omit hD [Fintype Q] [Fintype Γ] in
theorem chain_cons_of {x : Act Q Γ ⊕ Cmp} {xs : List (Act Q Γ ⊕ Cmp)} {z₁ z₂ : List (Act Q Γ)}
    (h₁ : D.ChainYield [x] z₁) (h₂ : D.ChainYield xs z₂) : D.ChainYield (x :: xs) (z₁ ++ z₂) :=
  chainYield_append_iff.2 ⟨z₁, z₂, rfl, h₁, h₂⟩

omit hD [Fintype Q] [Fintype Γ] in
theorem chain_act_of (a : Act Q Γ) : D.ChainYield [aT a] [a] := chain_acts [a]

theorem yield_core_of {p : Bool} {cd : CD Q Γ} (hv : ValidCD m n' N p cd) :
    D.ChainYield [cT (.core p)] [cd.core, cd.incw, .rv p cd.val] := by
  obtain ⟨-, hc, hi⟩ := hv
  have hrest : D.ChainYield [aT cd.core, cT (.incT p), aT (.rv p cd.val)]
      ([cd.core] ++ ([cd.incw] ++ [.rv p cd.val])) :=
    chain_cons_of (chain_act_of _) (chain_cons_of (yield_incT_of hD hi) (chain_act_of _))
  refine chain_of_body1 hD ?_ hrest
  rcases hc with ⟨g, h1, h2⟩ | ⟨d, hd, h1, h2⟩
  · rw [h1, h2]; simp [bodies, bodiesP]
  · rw [h1, h2]
    simp only [bodies, bodiesP]
    cases p <;> simp [hd]

theorem yield_rd0_of {rd : List (Act Q Γ)}
    (h : rd = [] ∨ rd = [.rblank] ∨ ∃ i b, i < n' ∧ rd = [.ri i b]) :
    D.ChainYield [cT .rd0] rd := by
  rcases h with rfl | rfl | ⟨i, b, hi, rfl⟩
  · exact chain_of_body hD (ls := []) (by simp [bodies]) (gridYield_nil_iff.2 rfl)
  · exact chain_of_body1 hD (by simp [bodies]) (chain_act_of _)
  · refine chain_of_body1 hD ?_ (chain_act_of _)
    cases b <;> simp [bodies, hi]

theorem yield_bit_top_of {p : Bool} {cd : CD Q Γ} (hv : ValidCD m n' N p cd) :
    D.ChainYield [cT (.bit p m)] (bitL m p m cd) := by
  rw [bitL_self]
  unfold midL
  rcases hv.1 with hrd | ⟨rfl, hrd⟩
  · rw [hrd, List.nil_append]
    cases p
    · exact chain_of_body1 hD (by simp [bodies, bodiesP]) (yield_core_of hD hv)
    · refine chain_of_body1 hD (by simp [bodies, bodiesP])
        (chain_cons_of (z₁ := []) (yield_rd0_of hD (Or.inl rfl)) (yield_core_of hD hv))
  · exact chain_of_body1 hD (by simp [bodies, bodiesP])
      (chain_cons_of (yield_rd0_of hD (Or.inr hrd)) (yield_core_of hD hv))

theorem yield_bit_of {p : Bool} : ∀ j k : ℕ, k + j = m → ∀ cd : CD Q Γ, ValidCD m n' N p cd →
    D.ChainYield [cT (.bit p k)] (bitL m p k cd) := by
  intro j
  induction j with
  | zero =>
    intro k hk cd hv
    rw [Nat.add_zero] at hk
    subst hk
    exact yield_bit_top_of hD hv
  | succ j ih =>
    intro k hk cd hv
    have hkm : k < m := by omega
    rw [bitL_of_lt p hkm, List.cons_append]
    refine chain_of_body1 hD ?_ (chainYield_cons_inl_iff.2 ⟨_, rfl,
      chain_cons_of (ih (k + 1) (by omega) cd hv) (chain_act_of _)⟩)
    cases cd.x k <;> cases cd.e k <;> simp [bodies, bodiesP, hkm]

theorem yield_tree_of {p : Bool} : ∀ k : ℕ, k ≤ m → ∀ cds : List (CD Q Γ), cds.length = 2 ^ k →
    (∀ cd ∈ cds, ValidCD m n' N p cd) → ∀ z : List (Act Q Γ),
      InterleaveList (cds.map (chainW m p)) z → D.ChainYield [cT (.tree p k)] z := by
  intro k
  induction k with
  | zero =>
    intro _ cds hlen hv z hz
    obtain ⟨cd, rfl⟩ := List.length_eq_one_iff.1 hlen
    rw [List.map_singleton] at hz
    rw [interleaveList_singleton_inv hz]
    exact chain_of_body1 hD (by simp [bodies, bodiesP]) (chainYield_cons_inl_iff.2 ⟨_, rfl,
      yield_bit_of hD m 0 (by omega) cd (hv cd (List.mem_singleton_self _))⟩)
  | succ k ih =>
    intro hk cds hlen hv z hz
    rw [← List.take_append_drop (2 ^ k) cds, List.map_append] at hz
    obtain ⟨z₁, z₂, h₁, h₂, hint⟩ := interleaveList_append_inv hz
    have hl1 : (cds.take (2 ^ k)).length = 2 ^ k := by
      rw [List.length_take, hlen, pow_succ]; omega
    have hl2 : (cds.drop (2 ^ k)).length = 2 ^ k := by
      rw [List.length_drop, hlen, pow_succ]; omega
    have y₁ := ih (by omega) _ hl1 (fun cd hcd => hv cd (List.mem_of_mem_take hcd)) z₁ h₁
    have y₂ := ih (by omega) _ hl2 (fun cd hcd => hv cd (List.mem_of_mem_drop hcd)) z₂ h₂
    refine chain_of_body hD (ls := [[cT (.tree p k)], [cT (.tree p k)]]) ?_
      (gridYield_cons_iff.2 ⟨z₁, z₂, y₁, gridYield_singleton_iff.2 y₂, hint⟩)
    have hkm : k < m := by omega
    simp [bodies, bodiesP, hkm]

/-- A block that the methods can produce: `2 ^ m` chain words with valid chain data and a head
move. -/
def GoodBlock (m n' : ℕ) (N : NTM Q Γ) (p : Bool) (bl : List (List (Act Q Γ))) : Prop :=
  ∃ (cds : List (CD Q Γ)) (h : Act Q Γ), cds.length = 2 ^ m ∧
    (∀ cd ∈ cds, ValidCD m n' N p cd) ∧ (Cmp.reT p, [[aT h]]) ∈ bodies m n' N ∧
      bl = cds.map (chainW m p) ++ [[h]]

theorem yield_block_of {p : Bool} {bl : List (List (Act Q Γ))} (hb : GoodBlock m n' N p bl)
    {z : List (Act Q Γ)} (hz : InterleaveList bl z) : D.ChainYield [cT (.block p)] z := by
  obtain ⟨cds, h, hlen, hv, hh, rfl⟩ := hb
  obtain ⟨z₁, z₂, h₁, h₂, hint⟩ := interleaveList_append_inv hz
  rw [interleaveList_singleton_inv h₂] at hint
  refine chain_of_body hD (ls := [[cT (.tree p m)], [cT (.reT p)]]) (by simp [bodies, bodiesP])
    (gridYield_cons_iff.2 ⟨z₁, [h], yield_tree_of hD m le_rfl cds hlen hv z₁ h₁,
      gridYield_singleton_iff.2 (chain_of_body1 hD hh (chain_act_of h)), hint⟩)

theorem yield_loop_of {p : Bool} : ∀ (bls : List (List (List (Act Q Γ)))) (z : List (Act Q Γ)),
    (∀ bl ∈ bls, GoodBlock m n' N p bl) → CS bls z → D.ChainYield [cT (.loop p)] z
  | [], z, _, hz => by
    rw [show z = [] from hz]
    exact chain_of_body hD (ls := []) (by simp [bodies, bodiesP]) (gridYield_nil_iff.2 rfl)
  | bl :: bls, _, hg, ⟨z₁, z₂, h₁, h₂, rfl⟩ =>
    chain_of_body1 hD (l := [cT (.block p), cT (.loop p)]) (by simp [bodies, bodiesP])
      (chain_cons_of (yield_block_of hD (hg bl (List.mem_cons_self ..)) h₁)
        (yield_loop_of bls z₂ (fun b hb => hg b (List.mem_cons_of_mem _ hb)) h₂))

theorem yield_drain_of : ∀ n : ℕ, D.ChainYield [cT .drainT] (List.replicate n (Act.drn : Act Q Γ))
  | 0 => chain_of_body hD (ls := []) (by simp [bodies]) (gridYield_nil_iff.2 rfl)
  | n + 1 => chain_of_body1 hD (l := [aT .drn, cT .drainT]) (by simp [bodies])
      (chainYield_cons_inl_iff.2 ⟨_, rfl, yield_drain_of n⟩)

theorem yield_finish_of {q : Q} (hq : q ∈ accL N) (n : ℕ) :
    D.ChainYield [cT .finish] (.fin q :: List.replicate n .drn) :=
  chain_of_body1 hD (l := [aT (.fin q), cT .drainT]) (by simp [bodies, hq])
    (chainYield_cons_inl_iff.2 ⟨_, rfl, yield_drain_of hD n⟩)

/-- **`boot` followed by a three-process interleaving of good blocks and a finish word refines
the root task.** -/
theorem chain_root_of_gen {bA bB : List (List (List (Act Q Γ)))} {q : Q} {n : ℕ}
    {z : List (Act Q Γ)} (hA : ∀ bl ∈ bA, GoodBlock m n' N true bl)
    (hB : ∀ bl ∈ bB, GoodBlock m n' N false bl) (hq : q ∈ accL N)
    (hgen : Gen bA bB (.fin q :: List.replicate n .drn) z) :
    D.ChainYield [cT .root] (.boot :: z) := by
  obtain ⟨zA, zB, zBF, hcA, hcB, h3, h4⟩ := hgen
  have hmain : D.ChainYield [cT .main] z :=
    chain_of_body hD (ls := [[cT (.loop true)], [cT (.loop false)], [cT .finish]])
      (by simp [bodies])
      (gridYield_cons_iff.2 ⟨zA, zBF, yield_loop_of hD bA zA hA hcA,
        gridYield_cons_iff.2 ⟨zB, _, yield_loop_of hD bB zB hB hcB,
          gridYield_singleton_iff.2 (yield_finish_of hD hq n), h3⟩, h4⟩)
  exact chain_of_body1 hD (l := [aT .boot, cT .main]) (by simp [bodies])
    (chainYield_cons_inl_iff.2 ⟨z, rfl, hmain⟩)

end Domain

end SpaceEnc

end HTN
