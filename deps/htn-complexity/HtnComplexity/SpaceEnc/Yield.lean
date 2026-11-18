import HtnComplexity.SpaceEnc.Words
import HtnPlanning.SpaceEnc.Machine
import HtnPlanning.Interleave.NetYield
/-!
# The refinements of the encoding

Every refinement of the initial task network of `HTN.SpaceEnc.prob` is `boot` followed by an
interleaving of loop words (chain words and round end words, `HTN.SpaceEnc.LoopW`) and of at
least one finish word (`HTN.SpaceEnc.FinW`): `HTN.SpaceEnc.netYield_root`.  The block structure
of the loops is forgotten — the soundness proof does not need it.
-/

namespace HTN

namespace SpaceEnc

open TM Domain

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] {m n' : ℕ} {N : NTM Q Γ}

/-! ### The methods of each compound task -/

section Bodies

variable {b : Cmp × List (List (Act Q Γ ⊕ Cmp))} (hb : b ∈ bodies m n' N)
include hb

theorem bodies_root (h1 : b.1 = .root) : b.2 = [[aT .boot, cT .main]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_main (h1 : b.1 = .main) :
    b.2 = [[cT (.loop true)], [cT (.loop false)], [cT .finish]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_loop {p : Bool} (h1 : b.1 = .loop p) :
    b.2 = [[cT (.block p), cT (.loop p)]] ∨ b.2 = [] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_block {p : Bool} (h1 : b.1 = .block p) :
    b.2 = [[cT (.tree p m)], [cT (.reT p)]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_tree0 {p : Bool} (h1 : b.1 = .tree p 0) : b.2 = [[aT (.ws p), cT (.bit p 0)]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_treeS {p : Bool} {k : ℕ} (h1 : b.1 = .tree p (k + 1)) :
    b.2 = [[cT (.tree p k)], [cT (.tree p k)]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_bit {p : Bool} {k : ℕ} (h1 : b.1 = .bit p k) :
    (k < m ∧ ∃ x e, b.2 = [[aT (.wb p k x e), cT (.bit p (k + 1)), aT (.rb p k x)]]) ∨
      (k = m ∧ b.2 = if p then [[cT .rd0, cT (.core p)]] else [[cT (.core p)]]) := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_rd0 (h1 : b.1 = .rd0) :
    b.2 = [] ∨ b.2 = [[aT .rblank]] ∨ ∃ i b', i < n' ∧ b.2 = [[aT (.ri i b')]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_core {p : Bool} (h1 : b.1 = .core p) :
    (∃ g, b.2 = [[aT (.cp p g), cT (.incT p), aT (.rv p g)]]) ∨
      ∃ d ∈ transL N, b.2 = [[aT (.tr p d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2), cT (.incT p),
        aT (.rv p d.2.2.2.1)]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_incT {p : Bool} (h1 : b.1 = .incT p) :
    (∃ k < m, b.2 = [[aT (.inc p k)]]) ∨ b.2 = [[aT (.wrap p)]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

theorem bodies_reT {p : Bool} (h1 : b.1 = .reT p) : ∃ h, IsHAct h ∧ b.2 = [[aT h]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop (add norm unfold IsHAct)

theorem bodies_finish (h1 : b.1 = .finish) : ∃ q ∈ accL N, b.2 = [[aT (.fin q), cT .drainT]] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

end Bodies

/-! ### From compound tasks to methods -/

/-- The methods of the encoding. -/
def methodsOf (m n' : ℕ) (N : NTM Q Γ) : Set (Method (ℕ × ℕ) (Act Q Γ) Cmp) :=
  {mt | ∃ b ∈ bodies m n' N, mt = ⟨b.1, TaskNetwork.grid b.2⟩}

section Domain

variable {F : Type} {D : Domain F (Act Q Γ) Cmp (ℕ × ℕ)} (hD : D.methods = methodsOf m n' N)
include hD

theorem grid_of_methodsOf : ∀ mt ∈ D.methods, ∃ ls, mt.subtasks = TaskNetwork.grid ls := by
  rw [hD]
  rintro mt ⟨b, -, rfl⟩
  exact ⟨b.2, rfl⟩

theorem body_of_gridBodyN {c : Cmp} {ls : List (List (Act Q Γ ⊕ Cmp))} {n : ℕ} {z : List (Act Q Γ)}
    (h : D.GridBody c ls) (hy : D.GridYieldN n ls z) :
    ∃ b ∈ bodies m n' N, b.1 = c ∧ D.GridYieldN n b.2 z := by
  obtain ⟨mt, hmt, h1, h2⟩ := h
  have hmt' := hmt
  rw [hD] at hmt'
  obtain ⟨b, hb, rfl⟩ := hmt'
  refine ⟨b, hb, h1, ?_⟩
  exact (gridYieldN_congr (grid_of_methodsOf hD) h2).2 hy

theorem body_of_chainN {c : Cmp} {n : ℕ} {z : List (Act Q Γ)} (h : D.ChainYieldN n [cT c] z) :
    ∃ b ∈ bodies m n' N, b.1 = c ∧ ∃ k < n, D.GridYieldN k b.2 z := by
  obtain ⟨k, n0, ls, bs, as, rfl, hm, hb, ht, rfl⟩ := chainYieldN_cons_inr_iff.1 h
  obtain ⟨rfl, rfl⟩ := chainYieldN_nil_iff.1 ht
  obtain ⟨b, hb', h1, hy⟩ := body_of_gridBodyN hD hm hb
  exact ⟨b, hb', h1, k, by omega, by simpa using hy⟩

theorem body_of_chain {c : Cmp} {z : List (Act Q Γ)} (h : D.ChainYield [cT c] z) :
    ∃ b ∈ bodies m n' N, b.1 = c ∧ D.GridYield b.2 z := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨b, hb, h1, k, -, hk⟩ := body_of_chainN hD hn
  exact ⟨b, hb, h1, k, hk⟩

omit hD [Fintype Q] [Fintype Γ] in
theorem chain_cons_comp {c : Cmp} {xs : List (Act Q Γ ⊕ Cmp)} {z : List (Act Q Γ)}
    (h : D.ChainYield (cT c :: xs) z) :
    ∃ z₁ z₂, z = z₁ ++ z₂ ∧ D.ChainYield [cT c] z₁ ∧ D.ChainYield xs z₂ := by
  have h' : D.ChainYield ([cT c] ++ xs) z := h
  exact chainYield_append_iff.1 h'

omit hD [Fintype Q] [Fintype Γ] in
theorem chain_cons_act {a : Act Q Γ} {xs : List (Act Q Γ ⊕ Cmp)} {z : List (Act Q Γ)}
    (h : D.ChainYield (aT a :: xs) z) : ∃ z', z = a :: z' ∧ D.ChainYield xs z' :=
  chainYield_cons_inl_iff.1 h

omit hD [Fintype Q] [Fintype Γ] in
theorem chain_act {a : Act Q Γ} {z : List (Act Q Γ)} (h : D.ChainYield [aT a] z) : z = [a] := by
  obtain ⟨z', rfl, h'⟩ := chain_cons_act h
  rw [chainYield_nil_iff] at h'
  rw [h']

omit hD [Fintype Q] [Fintype Γ] in
theorem grid_two {l₁ l₂ : List (Act Q Γ ⊕ Cmp)} {z : List (Act Q Γ)} (h : D.GridYield [l₁, l₂] z) :
    ∃ z₁ z₂, D.ChainYield l₁ z₁ ∧ D.ChainYield l₂ z₂ ∧ Interleave z₁ z₂ z := by
  obtain ⟨z₁, z₂, h₁, h₂, hi⟩ := gridYield_cons_iff.1 h
  exact ⟨z₁, z₂, h₁, gridYield_singleton_iff.1 h₂, hi⟩

/-! ### The words -/

theorem yield_rd0 {z : List (Act Q Γ)} (h : D.ChainYield [cT .rd0] z) :
    z = [] ∨ z = [.rblank] ∨ ∃ i b, i < n' ∧ z = [.ri i b] := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  rcases bodies_rd0 hb h1 with h2 | h2 | ⟨i, b', hi, h2⟩ <;> rw [h2] at hy
  · exact Or.inl (gridYield_nil_iff.1 hy)
  · exact Or.inr (Or.inl (chain_act (gridYield_singleton_iff.1 hy)))
  · exact Or.inr (Or.inr ⟨i, b', hi, chain_act (gridYield_singleton_iff.1 hy)⟩)

theorem yield_incT {p : Bool} {z : List (Act Q Γ)} (h : D.ChainYield [cT (.incT p)] z) :
    ∃ a, ((∃ k < m, a = .inc p k) ∨ a = .wrap p) ∧ z = [a] := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  rcases bodies_incT hb h1 with ⟨k, hk, h2⟩ | h2 <;> rw [h2] at hy
  · exact ⟨_, Or.inl ⟨k, hk, rfl⟩, chain_act (gridYield_singleton_iff.1 hy)⟩
  · exact ⟨_, Or.inr rfl, chain_act (gridYield_singleton_iff.1 hy)⟩

theorem yield_core {p : Bool} {z : List (Act Q Γ)} (h : D.ChainYield [cT (.core p)] z) :
    ∃ core incw val, ((∃ g, core = .cp p g ∧ val = g) ∨
      (∃ d ∈ transL N, core = .tr p d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 ∧
        val = d.2.2.2.1)) ∧ ((∃ k < m, incw = .inc p k) ∨ incw = .wrap p) ∧
      z = [core, incw, .rv p val] := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  rcases bodies_core hb h1 with ⟨g, h2⟩ | ⟨d, hd, h2⟩ <;> rw [h2] at hy <;>
    have hy' := gridYield_singleton_iff.1 hy
  · obtain ⟨z', rfl, h3⟩ := chain_cons_act hy'
    obtain ⟨z₁, z₂, rfl, h4, h5⟩ := chain_cons_comp h3
    obtain ⟨a, ha, rfl⟩ := yield_incT hD h4
    rw [chain_act h5]
    exact ⟨_, a, g, Or.inl ⟨g, rfl, rfl⟩, ha, rfl⟩
  · obtain ⟨z', rfl, h3⟩ := chain_cons_act hy'
    obtain ⟨z₁, z₂, rfl, h4, h5⟩ := chain_cons_comp h3
    obtain ⟨a, ha, rfl⟩ := yield_incT hD h4
    rw [chain_act h5]
    exact ⟨_, a, _, Or.inr ⟨d, hd, rfl, rfl⟩, ha, rfl⟩

omit hD [Fintype Q] [Fintype Γ] in
theorem bitL_congr {p : Bool} {k : ℕ} {cd cd' : CD Q Γ} (hx : ∀ i, k ≤ i → cd.x i = cd'.x i)
    (he : ∀ i, k ≤ i → cd.e i = cd'.e i) (hr : cd.rd = cd'.rd) (hc : cd.core = cd'.core)
    (hi : cd.incw = cd'.incw) (hv : cd.val = cd'.val) : bitL m p k cd = bitL m p k cd' := by
  have h1 : wbsL p k (m - k) cd = wbsL p k (m - k) cd' := by
    refine List.map_congr_left fun i hi' => ?_
    rw [List.mem_range'_1] at hi'
    rw [hx i hi'.1, he i hi'.1]
  have h2 : (rbsL p k (m - k) cd.x : List (Act Q Γ)) = rbsL p k (m - k) cd'.x := by
    unfold rbsL
    congr 1
    refine List.map_congr_left fun i hi' => ?_
    rw [List.mem_range'_1] at hi'
    rw [hx i hi'.1]
  unfold bitL midL
  rw [h1, h2, hr, hc, hi, hv]

theorem yield_bit_top {p : Bool} {z : List (Act Q Γ)} (h : D.ChainYield [cT (.bit p m)] z) :
    ∃ cd, ValidCD m n' N p cd ∧ z = bitL m p m cd := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  rcases bodies_bit hb h1 with ⟨hk, -⟩ | ⟨-, h2⟩
  · exact absurd hk (lt_irrefl m)
  rw [h2] at hy
  cases p
  · obtain ⟨core, incw, val, hc, hi, rfl⟩ := yield_core hD (gridYield_singleton_iff.1 hy)
    exact ⟨⟨fun _ => false, fun _ => false, [], core, incw, val⟩, ⟨Or.inl rfl, hc, hi⟩,
      by simp [bitL_self, midL]⟩
  · obtain ⟨z₁, z₂, rfl, h3, h4⟩ := chain_cons_comp (gridYield_singleton_iff.1 hy)
    obtain ⟨core, incw, val, hc, hi, rfl⟩ := yield_core hD h4
    refine ⟨⟨fun _ => false, fun _ => false, z₁, core, incw, val⟩, ⟨?_, hc, hi⟩,
      by simp [bitL_self, midL]⟩
    rcases yield_rd0 hD h3 with h5 | h5 | ⟨i, b', hi', h5⟩
    · exact Or.inl h5
    · exact Or.inr ⟨rfl, Or.inl h5⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨i, b', hi', h5⟩⟩

theorem yield_bit {p : Bool} : ∀ j k : ℕ, k + j = m → ∀ z : List (Act Q Γ),
    D.ChainYield [cT (.bit p k)] z → ∃ cd, ValidCD m n' N p cd ∧ z = bitL m p k cd := by
  intro j
  induction j with
  | zero =>
    intro k hk z h
    rw [Nat.add_zero] at hk
    subst hk
    exact yield_bit_top hD h
  | succ j ih =>
    intro k hk z h
    obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
    rcases bodies_bit hb h1 with ⟨hk', x, e, h2⟩ | ⟨hk', -⟩
    swap
    · omega
    rw [h2] at hy
    obtain ⟨z', rfl, h3⟩ := chain_cons_act (gridYield_singleton_iff.1 hy)
    obtain ⟨z₁, z₂, rfl, h4, h5⟩ := chain_cons_comp h3
    rw [chain_act h5]
    obtain ⟨cd, hv, rfl⟩ := ih (k + 1) (by omega) z₁ h4
    refine ⟨{ cd with x := Function.update cd.x k x, e := Function.update cd.e k e },
      hv, ?_⟩
    rw [bitL_of_lt p hk']
    simp only [Function.update_self, List.cons_append, List.cons.injEq, true_and]
    congr 1
    refine bitL_congr (fun i hi => ?_) (fun i hi => ?_) rfl rfl rfl rfl
    · simp [Function.update_of_ne (show i ≠ k by omega)]
    · simp [Function.update_of_ne (show i ≠ k by omega)]

theorem yield_tree {p : Bool} : ∀ k : ℕ, ∀ z : List (Act Q Γ), D.ChainYield [cT (.tree p k)] z →
    ∃ bl : List (List (Act Q Γ)), (∀ v ∈ bl, ∃ cd, ValidCD m n' N p cd ∧ v = chainW m p cd) ∧
      InterleaveList bl z := by
  intro k
  induction k with
  | zero =>
    intro z h
    obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
    rw [bodies_tree0 hb h1] at hy
    obtain ⟨z', rfl, h3⟩ := chain_cons_act (gridYield_singleton_iff.1 hy)
    obtain ⟨cd, hv, rfl⟩ := yield_bit hD m 0 (by omega) z' h3
    refine ⟨[chainW m p cd], ?_, InterleaveList.cons InterleaveList.nil (Interleave.nil_right _)⟩
    intro v hv'
    rw [List.mem_singleton] at hv'
    exact ⟨cd, hv, hv'⟩
  | succ k ih =>
    intro z h
    obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
    rw [bodies_treeS hb h1] at hy
    obtain ⟨z₁, z₂, h₁, h₂, hi⟩ := grid_two hy
    obtain ⟨bl₁, hv₁, hl₁⟩ := ih z₁ h₁
    obtain ⟨bl₂, hv₂, hl₂⟩ := ih z₂ h₂
    refine ⟨bl₁ ++ bl₂, ?_, hl₁.append hl₂ hi⟩
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact hv₁ v hv
    · exact hv₂ v hv

theorem yield_block {p : Bool} {z : List (Act Q Γ)} (h : D.ChainYield [cT (.block p)] z) :
    ∃ bl : List (List (Act Q Γ)), (∀ v ∈ bl, LoopW m n' N v) ∧ InterleaveList bl z := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  rw [bodies_block hb h1] at hy
  obtain ⟨z₁, z₂, h₁, h₂, hi⟩ := grid_two hy
  obtain ⟨bl₁, hv₁, hl₁⟩ := yield_tree hD m z₁ h₁
  obtain ⟨b', hb', h1', hy'⟩ := body_of_chain hD h₂
  obtain ⟨a, ha, h3⟩ := bodies_reT hb' h1'
  rw [h3] at hy'
  have h4 := chain_act (gridYield_singleton_iff.1 hy')
  subst h4
  refine ⟨bl₁ ++ [[a]], ?_, hl₁.append
    (InterleaveList.cons InterleaveList.nil (Interleave.nil_right _)) hi⟩
  intro v hv
  rcases List.mem_append.1 hv with hv | hv
  · obtain ⟨cd, hcd, rfl⟩ := hv₁ v hv
    exact Or.inl ⟨p, cd, hcd, rfl⟩
  · rw [List.mem_singleton] at hv
    exact Or.inr ⟨a, ha, hv⟩

theorem yield_loop {p : Bool} : ∀ n : ℕ, ∀ z : List (Act Q Γ), D.ChainYieldN n [cT (.loop p)] z →
    ∃ bl : List (List (Act Q Γ)), (∀ v ∈ bl, LoopW m n' N v) ∧ InterleaveList bl z := by
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
      obtain ⟨bl₁, hv₁, hl₁⟩ := yield_block hD (chainYield_singleton_inr_iff.2 ⟨ls, hm, k', hb'⟩)
      obtain ⟨bl₂, hv₂, hl₂⟩ := ih n'' (by omega) as' ht
      refine ⟨bl₁ ++ bl₂, ?_, hl₁.append hl₂ (Interleave.append _ _)⟩
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hv₁ v hv
      · exact hv₂ v hv
    · obtain ⟨-, rfl⟩ := gridYieldN_nil_iff.1 hy
      exact ⟨[], by simp, InterleaveList.nil⟩

theorem yield_finish {z : List (Act Q Γ)} (h : D.ChainYield [cT .finish] z) : FinW N z := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  obtain ⟨q, hq, h2⟩ := bodies_finish hb h1
  rw [h2] at hy
  obtain ⟨z', rfl, -⟩ := chain_cons_act (gridYield_singleton_iff.1 hy)
  exact ⟨q, hq, z', rfl⟩

/-- **The refinements of the root task.** -/
theorem yield_root {z : List (Act Q Γ)} (h : D.ChainYield [cT .root] z) :
    ∃ z' bl, z = .boot :: z' ∧ InterleaveList bl z' ∧
      (∀ v ∈ bl, LoopW m n' N v ∨ FinW N v) ∧ ∃ v ∈ bl, FinW N v := by
  obtain ⟨b, hb, h1, hy⟩ := body_of_chain hD h
  rw [bodies_root hb h1] at hy
  obtain ⟨z', rfl, h3⟩ := chain_cons_act (gridYield_singleton_iff.1 hy)
  obtain ⟨b', hb', h1', hy'⟩ := body_of_chain hD h3
  rw [bodies_main hb' h1'] at hy'
  obtain ⟨zA, zBF, hA, hBF, hi⟩ := gridYield_cons_iff.1 hy'
  obtain ⟨zB, zF, hB, hF, hi'⟩ := grid_two hBF
  obtain ⟨nA, hA⟩ := hA
  obtain ⟨nB, hB⟩ := hB
  obtain ⟨blA, hvA, hlA⟩ := yield_loop hD nA zA hA
  obtain ⟨blB, hvB, hlB⟩ := yield_loop hD nB zB hB
  have hfin := yield_finish hD hF
  refine ⟨z', blA ++ (blB ++ [zF]), rfl, hlA.append (hlB.append
    (InterleaveList.cons InterleaveList.nil (Interleave.nil_right _)) hi') hi, ?_,
    zF, by simp, hfin⟩
  intro v hv
  simp only [List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | hv | rfl
  · exact Or.inl (hvA v hv)
  · exact Or.inl (hvB v hv)
  · exact Or.inr hfin

end Domain

/-- **Every refinement of the initial task network of the encoding** is `boot` followed by an
interleaving of loop words and finish words, at least one of them a finish word. -/
theorem netYield_prob (ι : Bool → Γ) (w : List Bool) {z : List (Act Q Γ)}
    (h : (prob m n' ι N w).domain.NetYield (prob m n' ι N w).tnI z) :
    ∃ z' bl, z = .boot :: z' ∧ InterleaveList bl z' ∧
      (∀ v ∈ bl, LoopW m n' N v ∨ FinW N v) ∧ ∃ v ∈ bl, FinW N v := by
  have hD : (prob m n' ι N w).domain.methods = methodsOf m n' N := rfl
  have h' := (netYield_grid_iff (grid_of_methodsOf hD)).1 h
  exact yield_root hD (gridYield_singleton_iff.1 h')

end SpaceEnc

end HTN
