import FondHtn.HardTR.TSound
import FondHtn.HardTR.TGame
import FondHtn.HardTR.TComp
/-!
# CB22 Thm 5: the canonical strategy on the networks of the description

Moves of the multiset chain game `FOND.HardTR.MWin` for the described problem: decomposition by
a described method, execution of an encoded action on an encoded state.  Then the phases of a
round: expansion of a block into fresh threads, the address bits of a writer thread, the read of
a tail, the transducer operation and the increment.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TD

open TL TT TE HardMP HTN HTN.Syn HTN.Article AcycHard.Sav ATM

variable {S : Type} {cS : S → ℕ} {X : Spec S} {allS : List S} {ops : List Op} {ens : List (En S)}
  {σ₀ : S}

/-- An action label. -/
abbrev aL (cS : S → ℕ) (a : Act Op (En S)) : ℕ ⊕ ℕ := Sum.inl (nmA cS a)

/-- A compound label. -/
abbrev nL (y : Nt) : ℕ ⊕ ℕ := Sum.inr (nmN y)

/-- The group tags. -/
abbrev preT (p : Bool) : Option (Bool × Bool) := some (p, false)
abbrev postT (p : Bool) : Option (Bool × Bool) := some (p, true)

/-- The chain game on encoded states. -/
abbrev MW (cS : S → ℕ) (X : Spec S) (allS : List S) (ops : List Op) (ens : List (En S)) (σ₀ : S)
    (M : Multiset (LCh ℕ ℕ)) (r : Rec (Ctl S)) : Prop :=
  MWin (desc cS X allS ops ens σ₀).toProblem M (toCfg cS r).enc

theorem mem_methods_of {e : MethodDesc} (he : e ∈ meths cS X ops ens) :
    e.toMethod ∈ (desc cS X allS ops ens σ₀).toProblem.methods :=
  ⟨e, by rw [methods_desc]; exact he, rfl⟩

/-- **Decomposition by a sequence method.** -/
theorem mv_seq {y : Nt} {ls : List (Bool × ℕ)} (he : (nmN y, seqTn ls) ∈ meths cS X ops ens)
    {xs₁ xs₂ : List (ℕ ⊕ ℕ)} {τ : Option (Bool × Bool)} {M : Multiset (LCh ℕ ℕ)} {r : Rec (Ctl S)}
    (h : MW cS X allS ops ens σ₀ (⟨xs₁ ++ ls.map toLab ++ xs₂, τ⟩ ::ₘ M) r) :
    MW cS X allS ops ens σ₀ (⟨xs₁ ++ nL y :: xs₂, τ⟩ ::ₘ M) r :=
  .seq (mem_methods_of he) rfl ⟨_, HardMP.isSeqNet_seqTn ls⟩ h

/-- **Decomposition by a set method.** -/
theorem mv_set {y : Nt} {ls : List (Bool × ℕ)} (he : (nmN y, setTn ls) ∈ meths cS X ops ens)
    {τ : Option (Bool × Bool)} {M : Multiset (LCh ℕ ℕ)} {r : Rec (Ctl S)}
    (h : MW cS X allS ops ens σ₀
      (⟨[], τ⟩ ::ₘ (M + ((ls.map toLab).map fun b => (⟨[b], τ⟩ : LCh ℕ ℕ) : Multiset (LCh ℕ ℕ)))) r) :
    MW cS X allS ops ens σ₀ (⟨[nL y], τ⟩ ::ₘ M) r :=
  .set (mem_methods_of he) rfl ⟨_, setNet_setTn ls⟩ h

/-- **Execution of an encoded action.** -/
theorem mv_prim (hS : Function.Injective cS) (hall : ∀ s, s ∈ allS) (hX : X.Valid)
    {a : Act Op (En S)} (ha : a ∈ acts X ops ens) {r : Rec (Ctl S)} (hG : Good X r)
    (happ : X.mach.app a r) {rest : List (ℕ ⊕ ℕ)} {τ : Option (Bool × Bool)} {M : Multiset (LCh ℕ ℕ)}
    (hfree : ∀ g, τ = some (g, true) → ∀ c ∈ M, c.tag = some (g, false) → c.lab = [])
    (h : ∀ r' ∈ X.mach.outs a r, Good X r' → MW cS X allS ops ens σ₀ (⟨rest, τ⟩ ::ₘ M) r') :
    MW cS X allS ops ens σ₀ (⟨aL cS a :: rest, τ⟩ ::ₘ M) r := by
  refine .prim hfree ?_ fun s' hs' => ?_
  · rw [δ_desc hS ha, applicable_enc, app_iff hS hX hG]; exact happ
  · rw [δ_desc hS ha, outcomes_enc _ (aspec_wf (cS := cS) (X := X) (allS := allS) a)
      ((app_iff hS hX hG a).2 happ), out_eq hall hG happ, Set.image_image] at hs'
    obtain ⟨r', hr', rfl⟩ := hs'
    exact h r' hr' (good_out hX hG happ hr')

/-! ## Membership of the methods used -/

section Mem

variable (cS) (X) (ops) (ens)

theorem mem_methsP {p : Bool} {e : MethodDesc} (he : e ∈ methsP cS X ops ens p) : e ∈ meths cS X ops ens := by
  cases p <;> simp [meths, he]

theorem m_loop (p : Bool) : (nmN (.loop p), seqTn [lN (.block p), lN (.loop p)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by simp [methsP])
theorem m_loopNil (p : Bool) : (nmN (.loop p), seqTn []) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by simp [methsP])
theorem m_block (p : Bool) :
    (nmN (.block p), setTn [lN (.tree p (mm X)), lN (.reT p)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by simp [methsP])
theorem m_tree0 (p : Bool) : (nmN (.tree p 0), seqTn [lN (.bit p 0)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by simp [methsP])
theorem m_bitM (p : Bool) : (nmN (.bit p (mm X)), seqTn [lN (.core p)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by simp [methsP])
theorem m_wrap (p : Bool) : (nmN (.incT p), seqTn [lA cS (.wrap p)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by simp [methsP])
theorem m_treeS (p : Bool) {k : ℕ} (hk : k < mm X) :
    (nmN (.tree p (k + 1)), setTn [lN (.tree p k), lN (.tree p k)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by
    simp only [methsP, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, by simp⟩)))))
theorem m_inc (p : Bool) {k : ℕ} (hk : k < mm X) :
    (nmN (.incT p), seqTn [lA cS (.inc p k)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by
    simp only [methsP, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, by simp⟩)))))
theorem m_bit (p : Bool) {k : ℕ} (hk : k < mm X) (b : Bool) :
    (nmN (.bit p k), seqTn [lA cS (.wb p k b), lN (.bit p (k + 1)), lN (.rbT p k b)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by
    simp only [methsP, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, by cases b <;> simp⟩)))))
theorem m_rb (p : Bool) {k : ℕ} (hk : k < mm X) (b : Bool) :
    (nmN (.rbT p k b), seqTn [lA cS (.rb p k b)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by
    simp only [methsP, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, by cases b <;> simp⟩)))))
theorem m_rbD (p : Bool) {k : ℕ} (hk : k < mm X) (b : Bool) :
    (nmN (.rbT p k b), seqTn [lA cS (.dr p)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by
    simp only [methsP, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, by cases b <;> simp⟩)))))
theorem m_core (p : Bool) {o : Op} (ho : o ∈ ops) :
    (nmN (.core p), seqTn [lA cS (.op p o), lN (.incT p), lN (.rvT p (Spec.opW o))]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by
    simp only [methsP, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨o, ho, by simp⟩))))
theorem m_coreN (p : Bool) {o : Op} (ho : o ∈ ops) :
    (nmN (.core p), seqTn [lA cS (.nrd p), lA cS (.op p o), lN (.incT p), lN (.rvT p (Spec.opW o))]) ∈
      meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by
    simp only [methsP, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨o, ho, by simp⟩))))
theorem m_rv (p γ : Bool) : (nmN (.rvT p γ), seqTn [lA cS (.rv p γ)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by cases γ <;> simp [methsP])
theorem m_rvD (p γ : Bool) : (nmN (.rvT p γ), seqTn [lA cS (.dr p)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by cases γ <;> simp [methsP])
theorem m_re (p : Bool) {e : En S} (he : e ∈ ens) :
    (nmN (.reT p), seqTn [lA cS (.rend p e)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by
    simp only [methsP, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨e, he, rfl⟩))
theorem m_reD (p : Bool) : (nmN (.reT p), seqTn [lA cS (.dr p)]) ∈ meths cS X ops ens :=
  mem_methsP cS X ops ens (p := p) (by simp [methsP])
theorem m_main : (nmN .main, setTn [lN (.loop true), lN (.loop false), lN .finT]) ∈ meths cS X ops ens := by
  simp [meths]
theorem m_finT : (nmN .finT, seqTn [lA cS .fin]) ∈ meths cS X ops ens := by
  simp [meths]

end Mem

@[simp] theorem toLab_lN (y : Nt) : toLab (lN y) = nL y := rfl
@[simp] theorem toLab_lA (a : Act Op (En S)) : toLab (lA cS a) = aL cS a := rfl

/-! ## Phase: the threads of a block -/

/-- A fresh writer thread. -/
abbrev freshC (ρ : Bool) : LCh ℕ ℕ := ⟨[nL (.bit ρ 0)], preT ρ⟩

/-- Junk: empty chains. -/
def Junk (J : Multiset (LCh ℕ ℕ)) : Prop := ∀ c ∈ J, c.lab = []

theorem junk_add {J J' : Multiset (LCh ℕ ℕ)} (h : Junk J) (h' : Junk J') : Junk (J + J') :=
  fun c hc => (Multiset.mem_add.1 hc).elim (h c) (h' c)

theorem junk_cons {J : Multiset (LCh ℕ ℕ)} (τ : Option (Bool × Bool)) (h : Junk J) :
    Junk (⟨[], τ⟩ ::ₘ J) := fun c hc => by
  rcases Multiset.mem_cons.1 hc with rfl | hc
  · rfl
  · exact h c hc

/-- **Expanding a tree into fresh threads.** -/
theorem play_tree (ρ : Bool) : ∀ k, k ≤ mm X → ∀ (M : Multiset (LCh ℕ ℕ)) (r : Rec (Ctl S)),
    (∀ J, Junk J → MW cS X allS ops ens σ₀ (M + J + 2 ^ k • {freshC ρ}) r) →
      MW cS X allS ops ens σ₀ (⟨[nL (.tree ρ k)], preT ρ⟩ ::ₘ M) r := by
  intro k
  induction k with
  | zero =>
    intro _ M r h
    have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_tree0 cS X ops ens ρ)
      (xs₁ := []) (xs₂ := []) (τ := preT ρ) (M := M) (r := r)
    simp only [List.nil_append, List.append_nil, List.map_cons, List.map_nil, toLab_lN] at this
    apply this
    have h0 := h 0 (fun c hc => by simp at hc)
    rw [add_zero, pow_zero, one_nsmul, add_comm, Multiset.singleton_add] at h0
    exact h0
  | succ k ih =>
    intro hk M r h
    apply mv_set (m_treeS cS X ops ens ρ (by omega))
    simp only [List.map_cons, List.map_nil, toLab_lN]
    set T : LCh ℕ ℕ := ⟨[nL (.tree ρ k)], preT ρ⟩ with hT
    have e : (⟨[], preT ρ⟩ ::ₘ (M + (([T, T] : List (LCh ℕ ℕ)) : Multiset (LCh ℕ ℕ))) : Multiset (LCh ℕ ℕ)) =
        T ::ₘ (T ::ₘ (⟨[], preT ρ⟩ ::ₘ M)) := by
      simp only [← Multiset.cons_coe, Multiset.coe_nil, ← Multiset.singleton_add]
      abel
    rw [e]
    refine ih (by omega) _ r fun J hJ => ?_
    have e2 : T ::ₘ (⟨[], preT ρ⟩ ::ₘ M) + J + 2 ^ k • {freshC ρ} =
        T ::ₘ ((⟨[], preT ρ⟩ ::ₘ M) + J + 2 ^ k • {freshC ρ}) := by
      simp only [Multiset.cons_add]
    rw [e2]
    refine ih (by omega) _ r fun J' hJ' => ?_
    have e3 : (⟨[], preT ρ⟩ ::ₘ M) + J + 2 ^ k • {freshC ρ} + J' + 2 ^ k • {freshC ρ} =
        M + (⟨[], preT ρ⟩ ::ₘ (J + J')) + 2 ^ (k + 1) • {freshC ρ} := by
      rw [pow_succ, mul_two, add_nsmul]
      simp only [← Multiset.singleton_add]
      abel
    rw [e3]
    exact h _ (junk_cons _ (junk_add hJ hJ'))

/-! ## Phase: the address bits of a writer thread -/

/-- The pending address checks of a thread with address `c` below bit `k`. -/
def rbs (p : Bool) (c k : ℕ) : List (ℕ ⊕ ℕ) :=
  (List.range k).reverse.map fun j => nL (.rbT p j (c.testBit j))

theorem rbs_succ (p : Bool) (c k : ℕ) : rbs p c (k + 1) = nL (.rbT p k (c.testBit k)) :: rbs p c k := by
  simp [rbs, List.range_succ]

/-- The phase before writing bit `k`. -/
def phk (X : Spec S) (k : ℕ) : Ph := if k < mm X then .wb k else .rv

variable (hS : Function.Injective cS) (hall : ∀ s, s ∈ allS) (hX : X.Valid)
include hS hall hX

/-- **Writing the address bits.** -/
theorem play_bits (ρ : Bool) {c : ℕ} (M : Multiset (LCh ℕ ℕ)) (y : Bool) (g : Ctl S) :
    ∀ j k, k + j = mm X → Good X ⟨phk X k, c, ρ, y, g⟩ →
      MW cS X allS ops ens σ₀ (⟨nL (.bit ρ (mm X)) :: rbs ρ c (mm X), preT ρ⟩ ::ₘ M) ⟨.rv, c, ρ, y, g⟩ →
      MW cS X allS ops ens σ₀ (⟨nL (.bit ρ k) :: rbs ρ c k, preT ρ⟩ ::ₘ M) ⟨phk X k, c, ρ, y, g⟩ := by
  intro j
  induction j with
  | zero =>
    intro k hk _ h
    simp only [Nat.add_zero] at hk; subst hk
    simpa [phk] using h
  | succ j ih =>
    intro k hk hG h
    have hkm : k < mm X := by omega
    have hph : phk X k = .wb k := by simp [phk, hkm]
    rw [hph] at hG ⊢
    have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_bit cS X ops ens ρ hkm (c.testBit k))
      (xs₁ := []) (xs₂ := rbs ρ c k) (τ := preT ρ) (M := M) (r := ⟨.wb k, c, ρ, y, g⟩)
    simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, toLab_lN,
      List.cons_append] at this
    apply this
    refine mv_prim hS hall hX (a := .wb ρ k (c.testBit k))
      (by rw [mem_acts_iff]; exact Or.inl ⟨ρ, k, _, hkm, rfl⟩) hG
      ⟨rfl, rfl, rfl⟩ (fun g h => by simp at h) fun r' hr' hG' => ?_
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'
    subst hr'
    have hnext : X.mach.nextWb k = phk X (k + 1) := by
      unfold Mach.nextWb phk; rfl
    rw [hnext] at hG' ⊢
    have := ih (k + 1) (by omega) hG' h
    rwa [rbs_succ] at this

/-! ## Phase: reading a tail -/

omit hS hall hX in
/-- A stored tail. -/
abbrev tailC (X : Spec S) (p : Bool) (a : ℕ) (γ : Bool) : LCh ℕ ℕ :=
  ⟨nL (.rvT p γ) :: rbs p a (mm X), preT p⟩

omit hS hall hX in
/-- The phase while `k` address bits remain to be checked. -/
def phr (k : ℕ) : Ph := if k = 0 then .op else .rb (k - 1)

/-- **Checking the address bits of a tail.** -/
theorem play_rbs (ρ : Bool) {c : ℕ} (M : Multiset (LCh ℕ ℕ)) (y : Bool) (g : Ctl S) :
    ∀ k, k ≤ mm X → Good X ⟨phr k, c, ρ, y, g⟩ →
      MW cS X allS ops ens σ₀ (⟨[], preT (!ρ)⟩ ::ₘ M) ⟨.op, c, ρ, y, g⟩ →
      MW cS X allS ops ens σ₀ (⟨rbs (!ρ) c k, preT (!ρ)⟩ ::ₘ M) ⟨phr k, c, ρ, y, g⟩ := by
  intro k
  induction k with
  | zero => intro _ _ h; simpa [phr, rbs] using h
  | succ k ih =>
    intro hk hG h
    rw [rbs_succ]
    have hph : phr (k + 1) = .rb k := by simp [phr]
    rw [hph] at hG ⊢
    have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀)
      (m_rb cS X ops ens (!ρ) (k := k) (by omega) (c.testBit k))
      (xs₁ := []) (xs₂ := rbs (!ρ) c k) (τ := preT (!ρ)) (M := M) (r := ⟨.rb k, c, ρ, y, g⟩)
    simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.cons_append] at this
    apply this
    refine mv_prim hS hall hX (a := .rb (!ρ) k (c.testBit k))
      (by rw [mem_acts_iff]; exact Or.inr (Or.inl ⟨!ρ, k, _, by omega, rfl⟩)) hG
      ⟨rfl, by simp, rfl⟩ (fun g h => by simp at h) fun r' hr' hG' => ?_
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'
    subst hr'
    have hnext : Mach.nextRb k = phr k := by unfold Mach.nextRb phr; rfl
    rw [hnext] at hG' ⊢
    exact ih (by omega) hG' h

/-- **Reading a tail**: the value `γ` stored for the cell `c`. -/
theorem play_read (ρ γ : Bool) {c : ℕ} (M : Multiset (LCh ℕ ℕ)) (y : Bool) (g : Ctl S)
    (hG : Good X ⟨.rv, c, ρ, y, g⟩)
    (h : MW cS X allS ops ens σ₀ (⟨[], preT (!ρ)⟩ ::ₘ M) ⟨.op, c, ρ, γ, g⟩) :
    MW cS X allS ops ens σ₀ (tailC X (!ρ) c γ ::ₘ M) ⟨.rv, c, ρ, y, g⟩ := by
  have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_rv cS X ops ens (!ρ) γ)
    (xs₁ := []) (xs₂ := rbs (!ρ) c (mm X)) (τ := preT (!ρ)) (M := M) (r := ⟨.rv, c, ρ, y, g⟩)
  simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.cons_append] at this
  apply this
  refine mv_prim hS hall hX (a := .rv (!ρ) γ)
    (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨!ρ, γ, rfl⟩)))) hG
    ⟨rfl, by simp⟩ (fun g h => by simp at h) fun r' hr' hG' => ?_
  simp only [Mach.outs, Set.mem_singleton_iff] at hr'
  subst hr'
  have hm : X.mach.m - 1 + 1 = mm X := by simp [Spec.mach, mm]
  have hph : Ph.rb (X.mach.m - 1) = phr (mm X) := by simp [phr, Spec.mach, mm]
  rw [hph] at hG' ⊢
  exact play_rbs hS hall hX ρ M γ g (mm X) le_rfl hG' h

/-! ## Phase: the operation and the counter increment -/

omit hS hall hX in
/-- The lowest zero bit of a counter, or all bits are set. -/
theorem low_zero {c m : ℕ} (hc : c < 2 ^ m) :
    (c + 1 < 2 ^ m ∧ ∃ k < m, c.testBit k = false ∧ ∀ j < k, c.testBit j = true) ∨
      (¬ c + 1 < 2 ^ m ∧ ∀ j < m, c.testBit j = true) := by
  have hex : ∃ k, c.testBit k = false := ⟨m, Nat.testBit_lt_two_pow hc⟩
  classical
  set k := Nat.find hex with hk
  have hkf : c.testBit k = false := Nat.find_spec hex
  have hlow : ∀ j < k, c.testBit j = true := fun j hj => by
    have := Nat.find_min hex hj
    simpa using this
  by_cases hkm : k < m
  · refine Or.inl ⟨?_, k, hkm, hkf, hlow⟩
    have hne : c ≠ 2 ^ m - 1 := by
      rintro rfl
      rw [Nat.testBit_two_pow_sub_one] at hkf
      simp [hkm] at hkf
    omega
  · have hall' : ∀ j < m, c.testBit j = true := fun j hj => hlow j (by omega)
    refine Or.inr ⟨?_, hall'⟩
    have hc1 : c = 2 ^ m - 1 := by
      refine TL.Mach.eq_of_testBit_lt (m := m) hc (by have := Nat.one_le_two_pow (n := m); omega) ?_
      intro j hj
      rw [hall' j hj, Nat.testBit_two_pow_sub_one]; simp [hj]
    omega

/-- The record after the counter increment. -/
def incR (X : Spec S) (c : ℕ) (ρ y : Bool) (g : Ctl S) : Rec (Ctl S) :=
  if c + 1 < 2 ^ mm X then ⟨.wb 0, c + 1, ρ, y, g⟩ else ⟨.fin, 0, ρ, y, g⟩

/-- **The operation and the increment.** -/
theorem play_core (ρ : Bool) {c : ℕ} (M : Multiset (LCh ℕ ℕ)) (y : Bool) (g : Ctl S) {o : Op}
    (ho : o ∈ ops) (hok : X.opOK o g y c) (hG : Good X ⟨.op, c, ρ, y, g⟩)
    (h : Good X (incR X c ρ y (X.opEff o g)) →
      MW cS X allS ops ens σ₀ (tailC X ρ c (Spec.opW o) ::ₘ M) (incR X c ρ y (X.opEff o g))) :
    MW cS X allS ops ens σ₀
      (⟨aL cS (.op ρ o) :: nL (.incT ρ) :: nL (.rvT ρ (Spec.opW o)) :: rbs ρ c (mm X), preT ρ⟩ ::ₘ M)
      ⟨.op, c, ρ, y, g⟩ := by
  refine mv_prim hS hall hX (a := .op ρ o)
    (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨ρ, o, ho, rfl⟩)))))))) hG
    ⟨rfl, rfl, hok⟩ (fun g h => by simp at h) fun r' hr' hG' => ?_
  simp only [Mach.outs, Set.mem_singleton_iff] at hr'
  subst hr'
  have hc := hG.c_lt
  rcases low_zero hc with ⟨hlt, k, hk, hk0, hlow⟩ | ⟨hlt, hall'⟩
  · have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_inc cS X ops ens ρ hk)
      (xs₁ := []) (xs₂ := nL (.rvT ρ (Spec.opW o)) :: rbs ρ c (mm X)) (τ := preT ρ) (M := M)
      (r := ⟨.inc, c, ρ, y, X.mach.opEff o g⟩)
    simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.cons_append] at this
    apply this
    refine mv_prim hS hall hX (a := .inc ρ k)
      (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inl ⟨ρ, k, hk, rfl⟩))) hG'
      ⟨rfl, rfl, by simpa [Spec.mach, mm] using hk, hk0, hlow⟩ (fun g h => by simp at h)
      fun r'' hr'' hG'' => ?_
    simp only [Mach.outs, Set.mem_singleton_iff] at hr''
    subst hr''
    have e : incR X c ρ y (X.opEff o g) = ⟨.wb 0, c + 1, ρ, y, X.opEff o g⟩ := by
      simp [incR, hlt]
    rw [e] at h
    exact h hG''
  · have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_wrap cS X ops ens ρ)
      (xs₁ := []) (xs₂ := nL (.rvT ρ (Spec.opW o)) :: rbs ρ c (mm X)) (τ := preT ρ) (M := M)
      (r := ⟨.inc, c, ρ, y, X.mach.opEff o g⟩)
    simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.cons_append] at this
    apply this
    refine mv_prim hS hall hX (a := .wrap ρ)
      (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ρ, rfl⟩))))) hG'
      ⟨rfl, rfl, by simpa [Spec.mach, mm] using hall'⟩ (fun g h => by simp at h)
      fun r'' hr'' hG'' => ?_
    simp only [Mach.outs, Set.mem_singleton_iff] at hr''
    subst hr''
    have e : incR X c ρ y (X.opEff o g) = ⟨.fin, 0, ρ, y, X.opEff o g⟩ := by
      simp [incR, hlt]
    rw [e] at h
    exact h hG''

/-! ## One position of a round -/

/-- **One position of a normal round**: write the address, read the old value `γ`, apply the
operation `o`, store the new value and increment the counter. -/
theorem play_pos (ρ γ : Bool) {c : ℕ} (M : Multiset (LCh ℕ ℕ)) (y : Bool) (g : Ctl S) {o : Op}
    (ho : o ∈ ops) (hok : X.opOK o g γ c) (hG : Good X ⟨.wb 0, c, ρ, y, g⟩)
    (h : Good X (incR X c ρ γ (X.opEff o g)) →
      MW cS X allS ops ens σ₀ (tailC X ρ c (Spec.opW o) ::ₘ ⟨[], preT (!ρ)⟩ ::ₘ M)
        (incR X c ρ γ (X.opEff o g))) :
    MW cS X allS ops ens σ₀ (freshC ρ ::ₘ tailC X (!ρ) c γ ::ₘ M) ⟨.wb 0, c, ρ, y, g⟩ := by
  have hph : phk X 0 = .wb 0 := by simp [phk, mm]
  have h0 := play_bits (ops := ops) (ens := ens) (σ₀ := σ₀) hS hall hX ρ (tailC X (!ρ) c γ ::ₘ M) y g (mm X) 0 (by simp)
    (by rw [hph]; exact hG) ?_
  · simpa [hph, rbs] using h0
  rw [Multiset.cons_swap]
  refine play_read hS hall hX ρ γ _ y g
    ⟨hG.c_lt, (fun _ h => by cases h), (fun _ h => by cases h), hG.gs_lt, hG.s_le⟩ ?_
  rw [Multiset.cons_swap]
  have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_bitM cS X ops ens ρ)
    (xs₁ := []) (xs₂ := rbs ρ c (mm X)) (τ := preT ρ) (M := ⟨[], preT (!ρ)⟩ ::ₘ M)
    (r := ⟨.op, c, ρ, γ, g⟩)
  simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lN, List.cons_append] at this
  apply this
  have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_core cS X ops ens ρ ho)
    (xs₁ := []) (xs₂ := rbs ρ c (mm X)) (τ := preT ρ) (M := ⟨[], preT (!ρ)⟩ ::ₘ M)
    (r := ⟨.op, c, ρ, γ, g⟩)
  simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lN, toLab_lA,
    List.cons_append] at this
  apply this
  exact play_core hS hall hX ρ _ γ g ho hok
    ⟨hG.c_lt, (fun _ h => by cases h), (fun _ h => by cases h), hG.gs_lt, hG.s_le⟩ h

/-- **One position of the boot round**: no tail is read (`nrd`), the read bit is `false`. -/
theorem play_posB (ρ : Bool) {c : ℕ} (M : Multiset (LCh ℕ ℕ)) (y : Bool) (g : Ctl S) {o : Op}
    (ho : o ∈ ops) (hb : g.boot = true) (hok : X.opOK o g false c)
    (hG : Good X ⟨.wb 0, c, ρ, y, g⟩)
    (h : Good X (incR X c ρ false (X.opEff o g)) →
      MW cS X allS ops ens σ₀ (tailC X ρ c (Spec.opW o) ::ₘ M) (incR X c ρ false (X.opEff o g))) :
    MW cS X allS ops ens σ₀ (freshC ρ ::ₘ M) ⟨.wb 0, c, ρ, y, g⟩ := by
  have hph : phk X 0 = .wb 0 := by simp [phk, mm]
  have h0 := play_bits (ops := ops) (ens := ens) (σ₀ := σ₀) hS hall hX ρ M y g (mm X) 0 (by simp) (by rw [hph]; exact hG) ?_
  · simpa [hph, rbs] using h0
  have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_bitM cS X ops ens ρ)
    (xs₁ := []) (xs₂ := rbs ρ c (mm X)) (τ := preT ρ) (M := M) (r := ⟨.rv, c, ρ, y, g⟩)
  simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lN, List.cons_append] at this
  apply this
  have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_coreN cS X ops ens ρ ho)
    (xs₁ := []) (xs₂ := rbs ρ c (mm X)) (τ := preT ρ) (M := M) (r := ⟨.rv, c, ρ, y, g⟩)
  simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lN, toLab_lA,
    List.cons_append] at this
  apply this
  refine mv_prim (ops := ops) (ens := ens) (r := ⟨.rv, c, ρ, y, g⟩) hS hall hX (a := .nrd ρ)
    (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ρ, rfl⟩))))))
    ⟨hG.c_lt, (fun _ h => by cases h), (fun _ h => by cases h), hG.gs_lt, hG.s_le⟩
    ⟨rfl, rfl, hb⟩ (fun g h => by simp at h) fun r' hr' hG' => ?_
  simp only [Mach.outs, Set.mem_singleton_iff] at hr'
  subst hr'
  exact play_core hS hall hX ρ M false g ho hok hG' h

/-! ## A sweep over all positions -/

omit hS hall hX in
/-- The stored tails of the cells `c, …, c + n - 1`. -/
def tails (X : Spec S) (p : Bool) (v : ℕ → Bool) (c n : ℕ) : Multiset (LCh ℕ ℕ) :=
  ((List.range' c n).map fun a => tailC X p a (v a) : List (LCh ℕ ℕ))

omit hS hall hX in
theorem tails_succ (p : Bool) (v : ℕ → Bool) (c n : ℕ) :
    tails X p v c (n + 1) = tailC X p c (v c) ::ₘ tails X p v (c + 1) n := by
  simp [tails, List.range'_succ]

omit hS hall hX in
theorem tails_snoc (p : Bool) (v : ℕ → Bool) (c : ℕ) :
    tails X p v 0 (c + 1) = tailC X p c (v c) ::ₘ tails X p v 0 c := by
  simp only [tails]
  rw [List.range'_concat, List.map_append, ← Multiset.coe_add, add_comm]
  simp

omit hS hall hX in
theorem srun_cases {rd w' : ℕ → Bool} {c : ℕ} {g g' : Ctl S} (h : Mach.SRun X.mach rd w' c g g') :
    (c = 2 ^ mm X ∧ g = g') ∨ (c < 2 ^ mm X ∧ ∃ o, X.opOK o g (rd c) c ∧ w' c = Spec.opW o ∧
      Mach.SRun X.mach rd w' (c + 1) (X.opEff o g) g') := by
  cases h with
  | done => exact Or.inl ⟨rfl, rfl⟩
  | step hc hok hw h => exact Or.inr ⟨hc, _, hok, hw, h⟩

/-- **A normal sweep**: following a run of the transducer, every position reads the tail of the
previous round and stores a new tail. -/
theorem play_sweep (ρ : Bool) (rd w' : ℕ → Bool) (g' : Ctl S)
    (hops : ∀ o g b c, X.opOK o g b c → (∀ ℓ, g.gs = some ℓ → ℓ < X.no) → o ∈ ops) :
    ∀ n c (g : Ctl S) (y : Bool) (Rest : Multiset (LCh ℕ ℕ)), c + (n + 1) = 2 ^ mm X →
      Mach.SRun X.mach rd w' c g g' → Good X ⟨.wb 0, c, ρ, y, g⟩ →
      (∀ J, Junk J → ∀ y', Good X ⟨.fin, 0, ρ, y', g'⟩ →
        MW cS X allS ops ens σ₀ (tails X ρ w' 0 (2 ^ mm X) + J + Rest) ⟨.fin, 0, ρ, y', g'⟩) →
      MW cS X allS ops ens σ₀
        ((n + 1) • {freshC ρ} + tails X (!ρ) rd c (n + 1) + tails X ρ w' 0 c + Rest)
        ⟨.wb 0, c, ρ, y, g⟩ := by
  intro n
  induction n with
  | zero =>
    intro c g y Rest hc hrun hG hend
    rcases srun_cases hrun with ⟨hcW, -⟩ | ⟨-, o, hok, hw, hrun'⟩
    · omega
    have hc1 : c + 1 = 2 ^ mm X := by simpa using hc
    rcases srun_cases hrun' with ⟨-, rfl⟩ | ⟨hlt, -⟩
    swap; · omega
    have e : (0 + 1) • ({freshC ρ} : Multiset (LCh ℕ ℕ)) + tails X (!ρ) rd c (0 + 1) +
        tails X ρ w' 0 c + Rest = freshC ρ ::ₘ tailC X (!ρ) c (rd c) ::ₘ (tails X ρ w' 0 c + Rest) := by
      rw [tails_succ]
      simp only [zero_add, one_nsmul, tails, List.range'_zero, List.map_nil, Multiset.coe_nil,
        ← Multiset.singleton_add]
      abel
    rw [e]
    refine play_pos hS hall hX ρ (rd c) _ y g (hops _ _ _ _ hok hG.gs_lt) hok hG fun hG' => ?_
    have hi : incR X c ρ (rd c) (X.opEff o g) = ⟨.fin, 0, ρ, rd c, X.opEff o g⟩ := by
      simp [incR, hc1]
    rw [hi] at hG' ⊢
    have e2 : tailC X ρ c (Spec.opW o) ::ₘ ⟨[], preT (!ρ)⟩ ::ₘ (tails X ρ w' 0 c + Rest) =
        tails X ρ w' 0 (2 ^ mm X) + {⟨[], preT (!ρ)⟩} + Rest := by
      rw [← hc1, tails_snoc, ← hw]
      simp only [← Multiset.singleton_add]
      abel
    rw [e2]
    exact hend _ (junk_cons _ (fun _ h => by simp at h)) _ hG'
  | succ n ih =>
    intro c g y Rest hc hrun hG hend
    rcases srun_cases hrun with ⟨hcW, -⟩ | ⟨-, o, hok, hw, hrun'⟩
    · omega
    have hc1 : c + 1 < 2 ^ mm X := by omega
    have e : (n + 1 + 1) • ({freshC ρ} : Multiset (LCh ℕ ℕ)) + tails X (!ρ) rd c (n + 1 + 1) +
        tails X ρ w' 0 c + Rest = freshC ρ ::ₘ tailC X (!ρ) c (rd c) ::ₘ
          ((n + 1) • {freshC ρ} + tails X (!ρ) rd (c + 1) (n + 1) + tails X ρ w' 0 c + Rest) := by
      rw [tails_succ, succ_nsmul]
      simp only [← Multiset.singleton_add]
      abel
    rw [e]
    refine play_pos hS hall hX ρ (rd c) _ y g (hops _ _ _ _ hok hG.gs_lt) hok hG fun hG' => ?_
    have hi : incR X c ρ (rd c) (X.opEff o g) = ⟨.wb 0, c + 1, ρ, rd c, X.opEff o g⟩ := by
      simp [incR, hc1]
    rw [hi] at hG' ⊢
    have e2 : tailC X ρ c (Spec.opW o) ::ₘ ⟨[], preT (!ρ)⟩ ::ₘ
          ((n + 1) • {freshC ρ} + tails X (!ρ) rd (c + 1) (n + 1) + tails X ρ w' 0 c + Rest) =
        (n + 1) • {freshC ρ} + tails X (!ρ) rd (c + 1) (n + 1) + tails X ρ w' 0 (c + 1) +
          (⟨[], preT (!ρ)⟩ ::ₘ Rest) := by
      rw [tails_snoc, hw]
      simp only [← Multiset.singleton_add]
      abel
    rw [e2]
    refine ih (c + 1) _ _ _ (by omega) hrun' hG' fun J hJ y' hG'' => ?_
    have e3 : tails X ρ w' 0 (2 ^ mm X) + J + (⟨[], preT (!ρ)⟩ ::ₘ Rest) =
        tails X ρ w' 0 (2 ^ mm X) + (⟨[], preT (!ρ)⟩ ::ₘ J) + Rest := by
      simp only [← Multiset.singleton_add]
      abel
    rw [e3]
    exact hend _ (junk_cons _ hJ) _ hG''

/-- **The boot sweep**: every position writes the canonical boot tape for the index `i`. -/
theorem play_sweepB (ρ : Bool) (i : ℕ) (σ : S)
    (hops : ∀ o g b c, X.opOK o g b c → (∀ ℓ, g.gs = some ℓ → ℓ < X.no) → o ∈ ops) :
    ∀ n c (y : Bool) (Rest : Multiset (LCh ℕ ℕ)), c + (n + 1) = 2 ^ mm X →
      Good X ⟨.wb 0, c, ρ, y, g0 σ⟩ →
      (∀ J, Junk J → ∀ y', Good X ⟨.fin, 0, ρ, y', g0 σ⟩ →
        MW cS X allS ops ens σ₀ (tails X ρ (X.wB i) 0 (2 ^ mm X) + J + Rest) ⟨.fin, 0, ρ, y', g0 σ⟩) →
      MW cS X allS ops ens σ₀ ((n + 1) • {freshC ρ} + tails X ρ (X.wB i) 0 c + Rest)
        ⟨.wb 0, c, ρ, y, g0 σ⟩ := by
  intro n
  induction n with
  | zero =>
    intro c y Rest hc hG hend
    have hc1 : c + 1 = 2 ^ mm X := by simpa using hc
    have e : (0 + 1) • ({freshC ρ} : Multiset (LCh ℕ ℕ)) + tails X ρ (X.wB i) 0 c + Rest =
        freshC ρ ::ₘ (tails X ρ (X.wB i) 0 c + Rest) := by
      simp only [zero_add, one_nsmul, ← Multiset.singleton_add]
      abel
    rw [e]
    refine play_posB hS hall hX ρ _ y _ (hops _ _ _ _ (X.opOK_opB i c σ false) hG.gs_lt) rfl
      (X.opOK_opB i c σ false) hG fun hG' => ?_
    have hi : incR X c ρ false (X.opEff (X.opB i c) (g0 σ)) = ⟨.fin, 0, ρ, false, g0 σ⟩ := by
      simp [incR, hc1, TT.Spec.opEff_opB]
    rw [hi] at hG' ⊢
    have e2 : tailC X ρ c (Spec.opW (X.opB i c)) ::ₘ (tails X ρ (X.wB i) 0 c + Rest) =
        tails X ρ (X.wB i) 0 (2 ^ mm X) + 0 + Rest := by
      rw [← hc1, tails_snoc]
      simp only [← Multiset.singleton_add, add_zero, Spec.wB]
      abel
    rw [e2]
    exact hend _ (fun _ h => by simp at h) _ hG'
  | succ n ih =>
    intro c y Rest hc hG hend
    have hc1 : c + 1 < 2 ^ mm X := by omega
    have e : (n + 1 + 1) • ({freshC ρ} : Multiset (LCh ℕ ℕ)) + tails X ρ (X.wB i) 0 c + Rest =
        freshC ρ ::ₘ ((n + 1) • {freshC ρ} + tails X ρ (X.wB i) 0 c + Rest) := by
      rw [succ_nsmul]
      simp only [← Multiset.singleton_add]
      abel
    rw [e]
    refine play_posB hS hall hX ρ _ y _ (hops _ _ _ _ (X.opOK_opB i c σ false) hG.gs_lt) rfl
      (X.opOK_opB i c σ false) hG fun hG' => ?_
    have hi : incR X c ρ false (X.opEff (X.opB i c) (g0 σ)) = ⟨.wb 0, c + 1, ρ, false, g0 σ⟩ := by
      simp [incR, hc1, TT.Spec.opEff_opB]
    rw [hi] at hG' ⊢
    have e2 : tailC X ρ c (Spec.opW (X.opB i c)) ::ₘ ((n + 1) • {freshC ρ} + tails X ρ (X.wB i) 0 c + Rest) =
        (n + 1) • {freshC ρ} + tails X ρ (X.wB i) 0 (c + 1) + Rest := by
      rw [tails_snoc]
      simp only [← Multiset.singleton_add, Spec.wB]
      abel
    rw [e2]
    exact ih (c + 1) _ _ (by omega) hG' hend

/-! ## Draining after the finish -/

omit hS hall hX in
/-- The labels that can be drained. -/
def DrL (X : Spec S) (x : ℕ ⊕ ℕ) : Prop :=
  (∃ p γ, x = nL (.rvT p γ)) ∨ (∃ p k b, k < mm X ∧ x = nL (.rbT p k b)) ∨ (∃ p, x = nL (.reT p))

omit hS hall hX in
/-- The chains that can be drained. -/
def Drainable (X : Spec S) (c : LCh ℕ ℕ) : Prop :=
  c.lab = [] ∨ (∃ p, c.tag = preT p ∧ ∀ x ∈ c.lab, DrL X x) ∨ (∃ p, c.lab = [nL (.loop p)])

theorem drain_chain {r : Rec (Ctl S)} (hr : r.ph = .drain) (hG : Good X r) (p : Bool)
    (M : Multiset (LCh ℕ ℕ)) : ∀ l : List (ℕ ⊕ ℕ), (∀ x ∈ l, DrL X x) →
      MW cS X allS ops ens σ₀ (⟨[], preT p⟩ ::ₘ M) r → MW cS X allS ops ens σ₀ (⟨l, preT p⟩ ::ₘ M) r := by
  intro l
  induction l with
  | nil => exact fun _ h => h
  | cons x l ih =>
    intro hl h
    have hdr : ∀ p', MW cS X allS ops ens σ₀ (⟨aL cS (.dr p') :: l, preT p⟩ ::ₘ M) r := fun p' =>
      mv_prim hS hall hX (a := .dr p')
        (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p', rfl⟩)))))))
        hG hr (fun g h => by simp at h) fun r' hr' _ => by
          simp only [Mach.outs, Set.mem_singleton_iff] at hr'
          subst hr'
          exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h
    rcases hl x List.mem_cons_self with ⟨p', γ, rfl⟩ | ⟨p', k, b, hk, rfl⟩ | ⟨p', rfl⟩
    · have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_rvD cS X ops ens p' γ)
        (xs₁ := []) (xs₂ := l) (τ := preT p) (M := M) (r := r)
      simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.cons_append] at this
      exact this (hdr p')
    · have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_rbD cS X ops ens p' hk b)
        (xs₁ := []) (xs₂ := l) (τ := preT p) (M := M) (r := r)
      simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.cons_append] at this
      exact this (hdr p')
    · have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_reD cS X ops ens p')
        (xs₁ := []) (xs₂ := l) (τ := preT p) (M := M) (r := r)
      simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.cons_append] at this
      exact this (hdr p')

/-- **Draining**: after the finish, every remaining chain can be emptied. -/
theorem drain_all {r : Rec (Ctl S)} (hr : r.ph = .drain) (hG : Good X r)
    (M : Multiset (LCh ℕ ℕ)) (hM : ∀ c ∈ M, Drainable X c) :
    ∀ J, Junk J → MW cS X allS ops ens σ₀ (M + J) r := by
  induction M using Multiset.induction_on with
  | empty =>
    intro J hJ
    exact .empty fun c hc => hJ c (by simpa using hc)
  | cons a M ih =>
    intro J hJ
    have ih' := ih fun c hc => hM c (Multiset.mem_cons_of_mem hc)
    obtain ⟨l, τ⟩ := a
    have e : (⟨l, τ⟩ ::ₘ M) + J = ⟨l, τ⟩ ::ₘ (M + J) := Multiset.cons_add _ _ _
    have e' : ∀ τ', (⟨[], τ'⟩ ::ₘ (M + J) : Multiset (LCh ℕ ℕ)) = M + (⟨[], τ'⟩ ::ₘ J) := fun τ' => by
      simp only [← Multiset.singleton_add]; abel
    rw [e]
    rcases hM _ (Multiset.mem_cons_self _ _) with hl | ⟨p, hτ, hl⟩ | ⟨p, hl⟩
    · simp only at hl; subst hl
      rw [e']; exact ih' _ (junk_cons _ hJ)
    · simp only at hτ hl; subst hτ
      refine drain_chain hS hall hX hr hG p _ l hl ?_
      rw [e']; exact ih' _ (junk_cons _ hJ)
    · simp only at hl; subst hl
      have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_loopNil cS X ops ens p)
        (xs₁ := []) (xs₂ := []) (τ := τ) (M := M + J) (r := r)
      simp only [List.nil_append, List.map_nil, List.append_nil] at this
      apply this
      rw [e']; exact ih' _ (junk_cons _ hJ)

omit hS hall hX in
theorem drainable_tails (p : Bool) (v : ℕ → Bool) (c n : ℕ) :
    ∀ x ∈ tails X p v c n, Drainable X x := by
  intro x hx
  simp only [tails, Multiset.mem_coe, List.mem_map, List.mem_range'] at hx
  obtain ⟨a, -, rfl⟩ := hx
  refine Or.inr (Or.inl ⟨p, rfl, fun x hx => ?_⟩)
  simp only [tailC, rbs, List.mem_cons, List.mem_map, List.mem_reverse, List.mem_range] at hx
  rcases hx with rfl | ⟨j, hj, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, _, hj, rfl⟩)

/-! ## The start of a round -/

omit hS hall hX in
/-- **The start of a round** of the loop `ρ`: one more block (split off the loop), whose tree
is expanded into `2 ^ m` fresh threads. -/
theorem play_start (ρ : Bool) (M : Multiset (LCh ℕ ℕ)) (r : Rec (Ctl S))
    (hpre : ∀ c ∈ M, c.tag = preT ρ → c.lab = []) (hpost : ∀ c ∈ M, c.tag = postT ρ → c.lab = [])
    (h : ∀ J, Junk J → MW cS X allS ops ens σ₀
      (2 ^ mm X • {freshC ρ} + (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ M) + J) r) :
    MW cS X allS ops ens σ₀ (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ M) r := by
  have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_loop cS X ops ens ρ)
    (xs₁ := []) (xs₂ := []) (τ := postT ρ) (M := M) (r := r)
  simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lN, List.append_nil] at this
  apply this
  have hs : MW cS X allS ops ens σ₀ (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.block ρ)], preT ρ⟩ ::ₘ M) r → 
      MW cS X allS ops ens σ₀ (⟨[nL (.block ρ)] ++ [nL (.loop ρ)], postT ρ⟩ ::ₘ M) r :=
    MWin.split hpre hpost
  apply hs
  rw [Multiset.cons_swap]
  apply mv_set (m_block cS X ops ens ρ)
  simp only [List.map_cons, List.map_nil, toLab_lN, ← Multiset.cons_coe, Multiset.coe_nil]
  have e : (⟨[], preT ρ⟩ ::ₘ ((⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ M) +
        ((⟨[nL (.tree ρ (mm X))], preT ρ⟩ : LCh ℕ ℕ) ::ₘ (⟨[nL (.reT ρ)], preT ρ⟩ : LCh ℕ ℕ) ::ₘ 0)) :
        Multiset (LCh ℕ ℕ)) =
      ⟨[nL (.tree ρ (mm X))], preT ρ⟩ ::ₘ
        ((⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ M) + {⟨[], preT ρ⟩}) := by
    simp only [← Multiset.singleton_add]; abel
  rw [e]
  refine play_tree ρ (mm X) le_rfl _ r fun J hJ => ?_
  have e2 : (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ M) + {⟨[], preT ρ⟩} + J +
        2 ^ mm X • {freshC ρ} =
      2 ^ mm X • {freshC ρ} + (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ M) +
        (⟨[], preT ρ⟩ ::ₘ J) := by
    simp only [← Multiset.singleton_add]; abel
  rw [e2]
  exact h _ (junk_cons _ hJ)

/-! ## The rounds -/

omit hS hall hX in
/-- The chains at the start of a round of the loop `ρ`: both loops, the finish, and the tails of
the previous round (tape `v`). -/
def St (X : Spec S) (ρ : Bool) (v : ℕ → Bool) (J : Multiset (LCh ℕ ℕ)) : Multiset (LCh ℕ ℕ) :=
  ⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ ⟨[nL .finT], none⟩ ::ₘ
    (tails X (!ρ) v 0 (2 ^ mm X) + J)

omit hS hall hX in
theorem tag_tails {p : Bool} {v : ℕ → Bool} {c n : ℕ} :
    ∀ x ∈ tails X p v c n, x.tag = preT p := by
  intro x hx
  simp only [tails, Multiset.mem_coe, List.mem_map] at hx
  obtain ⟨a, -, rfl⟩ := hx
  rfl

omit hS hall hX in
theorem good_rst (ρ y : Bool) (σ : S) (cy dec : Bool) : Good X ⟨.wb 0, 0, ρ, y, rst σ cy dec⟩ where
  c_lt := Nat.two_pow_pos _
  wb_lt k h := by cases h; simp [mm]
  rb_lt k h := by cases h
  gs_lt ℓ h := by cases h
  s_le := Nat.zero_le _

/-- **A normal round** following the canonical run with guess `G`: the round start, the sweep,
then the continuation at the round end. -/
theorem play_normal (ρ : Bool) (rd : ℕ → Bool) (σ : S) (cy dec y : Bool) (J : Multiset (LCh ℕ ℕ))
    (hJ : Junk J) {G : Option ℕ} (hG : ∀ ℓ, G = some ℓ → ℓ < X.no ∧ σ = X.sg ℓ)
    (hops : ∀ o g b c, X.opOK o g b c → (∀ ℓ, g.gs = some ℓ → ℓ < X.no) → o ∈ ops)
    (hend : ∀ J', Junk J' → ∀ y', Good X ⟨.fin, 0, ρ, y', X.gAt G rd (rst σ cy dec) (4 * X.B)⟩ →
      MW cS X allS ops ens σ₀
        (tails X ρ (X.wAt G rd (rst σ cy dec)) 0 (2 ^ mm X) +
          (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ
            ⟨[nL .finT], none⟩ ::ₘ J'))
        ⟨.fin, 0, ρ, y', X.gAt G rd (rst σ cy dec) (4 * X.B)⟩) :
    MW cS X allS ops ens σ₀ (St X ρ rd J) ⟨.wb 0, 0, ρ, y, rst σ cy dec⟩ := by
  unfold St
  refine play_start ρ _ _ (fun c hc ht => ?_) (fun c hc ht => ?_) fun J' hJ' => ?_
  · simp only [Multiset.mem_cons, Multiset.mem_add] at hc
    rcases hc with rfl | rfl | hc | hc
    · cases ρ <;> simp at ht
    · simp at ht
    · rw [tag_tails c hc] at ht; cases ρ <;> simp at ht
    · exact hJ c hc
  · simp only [Multiset.mem_cons, Multiset.mem_add] at hc
    rcases hc with rfl | rfl | hc | hc
    · cases ρ <;> simp at ht
    · simp at ht
    · rw [tag_tails c hc] at ht; simp at ht
    · exact hJ c hc
  have hW : 2 ^ mm X = (2 ^ mm X - 1) + 1 := by have := Nat.two_pow_pos (mm X); omega
  have hrun := TT.Spec.srun_canon (X := X) (G := G) (rd := rd) (g₀ := rst σ cy dec) rfl
    (fun ℓ h => hG ℓ h) X.mach.W 0 (by simp)
  rw [X.mach_W] at hrun
  have e : 2 ^ mm X • {freshC ρ} + (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ
      ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ ⟨[nL .finT], none⟩ ::ₘ (tails X (!ρ) rd 0 (2 ^ mm X) + J)) + J' =
      (2 ^ mm X - 1 + 1) • {freshC ρ} + tails X (!ρ) rd 0 (2 ^ mm X - 1 + 1) +
        tails X ρ (X.wAt G rd (rst σ cy dec)) 0 0 +
        (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ
          ⟨[nL .finT], none⟩ ::ₘ (J + J')) := by
    rw [← hW]
    simp only [tails, List.range'_zero, List.map_nil, Multiset.coe_nil, ← Multiset.singleton_add]
    abel
  rw [e]
  refine play_sweep hS hall hX ρ rd (X.wAt G rd (rst σ cy dec)) (X.gAt G rd (rst σ cy dec) (4 * X.B)) hops
    (2 ^ mm X - 1) 0 (rst σ cy dec) y _ (by omega) ?_ (good_rst ρ y σ cy dec)
    fun J'' hJ'' y' hG' => ?_
  · exact hrun
  · have e2 : tails X ρ (X.wAt G rd (rst σ cy dec)) 0 (2 ^ mm X) + J'' +
        (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ
          ⟨[nL .finT], none⟩ ::ₘ (J + J')) =
        tails X ρ (X.wAt G rd (rst σ cy dec)) 0 (2 ^ mm X) +
          (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ
            ⟨[nL .finT], none⟩ ::ₘ (J + J' + J'')) := by
      simp only [← Multiset.singleton_add]; abel
    rw [e2]
    exact hend _ (junk_add (junk_add hJ hJ') hJ'') y' hG'

/-- **The finish**: execute `fin`, then drain every remaining chain. -/
theorem play_fin (ρ : Bool) (w' : ℕ → Bool) (g' : Ctl S) (y' : Bool) (J : Multiset (LCh ℕ ℕ))
    (hJ : Junk J) (hfin : X.finOK g') (hG : Good X ⟨.fin, 0, ρ, y', g'⟩) :
    MW cS X allS ops ens σ₀
      (tails X ρ w' 0 (2 ^ mm X) +
        (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ
          ⟨[nL .finT], none⟩ ::ₘ J))
      ⟨.fin, 0, ρ, y', g'⟩ := by
  set D : Multiset (LCh ℕ ℕ) := tails X ρ w' 0 (2 ^ mm X) +
    (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ {⟨[nL (.loop (!ρ))], postT (!ρ)⟩}) with hD
  have e : tails X ρ w' 0 (2 ^ mm X) +
      (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ
        ⟨[nL .finT], none⟩ ::ₘ J) = ⟨[nL .finT], none⟩ ::ₘ (D + J) := by
    rw [hD]; simp only [← Multiset.singleton_add]; abel
  rw [e]
  have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_finT cS X ops ens)
    (xs₁ := []) (xs₂ := []) (τ := none) (M := D + J) (r := ⟨.fin, 0, ρ, y', g'⟩)
  simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.append_nil] at this
  apply this
  refine mv_prim hS hall hX (a := .fin)
    (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr rfl))))))))) hG ⟨rfl, hfin⟩ (fun g h => by simp at h) fun r' hr' hG' => ?_
  simp only [Mach.outs, Set.mem_singleton_iff] at hr'
  subst hr'
  have e2 : (⟨[], none⟩ ::ₘ (D + J) : Multiset (LCh ℕ ℕ)) = D + (⟨[], none⟩ ::ₘ J) := by
    simp only [← Multiset.singleton_add]; abel
  rw [e2]
  refine drain_all hS hall hX rfl hG' D (fun c hc => ?_) _ (junk_cons _ hJ)
  rw [hD] at hc
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hc
  rcases hc with hc | rfl | rfl | rfl
  · exact drainable_tails ρ w' 0 _ c hc
  · exact Or.inr (Or.inr ⟨ρ, rfl⟩)
  · exact Or.inr (Or.inl ⟨ρ, rfl, fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact Or.inr (Or.inr ⟨ρ, rfl⟩)⟩)
  · exact Or.inr (Or.inr ⟨!ρ, rfl⟩)

/-- **All normal rounds**: a true claim (`TabWin`) at the start of a normal round is won, by
induction on the time `t`. -/
theorem play_rounds (hcover : ∀ i < 2 ^ (X.B + 1), ∃ ℓ < X.no, X.lo ℓ ≤ i ∧ i < X.hi ℓ)
    (hops : ∀ o g b c, X.opOK o g b c → (∀ ℓ, g.gs = some ℓ → ℓ < X.no) → o ∈ ops)
    (hens : ∀ e g, X.endOK e g → e ∈ ens) :
    ∀ t (ρ : Bool) (rd : ℕ → Bool) (σ : S) (cy dec y : Bool) (i : ℕ) (J : Multiset (LCh ℕ ℕ)),
      Junk J → ev rd (2 * X.B) = t →
      (if dec then i + cy.toNat = od rd (2 * X.B) else i = od rd (2 * X.B) + cy.toNat) →
      i + t < 2 ^ (X.B + 1) → TabWin X.F X.row0 t i σ →
      MW cS X allS ops ens σ₀ (St X ρ rd J) ⟨.wb 0, 0, ρ, y, rst σ cy dec⟩ := by
  intro t
  induction t with
  | zero =>
    intro ρ rd σ cy dec y i J hJ ht hi hb htab
    obtain ⟨G, hG, h⟩ := X.normal_round hX hcover hi (by rw [ht]; exact hb) (by rw [ht]; exact htab)
    rcases h with ⟨-, hfin⟩ | ⟨t', ht', -⟩
    · exact play_normal hS hall hX ρ rd σ cy dec y J hJ hG hops fun J' hJ' y' hG' =>
        play_fin hS hall hX ρ _ _ y' J' hJ' hfin hG'
    · omega
  | succ t ih =>
    intro ρ rd σ cy dec y i J hJ ht hi hb htab
    obtain ⟨G, hG, h⟩ := X.normal_round hX hcover hi (by rw [ht]; exact hb) (by rw [ht]; exact htab)
    rcases h with ⟨h0, -⟩ | ⟨t', ht', hevw, e, hok, hnext⟩
    · omega
    have htt : t' = t := by omega
    subst htt
    refine play_normal hS hall hX ρ rd σ cy dec y J hJ hG hops fun J' hJ' y' hG' => ?_
    set g' := X.gAt G rd (rst σ cy dec) (4 * X.B) with hg'
    set w' := X.wAt G rd (rst σ cy dec) with hw'
    have e1 : tails X ρ w' 0 (2 ^ mm X) +
        (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ
          ⟨[nL .finT], none⟩ ::ₘ J') =
        ⟨[nL (.reT ρ)], preT ρ⟩ ::ₘ (tails X ρ w' 0 (2 ^ mm X) +
          (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ ⟨[nL .finT], none⟩ ::ₘ J')) := by
      simp only [← Multiset.singleton_add]; abel
    rw [e1]
    have he := hens e g' hok
    have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_re cS X ops ens ρ he)
      (xs₁ := []) (xs₂ := []) (τ := preT ρ) (r := ⟨.fin, 0, ρ, y', g'⟩)
      (M := tails X ρ w' 0 (2 ^ mm X) +
          (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ ⟨[nL .finT], none⟩ ::ₘ J'))
    simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.append_nil] at this
    apply this
    refine mv_prim hS hall hX (a := .rend ρ e)
      (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨ρ, e, he, rfl⟩))))))))) hG' ⟨rfl, rfl, hok⟩ (fun g h => by simp at h)
      fun r' hr' hG'' => ?_
    simp only [Mach.outs, Set.mem_setOf_eq] at hr'
    obtain ⟨g'', hg'', rfl⟩ := hr'
    obtain ⟨σ'', cy'', dec'', i'', rfl, hi'', hb'', htab''⟩ := hnext g'' hg''
    have e2 : (⟨[], preT ρ⟩ ::ₘ (tails X ρ w' 0 (2 ^ mm X) +
          (⟨[nL (.loop ρ)], postT ρ⟩ ::ₘ ⟨[nL (.loop (!ρ))], postT (!ρ)⟩ ::ₘ ⟨[nL .finT], none⟩ ::ₘ J')) :
          Multiset (LCh ℕ ℕ)) = St X (!ρ) w' (⟨[], preT ρ⟩ ::ₘ J') := by
      simp only [St, Bool.not_not, ← Multiset.singleton_add]; abel
    rw [e2]
    exact ih (!ρ) w' σ'' cy'' dec'' y' i'' _ (junk_cons _ hJ') hevw hi'' hb'' htab''

/-! ## The opening and completeness -/

/-- **The opening**: decompose `main`, tag the loops, play the boot round writing the index `i`,
and end it with the accepting claim `σ`. -/
theorem play_open (hcover : ∀ i < 2 ^ (X.B + 1), ∃ ℓ < X.no, X.lo ℓ ≤ i ∧ i < X.hi ℓ)
    (hops : ∀ o g b c, X.opOK o g b c → (∀ ℓ, g.gs = some ℓ → ℓ < X.no) → o ∈ ops)
    (hens : ∀ e g, X.endOK e g → e ∈ ens) {σ : S} {i : ℕ} (hσ : σ ∈ X.acc) (hi : i < 2 ^ X.B)
    (htab : TabWin X.F X.row0 (2 ^ X.B - 1) i σ) :
    MW cS X allS ops ens σ₀ {⟨[nL .main], none⟩} (r₀ σ₀) := by
  apply mv_set (M := 0) (m_main cS X ops ens)
  simp only [List.map_cons, List.map_nil, toLab_lN, ← Multiset.cons_coe, Multiset.coe_nil, zero_add]
  -- tag the loops
  have e0 : (⟨[], none⟩ ::ₘ ⟨[nL (.loop true)], none⟩ ::ₘ ⟨[nL (.loop false)], none⟩ ::ₘ
      ⟨[nL .finT], none⟩ ::ₘ 0 : Multiset (LCh ℕ ℕ)) =
      ⟨[nL (.loop true)], none⟩ ::ₘ (⟨[], none⟩ ::ₘ ⟨[nL (.loop false)], none⟩ ::ₘ
        ⟨[nL .finT], none⟩ ::ₘ 0) := by
    simp only [← Multiset.singleton_add]; abel
  rw [e0]
  refine MWin.retag (g := true) (fun c hc ht => ?_) ?_
  · simp at hc
    rcases hc with rfl | rfl | rfl <;> simp at ht ⊢
  have e1 : (⟨[nL (.loop true)], postT true⟩ ::ₘ (⟨[], none⟩ ::ₘ ⟨[nL (.loop false)], none⟩ ::ₘ
      ⟨[nL .finT], none⟩ ::ₘ 0) : Multiset (LCh ℕ ℕ)) =
      ⟨[nL (.loop false)], none⟩ ::ₘ (⟨[nL (.loop true)], postT true⟩ ::ₘ ⟨[], none⟩ ::ₘ
        ⟨[nL .finT], none⟩ ::ₘ 0) := by
    simp only [← Multiset.singleton_add]; abel
  rw [e1]
  refine MWin.retag (g := false) (fun c hc ht => ?_) ?_
  · simp at hc
    rcases hc with rfl | rfl | rfl <;> simp at ht ⊢
  have e2 : (⟨[nL (.loop false)], postT false⟩ ::ₘ (⟨[nL (.loop true)], postT true⟩ ::ₘ ⟨[], none⟩ ::ₘ
      ⟨[nL .finT], none⟩ ::ₘ 0) : Multiset (LCh ℕ ℕ)) =
      ⟨[nL (.loop true)], postT true⟩ ::ₘ (⟨[nL (.loop false)], postT false⟩ ::ₘ
        ⟨[nL .finT], none⟩ ::ₘ {⟨[], none⟩}) := by
    simp only [← Multiset.singleton_add]; abel
  rw [e2]
  -- the boot round
  refine play_start true _ _ (fun c hc ht => ?_) (fun c hc ht => ?_) fun J hJ => ?_
  · simp at hc
    rcases hc with rfl | rfl | rfl <;> simp at ht ⊢
  · simp at hc
    rcases hc with rfl | rfl | rfl <;> simp at ht ⊢
  have hW : 2 ^ mm X = (2 ^ mm X - 1) + 1 := by have := Nat.two_pow_pos (mm X); omega
  set R : Multiset (LCh ℕ ℕ) := ⟨[nL (.loop true)], postT true⟩ ::ₘ ⟨[nL (.reT true)], preT true⟩ ::ₘ
    ⟨[nL (.loop false)], postT false⟩ ::ₘ ⟨[nL .finT], none⟩ ::ₘ (⟨[], none⟩ ::ₘ J) with hR
  have e : 2 ^ mm X • {freshC true} + (⟨[nL (.loop true)], postT true⟩ ::ₘ ⟨[nL (.reT true)], preT true⟩ ::ₘ
      ⟨[nL (.loop false)], postT false⟩ ::ₘ ⟨[nL .finT], none⟩ ::ₘ {⟨[], none⟩}) + J =
      (2 ^ mm X - 1 + 1) • {freshC true} + tails X true (X.wB i) 0 0 + R := by
    rw [← hW, hR]
    simp only [tails, List.range'_zero, List.map_nil, Multiset.coe_nil, ← Multiset.singleton_add]
    abel
  rw [e]
  refine play_sweepB hS hall hX true i σ₀ hops (2 ^ mm X - 1) 0 false R (by omega) good_r₀
    fun J' hJ' y' hG' => ?_
  -- the end of the boot round
  have e1 : tails X true (X.wB i) 0 (2 ^ mm X) + J' + R =
      ⟨[nL (.reT true)], preT true⟩ ::ₘ (tails X true (X.wB i) 0 (2 ^ mm X) +
        (⟨[nL (.loop true)], postT true⟩ ::ₘ ⟨[nL (.loop false)], postT false⟩ ::ₘ
          ⟨[nL .finT], none⟩ ::ₘ (⟨[], none⟩ ::ₘ (J + J')))) := by
    rw [hR]; simp only [← Multiset.singleton_add]; abel
  rw [e1]
  have he := hens (.boot σ) (g0 σ₀) ⟨rfl, hσ⟩
  have := mv_seq (cS := cS) (X := X) (allS := allS) (σ₀ := σ₀) (m_re cS X ops ens true he)
    (xs₁ := []) (xs₂ := []) (τ := preT true) (r := ⟨.fin, 0, true, y', g0 σ₀⟩)
    (M := tails X true (X.wB i) 0 (2 ^ mm X) +
        (⟨[nL (.loop true)], postT true⟩ ::ₘ ⟨[nL (.loop false)], postT false⟩ ::ₘ
          ⟨[nL .finT], none⟩ ::ₘ (⟨[], none⟩ ::ₘ (J + J'))))
  simp only [List.nil_append, List.map_cons, List.map_nil, toLab_lA, List.append_nil] at this
  apply this
  refine mv_prim hS hall hX (a := .rend true (.boot σ))
    (by rw [mem_acts_iff]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨true, _, he, rfl⟩))))))))) hG' ⟨rfl, rfl, rfl, hσ⟩ (fun g h => by simp at h)
    fun r' hr' hG'' => ?_
  simp only [Mach.outs, Set.mem_setOf_eq, Spec.mach, TT.Spec.endOut, Set.mem_singleton_iff] at hr'
  obtain ⟨g'', rfl, rfl⟩ := hr'
  have e2 : (⟨[], preT true⟩ ::ₘ (tails X true (X.wB i) 0 (2 ^ mm X) +
        (⟨[nL (.loop true)], postT true⟩ ::ₘ ⟨[nL (.loop false)], postT false⟩ ::ₘ
          ⟨[nL .finT], none⟩ ::ₘ (⟨[], none⟩ ::ₘ (J + J')))) : Multiset (LCh ℕ ℕ)) =
      St X false (X.wB i) (⟨[], preT true⟩ ::ₘ ⟨[], none⟩ ::ₘ (J + J')) := by
    simp only [St, Bool.not_false, ← Multiset.singleton_add]; abel
  rw [e2]
  have hB1 : 1 ≤ 2 ^ X.B := Nat.one_le_two_pow
  exact play_rounds hS hall hX hcover hops hens (2 ^ X.B - 1) false (X.wB i) σ false false y' i _
    (junk_cons _ (junk_cons _ (junk_add hJ hJ'))) (X.ev_wB i) (by simp [X.od_wB hi])
    (by rw [pow_succ]; omega) htab

/-- **Completeness of the description**: an accepting claim with a won tableau at the top time
gives a strong method-based policy. -/
theorem complete (hcover : ∀ i < 2 ^ (X.B + 1), ∃ ℓ < X.no, X.lo ℓ ≤ i ∧ i < X.hi ℓ)
    (hops : ∀ o g b c, X.opOK o g b c → (∀ ℓ, g.gs = some ℓ → ℓ < X.no) → o ∈ ops)
    (hens : ∀ e g, X.endOK e g → e ∈ ens) {σ : S} {i : ℕ} (hσ : σ ∈ X.acc) (hi : i < 2 ^ X.B)
    (htab : TabWin X.F X.row0 (2 ^ X.B - 1) i σ) :
    (desc cS X allS ops ens σ₀).toProblem.MPStrongSolvable := by
  have hv := valid cS X allS ops ens σ₀ hS
  have hP := FProbDesc.toProblem_wf hv
  rw [Problem.mpStrongSolvable_iff_mpAndOr hP]
  have hseq : (desc cS X allS ops ens σ₀).toProblem.tnI.IsSeqNet (List.range 1) [nL .main] := by
    have : (desc cS X allS ops ens σ₀).toProblem.tnI = (seqTn [lN .main]).toTaskNetwork := by
      simp only [FProbDesc.toProblem, tnI_desc]
    rw [this]
    simpa using isSeqNet_seqTn [lN .main]
  have hW := play_open hS hall hX hcover hops hens (allS := allS) (σ₀ := σ₀) hσ hi htab
  have hT := twin_of_mwin hW [⟨[nL .main], none⟩] rfl
  have := mpAndOr_of_twin hT (TC.of_isSeqNet hseq) rfl
  rwa [init_enc]

end TD

end HardTR

end FOND
