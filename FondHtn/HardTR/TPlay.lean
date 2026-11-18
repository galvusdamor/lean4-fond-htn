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

open TL TT TE HardMP HTN HTN.Syn HTN.Article AcycHard.Sav

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

end TD

end HardTR

end FOND
