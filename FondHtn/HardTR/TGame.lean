import FondHtn.HardTR.TChains
import FondHtn.MethodPolicies
import FondHtn.PCP.Decomp
import FondHtn.HardTR.NetY
/-!
# A game on tagged label chains

`FOND.HardTR.TWin P ls s`: a game on lists of tagged label chains — execute an unconstrained
action at the head of a chain, decompose a compound task inside a chain by a sequence method or
a singleton chain by a set method, or split a post-chain.  **`FOND.HardTR.mpAndOr_of_twin`**: a
won game is a won AND/OR game of method-based policies on every network that is the tagged
union of chains with these labels.  Strategies can thus be described on labels only.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

open HTN AcycHard

variable {F A C : Type}

/-- A tagged label chain. -/
structure LCh (A C : Type) where
  lab : List (A ⊕ C)
  tag : Option (Bool × Bool)

deriving instance DecidableEq for LCh

/-- The labels of a tagged chain. -/
def TCh.proj (c : TCh A C) : LCh A C := ⟨c.lab, c.tag⟩

variable (P : Problem F A C ℕ)

/-- **The game on tagged label chains.** -/
inductive TWin : List (LCh A C) → Set F → Prop
  | empty {ls : List (LCh A C)} {s : Set F} (h : ∀ c ∈ ls, c.lab = []) : TWin ls s
  | prim {ls : List (LCh A C)} {s : Set F} {k : ℕ} (hk : k < ls.length) {a : A}
      {rest : List (A ⊕ C)} {τ : Option (Bool × Bool)} (hc : ls[k] = ⟨.inl a :: rest, τ⟩)
      (hfree : ∀ g, τ = some (g, true) → ∀ i (hi : i < ls.length), ls[i].tag = some (g, false) →
        ls[i].lab = [])
      (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, TWin (ls.set k ⟨rest, τ⟩) s') : TWin ls s
  | seq {ls : List (LCh A C)} {s : Set F} {k : ℕ} (hk : k < ls.length) {xs₁ xs₂ : List (A ⊕ C)}
      {c : C} {τ : Option (Bool × Bool)} (hc : ls[k] = ⟨xs₁ ++ .inr c :: xs₂, τ⟩)
      {m : Method ℕ A C} (hm : m ∈ P.methods) (hmc : m.abstractTask = c) {bs : List (A ⊕ C)}
      (hseq : ∃ l, m.subtasks.IsSeqNet l bs)
      (h : TWin (ls.set k ⟨xs₁ ++ bs ++ xs₂, τ⟩) s) : TWin ls s
  | set {ls : List (LCh A C)} {s : Set F} {k : ℕ} (hk : k < ls.length) {c : C}
      {τ : Option (Bool × Bool)} (hc : ls[k] = ⟨[.inr c], τ⟩)
      {m : Method ℕ A C} (hm : m ∈ P.methods) (hmc : m.abstractTask = c) {bs : List (A ⊕ C)}
      (hset : ∃ l, SetNet m.subtasks l bs)
      (h : TWin (ls.set k ⟨[], τ⟩ ++ bs.map fun b => ⟨[b], τ⟩) s) : TWin ls s
  | split {ls : List (LCh A C)} {s : Set F} {k : ℕ} (hk : k < ls.length) {xs₁ xs₂ : List (A ⊕ C)}
      {g : Bool} (hc : ls[k] = ⟨xs₁ ++ xs₂, some (g, true)⟩)
      (hpre : ∀ i (hi : i < ls.length), ls[i].tag = some (g, false) → ls[i].lab = [])
      (hpost : ∀ i (hi : i < ls.length), i ≠ k → ls[i].tag = some (g, true) → ls[i].lab = [])
      (h : TWin (ls.set k ⟨xs₂, some (g, true)⟩ ++ [⟨xs₁, some (g, false)⟩]) s) : TWin ls s
  | retag {ls : List (LCh A C)} {s : Set F} {k : ℕ} (hk : k < ls.length) {xs : List (A ⊕ C)}
      {g : Bool} (hc : ls[k] = ⟨xs, none⟩)
      (hpre : ∀ i (hi : i < ls.length), ls[i].tag = some (g, false) → ls[i].lab = [])
      (h : TWin (ls.set k ⟨xs, some (g, true)⟩) s) : TWin ls s

/-! ## Simulation -/

variable {P}

theorem proj_get {cs : List (TCh A C)} {ls : List (LCh A C)} (he : cs.map TCh.proj = ls) {k : ℕ}
    (hk : k < cs.length) : ls[k]'(by rw [← he]; simpa using hk) = cs[k].proj := by
  subst he; simp

theorem len_eq {cs : List (TCh A C)} {ls : List (LCh A C)} (he : cs.map TCh.proj = ls) :
    cs.length = ls.length := by
  rw [← he, List.length_map]

/-- A fresh copy of a method's subtask network. -/
theorem fresh_copy {tn : TaskNetwork ℕ A C} (m : TaskNetwork ℕ A C) :
    Disjoint tn.T (PCP.shiftNet m (tn.T.sup id + 1)).T := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have h1 := (PCP.mem_shiftNet.1 hx').1
  have h2 : x ≤ tn.T.sup id := Finset.le_sup (f := id) hx
  omega

theorem map_singlesT {τ : Option (Bool × Bool)} :
    ∀ (lm : List ℕ) (bs : List (A ⊕ C)), lm.length = bs.length →
      (TC.singlesT lm bs τ).map TCh.proj = bs.map fun b => ⟨[b], τ⟩
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: lm, b :: bs, h => by
    simp only [TC.singlesT, List.zip_cons_cons, List.map_cons] at *
    congr 1
    exact map_singlesT lm bs (by simpa using h)

/-- **The label game simulates the AND/OR game.** -/
theorem mpAndOr_of_twin {ls : List (LCh A C)} {s : Set F} (h : TWin P ls s) :
    ∀ {tn : TaskNetwork ℕ A C} {cs : List (TCh A C)}, TC tn cs → cs.map TCh.proj = ls →
      P.MPAndOr tn s := by
  induction h with
  | @empty ls s hls =>
    intro tn cs htc he
    refine .empty (Finset.eq_empty_of_forall_notMem fun x hx => ?_)
    obtain ⟨j, hj, hx⟩ := (htc.mem x).1 hx
    have hl := hls (ls[j]'(by rw [← len_eq he]; exact hj)) (List.getElem_mem _)
    rw [proj_get he hj] at hl
    have := htc.lab j hj
    rw [show cs[j].lab = [] from hl] at this
    rw [List.map_eq_nil_iff] at this
    rw [this] at hx; simp at hx
  | @prim ls s k hk a rest τ hc hfree happ hall ih =>
    intro tn cs htc he
    have hk' : k < cs.length := by rw [len_eq he]; exact hk
    have hck := proj_get he hk'
    rw [hc] at hck
    have hlab := htc.lab k hk'
    have hl : cs[k].lab = .inl a :: rest := by have := congrArg LCh.lab hck; simpa [TCh.proj] using this.symm
    have htg : cs[k].tag = τ := by have := congrArg LCh.tag hck; simpa [TCh.proj] using this.symm
    rw [hl] at hlab
    obtain ⟨t, rids, hids, hαt, hrest⟩ := List.map_eq_cons_iff.1 hlab
    have hcs : cs[k] = ⟨t :: rids, .inl a :: rest, τ⟩ := by
      rw [← hids, ← hl, ← htg]
    have hu : tn.Unconstrained t := htc.unconstrained hk' hids fun g hg i hi hti => by
      have hi' : i < ls.length := by rw [← len_eq he]; exact hi
      have hp := proj_get he hi
      have h1 := hfree g (by rw [← htg]; exact hg) i hi' (by rw [hp]; exact hti)
      rw [hp] at h1
      have := htc.lab i hi
      rw [show cs[i].lab = [] from h1, List.map_eq_nil_iff] at this
      exact this
    refine .prim hu hαt happ fun s' hs' => ih s' hs' (htc.progress hk' hcs hu) ?_
    rw [List.map_set, he]
    simp [TCh.proj, hrest]
  | @seq ls s k hk xs₁ xs₂ c τ hc m hm hmc bs hseq hw ih =>
    intro tn cs htc he
    have hk' : k < cs.length := by rw [len_eq he]; exact hk
    have hck := proj_get he hk'
    rw [hc] at hck
    have hlab := htc.lab k hk'
    have hl : cs[k].lab = xs₁ ++ .inr c :: xs₂ := by
      have := congrArg LCh.lab hck; simpa [TCh.proj] using this.symm
    have htg : cs[k].tag = τ := by have := congrArg LCh.tag hck; simpa [TCh.proj] using this.symm
    rw [hl] at hlab
    obtain ⟨l₁, l', hids, hl₁, hl'⟩ := List.map_eq_append_iff.1 hlab
    obtain ⟨t, l₂, rfl, hαt, hl₂⟩ := List.map_eq_cons_iff.1 hl'
    have hcs : cs[k] = ⟨l₁ ++ t :: l₂, xs₁ ++ .inr c :: xs₂, τ⟩ := by
      rw [← hids, ← hl, ← htg]
    have hlen : l₁.length = xs₁.length := by rw [← hl₁, List.length_map]
    obtain ⟨l, hl0⟩ := hseq
    set u := PCP.shiftNet m.subtasks (tn.T.sup id + 1) with hu
    have hwf : u.WF := PCP.shiftNet_wf hl0.wf _
    have hiso : u.Iso m.subtasks := PCP.shiftNet_iso _ _
    obtain ⟨lm, hlm⟩ := hl0.iso hwf hiso.symm
    have hdisj : Disjoint tn.T u.T := fresh_copy m.subtasks
    have htT : t ∈ tn.T := (htc.mem t).2 ⟨k, hk', by rw [hcs]; simp⟩
    refine .decomp ⟨hm, htT, by rw [hαt, hmc], u, hwf, hiso, hdisj, rfl⟩
      (ih (htc.step_seq hk' hcs hlen hlm hdisj) ?_)
    rw [List.map_set, he]
    rfl
  | @set ls s k hk c τ hc m hm hmc bs hset hw ih =>
    intro tn cs htc he
    have hk' : k < cs.length := by rw [len_eq he]; exact hk
    have hck := proj_get he hk'
    rw [hc] at hck
    have hlab := htc.lab k hk'
    have hl : cs[k].lab = [.inr c] := by
      have := congrArg LCh.lab hck; simpa [TCh.proj] using this.symm
    have htg : cs[k].tag = τ := by have := congrArg LCh.tag hck; simpa [TCh.proj] using this.symm
    rw [hl] at hlab
    obtain ⟨t, l₂, hids, hαt, hl₂⟩ := List.map_eq_cons_iff.1 hlab
    rw [List.map_eq_nil_iff] at hl₂
    subst hl₂
    have hcs : cs[k] = ⟨[t], [.inr c], τ⟩ := by rw [← hids, ← hl, ← htg]
    obtain ⟨l, hl0⟩ := hset
    set u := PCP.shiftNet m.subtasks (tn.T.sup id + 1) with hu
    have hwf : u.WF := PCP.shiftNet_wf (setNet_wf hl0) _
    have hiso : u.Iso m.subtasks := PCP.shiftNet_iso _ _
    obtain ⟨lm, hlm⟩ := hl0.iso hwf hiso.symm
    have hdisj : Disjoint tn.T u.T := fresh_copy m.subtasks
    have htT : t ∈ tn.T := (htc.mem t).2 ⟨k, hk', by rw [hcs]; simp⟩
    have hlmb : lm.length = bs.length := by rw [← hlm.labels, List.length_map]
    refine .decomp ⟨hm, htT, by rw [hαt, hmc], u, hwf, hiso, hdisj, rfl⟩
      (ih (htc.step_set hk' hcs hlm hdisj) ?_)
    rw [List.map_append, List.map_set, he, map_singlesT _ _ hlmb]
    rfl
  | @split ls s k hk xs₁ xs₂ g hc hpre hpost hw ih =>
    intro tn cs htc he
    have hk' : k < cs.length := by rw [len_eq he]; exact hk
    have hck := proj_get he hk'
    rw [hc] at hck
    have hlab := htc.lab k hk'
    have hl : cs[k].lab = xs₁ ++ xs₂ := by
      have := congrArg LCh.lab hck; simpa [TCh.proj] using this.symm
    have htg : cs[k].tag = some (g, true) := by
      have := congrArg LCh.tag hck; simpa [TCh.proj] using this.symm
    rw [hl] at hlab
    obtain ⟨l₁, l₂, hids, hl₁, hl₂⟩ := List.map_eq_append_iff.1 hlab
    have hcs : cs[k] = ⟨l₁ ++ l₂, xs₁ ++ xs₂, some (g, true)⟩ := by rw [← hids, ← hl, ← htg]
    have hlen : l₁.length = xs₁.length := by rw [← hl₁, List.length_map]
    have hempty : ∀ i (hi : i < cs.length), (ls[i]'(by rw [← len_eq he]; exact hi)).lab = [] →
        cs[i].ids = [] := fun i hi h1 => by
      rw [proj_get he hi] at h1
      have := htc.lab i hi
      rw [show cs[i].lab = [] from h1, List.map_eq_nil_iff] at this
      exact this
    have hsp := htc.split hk' hcs hlen
      (fun i hi hti => hempty i hi (hpre i _ (by rw [proj_get he hi]; exact hti)))
      (fun i hi hik hti => hempty i hi (hpost i _ hik (by rw [proj_get he hi]; exact hti)))
    refine ih hsp ?_
    rw [List.map_append, List.map_set, he]
    simp [TCh.proj, hl₁, hl₂]
  | @retag ls s k hk xs g hc hpre hw ih =>
    intro tn cs htc he
    have hk' : k < cs.length := by rw [len_eq he]; exact hk
    have hck := proj_get he hk'
    rw [hc] at hck
    have hl : cs[k].lab = xs := by have := congrArg LCh.lab hck; simpa [TCh.proj] using this.symm
    have htg : cs[k].tag = none := by have := congrArg LCh.tag hck; simpa [TCh.proj] using this.symm
    have hcs : cs[k] = ⟨cs[k].ids, xs, none⟩ := by rw [← hl, ← htg]
    have hempty : ∀ i (hi : i < cs.length), (ls[i]'(by rw [← len_eq he]; exact hi)).lab = [] →
        cs[i].ids = [] := fun i hi h1 => by
      rw [proj_get he hi] at h1
      have := htc.lab i hi
      rw [show cs[i].lab = [] from h1, List.map_eq_nil_iff] at this
      exact this
    refine ih (htc.retag hk' hcs (fun i hi hti => hempty i hi (hpre i _ (by rw [proj_get he hi]; exact hti)))) ?_
    rw [List.map_set, he]
    rfl

/-! ## The game on multisets of chains -/

variable (P)

/-- **The game on multisets of tagged label chains**: the chosen chain is split off. -/
inductive MWin : Multiset (LCh A C) → Set F → Prop
  | empty {M : Multiset (LCh A C)} {s : Set F} (h : ∀ c ∈ M, c.lab = []) : MWin M s
  | prim {M : Multiset (LCh A C)} {s : Set F} {a : A} {rest : List (A ⊕ C)}
      {τ : Option (Bool × Bool)}
      (hfree : ∀ g, τ = some (g, true) → ∀ c ∈ M, c.tag = some (g, false) → c.lab = [])
      (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, MWin (⟨rest, τ⟩ ::ₘ M) s') :
      MWin (⟨.inl a :: rest, τ⟩ ::ₘ M) s
  | seq {M : Multiset (LCh A C)} {s : Set F} {xs₁ xs₂ : List (A ⊕ C)} {c : C}
      {τ : Option (Bool × Bool)} {m : Method ℕ A C} (hm : m ∈ P.methods) (hmc : m.abstractTask = c)
      {bs : List (A ⊕ C)} (hseq : ∃ l, m.subtasks.IsSeqNet l bs)
      (h : MWin (⟨xs₁ ++ bs ++ xs₂, τ⟩ ::ₘ M) s) : MWin (⟨xs₁ ++ .inr c :: xs₂, τ⟩ ::ₘ M) s
  | set {M : Multiset (LCh A C)} {s : Set F} {c : C} {τ : Option (Bool × Bool)}
      {m : Method ℕ A C} (hm : m ∈ P.methods) (hmc : m.abstractTask = c) {bs : List (A ⊕ C)}
      (hset : ∃ l, SetNet m.subtasks l bs)
      (h : MWin (⟨[], τ⟩ ::ₘ (M + (bs.map fun b => (⟨[b], τ⟩ : LCh A C) : Multiset (LCh A C)))) s) :
      MWin (⟨[.inr c], τ⟩ ::ₘ M) s
  | split {M : Multiset (LCh A C)} {s : Set F} {xs₁ xs₂ : List (A ⊕ C)} {g : Bool}
      (hpre : ∀ c ∈ M, c.tag = some (g, false) → c.lab = [])
      (hpost : ∀ c ∈ M, c.tag = some (g, true) → c.lab = [])
      (h : MWin (⟨xs₂, some (g, true)⟩ ::ₘ ⟨xs₁, some (g, false)⟩ ::ₘ M) s) :
      MWin (⟨xs₁ ++ xs₂, some (g, true)⟩ ::ₘ M) s
  | retag {M : Multiset (LCh A C)} {s : Set F} {xs : List (A ⊕ C)} {g : Bool}
      (hpre : ∀ c ∈ M, c.tag = some (g, false) → c.lab = [])
      (h : MWin (⟨xs, some (g, true)⟩ ::ₘ M) s) : MWin (⟨xs, none⟩ ::ₘ M) s

variable {P}

theorem coe_eraseIdx {α : Type} : ∀ (ls : List α) {k : ℕ} (hk : k < ls.length),
    (ls : Multiset α) = ls[k] ::ₘ ((ls.eraseIdx k : List α) : Multiset α)
  | [], _, hk => by simp at hk
  | a :: l, 0, _ => by simp
  | a :: l, k + 1, hk => by
    simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, ← Multiset.cons_coe]
    rw [coe_eraseIdx l (by simpa using hk), Multiset.cons_swap]

theorem coe_set_idx {α : Type} : ∀ (ls : List α) {k : ℕ} (hk : k < ls.length) (x : α),
    ((ls.set k x : List α) : Multiset α) = x ::ₘ ((ls.eraseIdx k : List α) : Multiset α)
  | [], _, hk, _ => by simp at hk
  | a :: l, 0, _, x => by simp
  | a :: l, k + 1, hk, x => by
    simp only [List.set_cons_succ, List.eraseIdx_cons_succ, ← Multiset.cons_coe]
    rw [coe_set_idx l (by simpa using hk), Multiset.cons_swap]

theorem pick {α : Type} {ls : List α} {c : α} {M : Multiset α} (he : (ls : Multiset α) = c ::ₘ M) :
    ∃ k, ∃ hk : k < ls.length, ls[k] = c ∧ ((ls.eraseIdx k : List α) : Multiset α) = M := by
  have hc : c ∈ ls := by
    have : c ∈ (ls : Multiset α) := by rw [he]; exact Multiset.mem_cons_self _ _
    simpa using this
  obtain ⟨k, hk, hkc⟩ := List.getElem_of_mem hc
  refine ⟨k, hk, hkc, ?_⟩
  have := coe_eraseIdx ls hk
  rw [he, hkc] at this
  exact (Multiset.cons_inj_right c).1 this.symm

theorem mem_rest {α : Type} {ls : List α} {k i : ℕ} (hi : i < ls.length) (hik : i ≠ k) :
    ls[i] ∈ ((ls.eraseIdx k : List α) : Multiset α) := by
  rw [Multiset.mem_coe, List.mem_eraseIdx_iff_getElem]
  exact ⟨i, hi, hik, rfl⟩

/-- **The multiset game is the list game.** -/
theorem twin_of_mwin [DecidableEq A] [DecidableEq C] {M : Multiset (LCh A C)} {s : Set F}
    (h : MWin P M s) : ∀ ls : List (LCh A C), (ls : Multiset (LCh A C)) = M → TWin P ls s := by
  induction h with
  | @empty M s hM =>
    intro ls he
    exact .empty fun c hc => hM c (by rw [← he]; simpa using hc)
  | @prim M s a rest τ hfree happ hall ih =>
    intro ls he
    obtain ⟨k, hk, hkc, hM⟩ := pick he
    refine .prim hk hkc (fun g hg i hi hti => ?_) happ fun s' hs' => ih s' hs' _ ?_
    · have hik : i ≠ k := fun e => by subst e; rw [hkc] at hti; rw [hg] at hti; simp at hti
      exact hfree g hg _ (by rw [← hM]; exact mem_rest hi hik) hti
    · rw [coe_set_idx ls hk, hM]
  | @seq M s xs₁ xs₂ c τ m hm hmc bs hseq hw ih =>
    intro ls he
    obtain ⟨k, hk, hkc, hM⟩ := pick he
    refine .seq hk hkc hm hmc hseq (ih _ ?_)
    rw [coe_set_idx ls hk, hM]
  | @set M s c τ m hm hmc bs hset hw ih =>
    intro ls he
    obtain ⟨k, hk, hkc, hM⟩ := pick he
    refine .set hk hkc hm hmc hset (ih _ ?_)
    rw [← Multiset.coe_add, coe_set_idx ls hk, hM, Multiset.cons_add]
  | @split M s xs₁ xs₂ g hpre hpost hw ih =>
    intro ls he
    obtain ⟨k, hk, hkc, hM⟩ := pick he
    refine .split hk hkc (fun i hi hti => ?_) (fun i hi hik hti => ?_) (ih _ ?_)
    · have hik : i ≠ k := fun e => by subst e; rw [hkc] at hti; simp at hti
      exact hpre _ (by rw [← hM]; exact mem_rest hi hik) hti
    · exact hpost _ (by rw [← hM]; exact mem_rest hi hik) hti
    · rw [← Multiset.coe_add, coe_set_idx ls hk, hM, Multiset.coe_singleton, Multiset.cons_add,
        Multiset.add_comm, Multiset.singleton_add]
  | @retag M s xs g hpre hw ih =>
    intro ls he
    obtain ⟨k, hk, hkc, hM⟩ := pick he
    refine .retag (g := g) hk hkc (fun i hi hti => ?_) (ih _ ?_)
    · have hik : i ≠ k := fun e => by subst e; rw [hkc] at hti; simp at hti
      exact hpre _ (by rw [← hM]; exact mem_rest hi hik) hti
    · rw [coe_set_idx ls hk, hM]

/-- Empty chains do not matter. -/
theorem MWin.add_empty {M : Multiset (LCh A C)} {s : Set F} (h : MWin P M s) :
    ∀ {J : Multiset (LCh A C)}, (∀ c ∈ J, c.lab = []) → MWin P (M + J) s := by
  induction h with
  | empty hM =>
    intro J hJ
    exact .empty fun c hc => (Multiset.mem_add.1 hc).elim (hM c) (hJ c)
  | prim hfree happ hall ih =>
    intro J hJ
    rw [Multiset.cons_add]
    refine .prim (fun g hg c hc htc => ?_) happ fun s' hs' => by
      have := ih s' hs' hJ; rwa [Multiset.cons_add] at this
    rcases Multiset.mem_add.1 hc with hc | hc
    · exact hfree g hg c hc htc
    · exact hJ c hc
  | seq hm hmc hseq hw ih =>
    intro J hJ
    rw [Multiset.cons_add]
    exact .seq hm hmc hseq (by have := ih hJ; rwa [Multiset.cons_add] at this)
  | set hm hmc hset hw ih =>
    intro J hJ
    rw [Multiset.cons_add]
    refine .set hm hmc hset ?_
    have := ih hJ
    rw [Multiset.cons_add] at this
    convert this using 2
    rw [add_right_comm]
  | split hpre hpost hw ih =>
    intro J hJ
    rw [Multiset.cons_add]
    refine .split (fun c hc htc => ?_) (fun c hc htc => ?_) ?_
    · rcases Multiset.mem_add.1 hc with hc | hc
      · exact hpre c hc htc
      · exact hJ c hc
    · rcases Multiset.mem_add.1 hc with hc | hc
      · exact hpost c hc htc
      · exact hJ c hc
    · have := ih hJ; rwa [Multiset.cons_add, Multiset.cons_add] at this
  | @retag M s xs g hpre hw ih =>
    intro J hJ
    rw [Multiset.cons_add]
    refine .retag (g := g) (fun c hc htc => ?_) ?_
    · rcases Multiset.mem_add.1 hc with hc | hc
      · exact hpre c hc htc
      · exact hJ c hc
    · have := ih hJ; rwa [Multiset.cons_add] at this

end HardTR

end FOND
