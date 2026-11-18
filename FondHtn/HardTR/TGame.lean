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

end HardTR

end FOND
