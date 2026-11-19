import FondHtn.HardTR.TGame
import FondHtn.MPStrong.CyclicGame
/-!
# A fair game on label chains

The fair counterpart of the label game `FOND.HardTR.TWin`: a set `Z` of chain positions
(lists of tagged label chains with a state) every position of which lies in the **attractor**
`FOND.FU.CA P Z` — all chains empty; or an executable action at the head of a chain, all of
whose outcomes stay in `Z` and one of which is in the attractor of lower rank; or the
decomposition of a chain head by a sequence method, or of a single-task chain by a set method,
staying in `Z` and in the attractor of lower rank.

**`FOND.FU.fairWin_of_chains`**: such a set gives the fair game `FOND.Problem.FairWin false` on
every network that is the tagged union of chains with the labels of a position of `Z`.  The
set of the network game consists of the networks isomorphic to such tagged unions; the moves
are those of `FOND.HardTR.mpAndOr_of_twin`.
-/

namespace FOND

namespace FU

open HTN HTN.TaskNetwork HardTR

variable {F A C : Type} (P : Problem F A C ℕ)

/-- **The attractor of the fair chain game.** -/
inductive CA (Z : List (LCh A C) → Set F → Prop) : ℕ → List (LCh A C) → Set F → Prop
  | goal {n : ℕ} {ls : List (LCh A C)} {s : Set F} (h : ∀ c ∈ ls, c.lab = []) : CA Z n ls s
  | prim {n : ℕ} {ls : List (LCh A C)} {s : Set F} {k : ℕ} (hk : k < ls.length) {a : A}
      {rest : List (A ⊕ C)} {τ : Option (Bool × Bool)} (hc : ls[k] = ⟨.inl a :: rest, τ⟩)
      (hfree : ∀ g, τ = some (g, true) → ∀ i (hi : i < ls.length), ls[i].tag = some (g, false) →
        ls[i].lab = [])
      (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, Z (ls.set k ⟨rest, τ⟩) s') {s₀ : Set F}
      (hs₀ : s₀ ∈ (P.δ a).outcomes s) (h : CA Z n (ls.set k ⟨rest, τ⟩) s₀) : CA Z (n + 1) ls s
  | seq {n : ℕ} {ls : List (LCh A C)} {s : Set F} {k : ℕ} (hk : k < ls.length)
      {xs₁ xs₂ : List (A ⊕ C)} {c : C} {τ : Option (Bool × Bool)}
      (hc : ls[k] = ⟨xs₁ ++ .inr c :: xs₂, τ⟩)
      {m : Method ℕ A C} (hm : m ∈ P.methods) (hmc : m.abstractTask = c) {bs : List (A ⊕ C)}
      (hseq : ∃ l, m.subtasks.IsSeqNet l bs)
      (hZ : Z (ls.set k ⟨xs₁ ++ bs ++ xs₂, τ⟩) s)
      (h : CA Z n (ls.set k ⟨xs₁ ++ bs ++ xs₂, τ⟩) s) : CA Z (n + 1) ls s
  | set {n : ℕ} {ls : List (LCh A C)} {s : Set F} {k : ℕ} (hk : k < ls.length) {c : C}
      {τ : Option (Bool × Bool)} (hc : ls[k] = ⟨[.inr c], τ⟩)
      {m : Method ℕ A C} (hm : m ∈ P.methods) (hmc : m.abstractTask = c) {bs : List (A ⊕ C)}
      (hset : ∃ l, AcycHard.SetNet m.subtasks l bs)
      (hZ : Z (ls.set k ⟨[], τ⟩ ++ bs.map fun b => ⟨[b], τ⟩) s)
      (h : CA Z n (ls.set k ⟨[], τ⟩ ++ bs.map fun b => ⟨[b], τ⟩) s) : CA Z (n + 1) ls s

/-- A fair set of chain positions. -/
def CSet (Z : List (LCh A C) → Set F → Prop) : Prop := ∀ ls s, Z ls s → ∃ n, CA P Z n ls s

/-- The networks isomorphic to tagged unions of the chains of a position. -/
def XN (Z : List (LCh A C) → Set F → Prop) : Problem.NSet F A C ℕ := fun tn s =>
  tn.WF ∧ ∃ (tn' : TaskNetwork ℕ A C) (σ : ℕ → ℕ) (cs : List (TCh A C)), tn'.WF ∧ IsoVia σ tn' tn ∧
    TC tn' cs ∧ Z (cs.map TCh.proj) s

variable {P}

theorem xn_good (Z : List (LCh A C) → Set F → Prop) : Problem.NGood (XN Z) := by
  refine ⟨fun _ _ h => h.1, fun tn tn' s σ h hw' hσ => ?_⟩
  obtain ⟨-, u, τ, cs, hu, hτ, htc, hz⟩ := h
  exact ⟨hw', u, σ ∘ τ, cs, hu, hτ.comp hσ, htc, hz⟩

theorem xn_of_tc {Z : List (LCh A C) → Set F → Prop} {tn : TaskNetwork ℕ A C} {cs : List (TCh A C)}
    {s : Set F} (hwf : tn.WF) (htc : TC tn cs) (hz : Z (cs.map TCh.proj) s) : XN Z tn s :=
  ⟨hwf, tn, id, cs, hwf, IsoVia.refl _, htc, hz⟩

/-- **The chain attractor gives the network attractor.** -/
theorem fattr_of_ca {Z : List (LCh A C) → Set F → Prop} {n : ℕ} {ls : List (LCh A C)} {s : Set F}
    (h : CA P Z n ls s) :
    ∀ {tn : TaskNetwork ℕ A C} {cs : List (TCh A C)}, tn.WF → TC tn cs → cs.map TCh.proj = ls →
      P.FAttrH false (XN Z) n tn s := by
  induction h with
  | @goal n ls s hls =>
    intro tn cs _ htc he
    refine .goal (Finset.eq_empty_of_forall_notMem fun x hx => ?_)
    obtain ⟨j, hj, hx⟩ := (htc.mem x).1 hx
    have hl := hls (ls[j]'(by rw [← len_eq he]; exact hj)) (List.getElem_mem _)
    rw [proj_get he hj] at hl
    have := htc.lab j hj
    rw [show cs[j].lab = [] from hl] at this
    rw [List.map_eq_nil_iff] at this
    rw [this] at hx; simp at hx
  | @prim n ls s k hk a rest τ hc hfree happ hall s₀ hs₀ _ ih =>
    intro tn cs hwf htc he
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
    have hwf' := TaskNetwork.progress_wf hwf hu
    have htc' := htc.progress hk' hcs hu
    have he' : (cs.set k ⟨rids, rest, τ⟩).map TCh.proj = ls.set k ⟨rest, τ⟩ := by
      rw [List.map_set, he]
      simp [TCh.proj, hrest]
    refine .prim hu hαt happ (fun s' hs' => xn_of_tc hwf' htc' (by rw [he']; exact hall s' hs')) hs₀
      (ih hwf' htc' he')
  | @seq n ls s k hk xs₁ xs₂ c τ hc m hm hmc bs hseq hZ _ ih =>
    intro tn cs hwf htc he
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
    have huwf : u.WF := PCP.shiftNet_wf hl0.wf _
    have hiso : u.Iso m.subtasks := PCP.shiftNet_iso _ _
    obtain ⟨lm, hlm⟩ := hl0.iso huwf hiso.symm
    have hdisj : Disjoint tn.T u.T := fresh_copy m.subtasks
    have htT : t ∈ tn.T := (htc.mem t).2 ⟨k, hk', by rw [hcs]; simp⟩
    have hwf' := decomposeWith_wf (t := t) hwf huwf hdisj
    have htc' := htc.step_seq hk' hcs hlen hlm hdisj
    have he' : (cs.set k ⟨l₁ ++ lm ++ l₂, xs₁ ++ bs ++ xs₂, τ⟩).map TCh.proj =
        ls.set k ⟨xs₁ ++ bs ++ xs₂, τ⟩ := by
      rw [List.map_set, he]; rfl
    refine .decomp (fun h => absurd h (by simp)) ⟨hm, htT, by rw [hαt, hmc], u, huwf, hiso, hdisj, rfl⟩
      (xn_of_tc hwf' htc' (by rw [he']; exact hZ)) (ih hwf' htc' he')
  | @set n ls s k hk c τ hc m hm hmc bs hset hZ _ ih =>
    intro tn cs hwf htc he
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
    have huwf : u.WF := PCP.shiftNet_wf (setNet_wf hl0) _
    have hiso : u.Iso m.subtasks := PCP.shiftNet_iso _ _
    obtain ⟨lm, hlm⟩ := hl0.iso huwf hiso.symm
    have hdisj : Disjoint tn.T u.T := fresh_copy m.subtasks
    have htT : t ∈ tn.T := (htc.mem t).2 ⟨k, hk', by rw [hcs]; simp⟩
    have hlmb : lm.length = bs.length := by rw [← hlm.labels, List.length_map]
    have hwf' := decomposeWith_wf (t := t) hwf huwf hdisj
    have htc' := htc.step_set hk' hcs hlm hdisj
    have he' : (cs.set k ⟨[], [], τ⟩ ++ TC.singlesT lm bs τ).map TCh.proj =
        ls.set k ⟨[], τ⟩ ++ bs.map fun b => ⟨[b], τ⟩ := by
      rw [List.map_append, List.map_set, he, map_singlesT _ _ hlmb]; rfl
    refine .decomp (fun h => absurd h (by simp)) ⟨hm, htT, by rw [hαt, hmc], u, huwf, hiso, hdisj, rfl⟩
      (xn_of_tc hwf' htc' (by rw [he']; exact hZ)) (ih hwf' htc' he')

/-- **A fair set of chain positions gives the fair game on the networks.** -/
theorem fairWin_of_chains [DecidableEq F] {Z : List (LCh A C) → Set F → Prop} (hZ : CSet P Z)
    {tn : TaskNetwork ℕ A C} {cs : List (TCh A C)} {s : Set F} (hwf : tn.WF) (htc : TC tn cs)
    (h0 : Z (cs.map TCh.proj) s) : P.FairWin false tn s := by
  refine ⟨XN Z, xn_good Z, xn_of_tc hwf htc h0, fun tn s hX => ?_⟩
  obtain ⟨hwf, tn', σ, cs, hwf', hiso, htc, hz⟩ := hX
  obtain ⟨n, hn⟩ := hZ _ _ hz
  exact ⟨n, (fattr_of_ca hn hwf' htc rfl).isoVia (xn_good Z) hwf' hwf hiso⟩

end FU

end FOND
