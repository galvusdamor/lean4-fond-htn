import FondHtn.AcycHard.Fifo
/-!
# Supply: the queue game with a rich pool

The queue game `FOND.AcycHard.FSpec.QWin` keeps track of the pool `U` of fresh cells and
options.  If every allowed symbol and every allowed option is available at least as often as
there are steps left (and the pool holds nothing else), the pool never runs out and can be
forgotten:

* `FOND.AcycHard.FSpec.QI` — the **supply-free queue game**: a step on `σ :: q` lets the player
  append an allowed `τ` and execute an allowed option `o`;
* **`FOND.AcycHard.FSpec.qwin_iff_qi`** — `QWin prog q U d ↔ QI prog q d` for a rich `U`;
* **`FOND.AcycHard.FSpec.cwin_iff_qi`** — the chain game of the cell construction is the
  supply-free queue game started from `b^S`.
-/

namespace FOND

namespace AcycHard

set_option linter.unusedSectionVars false

namespace FSpec

variable {Sym O D P : Type} [DecidableEq Sym] [DecidableEq O] (X : FSpec Sym O D P)
  (aS : Sym → Prop) (aO : O → Prop)

/-- **The supply-free queue game** with allowed symbols `aS` and allowed options `aO`. -/
def QI : List (Option P) → List Sym → Set D → Prop
  | [], _, _ => True
  | some p :: r, q, d => X.ppre p ⊆ d ∧ ∀ e ∈ X.peffs p, QI r q (WSys.upd d e.1 e.2)
  | none :: _, [], _ => False
  | none :: r, σ :: q, d => ∃ τ, aS τ ∧ ∃ o, aO o ∧
      X.opre o ⊆ insert (X.wr τ) (insert (X.rd σ) d) ∧
      QI r (q ++ [τ]) (WSys.upd (insert (X.wr τ) (insert (X.rd σ) d)) (X.oadd o) (X.odel o))

/-- A pool with at least `n` fresh cells of every allowed symbol and `n` copies of every allowed
option, and nothing else besides finished chains. -/
structure Rich (U : Multiset (List (PA Sym O))) (n : ℕ) : Prop where
  cells : ∀ τ, aS τ → n ≤ U.count (X.newCell τ)
  opts : ∀ o, aO o → n ≤ U.count [.opt o]
  shape : ∀ c ∈ U, c = [] ∨ (∃ τ, aS τ ∧ c = X.newCell τ) ∨ ∃ o, aO o ∧ c = [.opt o]

variable {X aS aO}

lemma Rich.uok {U : Multiset (List (PA Sym O))} {n : ℕ} (h : X.Rich aS aO U n) : X.UOk U := by
  intro c hc
  rcases h.shape c hc with h' | ⟨τ, -, h'⟩ | ⟨o, -, h'⟩
  · exact Or.inl h'
  · exact Or.inr (Or.inl ⟨τ, h'⟩)
  · exact Or.inr (Or.inr ⟨o, h'⟩)

lemma newCell_ne_nil (τ : Sym) : X.newCell τ ≠ ([] : List (PA Sym O)) := by simp [newCell]

lemma newCell_ne_opt (τ : Sym) (o : O) : X.newCell τ ≠ [PA.opt o] := by simp [newCell]

lemma newCell_inj {τ τ' : Sym} (h : X.newCell (O := O) τ = X.newCell τ') : τ = τ' := by
  simp only [newCell, List.cons.injEq, PA.init.injEq] at h
  exact h.1

lemma count_erase_ge {α : Type} [DecidableEq α] (a b : α) (s : Multiset α) :
    s.count a - 1 ≤ (s.erase b).count a := by
  by_cases h : a = b
  · subst h; rw [Multiset.count_erase_self]
  · rw [Multiset.count_erase_of_ne h]; omega

lemma Rich.step {U : Multiset (List (PA Sym O))} {n : ℕ} (h : X.Rich aS aO U (n + 1))
    (τ : Sym) (o : O) :
    X.Rich aS aO ([] ::ₘ (([] ::ₘ U).erase (X.newCell τ)).erase [.opt o]) n := by
  refine ⟨fun τ' hτ' => ?_, fun o' ho' => ?_, fun c hc' => ?_⟩
  · rw [Multiset.count_cons_of_ne (newCell_ne_nil τ'),
      Multiset.count_erase_of_ne (newCell_ne_opt τ' o)]
    have h1 := count_erase_ge (X.newCell τ') (X.newCell τ) ([] ::ₘ U)
    rw [Multiset.count_cons_of_ne (newCell_ne_nil τ')] at h1
    have := h.cells τ' hτ'
    omega
  · rw [Multiset.count_cons_of_ne (by simp)]
    have h1 := count_erase_ge [PA.opt o'] [PA.opt o] (([] ::ₘ U).erase (X.newCell τ))
    rw [Multiset.count_erase_of_ne (fun h => newCell_ne_opt τ o' h.symm),
      Multiset.count_cons_of_ne (by simp)] at h1
    have := h.opts o' ho'
    omega
  · rcases Multiset.mem_cons.1 hc' with rfl | hc'
    · exact Or.inl rfl
    · have := Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hc')
      rcases Multiset.mem_cons.1 this with rfl | this
      · exact Or.inl rfl
      · exact h.shape c this

/-- **With a rich pool, the queue game is the supply-free queue game.** -/
theorem qwin_iff_qi : ∀ (prog : List (Option P)) (q : List Sym) (U : Multiset (List (PA Sym O)))
    (d : Set D), X.Rich aS aO U (steps prog) → (X.QWin prog q U d ↔ X.QI aS aO prog q d) := by
  intro prog
  induction prog with
  | nil => intro q U d _; simp [QWin, QI]
  | cons i r ih =>
    intro q U d hU
    cases i with
    | some p =>
      simp only [QWin, QI]
      exact and_congr_right fun _ => forall₂_congr fun e _ => ih q U _ (by simpa [steps] using hU)
    | none =>
      cases q with
      | nil => simp [QWin, QI]
      | cons σ q =>
        simp only [QWin, QI]
        have hU' : X.Rich aS aO U (steps r + 1) := by simpa [steps] using hU
        have hmemτ : ∀ τ, X.newCell τ ∈ [] ::ₘ U ↔ aS τ := by
          intro τ
          constructor
          · intro hm
            rcases Multiset.mem_cons.1 hm with h' | hm
            · exact absurd h' (newCell_ne_nil τ)
            · rcases hU'.shape _ hm with h' | ⟨τ', hτ', h'⟩ | ⟨o, -, h'⟩
              · exact absurd h' (newCell_ne_nil τ)
              · exact newCell_inj h' ▸ hτ'
              · exact absurd h' (newCell_ne_opt τ o)
          · intro hτ
            refine Multiset.mem_cons_of_mem (Multiset.count_pos.1 ?_)
            have := hU'.cells τ hτ
            omega
        have hmemo : ∀ τ o, [PA.opt o] ∈ ([] ::ₘ U).erase (X.newCell τ) ↔ aO o := by
          intro τ o
          rw [Multiset.mem_erase_of_ne (fun h => newCell_ne_opt τ o h.symm)]
          constructor
          · intro hm
            rcases Multiset.mem_cons.1 hm with h' | hm
            · simp at h'
            · rcases hU'.shape _ hm with h' | ⟨τ', -, h'⟩ | ⟨o', ho', h'⟩
              · simp at h'
              · exact absurd h'.symm (newCell_ne_opt τ' o)
              · simp only [List.cons.injEq, PA.opt.injEq, and_true] at h'
                exact h' ▸ ho'
          · intro ho
            refine Multiset.mem_cons_of_mem (Multiset.count_pos.1 ?_)
            have := hU'.opts o ho
            omega
        constructor
        · rintro ⟨τ, hτ, o, ho, hpre, hw⟩
          have hτ' := (hmemτ τ).1 hτ
          have ho' := (hmemo τ o).1 ho
          exact ⟨τ, hτ', o, ho', hpre, (ih _ _ _ (hU'.step τ o)).1 hw⟩
        · rintro ⟨τ, hτ, o, ho, hpre, hw⟩
          exact ⟨τ, (hmemτ τ).2 hτ, o, (hmemo τ o).2 ho, hpre,
            (ih _ _ _ (hU'.step τ o)).2 hw⟩

/-- **The cell construction is the supply-free queue game**: the chain game (control chain
`preW (tri S) · expandQ prog · refill^R`, pool of `S` blank cells and a rich supply `U`) is won
iff the supply-free queue game is won from the queue `b^S`. -/
theorem cwin_iff_qi (hne : ∀ p, (X.peffs p).Nonempty) {U : Multiset (List (PA Sym O))}
    (prog : List (Option P)) (hU : X.Rich aS aO U (steps prog)) (hst : X.S ≤ steps prog)
    (b : Sym) (d : Set D) (R : ℕ)
    (hR : WSys.size (liveR (Multiset.replicate X.S (b, X.S)) + U) ≤ R) :
    CWin X.sys.δC X.sys.δP (WSys.expand (preW (tri X.S) ++ X.expandQ prog) ++
        List.replicate R .refill) (liveR (Multiset.replicate X.S (b, X.S)) + U) (WSys.idle d) ↔
      X.QI aS aO prog (List.replicate X.S b) d := by
  rw [X.cwin_fifo_iff hne hU.uok prog hst b d R hR]
  exact qwin_iff_qi prog _ U d hU

end FSpec

end AcycHard

end FOND
