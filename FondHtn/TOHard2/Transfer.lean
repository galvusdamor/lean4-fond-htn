import FondHtn.TOHard2.Shape
/-!
# Two chains after a claim: the transfer of claims

Every method of a claim `K a` (except the first row of the prefix) ends with two nested chains
`Ch(A₁, Ch(A₂, y))`: after `y`, the chain of `A₂` (on the cell digit) and then the chain of `A₁`
(on the time digit) run.

* `FOND.TOHard2.lgh_ch2` — in the list game, the two chains commit runs of the automata before
  `y` runs; `FOND.TOHard2.LG.ch2` is the converse;
* `FOND.TOHard2.wp_chain2` — the semantics of the two chains (`wp_chain` twice);
* **`FOND.TOHard2.transfer`** — if the postcondition `Ψ'` of the inner claim is *covered* (it
  contains states for every challenged index, `FOND.TOHard2.Cover`), then the outer
  postcondition is covered, and every *pinning* of the outer postcondition by digit functions
  `tg, ig` (`FOND.TOHard2.Pin`) pins the inner postcondition by digit functions related to
  `tg, ig` by the committed digit types.
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

variable (P : Par)

/-- States with a clean counter. -/
def Shaped (s : St) : Prop := s.ov = false ∧ s.ctr = fun _ => false

/-- The postcondition contains clean states for all challenged indices. -/
def Cover (Ψ : Set Cfg) : Prop := ∀ k < 2 ^ P.b, ∃ s, Shaped s ∧ s.chkV P.b = k ∧ s.cfg ∈ Ψ

/-- The clean states of the postcondition hold the digits of `tg`, `ig` at the challenged index. -/
def Pin (Ψ : Set Cfg) (tg ig : ℕ → Bool) : Prop :=
  ∀ s, Shaped s → s.cfg ∈ Ψ → s.tb = tg (s.chkV P.b) ∧ s.ib = ig (s.chkV P.b)

theorem shaped_fn (s : St) : Shaped (fn s) := ⟨rfl, rfl⟩

theorem fn_setReg (s : St) (r v : Bool) : fn ((fn s).setReg r v) = fn (s.setReg r v) := by
  cases r <;> rfl

/-! ## The list game -/

theorem lgh_ch {A : Comp} {y n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} {Ψ : Set Cfg}
    (h : LGH (gram P) n ((true, chN A y) :: xs) c Ψ) :
    ∃ as, Run A.aut as A.aut.acc ∧ LGH (gram P) n ((true, y) :: syms (chain P.b P.cs as) ++ xs) c Ψ := by
  rcases n with _ | n
  · exact absurd h not_lgh_zero
  obtain ⟨bs, hb, h⟩ := lgh_comp_iff.1 h
  rw [gram_methL] at hb
  rw [meth_ch P hb] at h
  simp only [chBody, List.cons_append, List.nil_append] at h
  obtain ⟨as, hrun, h'⟩ := lgh_lam (G := gram P) (A := A.aut) (lam := fun σ => lamN A σ y) (y := y)
    (blk := block P.b P.cs) (fun σ bs h => lam_sound P σ bs h) h
  have h'' := h'.mono (n' := n + 1) (by omega) le_rfl
  exact ⟨as, hrun, by simpa [chain, blocks, List.append_assoc] using h''⟩

theorem lgh_ch2 {A₁ A₂ : Comp} {y n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} {Ψ : Set Cfg}
    (h : LGH (gram P) n ((true, chN A₁ (chN A₂ y)) :: xs) c Ψ) :
    ∃ as₁ as₂, Run A₁.aut as₁ A₁.aut.acc ∧ Run A₂.aut as₂ A₂.aut.acc ∧
      LGH (gram P) n ((true, y) :: syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ xs) c Ψ := by
  obtain ⟨as₁, h1, h⟩ := lgh_ch P h
  rw [List.cons_append] at h
  obtain ⟨as₂, h2, h⟩ := lgh_ch P h
  exact ⟨as₁, as₂, h1, h2, by simpa [List.append_assoc] using h⟩

theorem LG.ch {A : Comp} {y : ℕ} (hin : ChIn P A y) {as : List AT} (hrun : Run A.aut as A.aut.acc)
    {xs : List (Bool × ℕ)} {c : Cfg} {Ψ : Set Cfg}
    (h : LG (gram P) ((true, y) :: syms (chain P.b P.cs as) ++ xs) c Ψ) :
    LG (gram P) ((true, chN A y) :: xs) c Ψ := by
  refine LG.comp (hin _ (List.mem_cons_self ..)) ?_
  simp only [chBody, List.cons_append, List.nil_append]
  refine LG.ofLam (G := gram P) (A := A.aut) (lam := fun σ => lamN A σ y) (y := y)
    (blk := block P.b P.cs) (fun σ bs h => lam_complete P hin σ bs h) hrun ?_
  simpa [chain, blocks, List.append_assoc] using h

theorem LG.ch2 {A₁ A₂ : Comp} {y : ℕ} (hin₁ : ChIn P A₁ (chN A₂ y)) (hin₂ : ChIn P A₂ y)
    {as₁ as₂ : List AT} (hrun₁ : Run A₁.aut as₁ A₁.aut.acc) (hrun₂ : Run A₂.aut as₂ A₂.aut.acc)
    {xs : List (Bool × ℕ)} {c : Cfg} {Ψ : Set Cfg}
    (h : LG (gram P) ((true, y) :: syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ xs) c Ψ) :
    LG (gram P) ((true, chN A₁ (chN A₂ y)) :: xs) c Ψ :=
  LG.ch P hin₁ hrun₁ (by rw [List.cons_append]; exact LG.ch P hin₂ hrun₂ (by simpa [List.append_assoc] using h))

/-! ## The semantics of the chains -/

section Sem

variable {P} (hcs : ∀ k, ∀ e ∈ P.cs.getI k, e < 2 ^ P.b)
include hcs

/-- **A chain on a register.** -/
theorem wp_chainR {as : List AT} {r : Bool} (hreg : ∀ a ∈ as, a = .id ∨ a.reg = r) {Ψ : Set Cfg}
    {s : St} (hs : Shaped s) :
    s.cfg ∈ wpP (inss (chain P.b P.cs as)) Ψ ↔ as.length = 2 ^ P.b ∧
      ∃ v, (as.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) (s.reg r) = some v ∧
        (fn (s.setReg r v)).cfg ∈ Ψ := by
  rw [wp_chain hcs as hs.1 hs.2]
  refine and_congr_right fun hl => ?_
  have hk : s.chkV P.b < as.length := hl ▸ ofB_lt _ _
  rcases hreg _ (List.getD_mem' hk) with ha | ha
  · rw [ha]
    simp only [rho_id, exists_eq_left, St.setReg_reg]
  · rw [ha]


/-- **Two chains**: the cell chain `as₂`, then the time chain `as₁`. -/
theorem wp_chain2 {as₁ as₂ : List AT} (hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = true)
    (hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false) {Ψ : Set Cfg} {s : St} (hs : Shaped s) :
    s.cfg ∈ wpP (inss (chain P.b P.cs as₂ ++ chain P.b P.cs as₁)) Ψ ↔
      as₂.length = 2 ^ P.b ∧ as₁.length = 2 ^ P.b ∧
      ∃ v₂ v₁, (as₂.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) s.ib = some v₂ ∧
        (as₁.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) s.tb = some v₁ ∧
        (fn { s with ib := v₂, tb := v₁ }).cfg ∈ Ψ := by
  rw [inss_append, wpP_append, wp_chainR hcs hreg₂ hs]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨v₂, h2, h⟩
    rw [wp_chainR hcs hreg₁ (shaped_fn _)] at h
    obtain ⟨hl, v₁, h1, h⟩ := h
    exact ⟨hl, v₂, v₁, h2, h1, by rwa [fn_setReg] at h⟩
  · rintro ⟨hl, v₂, v₁, h2, h1, h⟩
    refine ⟨v₂, h2, ?_⟩
    rw [wp_chainR hcs hreg₁ (shaped_fn _)]
    exact ⟨hl, v₁, h1, by rwa [fn_setReg]⟩

/-- **Two chains on the cell digit.** -/
theorem wp_chain2I {as₁ as₂ : List AT} (hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = false)
    (hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false) {Ψ : Set Cfg} {s : St} (hs : Shaped s) :
    s.cfg ∈ wpP (inss (chain P.b P.cs as₂ ++ chain P.b P.cs as₁)) Ψ ↔
      as₂.length = 2 ^ P.b ∧ as₁.length = 2 ^ P.b ∧
      ∃ v₂ v₁, (as₂.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) s.ib = some v₂ ∧
        (as₁.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) v₂ = some v₁ ∧
        (fn { s with ib := v₁ }).cfg ∈ Ψ := by
  rw [inss_append, wpP_append, wp_chainR hcs hreg₂ hs]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨v₂, h2, h⟩
    rw [wp_chainR hcs hreg₁ (shaped_fn _)] at h
    obtain ⟨hl, v₁, h1, h⟩ := h
    exact ⟨hl, v₂, v₁, h2, h1, by rwa [fn_setReg] at h⟩
  · rintro ⟨hl, v₂, v₁, h2, h1, h⟩
    refine ⟨v₂, h2, ?_⟩
    rw [wp_chainR hcs hreg₁ (shaped_fn _)]
    exact ⟨hl, v₁, h1, by rwa [fn_setReg]⟩

/-- **The transfer of claims through two chains.** -/
theorem transfer {as₁ as₂ : List AT} (hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = true)
    (hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false) {Ψ Ψ' : Set Cfg}
    (hΨ' : ∀ s, Shaped s → s.cfg ∈ Ψ' → s.cfg ∈ wpP (inss (chain P.b P.cs as₂ ++ chain P.b P.cs as₁)) Ψ)
    (hcov : Cover P Ψ') :
    Cover P Ψ ∧ as₁.length = 2 ^ P.b ∧ as₂.length = 2 ^ P.b ∧ ∀ tg ig, Pin P Ψ tg ig →
      ∃ tg' ig', Pin P Ψ' tg' ig' ∧ Rel P.cs as₁ tg' tg ∧ Rel P.cs as₂ ig' ig := by
  have key : ∀ s, Shaped s → s.cfg ∈ Ψ' → as₂.length = 2 ^ P.b ∧ as₁.length = 2 ^ P.b ∧
      ∃ v₂ v₁, (as₂.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) s.ib = some v₂ ∧
        (as₁.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) s.tb = some v₁ ∧
        (fn { s with ib := v₂, tb := v₁ }).cfg ∈ Ψ := fun s hs h =>
    (wp_chain2 hcs hreg₁ hreg₂ hs).1 (hΨ' s hs h)
  obtain ⟨s0, hs0, -, h0⟩ := hcov 0 (Nat.two_pow_pos _)
  obtain ⟨hl₂, hl₁, -⟩ := key s0 hs0 h0
  refine ⟨fun k hk => ?_, hl₁, hl₂, fun tg ig hpin => ?_⟩
  · obtain ⟨s, hs, hk', h⟩ := hcov k hk
    obtain ⟨-, -, v₂, v₁, -, -, h⟩ := key s hs h
    exact ⟨_, shaped_fn { s with ib := v₂, tb := v₁ }, hk', h⟩
  · -- the outputs at each challenged index are the digits of `tg`, `ig`
    have hout : ∀ s, Shaped s → s.cfg ∈ Ψ' →
        (as₂.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) s.ib = some (ig (s.chkV P.b)) ∧
        (as₁.getD (s.chkV P.b) .id).rho P.cs (s.chkV P.b) s.tb = some (tg (s.chkV P.b)) := by
      intro s hs h
      obtain ⟨-, -, v₂, v₁, h2, h1, h⟩ := key s hs h
      obtain ⟨e1, e2⟩ := hpin _ (shaped_fn _) h
      have : (fn { s with ib := v₂, tb := v₁ }).chkV P.b = s.chkV P.b := rfl
      rw [this] at e1 e2
      exact ⟨e2 ▸ h2, e1 ▸ h1⟩
    classical
    let wit : ℕ → St := fun k => if hk : k < 2 ^ P.b then (hcov k hk).choose else s0
    have hwit : ∀ k < 2 ^ P.b, Shaped (wit k) ∧ (wit k).chkV P.b = k ∧ (wit k).cfg ∈ Ψ' := by
      intro k hk
      simp only [wit, dif_pos hk]
      exact (hcov k hk).choose_spec
    refine ⟨fun k => (wit k).tb, fun k => (wit k).ib, fun s hs h => ?_, fun d hd => ?_, fun d hd => ?_⟩
    · have hk : s.chkV P.b < 2 ^ P.b := ofB_lt _ _
      obtain ⟨hw1, hw2, hw3⟩ := hwit _ hk
      obtain ⟨o2, o1⟩ := hout s hs h
      obtain ⟨o2', o1'⟩ := hout _ hw1 hw3
      rw [hw2] at o2' o1'
      exact ⟨AT.rho_inj o1 o1', AT.rho_inj o2 o2'⟩
    · obtain ⟨hw1, hw2, hw3⟩ := hwit d (hl₁ ▸ hd)
      have := (hout _ hw1 hw3).2
      rwa [hw2] at this
    · obtain ⟨hw1, hw2, hw3⟩ := hwit d (hl₂ ▸ hd)
      have := (hout _ hw1 hw3).1
      rwa [hw2] at this

end Sem

end TOHard2

end FOND
