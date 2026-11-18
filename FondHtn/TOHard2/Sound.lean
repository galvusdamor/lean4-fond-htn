import FondHtn.TOHard2.Transfer
import HtnComplexity.Article.TOHardSound
/-!
# Soundness of the claims

`FOND.TOHard2.Hyp P d tabC`: the parameters `P` describe the tableau data `d` (with
`d.B = 2 ^ b`) of a table `tabC` satisfying `HTN.Article.TabData.Good`, and the constants `cs`
are the set digits of `c₁`, `c₂` and of the prefix cells.

**`FOND.TOHard2.sound`**: if the policy wins the claim `K a` from a clean state with
postcondition `Ψ`, then `Ψ` is covered (`FOND.TOHard2.Cover`), and whenever `Ψ` is pinned by
the digit functions `tg, ig` (`FOND.TOHard2.Pin`), `tabC t i = a` for the numbers `t, i` with
these digits.  Induction on the height of the list game; the step uses `FOND.TOHard2.transfer`
and the arithmetic of the components (`run_inc`, `run_dec`, `run_cpy`, `run_cmp`).

**`FOND.TOHard2.root_sound`**: a winning policy for the root yields a cell `i < 2 ^ D` whose
entry at the last time `2 ^ D - 1` is accepting.
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

/-- **The parameters describe the tableau.** -/
structure Hyp (P : Par) (d : TabData) (tabC : ℕ → ℕ → ℕ) : Prop where
  good : d.Good tabC
  hB : d.B = 2 ^ P.b
  mid : P.mid = d.mid
  lft : P.lft = d.lft
  rgt : P.rgt = d.rgt
  acc : P.acc = d.acc
  baseU : P.baseU = d.baseU
  c₁ : d.c₁ = P.baseU.length
  codeTrue : P.codeTrue = d.codeTrue
  codeNone : P.codeNone = d.codeNone
  csl : P.cs.length = 2 + P.baseU.length
  cs : ∀ k, ∀ e ∈ P.cs.getI k, e < 2 ^ P.b
  k0 : ofB (kDig P.cs 0) (2 ^ P.b) = d.c₁
  k1 : ofB (kDig P.cs 1) (2 ^ P.b) = d.c₂
  kc : ∀ c < P.baseU.length, ofB (kDig P.cs (2 + c)) (2 ^ P.b) = c

/-! ## Auxiliary facts -/

theorem Run.mem_trans {A : Aut} {as : List AT} {σ : ℕ} (h : Run A as σ) :
    ∀ a ∈ as, ∃ σ' σ'', (σ', a, σ'') ∈ A.trans := by
  induction h with
  | one ht => intro a ha; simp at ha; subst ha; exact ⟨_, _, ht⟩
  | snoc h ht ih =>
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact ih a ha
    · simp at ha; subst ha; exact ⟨_, _, ht⟩

/-- The register of a component. -/
def Comp.reg : Comp → Bool
  | .inc rg => rg
  | .dec rg => rg
  | _ => false

theorem Comp.reg_ok (A : Comp) : ∀ t ∈ A.aut.trans, t.2.1 = .id ∨ t.2.1.reg = A.reg := by
  cases A <;> simp [Comp.aut, Comp.reg, AT.reg]

theorem run_reg {A : Comp} {as : List AT} {σ : ℕ} (h : Run A.aut as σ) :
    ∀ a ∈ as, a = .id ∨ a.reg = A.reg := by
  intro a ha
  obtain ⟨σ', σ'', ht⟩ := h.mem_trans a ha
  exact A.reg_ok _ ht

/-- The constants used by a component. -/
def Comp.Ok (n : ℕ) : Comp → Prop
  | .cmp k _ => k < n
  | _ => True

theorem Comp.ok_trans {A : Comp} {n : ℕ} (hA : A.Ok n) : ∀ t ∈ A.aut.trans, t.2.1.Ok n := by
  cases A <;> simp_all [Comp.aut, AT.Ok, Comp.Ok]

theorem run_ok {A : Comp} {n : ℕ} (hA : A.Ok n) {as : List AT} {σ : ℕ} (h : Run A.aut as σ) :
    ∀ a ∈ as, a.Ok n := by
  intro a ha
  obtain ⟨σ', σ'', ht⟩ := h.mem_trans a ha
  exact Comp.ok_trans hA _ ht

/-- Check components do not change the register. -/
def Comp.Check : Comp → Prop
  | .cmp _ _ => True
  | .cpy => True
  | .bits => True
  | _ => False

theorem Comp.check_trans {A : Comp} (hA : A.Check) :
    ∀ t ∈ A.aut.trans, ∀ (cs : List (List ℕ)) (d : ℕ) (z v : Bool), t.2.1.rho cs d z = some v → v = z := by
  cases A <;> simp only [Comp.Check] at hA <;> simp [Comp.aut] <;> intros <;> simp_all

theorem run_check {A : Comp} (hA : A.Check) {as : List AT} {σ : ℕ} (h : Run A.aut as σ)
    {cs : List (List ℕ)} {d : ℕ} {z v : Bool} (hd : d < as.length)
    (hr : (as.getD d .id).rho cs d z = some v) : v = z := by
  obtain ⟨σ', σ'', ht⟩ := h.mem_trans _ (List.getD_mem' hd)
  exact Comp.check_trans hA _ ht cs d z v hr

theorem wp_pickChks_list (l : List ℕ) : ∀ {Ψ : Set Cfg} {s : St},
    s.cfg ∈ wpP (inss (l.map pickChkI)) Ψ ↔
      ∀ g : ℕ → Bool, { s with chk := fun r => if r ∈ l then g r else s.chk r }.cfg ∈ Ψ := by
  induction l with
  | nil => intro Ψ s; simp
  | cons r l ih =>
    intro Ψ s
    rw [List.map_cons, inss_cons, wpP_cons, wp_pickChk]
    simp only [ih]
    constructor
    · intro h g
      have := h (g r) g
      convert this using 3
      funext r'
      by_cases h1 : r' ∈ l
      · simp [h1]
      · by_cases h2 : r' = r
        · subst h2; simp
        · simp [h1, h2, Function.update_apply]
    · intro h v g
      have := h (fun r' => if r' ∈ l then g r' else if r' = r then v else s.chk r')
      convert this using 3
      funext r'
      by_cases h1 : r' ∈ l
      · simp [h1]
      · by_cases h2 : r' = r
        · subst h2; simp [h1]
        · simp [h1, h2, Function.update_apply]

theorem wp_pickChks (P : Par) {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpP (inss (pickChks P)) Ψ ↔
      ∀ g : ℕ → Bool, { s with chk := fun r => if r < P.b then g r else s.chk r }.cfg ∈ Ψ := by
  rw [pickChks, wp_pickChks_list]
  simp only [List.mem_range]

theorem chkV_pick (P : Par) (s : St) (g : ℕ → Bool) :
    ({ s with chk := fun r => if r < P.b then g r else s.chk r } : St).chkV P.b = ofB g P.b :=
  ofB_congr fun r hr => by simp [hr]

theorem ofB_eq_of_digits {g g' : ℕ → Bool} {n : ℕ} (h : ∀ r < n, g r = g' r) : ofB g n = ofB g' n :=
  ofB_congr h

theorem lgh_bs {G : Gram} {n : ℕ} {bs : List (Bool × ℕ)} {c : Cfg} {Ψ : Set Cfg}
    (h : LGH G n (bs ++ []) c Ψ) : LGH G n bs c Ψ := by simpa using h

/-! ## The modes -/

/-- The cell component of a challenge. -/
def modeI (m : ℕ) : Comp := if m = 0 then .inc false else if m = 1 then .cpy else .dec false

theorem modeBody_eq (m x : ℕ) : modeBody m x =
    [(false, (assertMI m).1), (true, chN (.inc true) (chN (modeI m) (KN x)))] := by
  unfold modeBody modeI
  split_ifs <;> rfl

section Modes

variable (P : Par) (hP : 2 ≤ P.cs.length)
include hP

theorem modeI_ok (m : ℕ) : (modeI m).Ok P.cs.length := by
  unfold modeI; split_ifs <;> trivial

/-- **A challenge body**, in the list game. -/
theorem mode_step {m x n : ℕ} (hm3 : m < 3) {postP : List (ℕ × List ASpec)}
    (hpost : ∀ q ∈ postP, q ∈ (gram P).insL)
    {s : St} {Ψ : Set Cfg} (h : LGH (gram P) n (modeBody m x ++ syms postP) s.cfg Ψ) :
    s.val (4 + m) = true ∧ ∃ n' < n, ∃ asT asI, Run (Comp.inc true).aut asT 1 ∧
      Run (modeI m).aut asI (modeI m).aut.acc ∧
      LGH (gram P) n' [(true, KN x)] s.cfg
        {c | c ∈ wpP (inss (chain P.b P.cs asI ++ chain P.b P.cs asT ++ postP)) Ψ} := by
  rw [modeBody_eq] at h
  rcases n with _ | n
  · exact absurd h not_lgh_zero
  simp only [List.cons_append, List.nil_append] at h
  have hm : (assertMI m) ∈ (gram P).insL := by
    apply insRaw_mem_of_mem
    interval_cases m <;> simp
  obtain ⟨hv, h⟩ := wp_assertM.1 ((lgh_ins_iff (gram_good P).nodup hm).1 h)
  obtain ⟨asT, asI, hT, hI, h⟩ := lgh_ch2 P h
  refine ⟨hv, n, by omega, asT, asI, hT, hI, ?_⟩
  have h' := lgh_append h (xs := [(true, KN x)])
    (ys := syms (chain P.b P.cs asI ++ chain P.b P.cs asT) ++ syms postP) (by simp)
  refine h'.mono le_rfl fun c hc => ?_
  have hc' : LGH (gram P) n (syms (chain P.b P.cs asI ++ chain P.b P.cs asT ++ postP) ++ []) c Ψ := by
    simpa [List.append_assoc] using hc
  have hmem : ∀ q ∈ chain P.b P.cs asI ++ chain P.b P.cs asT ++ postP, q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact chain_mem P (run_ok (modeI_ok P hP m) hI) q hq
    · exact chain_mem P (run_ok (by trivial) hT) q hq
    · exact hpost q hq
  exact wpP_mono _ (fun c' hc' => lgh_nil_iff.1 hc') (lgh_prog (gram_good P).nodup hmem hc')

end Modes

end TOHard2

end FOND
