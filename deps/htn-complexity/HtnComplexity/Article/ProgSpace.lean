import HtnComplexity.Article.ProgDescSize
import HtnComplexity.PT.Search
/-!
# Plan existence by progression in polynomial and exponential space

The search of Cor. 4.2.16–4.2.22: guess a certificate of the class membership, then progress
from the initial configuration (`HTN.Article.succs`) until the network is empty in a goal state.
A progression bound `n` (Def. 4.3) bounds the configurations by `40 (n + |p| + 1)³`
(`HTN.Article.sz_cfg_le`).

* **`HTN.Article.inPSpace_planEx`** — if a polynomial-time check of polynomial certificates
  decides the class `Y` on well-formed descriptions, and the problems of `Y` have polynomial
  progression bounds, then `PlanEx^Y_htn ∈ PSPACE`;
* **`HTN.Article.inExpSpace_planEx`** — the same with exponential certificates and progression
  bounds: `PlanEx^Y_htn ∈ EXPSPACE`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

instance decEqLblList : DecidableEq (List (ℕ × Bool × ℕ)) := inferInstance
instance decEqTnDesc : DecidableEq (List ℕ × List (ℕ × ℕ) × List (ℕ × Bool × ℕ)) := inferInstance
instance decEqPCfg : DecidableEq PCfg := inferInstance

section Gen

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

/-- The initial test: well-formed, certified, and the initial configuration. -/
def pInit (cB : ProbDesc × β → Bool) (x : ProbDesc × (β × PCfg)) : Bool :=
  validB x.1 && cB (x.1, x.2.1) && decide (x.2.2 = initCfg x.1)

/-- A step: the certificate is kept, the configuration progresses. -/
def pStep (x : ProbDesc × (β × PCfg) × (β × PCfg)) : Bool :=
  decide (x.2.2.1 = x.2.1.1) && decide (x.2.2.2 ∈ succs x.1 x.2.1.2)

/-- The acceptance test: no tasks left, a goal state. -/
def pAcc (x : ProbDesc × (β × PCfg)) : Bool := x.2.2.2.ids.isEmpty && goalB x.1 x.2.2.1

theorem pt_pInit {cB : ProbDesc × β → Bool} (hcB : PT cB) : PT (pInit cB) := by
  have h1 : PT fun x : ProbDesc × (β × PCfg) => validB x.1 := pt_validB.comp PT.fst
  have h2 : PT fun x : ProbDesc × (β × PCfg) => cB (x.1, x.2.1) :=
    hcB.comp (PT.pair PT.fst (PT.fst.comp PT.snd))
  have h3 : PT fun x : ProbDesc × (β × PCfg) => decide (x.2.2 = initCfg x.1) :=
    PT.eq (PT.snd.comp PT.snd) (pt_initCfg.comp PT.fst)
  exact (PT.and (PT.and h1 h2) h3).of_eq fun _ => rfl

theorem pt_pStep : PT (pStep (β := β)) := by
  have h1 : PT fun x : ProbDesc × (β × PCfg) × (β × PCfg) => decide (x.2.2.1 = x.2.1.1) :=
    PT.eq (PT.fst.comp (PT.snd.comp PT.snd)) (PT.fst.comp (PT.fst.comp PT.snd))
  have hs := pt_succs.comp (PT.pair (PT.fst (α := ProbDesc) (β := (β × PCfg) × (β × PCfg)))
    (PT.snd.comp (PT.fst.comp PT.snd)))
  have h2 := PT.elemL hs (PT.snd.comp (PT.snd.comp (PT.snd (α := ProbDesc)
    (β := (β × PCfg) × (β × PCfg)))))
  exact (PT.and h1 h2).of_eq fun _ => rfl

theorem pt_pAcc : PT (pAcc (β := β)) := by
  have h1 : PT fun x : ProbDesc × (β × PCfg) => x.2.2.2.ids.isEmpty :=
    PT.isEmpty (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd)))
  have h2 := pt_goalB.comp (PT.pair (PT.fst (α := ProbDesc) (β := β × PCfg))
    (PT.fst.comp (PT.snd.comp PT.snd)))
  exact (PT.and h1 h2).of_eq fun _ => rfl

/-- The language as a search, for a bound `B` on certificates and configurations. -/
theorem planEx_iff_search {Y : PClass} {cB : ProbDesc × β → Bool}
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (B : ℕ → ℕ)
    (hcomp : ∀ p : ProbDesc, p.Valid → Y p.toProblem → ∃ b, cB (p, b) = true ∧
      ∃ n, p.toProblem.IsHTNProgBound n ∧ sz b + 40 * (n + sz p + 1) ^ 3 ≤ B (sz p)) (p : ProbDesc) :
    (p.Valid ∧ Y p.toProblem ∧ p.toProblem.Solvable) ↔ ∃ c₀ c, sz c₀ ≤ B (sz p) ∧
      pInit cB (p, c₀) = true ∧
      Relation.ReflTransGen (fun c c' => sz c' ≤ B (sz p) ∧ pStep (p, c, c') = true) c₀ c ∧
      pAcc (p, c) = true := by
  constructor
  · rintro ⟨hp, hY, hsol⟩
    obtain ⟨b, hb, n, hn, hB⟩ := hcomp p hp hY
    obtain ⟨c, hrc, hids, hg⟩ := (solvable_iff_cfg hp).1 hsol
    have hsz : ∀ c, Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c →
        sz (b, c) ≤ B (sz p) := fun c hc => by
      rw [sz_prod]; have := sz_cfg_le hp hn hc; omega
    refine ⟨(b, initCfg p), (b, c), hsz _ .refl, ?_, ?_, ?_⟩
    · simp [pInit, (validB_iff p).2 hp, hb]
    · have key : ∀ c, Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c →
          Relation.ReflTransGen (fun c c' => sz c' ≤ B (sz p) ∧ pStep (p, c, c') = true)
            (b, initCfg p) (b, c) := by
        intro c hc
        induction hc with
        | refl => exact .refl
        | @tail c₁ c₂ hr hs ih =>
          exact ih.tail ⟨hsz c₂ (hr.tail hs), by simp [pStep, hs]⟩
      exact key c hrc
    · simp [pAcc, hids, hg]
  · rintro ⟨⟨b, c₀⟩, c, -, hi, hr, ha⟩
    simp only [pInit, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hv, hb⟩, rfl⟩ := hi
    have hp := (validB_iff p).1 hv
    refine ⟨hp, hsound p b hp hb, ?_⟩
    have key : ∀ c, Relation.ReflTransGen (fun c c' => sz c' ≤ B (sz p) ∧ pStep (p, c, c') = true)
        (b, initCfg p) c → Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c.2 := by
      intro c hc
      induction hc with
      | refl => exact .refl
      | @tail c₁ c₂ _ hs ih =>
        simp only [pStep, Bool.and_eq_true, decide_eq_true_eq] at hs
        exact ih.tail hs.2.2
    simp only [pAcc, Bool.and_eq_true, List.isEmpty_iff] at ha
    exact (solvable_iff_cfg hp).2 ⟨c.2, key c hr, ha.1, ha.2⟩

/-- **Plan existence by progression is in `PSPACE`** for classes with polynomial certificates
and polynomial progression bounds. -/
theorem inPSpace_planEx {Y : PClass} {cB : ProbDesc × β → Bool} (hcB : PT cB)
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (r : Polynomial ℕ)
    (hcomp : ∀ p : ProbDesc, p.Valid → Y p.toProblem → (∃ b, cB (p, b) = true ∧
      sz b ≤ r.eval (sz p)) ∧ p.toProblem.IsHTNProgBound (r.eval (sz p))) :
    Cx.PSPACE (PlanEx Y) := by
  let q : Polynomial ℕ := r + 40 * (r + Polynomial.X + 1) ^ 3
  have hq : ∀ n, q.eval n = r.eval n + 40 * (r.eval n + n + 1) ^ 3 := fun n => by simp [q]
  have h := inPSpace_codeLang_of_search (α := ProbDesc) (σ := β × PCfg)
    (Q := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.Solvable) (pt_pInit hcB) pt_pStep pt_pAcc q
    fun p => planEx_iff_search hsound (fun n => q.eval n) (fun p hp hY => by
        obtain ⟨⟨b, hb, hbs⟩, hn⟩ := hcomp p hp hY
        exact ⟨b, hb, _, hn, by show _ ≤ q.eval (sz p); rw [hq]; omega⟩) p
  exact h

/-- **Plan existence by progression is in `EXPSPACE`** for classes with exponential certificates
and exponential progression bounds. -/
theorem inExpSpace_planEx {Y : PClass} {cB : ProbDesc × β → Bool} (hcB : PT cB)
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (r : Polynomial ℕ)
    (hcomp : ∀ p : ProbDesc, p.Valid → Y p.toProblem → (∃ b, cB (p, b) = true ∧
      sz b ≤ 2 ^ r.eval (sz p)) ∧ p.toProblem.IsHTNProgBound (2 ^ r.eval (sz p))) :
    Cx.EXPSPACE (PlanEx Y) := by
  let q : Polynomial ℕ := 3 * r + 3 * Polynomial.X + 12
  have hq : ∀ n, q.eval n = 3 * r.eval n + 3 * n + 12 := fun n => by simp [q]
  have hbound : ∀ n e : ℕ, 2 ^ e + 40 * (2 ^ e + n + 1) ^ 3 < 2 ^ (3 * e + 3 * n + 12) := by
    intro n e
    have h1 : 2 ^ e + n + 1 ≤ 3 * 2 ^ (e + n) := by
      have := Nat.lt_two_pow_self (n := n)
      have : 2 ^ n ≤ 2 ^ (e + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ e ≤ 2 ^ (e + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : (2 ^ e + n + 1) ^ 3 ≤ 27 * 2 ^ (3 * (e + n)) := by
      calc (2 ^ e + n + 1) ^ 3 ≤ (3 * 2 ^ (e + n)) ^ 3 := Nat.pow_le_pow_left h1 3
        _ = 27 * 2 ^ (3 * (e + n)) := by rw [mul_pow, ← pow_mul]; ring_nf
    have h3 : 2 ^ e ≤ 2 ^ (3 * (e + n)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (3 * e + 3 * n + 12) = 4096 * 2 ^ (3 * (e + n)) := by
      rw [show 3 * e + 3 * n + 12 = 12 + 3 * (e + n) by ring, pow_add]; norm_num
    rw [h4]
    have : 0 < 2 ^ (3 * (e + n)) := by positivity
    omega
  have h := inExpSpace_codeLang_of_search (α := ProbDesc) (σ := β × PCfg)
    (Q := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.Solvable) (pt_pInit hcB) pt_pStep pt_pAcc q
    fun p => by
      have e := planEx_iff_search (cB := cB) (Y := Y) hsound (fun n => 2 ^ q.eval n - 1)
        (fun p hp hY => by
          obtain ⟨⟨b, hb, hbs⟩, hn⟩ := hcomp p hp hY
          refine ⟨b, hb, _, hn, ?_⟩
          have := hbound (sz p) (r.eval (sz p))
          show _ ≤ 2 ^ q.eval (sz p) - 1
          rw [hq]
          omega) p
      refine e.trans ?_
      have hlt : ∀ m, m ≤ 2 ^ q.eval (sz p) - 1 ↔ m < 2 ^ q.eval (sz p) := fun m => by
        have : 0 < 2 ^ q.eval (sz p) := by positivity
        omega
      simp only [hlt]
  exact h

end Gen

end Article

end HTN
