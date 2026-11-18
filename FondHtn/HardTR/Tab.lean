import FondHtn.HardTR.Round
import FondHtn.ATM.Tableau
/-!
# CB22 Thm 5, P3a: the tableau transducer

An instance of the abstract two-loop block machine `FOND.HardTR.TL.Mach` that plays the tableau
game `FOND.ATM.TabWin` (a local rule `F`, a first row `row0`).

**Tape.**  `W = 2 ^ (e + 2) = 4 B` cells, `B = 2 ^ e`; cell `2 j` holds bit `j` of the time `t`,
cell `2 j + 1` bit `j` of the cell index `i` (`2 B` bits each, least significant first).

**Control** `FOND.HardTR.TT.Ctl`: boot mode, the claim `σ`, the borrow `bo` of `t`, the carry
`cy` and direction `dec` of `i` (the move `d ∈ {-1, 0, 1}` chosen by nature at the previous round
end is applied in this sweep), the flag `zi` (new `i` = 0 so far), the guess `gs` of an interval
`[lo ℓ, hi ℓ)` of the first row (made at cell `0`, used only when `t = 0`), the two LSB-first
comparators `cl`, `ch`, and the schedule counter `s` of the special positions `P` (the positions
of the 1-bits of the interval bounds).

Every operation is FOND-friendly: its applicability is a conjunction of tests of control fields,
the read bit and address bits (`c.testBit 0`, `c.testBit (e+1)`, `c = 0`, `c = 2 P[s] + 1`), and
its effect sets control fields to constants determined by the operation.

Main results:

* **`FOND.HardTR.TT.Spec.sound`** — a won round start with tape `(t, i₀)` and control
  `rst σ cy dec` (claim `σ`, move `±cy`) yields `TabWin F row0 t i σ` for the moved index `i`.
* **`FOND.HardTR.TT.Spec.boot_win`** — a won boot round yields an accepting claim `σ ∈ acc`
  with `TabWin F row0 (2 ^ B - 1) i σ` for some `i < 2 ^ B`.
-/

namespace FOND

namespace HardTR

namespace TT

open TL ATM

/-! ## Bit sums -/

/-- The number stored in the even cells `2 j`, `j < n`. -/
def ev (w : ℕ → Bool) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (w (2 * j)).toNat * 2 ^ j

/-- The number stored in the odd cells `2 j + 1`, `j < n`. -/
def od (w : ℕ → Bool) (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (w (2 * j + 1)).toNat * 2 ^ j

@[simp] theorem ev_zero (w : ℕ → Bool) : ev w 0 = 0 := by simp [ev]

@[simp] theorem od_zero (w : ℕ → Bool) : od w 0 = 0 := by simp [od]

theorem ev_succ (w : ℕ → Bool) (n : ℕ) : ev w (n + 1) = ev w n + (w (2 * n)).toNat * 2 ^ n :=
  Finset.sum_range_succ _ _

theorem od_succ (w : ℕ → Bool) (n : ℕ) : od w (n + 1) = od w n + (w (2 * n + 1)).toNat * 2 ^ n :=
  Finset.sum_range_succ _ _

theorem ev_lt (w : ℕ → Bool) (n : ℕ) : ev w n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ev_succ, pow_succ]; cases w (2 * n) <;> simp <;> omega

theorem od_lt (w : ℕ → Bool) (n : ℕ) : od w n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [od_succ, pow_succ]; cases w (2 * n + 1) <;> simp <;> omega

/-! ## Comparators -/

/-- One LSB-first comparator step: the new bits `x` (number) and `k` (constant). -/
def upd (o : Ordering) (x k : Bool) : Ordering := if x = k then o else if x then .gt else .lt

theorem compare_nat (a b : ℕ) :
    compare a b = if a < b then .lt else if a = b then .eq else .gt := by
  rcases lt_trichotomy a b with h | h | h
  · simp [h, compare_lt_iff_lt]
  · subst h; simp
  · simp [show ¬ a < b by omega, show a ≠ b by omega, compare_gt_iff_gt, h]

theorem compare_add {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) (x y : Bool) :
    compare (a + x.toNat * 2 ^ k) (b + y.toNat * 2 ^ k) = upd (compare a b) x y := by
  rw [compare_nat, compare_nat]
  cases x <;> cases y <;> simp only [upd, Bool.toNat_false, Bool.toNat_true] <;>
    split_ifs <;> first | rfl | omega

theorem mod_succ_toNat (c k : ℕ) :
    c % 2 ^ (k + 1) = c % 2 ^ k + (c.testBit k).toNat * 2 ^ k := by
  rw [TL.Mach.mod_two_pow_succ']; cases c.testBit k <;> simp

/-! ## The schedule -/

/-- The number of special positions below `k`. -/
def cnt (P : List ℕ) (k : ℕ) : ℕ := P.countP (· < k)

theorem cnt_cons (a : ℕ) (P : List ℕ) (k : ℕ) :
    cnt (a :: P) k = cnt P k + if a < k then 1 else 0 := by
  simp [cnt, List.countP_cons]

theorem cnt_eq_zero {P : List ℕ} {k : ℕ} (h : ∀ p ∈ P, k ≤ p) : cnt P k = 0 := by
  unfold cnt
  rw [List.countP_eq_zero]
  intro p hp; have := h p hp; simp; omega

theorem lt_iff_lt_cnt {P : List ℕ} (hP : P.Pairwise (· < ·)) {s k : ℕ} (hs : s < P.length) :
    P.getD s 0 < k ↔ s < cnt P k := by
  induction P generalizing s with
  | nil => simp at hs
  | cons a P ih =>
    rw [List.pairwise_cons] at hP
    rw [cnt_cons]
    rcases s with _ | s
    · simp only [List.getD_cons_zero]
      by_cases ha : a < k
      · simp [ha]
      · rw [cnt_eq_zero fun p hp => by have := hP.1 p hp; omega]; simp [ha]
    · simp only [List.getD_cons_succ]
      have hs' : s < P.length := by simp at hs; omega
      by_cases ha : a < k
      · rw [ih hP.2 hs']; simp [ha]
      · rw [cnt_eq_zero fun p hp => by have := hP.1 p hp; omega]
        have hmem : P.getD s 0 ∈ P := by
          rw [List.getD_eq_getElem _ _ hs']; exact List.getElem_mem _
        have := hP.1 _ hmem
        simp only [ha, if_false, add_zero]
        constructor
        · intro h; omega
        · intro h; omega

theorem cnt_succ {P : List ℕ} (hP : P.Nodup) (k : ℕ) :
    cnt P (k + 1) = cnt P k + if k ∈ P then 1 else 0 := by
  induction P with
  | nil => simp [cnt]
  | cons a P ih =>
    rw [List.nodup_cons] at hP
    rw [cnt_cons, cnt_cons, ih hP.2]
    simp only [List.mem_cons]
    by_cases hak : a = k
    · subst hak; simp [hP.1]
    · have : (k = a ∨ k ∈ P) ↔ k ∈ P := by constructor <;> intro h <;> first | omega | tauto
      simp only [this]
      split_ifs <;> omega

theorem cnt_all {P : List ℕ} {n : ℕ} (h : ∀ p ∈ P, p < n) : cnt P n = P.length := by
  unfold cnt; rw [List.countP_eq_length]; simpa using h

/-! ## The machine -/

/-- The control of the tableau transducer. -/
structure Ctl (S : Type) where
  boot : Bool
  σ : S
  bo : Bool
  cy : Bool
  dec : Bool
  zi : Bool
  gs : Option ℕ
  cl : Ordering
  ch : Ordering
  s : ℕ

/-- The control at the start of a normal round: claim `σ`, move `cy` (`dec`: downwards). -/
def rst {S : Type} (σ : S) (cy dec : Bool) : Ctl S :=
  ⟨false, σ, true, cy, dec, true, none, .eq, .eq, 0⟩

/-- The initial control (boot mode). -/
def g0 {S : Type} (σ : S) : Ctl S := ⟨true, σ, true, false, false, true, none, .eq, .eq, 0⟩

/-- The operations (each carries the read bit `b` and the written bit `w`).
* `t gs b w` — a bit of `t` (decrement); at cell `0`, `gs = some ℓ` guesses the interval `ℓ`;
* `i dec b w sp` — a bit of `i` (increment / decrement); `sp = some (ℓ, s)`: the special
  position `P[s]` of the schedule, comparing with the bits of `lo ℓ`, `hi ℓ`;
* `bt w`, `bi w` — boot round: write `t = 2 ^ B - 1` and an arbitrary `i < 2 ^ B`. -/
inductive Op
  | t (gs : Option ℕ) (b w : Bool)
  | i (dec b w : Bool) (sp : Option (ℕ × ℕ))
  | bt (w : Bool)
  | bi (w : Bool)

/-- The round-end actions: the boot claim, or the three claims `l c r` of the previous row
(`z`: the cell is `0`). -/
inductive En (S : Type)
  | boot (σ : S)
  | norm (z : Bool) (l c r : S)

/-- The parameters: `B = 2 ^ e`, the tableau game, the accepting claims, the intervals of the
first row (`ℓ < no`: on `[lo ℓ, hi ℓ)` the first row is `sg ℓ`) and the special positions. -/
structure Spec (S : Type) where
  e : ℕ
  F : Option S → S → S → S
  row0 : ℕ → S
  acc : Set S
  no : ℕ
  sg : ℕ → S
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  P : List ℕ

variable {S : Type} (X : Spec S)

namespace Spec

/-- The number of bits of each counter is `2 B`. -/
abbrev B : ℕ := 2 ^ X.e

/-- The constant bit of a special operation. -/
def kb (f : ℕ → ℕ) : Option (ℕ × ℕ) → Bool
  | none => false
  | some (ℓ, s) => (f ℓ).testBit (X.P.getD s 0)

/-- Applicability of an operation: control, read bit, address. -/
def opOK : Op → Ctl S → Bool → ℕ → Prop
  | .t gs b w, g, sym, c => g.boot = false ∧ sym = b ∧ c.testBit 0 = false ∧ g.bo = xor b w ∧
      ∀ ℓ, gs = some ℓ → c = 0 ∧ ℓ < X.no ∧ g.σ = X.sg ℓ
  | .i dec b w sp, g, sym, c => g.boot = false ∧ sym = b ∧ c.testBit 0 = true ∧
      g.cy = xor b w ∧ g.dec = dec ∧
      ∀ ℓ s, sp = some (ℓ, s) → g.gs = some ℓ ∧ g.s = s ∧ s < X.P.length ∧
        c = 2 * X.P.getD s 0 + 1
  | .bt w, g, _, c => g.boot = true ∧ c.testBit 0 = false ∧ w = !c.testBit (X.e + 1)
  | .bi w, g, _, c => g.boot = true ∧ c.testBit 0 = true ∧ (c.testBit (X.e + 1) = true → w = false)

/-- The effect of an operation (constant assignments of fields). -/
def opEff : Op → Ctl S → Ctl S
  | .t gs b _, g => { g with bo := g.bo && !b, gs := gs.or g.gs }
  | .i dec b w sp, g =>
    { g with
      cy := g.cy && (if dec then !b else b)
      zi := g.zi && !w
      cl := upd g.cl w (X.kb X.lo sp)
      ch := upd g.ch w (X.kb X.hi sp)
      s := if sp.isSome then g.s + 1 else g.s }
  | .bt _, g => g
  | .bi _, g => g

/-- The written bit. -/
def opW : Op → Bool
  | .t _ _ w => w
  | .i _ _ w _ => w
  | .bt w => w
  | .bi w => w

/-- Applicability of a round end. -/
def endOK : En S → Ctl S → Prop
  | .boot σ, g => g.boot = true ∧ σ ∈ X.acc
  | .norm z l c r, g => g.boot = false ∧ g.bo = false ∧ g.cy = false ∧ g.zi = z ∧
      X.F (if z then none else some l) c r = g.σ

omit X in
/-- The outcomes of a round end (nature picks the next claim). -/
def endOut : En S → Ctl S → Set (Ctl S)
  | .boot σ, _ => {rst σ false false}
  | .norm z l c r, _ => {g | g = rst c false false ∨ g = rst r true false ∨
      (z = false ∧ g = rst l true true)}

/-- The finish condition: `t = 0` and the guessed interval contains `i` and fits the claim. -/
def finOK (g : Ctl S) : Prop :=
  g.boot = false ∧ g.bo = true ∧ g.cy = false ∧ g.s = X.P.length ∧ g.gs.isSome ∧
    g.cl ≠ .lt ∧ g.ch = .lt

/-- **The tableau transducer.** -/
def mach : Mach (Ctl S) Op (En S) where
  m := X.e + 2
  opOK := X.opOK
  opEff := X.opEff
  opW := opW
  endOK := X.endOK
  endOut := endOut
  finOK := X.finOK
  boot g := g.boot = true
  endNe e g _ := by
    cases e with
    | boot σ => exact ⟨_, rfl⟩
    | norm z l c r => exact ⟨rst c false false, Or.inl rfl⟩

theorem mach_W : X.mach.W = 4 * X.B := by
  simp only [Mach.W, mach, B, pow_add]; ring

/-- The hypotheses on the parameters. -/
structure Valid : Prop where
  sorted : X.P.Pairwise (· < ·)
  P_lt : ∀ p ∈ X.P, p < 2 * X.B
  lo_bit : ∀ ℓ < X.no, ∀ j, (X.lo ℓ).testBit j = true → j ∈ X.P
  hi_bit : ∀ ℓ < X.no, ∀ j, (X.hi ℓ).testBit j = true → j ∈ X.P
  lo_lt : ∀ ℓ < X.no, X.lo ℓ < 2 ^ (2 * X.B)
  hi_lt : ∀ ℓ < X.no, X.hi ℓ < 2 ^ (2 * X.B)
  row : ∀ ℓ < X.no, ∀ i, X.lo ℓ ≤ i → i < X.hi ℓ → X.sg ℓ = X.row0 i

end Spec

/-! ## Runs of the transducer -/

/-- An invariant of a relational run. -/
theorem srun_inv {G Op En : Type} {M : Mach G Op En} {rd w' : ℕ → Bool} (I : ℕ → G → Prop)
    (hstep : ∀ c g o, c < M.W → I c g → M.opOK o g (rd c) c → w' c = M.opW o →
      I (c + 1) (M.opEff o g)) :
    ∀ {c : ℕ} {g g' : G}, Mach.SRun M rd w' c g g' → I c g → I M.W g' := by
  intro c g g' h
  induction h with
  | done => exact id
  | step hc hok hw _ ih => exact fun hI => ih (hstep _ _ _ hc hI hok hw)

namespace Spec

/-- **The invariant of a normal sweep** before cell `c` (read tape `rd`, written tape `w'`,
claim `σ`, move `cy0`, direction `dec`). -/
def NInv (rd w' : ℕ → Bool) (σ : S) (cy0 dec : Bool) (c : ℕ) (g : Ctl S) : Prop :=
  g.boot = false ∧ g.σ = σ ∧ g.dec = dec ∧
  ev w' ((c + 1) / 2) + 1 = ev rd ((c + 1) / 2) + g.bo.toNat * 2 ^ ((c + 1) / 2) ∧
  (if dec then od w' (c / 2) + cy0.toNat = od rd (c / 2) + g.cy.toNat * 2 ^ (c / 2)
    else od w' (c / 2) + g.cy.toNat * 2 ^ (c / 2) = od rd (c / 2) + cy0.toNat) ∧
  (g.zi = true ↔ od w' (c / 2) = 0) ∧
  (∀ ℓ, g.gs = some ℓ → ℓ < X.no ∧ σ = X.sg ℓ) ∧
  (c / 2 = 0 → g.cl = .eq ∧ g.ch = .eq) ∧
  g.s ≤ cnt X.P (c / 2) ∧
  (g.s = cnt X.P (c / 2) → ∀ ℓ, g.gs = some ℓ →
    g.cl = compare (od w' (c / 2)) (X.lo ℓ % 2 ^ (c / 2)) ∧
    g.ch = compare (od w' (c / 2)) (X.hi ℓ % 2 ^ (c / 2)))

theorem nInv_zero {rd w' : ℕ → Bool} {σ : S} {cy0 dec : Bool} :
    X.NInv rd w' σ cy0 dec 0 (rst σ cy0 dec) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cases dec <;> simp [rst]

variable {X}

theorem nInv_step (hX : X.Valid) {rd w' : ℕ → Bool} {σ : S} {cy0 dec : Bool} (c : ℕ)
    (g : Ctl S) (o : Op) (hI : X.NInv rd w' σ cy0 dec c g) (hok : X.opOK o g (rd c) c)
    (hw : w' c = opW o) : X.NInv rd w' σ cy0 dec (c + 1) (X.opEff o g) := by
  obtain ⟨boot, σ', bo, cy, dg, zi, gs, cl, ch, s⟩ := g
  obtain ⟨hb, hσ, hd, hev, hod, hzi, hgs, h0, hs, hcmp⟩ := hI
  simp only at hb hσ hd hev hod hzi hgs h0 hs hcmp
  subst hb hσ hd
  cases o with
  | bt w => exact absurd hok.1 (by simp)
  | bi w => exact absurd hok.1 (by simp)
  | t gs' b w =>
    obtain ⟨-, hsym, hpar, hbo, hgs'⟩ := hok
    simp only [opW] at hw
    simp only at hsym hbo hgs'
    obtain ⟨h, rfl⟩ : ∃ h, c = 2 * h :=
      ⟨c / 2, by rw [Nat.testBit_zero] at hpar; simp at hpar; omega⟩
    have e1 : (2 * h + 1) / 2 = h := by omega
    have e2 : (2 * h + 1 + 1) / 2 = h + 1 := by omega
    have e3 : (2 * h) / 2 = h := by omega
    rw [e1] at hev
    rw [e3] at hod hzi h0 hs hcmp
    simp only [NInv, opEff, e1, e2]
    refine ⟨by trivial, by trivial, by trivial, ?_, hod, hzi, ?_, h0, hs, ?_⟩
    · rw [ev_succ, ev_succ, hw, hsym, pow_succ]
      subst hbo
      cases b <;> cases w <;> (try simp at hev ⊢) <;> omega
    · intro ℓ hℓ
      cases gs' with
      | none => exact hgs ℓ hℓ
      | some ℓ' =>
        simp at hℓ
        subst hℓ
        obtain ⟨-, h1, h2⟩ := hgs' _ rfl
        exact ⟨h1, h2⟩
    · intro hs' ℓ hℓ
      cases gs' with
      | none => exact hcmp hs' ℓ hℓ
      | some ℓ' =>
        obtain ⟨hc0, -⟩ := hgs' _ rfl
        have : h = 0 := by omega
        subst this
        simp [h0 rfl, Nat.mod_one]
  | i dec' b w sp =>
    obtain ⟨-, hsym, hpar, hcy, hdec, hsp⟩ := hok
    simp only [opW] at hw
    simp only at hsym hcy hdec hsp
    subst hdec
    obtain ⟨k, rfl⟩ : ∃ k, c = 2 * k + 1 :=
      ⟨c / 2, by rw [Nat.testBit_zero] at hpar; simp at hpar; omega⟩
    have e1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have e2 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
    have e3 : (2 * k + 1) / 2 = k := by omega
    rw [e1] at hev
    rw [e3] at hod hzi h0 hs hcmp
    simp only [NInv, opEff, e1, e2]
    have hnd : X.P.Nodup := hX.sorted.imp (fun h => Nat.ne_of_lt h)
    refine ⟨by trivial, by trivial, by trivial, hev, ?_, ?_, hgs, by omega, ?_⟩
    · rw [od_succ, od_succ, hw, hsym, pow_succ]
      subst hcy
      cases dg <;> cases b <;> cases w <;> cases cy0 <;> (try simp at hod ⊢) <;> omega
    · rw [od_succ, hw]
      have := Nat.two_pow_pos k
      cases zi <;> cases w <;> simp at hzi ⊢ <;> omega
    · rw [cnt_succ hnd k]
      cases sp with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, if_false, kb]
        refine ⟨by split_ifs <;> omega, fun hs' ℓ hℓ => ?_⟩
        have hkP : k ∉ X.P := by intro hk; simp [hk] at hs'; omega
        simp only [hkP, if_false, add_zero] at hs'
        obtain ⟨hcl, hch⟩ := hcmp hs' ℓ hℓ
        have hℓn := (hgs ℓ hℓ).1
        have hlo : (X.lo ℓ).testBit k = false := by
          by_contra hc; exact hkP (hX.lo_bit ℓ hℓn k (by simpa using hc))
        have hhi : (X.hi ℓ).testBit k = false := by
          by_contra hc; exact hkP (hX.hi_bit ℓ hℓn k (by simpa using hc))
        rw [od_succ, hw, mod_succ_toNat, mod_succ_toNat, hlo, hhi,
          compare_add (od_lt _ _) (Nat.mod_lt _ (by positivity)),
          compare_add (od_lt _ _) (Nat.mod_lt _ (by positivity)), hcl, hch]
        exact ⟨rfl, rfl⟩
      | some p =>
        obtain ⟨ℓ, s0⟩ := p
        obtain ⟨hgsl, hss, hslt, hc⟩ := hsp ℓ s0 rfl
        subst hgsl hss
        have hk : X.P.getD s 0 = k := by omega
        have hkP : k ∈ X.P := by
          rw [← hk, List.getD_eq_getElem _ _ hslt]; exact List.getElem_mem _
        have hlt : s < cnt X.P (k + 1) := (lt_iff_lt_cnt hX.sorted hslt).1 (by omega)
        rw [cnt_succ hnd k] at hlt
        simp only [hkP, if_true] at hlt ⊢
        simp only [Option.isSome_some, if_true]
        refine ⟨by omega, fun hs' ℓ' hℓ' => ?_⟩
        simp only [Option.some.injEq] at hℓ'
        subst hℓ'
        obtain ⟨hcl, hch⟩ := hcmp (by omega) _ rfl
        simp only [kb, hk]
        rw [od_succ, hw, mod_succ_toNat, mod_succ_toNat,
          compare_add (od_lt _ _) (Nat.mod_lt _ (by positivity)),
          compare_add (od_lt _ _) (Nat.mod_lt _ (by positivity)), hcl, hch]
        exact ⟨rfl, rfl⟩

end Spec

/-! ## Soundness -/

namespace Spec

variable {X}

theorem mach_m_pos : 0 < X.mach.m := by simp [mach]

theorem mach_boot (o : Op) (g : Ctl S) : X.mach.boot (X.mach.opEff o g) ↔ X.mach.boot g := by
  cases o <;> simp [mach, opEff]

/-- One normal round: the invariant at the end of the sweep and the round end. -/
theorem round (hX : X.Valid) {w : ℕ → Bool} {ρ y : Bool} {σ : S} {cy dec : Bool}
    (h : X.mach.Win {X.mach.start ρ w} ⟨.wb 0, 0, ρ, y, rst σ cy dec⟩) :
    ∃ w' g' y', X.NInv w w' σ cy dec (4 * X.B) g' ∧ (X.finOK g' ∨ ∃ e, X.endOK e g' ∧
      ∀ g'' ∈ endOut e g', X.mach.Win {X.mach.start (!ρ) w'} ⟨.wb 0, 0, !ρ, y', g''⟩) := by
  obtain ⟨w', g', y', hrun, hend⟩ :=
    Mach.round_sound mach_m_pos mach_boot (by simp [mach, rst]) h
  refine ⟨w', g', y', ?_, hend⟩
  have := srun_inv (M := X.mach) (X.NInv w w' σ cy dec)
    (fun c g o _ hI hok hw => nInv_step hX c g o hI hok hw) hrun (nInv_zero X)
  rwa [mach_W] at this

theorem nInv_end (hX : X.Valid) {w w' : ℕ → Bool} {σ : S} {cy dec : Bool} {g : Ctl S}
    (h : X.NInv w w' σ cy dec (4 * X.B) g) :
    g.boot = false ∧ g.σ = σ ∧
    ev w' (2 * X.B) + 1 = ev w (2 * X.B) + g.bo.toNat * 2 ^ (2 * X.B) ∧
    (g.cy = false → if dec then od w' (2 * X.B) + cy.toNat = od w (2 * X.B)
      else od w' (2 * X.B) = od w (2 * X.B) + cy.toNat) ∧
    (g.zi = true ↔ od w' (2 * X.B) = 0) ∧
    (∀ ℓ, g.gs = some ℓ → ℓ < X.no ∧ σ = X.sg ℓ) ∧
    (g.s = X.P.length → ∀ ℓ, g.gs = some ℓ →
      g.cl = compare (od w' (2 * X.B)) (X.lo ℓ % 2 ^ (2 * X.B)) ∧
      g.ch = compare (od w' (2 * X.B)) (X.hi ℓ % 2 ^ (2 * X.B))) := by
  have e1 : (4 * X.B + 1) / 2 = 2 * X.B := by omega
  have e2 : (4 * X.B) / 2 = 2 * X.B := by omega
  obtain ⟨hb, hσ, hd, hev, hod, hzi, hgs, -, -, hcmp⟩ := h
  rw [e1] at hev
  rw [e2] at hod hzi hcmp
  refine ⟨hb, hσ, hev, fun hcy => ?_, hzi, hgs, fun hs => hcmp (by rw [hs, cnt_all hX.P_lt])⟩
  rw [hcy] at hod
  cases dec <;> simpa using hod

/-- **Soundness of the tableau transducer**: a won round start with tape `(t, i₀)` and control
`rst σ cy dec` gives the tableau claim `(t, i, σ)` for the moved index `i = i₀ ± cy`. -/
theorem sound (hX : X.Valid) : ∀ (t : ℕ) (w : ℕ → Bool) (ρ y : Bool) (σ : S) (cy dec : Bool),
    ev w (2 * X.B) = t → X.mach.Win {X.mach.start ρ w} ⟨.wb 0, 0, ρ, y, rst σ cy dec⟩ →
    ∃ i, (if dec then i + cy.toNat = od w (2 * X.B) else i = od w (2 * X.B) + cy.toNat) ∧
      TabWin X.F X.row0 t i σ := by
  intro t
  induction t with
  | zero =>
    intro w ρ y σ cy dec ht h
    obtain ⟨w', g', y', hI, hend⟩ := round hX h
    obtain ⟨hb, hσ, hev, hod, -, hgs, hcmp⟩ := nInv_end hX hI
    rw [ht] at hev
    have hbo : g'.bo = true := by
      cases hbo : g'.bo
      · rw [hbo] at hev; simp at hev
      · rfl
    rcases hend with hfin | ⟨e, he, -⟩
    · obtain ⟨-, -, hcy, hsP, hgsS, hcl, hch⟩ := hfin
      obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.1 hgsS
      obtain ⟨hℓn, hσℓ⟩ := hgs ℓ hℓ
      obtain ⟨hcl', hch'⟩ := hcmp hsP ℓ hℓ
      rw [Nat.mod_eq_of_lt (hX.lo_lt ℓ hℓn)] at hcl'
      rw [Nat.mod_eq_of_lt (hX.hi_lt ℓ hℓn)] at hch'
      refine ⟨od w' (2 * X.B), hod hcy, ?_⟩
      have h1 : X.lo ℓ ≤ od w' (2 * X.B) := by
        by_contra hlt
        exact hcl (by rw [hcl']; exact compare_lt_iff_lt.2 (by omega))
      have h2 : od w' (2 * X.B) < X.hi ℓ := by
        rw [hch'] at hch; exact compare_lt_iff_lt.1 hch
      show σ = X.row0 _
      rw [hσℓ]; exact hX.row ℓ hℓn _ h1 h2
    · cases e with
      | boot σ' => exact absurd he.1 (by simp [hb])
      | norm z l c r => exact absurd he.2.1 (by simp [hbo])
  | succ t ih =>
    intro w ρ y σ cy dec ht h
    obtain ⟨w', g', y', hI, hend⟩ := round hX h
    obtain ⟨hb, hσ, hev, hod, hzi, -, -⟩ := nInv_end hX hI
    rw [ht] at hev
    have hlt := ev_lt w' (2 * X.B)
    have hbo : g'.bo = false := by
      cases hbo : g'.bo
      · rfl
      · rw [hbo] at hev; simp at hev; omega
    rw [hbo] at hev
    simp only [Bool.toNat_false, zero_mul, add_zero, Nat.add_right_cancel_iff] at hev
    rcases hend with hfin | ⟨e, he, hW⟩
    · exact absurd hfin.2.1 (by simp [hbo])
    · cases e with
      | boot σ' => exact absurd he.1 (by simp [hb])
      | norm z l c r =>
        obtain ⟨-, -, hcy, hz, hF⟩ := he
        refine ⟨od w' (2 * X.B), hod hcy, ?_⟩
        obtain ⟨i1, hi1, hc⟩ := ih w' (!ρ) y' c false false hev (hW _ (Or.inl rfl))
        obtain ⟨i2, hi2, hr⟩ := ih w' (!ρ) y' r true false hev (hW _ (Or.inr (Or.inl rfl)))
        simp only [Bool.false_eq_true, if_false, Bool.toNat_false, add_zero,
          Bool.toNat_true] at hi1 hi2
        subst hi1 hi2
        refine ⟨l, c, r, ?_, fun hne => ?_, hc, hr⟩
        · rw [← hσ, ← hF, ← hz]
          by_cases h0 : od w' (2 * X.B) = 0
          · simp [h0, hzi.2 h0]
          · have : g'.zi = false := by
              cases hz' : g'.zi
              · rfl
              · exact absurd (hzi.1 hz') h0
            simp [h0, this]
        · have hz0 : z = false := by
            rw [← hz]; cases hz' : g'.zi
            · rfl
            · exact absurd (hzi.1 hz') hne
          obtain ⟨i3, hi3, hl⟩ :=
            ih w' (!ρ) y' l true true hev (hW _ (Or.inr (Or.inr ⟨hz0, rfl⟩)))
          simp only [if_true, Bool.toNat_true] at hi3
          rwa [show od w' (2 * X.B) - 1 = i3 by omega]

/-! ## The boot round -/

theorem testBit_top {c e : ℕ} (hc : c < 2 ^ (e + 2)) :
    c.testBit (e + 1) = decide (2 ^ (e + 1) ≤ c) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hp : 0 < 2 ^ (e + 1) := Nat.two_pow_pos _
  have h2 : c / 2 ^ (e + 1) < 2 :=
    (Nat.div_lt_iff_lt_mul hp).2 (by rw [pow_succ] at hc; linarith)
  have h3 : 2 ^ (e + 1) ≤ c ↔ 1 ≤ c / 2 ^ (e + 1) := by
    rw [Nat.le_div_iff_mul_le hp]; simp
  by_cases h : 2 ^ (e + 1) ≤ c
  · have := h3.1 h; simp [h, show c / 2 ^ (e + 1) = 1 by omega]
  · have : c / 2 ^ (e + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_le h)
    simp [h, this]

theorem ev_boot {w : ℕ → Bool} {B : ℕ} (hw : ∀ j < 2 * B, w (2 * j) = decide (j < B)) :
    ∀ n ≤ 2 * B, ev w n = 2 ^ min n B - 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    rw [ev_succ, ih (by omega), hw n (by omega)]
    by_cases h : n < B
    · rw [min_eq_left (by omega), min_eq_left (by omega), pow_succ]
      have := Nat.two_pow_pos n
      simp [h]; omega
    · rw [min_eq_right (by omega), min_eq_right (by omega)]; simp [h]

theorem od_boot {w : ℕ → Bool} {B : ℕ} (hw : ∀ j < 2 * B, B ≤ j → w (2 * j + 1) = false) :
    ∀ n ≤ 2 * B, od w n < 2 ^ min n B := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    by_cases h : n < B
    · rw [min_eq_left (by omega)]; exact od_lt _ _
    · rw [od_succ, hw n (by omega) (by omega), min_eq_right (by omega)]
      have := ih (by omega); rw [min_eq_right (by omega)] at this; simpa using this

/-- The invariant of the boot sweep. -/
def BInv (w' : ℕ → Bool) (σ : S) (c : ℕ) (g : Ctl S) : Prop :=
  g = g0 σ ∧ ∀ c' < c, (c'.testBit 0 = false → w' c' = !c'.testBit (X.e + 1)) ∧
    (c'.testBit 0 = true → c'.testBit (X.e + 1) = true → w' c' = false)

/-- **The boot round**: a won boot round yields an accepting claim at time `2 ^ B - 1` for a
cell `i < 2 ^ B`. -/
theorem boot_win (hX : X.Valid) {ρ y : Bool} {σ : S}
    (h : X.mach.Win {cfg ρ 0 0} ⟨.wb 0, 0, ρ, y, g0 σ⟩) :
    ∃ σ' ∈ X.acc, ∃ i < 2 ^ X.B, TabWin X.F X.row0 (2 ^ X.B - 1) i σ' := by
  obtain ⟨w', g', y', hrun, hend⟩ := Mach.boot_sound mach_m_pos h
  have hI := srun_inv (M := X.mach) (rd := fun _ => false) (X.BInv w' σ)
    (fun c g o _ hI hok hw => by
      obtain ⟨rfl, hI⟩ := hI
      cases o with
      | t gs b w => exact absurd hok.1 (by simp [g0])
      | i d b w sp => exact absurd hok.1 (by simp [g0])
      | bt w =>
        obtain ⟨-, hpar, hw'⟩ := hok
        refine ⟨rfl, fun c' hc' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with hc' | rfl
        · exact hI c' hc'
        · refine ⟨fun _ => ?_, fun h => by simp [hpar] at h⟩
          rw [hw]; exact hw'
      | bi w =>
        obtain ⟨-, hpar, hw'⟩ := hok
        refine ⟨rfl, fun c' hc' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with hc' | rfl
        · exact hI c' hc'
        · refine ⟨fun h => by simp [hpar] at h, fun _ h => ?_⟩
          rw [hw]; exact hw' h)
    hrun ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [mach_W] at hI
  obtain ⟨rfl, htape⟩ := hI
  have hW4 : 4 * X.B = 2 ^ (X.e + 2) := by simp only [B, pow_add]; ring
  have hB2 : 2 ^ (X.e + 1) = 2 * X.B := by simp only [B, pow_succ]; ring
  have hev : ∀ j < 2 * X.B, w' (2 * j) = decide (j < X.B) := by
    intro j hj
    have := (htape (2 * j) (by omega)).1 (by simp [Nat.testBit_zero])
    rw [this, testBit_top (by omega), hB2]
    by_cases h : j < X.B <;> simp [h]; omega
  have hod : ∀ j < 2 * X.B, X.B ≤ j → w' (2 * j + 1) = false := by
    intro j hj hBj
    refine (htape (2 * j + 1) (by omega)).2 (by simp [Nat.testBit_zero]) ?_
    rw [testBit_top (by omega), hB2]; simp; omega
  rcases hend with hfin | ⟨e, he, hW⟩
  · exact absurd hfin.1 (by simp [g0])
  · cases e with
    | norm z l c r => exact absurd he.1 (by simp [g0])
    | boot σ' =>
      obtain ⟨-, hacc⟩ := he
      obtain ⟨i, hi, htab⟩ := sound hX _ w' (!ρ) y' σ' false false rfl (hW _ rfl)
      simp only [Bool.false_eq_true, if_false, Bool.toNat_false, add_zero] at hi
      refine ⟨σ', hacc, i, ?_, ?_⟩
      · have := od_boot hod (2 * X.B) le_rfl
        rwa [min_eq_right (by omega), ← hi] at this
      · rwa [ev_boot hev (2 * X.B) le_rfl, min_eq_right (by omega)] at htab

end Spec

end TT

end HardTR

end FOND
