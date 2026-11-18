import FondHtn.HardTR.Tab
/-!
# CB22 Thm 5: completeness of the tableau transducer

The canonical run of a normal sweep: at every cell the operation is forced (the written bit is
the read bit corrected by the borrow of `t` or the carry of `i`), except for the interval guess
at cell `0` and the schedule of the special positions, which follow the guess.
`FOND.HardTR.TT.Spec.srun_canon`: the canonical run is a run of the transducer; its end state is
described by the soundness invariant `NInv`.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TT

open TL ATM

variable {S : Type} (X : Spec S)

namespace Spec

/-- The special position of the schedule at cell `c`, if any. -/
def spAt (g : Ctl S) (c : ℕ) : Option (ℕ × ℕ) :=
  match g.gs with
  | some ℓ => if g.s < X.P.length ∧ c = 2 * X.P.getD g.s 0 + 1 then some (ℓ, g.s) else none
  | none => none

/-- **The canonical operation** at cell `c` (guess `G` at cell `0`, read tape `rd`). -/
def opAt (G : Option ℕ) (rd : ℕ → Bool) (c : ℕ) (g : Ctl S) : Op :=
  if c.testBit 0 then .i g.dec (rd c) (xor (rd c) g.cy) (X.spAt g c)
  else .t (if c = 0 then G else none) (rd c) (xor (rd c) g.bo)

/-- The controls of the canonical run. -/
def gAt (G : Option ℕ) (rd : ℕ → Bool) (g₀ : Ctl S) : ℕ → Ctl S
  | 0 => g₀
  | c + 1 => X.opEff (X.opAt G rd c (gAt G rd g₀ c)) (gAt G rd g₀ c)

/-- The written tape of the canonical run. -/
def wAt (G : Option ℕ) (rd : ℕ → Bool) (g₀ : Ctl S) (c : ℕ) : Bool :=
  opW (X.opAt G rd c (X.gAt G rd g₀ c))

variable {X}

theorem boot_gAt {G : Option ℕ} {rd : ℕ → Bool} {g₀ : Ctl S} :
    ∀ c, (X.gAt G rd g₀ c).boot = g₀.boot ∧ (X.gAt G rd g₀ c).σ = g₀.σ ∧
      (X.gAt G rd g₀ c).dec = g₀.dec
  | 0 => ⟨rfl, rfl, rfl⟩
  | c + 1 => by
    obtain ⟨h1, h2, h3⟩ := boot_gAt (G := G) (rd := rd) (g₀ := g₀) c
    simp only [gAt, opAt]
    split_ifs <;> simp [opEff, h1, h2, h3]

theorem opOK_opAt {G : Option ℕ} {rd : ℕ → Bool} {c : ℕ} {g : Ctl S} (hb : g.boot = false)
    (hG : ∀ ℓ, c = 0 → G = some ℓ → ℓ < X.no ∧ g.σ = X.sg ℓ) :
    X.opOK (X.opAt G rd c g) g (rd c) c := by
  by_cases hc : c.testBit 0 = true
  · simp only [opAt, hc, if_true]
    refine ⟨hb, rfl, hc, by cases rd c <;> cases g.cy <;> rfl, rfl, fun ℓ s hsp => ?_⟩
    unfold spAt at hsp
    cases hgs : g.gs with
    | none => rw [hgs] at hsp; simp at hsp
    | some ℓ' =>
      rw [hgs] at hsp
      simp only at hsp
      by_cases h : g.s < X.P.length ∧ c = 2 * X.P.getD g.s 0 + 1
      · rw [if_pos h] at hsp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp
        obtain ⟨rfl, rfl⟩ := hsp
        exact ⟨rfl, rfl, h.1, h.2⟩
      · rw [if_neg h] at hsp; simp at hsp
  · simp only [opAt, hc, if_false, Bool.false_eq_true]
    refine ⟨hb, rfl, by simpa using hc, by cases rd c <;> cases g.bo <;> rfl, fun ℓ hℓ => ?_⟩
    by_cases h0 : c = 0
    · rw [if_pos h0] at hℓ
      obtain ⟨h1, h2⟩ := hG ℓ h0 hℓ
      exact ⟨h0, h1, h2⟩
    · rw [if_neg h0] at hℓ; simp at hℓ

/-- **The canonical run is a run.** -/
theorem srun_canon {G : Option ℕ} {rd : ℕ → Bool} {g₀ : Ctl S} (hb : g₀.boot = false)
    (hG : ∀ ℓ, G = some ℓ → ℓ < X.no ∧ g₀.σ = X.sg ℓ) :
    ∀ n c, c + n = X.mach.W →
      Mach.SRun X.mach rd (X.wAt G rd g₀) c (X.gAt G rd g₀ c) (X.gAt G rd g₀ X.mach.W) := by
  intro n
  induction n with
  | zero => intro c hc; simp only [Nat.add_zero] at hc; subst hc; exact .done
  | succ n ih =>
    intro c hc
    refine .step (by omega) ?_ rfl ?_
    · exact opOK_opAt (by rw [(boot_gAt c).1, hb])
        (fun ℓ hc0 hℓ => by subst hc0; exact hG ℓ hℓ)
    · exact ih (c + 1) (by omega)

/-! ## The guess and the schedule -/

theorem gs_gAt {G : Option ℕ} {rd : ℕ → Bool} {g₀ : Ctl S} (h0 : g₀.gs = none) :
    ∀ c, (X.gAt G rd g₀ (c + 1)).gs = G
  | 0 => by simp [gAt, opAt, opEff, h0]
  | c + 1 => by
    have ih : (X.gAt G rd g₀ (c + 1)).gs = G := gs_gAt h0 c
    show (X.opEff (X.opAt G rd (c + 1) (X.gAt G rd g₀ (c + 1))) (X.gAt G rd g₀ (c + 1))).gs = G
    generalize X.gAt G rd g₀ (c + 1) = g at ih ⊢
    unfold opAt
    by_cases h1 : (c + 1).testBit 0 = true
    · simp [h1, opEff, ih]
    · simp [h1, opEff, ih]

theorem mem_iff_cnt {P : List ℕ} (hP : P.Pairwise (· < ·)) (h : ℕ) :
    h ∈ P ↔ cnt P h < P.length ∧ P.getD (cnt P h) 0 = h := by
  have hnd : P.Nodup := hP.imp (fun h => Nat.ne_of_lt h)
  have hle : ∀ k, cnt P k ≤ P.length := fun k => List.countP_le_length
  constructor
  · intro hh
    have h1 := cnt_succ hnd h
    rw [if_pos hh] at h1
    have hlt : cnt P h < P.length := by have := hle (h + 1); omega
    refine ⟨hlt, ?_⟩
    have a1 := (lt_iff_lt_cnt hP hlt (k := h + 1)).2 (by omega)
    have a2 : ¬ P.getD (cnt P h) 0 < h := fun hc => by
      have := (lt_iff_lt_cnt hP hlt (k := h)).1 hc; omega
    omega
  · rintro ⟨hlt, he⟩
    rw [← he, List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem _

theorem s_gAt (hX : X.Valid) {ℓ : ℕ} {rd : ℕ → Bool} {σ : S} {cy dec : Bool} :
    ∀ c, (X.gAt (some ℓ) rd (rst σ cy dec) c).s = cnt X.P (c / 2)
  | 0 => by simp [gAt, rst, cnt]
  | c + 1 => by
    have ih := s_gAt hX (ℓ := ℓ) (rd := rd) (σ := σ) (cy := cy) (dec := dec) c
    have hnd : X.P.Nodup := hX.sorted.imp (fun h => Nat.ne_of_lt h)
    simp only [gAt]
    by_cases h1 : c.testBit 0 = true
    · -- an odd cell `2 k + 1`
      obtain ⟨k, rfl⟩ : ∃ k, c = 2 * k + 1 :=
        ⟨c / 2, by rw [Nat.testBit_zero] at h1; simp at h1; omega⟩
      have e1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have e2 : (2 * k + 1) / 2 = k := by omega
      rw [e2] at ih
      rw [e1, cnt_succ hnd k]
      have hgs : (X.gAt (some ℓ) rd (rst σ cy dec) (2 * k + 1)).gs = some ℓ :=
        gs_gAt (by rfl) (2 * k)
      simp only [opAt, h1, if_true, opEff, spAt, hgs, ih]
      have key := mem_iff_cnt hX.sorted k
      by_cases hk : k ∈ X.P
      · obtain ⟨hlt, he⟩ := key.1 hk
        rw [if_pos (show cnt X.P k < X.P.length ∧ 2 * k + 1 = 2 * X.P.getD (cnt X.P k) 0 + 1 from
          ⟨hlt, by omega⟩), if_pos hk]; simp
      · have : ¬ (cnt X.P k < X.P.length ∧ 2 * k + 1 = 2 * X.P.getD (cnt X.P k) 0 + 1) :=
          fun h => hk (key.2 ⟨h.1, by omega⟩)
        rw [if_neg this, if_neg hk]; simp
    · obtain ⟨k, rfl⟩ : ∃ k, c = 2 * k :=
        ⟨c / 2, by rw [Nat.testBit_zero] at h1; simp at h1; omega⟩
      have e1 : (2 * k + 1) / 2 = k := by omega
      have e2 : (2 * k) / 2 = k := by omega
      rw [e2] at ih; rw [e1]
      simp only [opAt, h1, if_false, Bool.false_eq_true]
      simp [opEff, ih]

/-! ## The end of a normal round -/

/-- The invariant at the end of the canonical run. -/
theorem nInv_canon (hX : X.Valid) {G : Option ℕ} {rd : ℕ → Bool} {σ : S} {cy dec : Bool}
    (hG : ∀ ℓ, G = some ℓ → ℓ < X.no ∧ σ = X.sg ℓ) :
    X.NInv rd (X.wAt G rd (rst σ cy dec)) σ cy dec (4 * X.B) (X.gAt G rd (rst σ cy dec) (4 * X.B)) := by
  have hrun := srun_canon (X := X) (G := G) (rd := rd) (g₀ := rst σ cy dec) rfl
    (fun ℓ h => hG ℓ h) X.mach.W 0 (by simp)
  have := srun_inv (M := X.mach) (X.NInv rd (X.wAt G rd (rst σ cy dec)) σ cy dec)
    (fun c g o _ hI hok hw => nInv_step hX c g o hI hok hw) hrun (nInv_zero X)
  rwa [mach_W] at this

/-- The data of the next round: claim, move, moved index. -/
def NextOK (w' : ℕ → Bool) (t : ℕ) (g'' : Ctl S) : Prop :=
  ∃ σ'' cy'' dec'' i'', g'' = rst σ'' cy'' dec'' ∧
    (if dec'' then i'' + cy''.toNat = od w' (2 * X.B) else i'' = od w' (2 * X.B) + cy''.toNat) ∧
    i'' + t < 2 ^ (X.B + 1) ∧ TabWin X.F X.row0 t i'' σ''

/-- **A true claim can be played**: the canonical run ends in a finish (`t = 0`) or in a round
end all of whose outcomes start a next round with a true claim and `t - 1`. -/
theorem normal_round (hX : X.Valid)
    (hcover : ∀ i < 2 ^ (X.B + 1), ∃ ℓ < X.no, X.lo ℓ ≤ i ∧ i < X.hi ℓ)
    {rd : ℕ → Bool} {σ : S} {cy dec : Bool} {i : ℕ}
    (hi : if dec then i + cy.toNat = od rd (2 * X.B) else i = od rd (2 * X.B) + cy.toNat)
    (hb : i + ev rd (2 * X.B) < 2 ^ (X.B + 1))
    (htab : TabWin X.F X.row0 (ev rd (2 * X.B)) i σ) :
    ∃ G : Option ℕ, (∀ ℓ, G = some ℓ → ℓ < X.no ∧ σ = X.sg ℓ) ∧
      ((ev rd (2 * X.B) = 0 ∧ X.finOK (X.gAt G rd (rst σ cy dec) (4 * X.B))) ∨
       (∃ t', ev rd (2 * X.B) = t' + 1 ∧ ev (X.wAt G rd (rst σ cy dec)) (2 * X.B) = t' ∧
        ∃ e, X.endOK e (X.gAt G rd (rst σ cy dec) (4 * X.B)) ∧
          ∀ g'' ∈ endOut e (X.gAt G rd (rst σ cy dec) (4 * X.B)),
            X.NextOK (X.wAt G rd (rst σ cy dec)) t' g'')) := by
  have hB1 : 1 ≤ X.B := Nat.one_le_two_pow
  have hBB : 2 ^ (X.B + 1) ≤ 2 ^ (2 * X.B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the guess
  obtain ⟨G, hG, hGfin⟩ : ∃ G : Option ℕ, (∀ ℓ, G = some ℓ → ℓ < X.no ∧ σ = X.sg ℓ) ∧
      (ev rd (2 * X.B) = 0 → ∃ ℓ, G = some ℓ ∧ X.lo ℓ ≤ i ∧ i < X.hi ℓ) := by
    by_cases ht : ev rd (2 * X.B) = 0
    · obtain ⟨ℓ, hℓ, hlo, hhi⟩ := hcover i (by omega)
      rw [ht] at htab
      refine ⟨some ℓ, fun ℓ' h => ?_, fun _ => ⟨ℓ, rfl, hlo, hhi⟩⟩
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hℓ, ?_⟩
      rw [hX.row ℓ hℓ i hlo hhi]; exact htab
    · exact ⟨none, by simp, fun h => absurd h ht⟩
  refine ⟨G, hG, ?_⟩
  have hI := nInv_canon hX (cy := cy) (dec := dec) (rd := rd) hG
  set g' := X.gAt G rd (rst σ cy dec) (4 * X.B) with hg'
  set w' := X.wAt G rd (rst σ cy dec) with hw'
  have e1 : (4 * X.B + 1) / 2 = 2 * X.B := by omega
  have e2 : (4 * X.B) / 2 = 2 * X.B := by omega
  obtain ⟨hboot, hσ, hdec, hev, hod, hzi, -, -, -, hcmp⟩ := hI
  rw [e1] at hev
  rw [e2] at hod hzi hcmp
  have hevw := ev_lt w' (2 * X.B)
  have hodw := od_lt w' (2 * X.B)
  have hodr := od_lt rd (2 * X.B)
  -- no carry out of the index
  have hcy : g'.cy = false := by
    cases hc : g'.cy
    · rfl
    · exfalso
      rw [hc] at hod
      have hcy1 := Bool.toNat_le cy
      have h2 : (true).toNat = 1 := rfl
      by_cases hd : dec = true
      · rw [if_pos hd] at hod hi; rw [h2] at hod; omega
      · rw [if_neg hd] at hod hi; rw [h2] at hod; omega
  have hnew : od w' (2 * X.B) = i := by
    rw [hcy] at hod
    have hcy1 := Bool.toNat_le cy
    have h2 : (false).toNat = 0 := rfl
    by_cases hd : dec = true
    · rw [if_pos hd] at hod hi; rw [h2] at hod; omega
    · rw [if_neg hd] at hod hi; rw [h2] at hod; omega
  by_cases ht : ev rd (2 * X.B) = 0
  · left
    refine ⟨ht, ?_⟩
    obtain ⟨ℓ, hGℓ, hlo, hhi⟩ := hGfin ht
    have hbo : g'.bo = true := by
      cases hc : g'.bo
      · rw [hc, ht] at hev; simp at hev
      · rfl
    have hs : g'.s = X.P.length := by
      rw [hg', hGℓ, s_gAt hX, e2, cnt_all hX.P_lt]
    have hgs : g'.gs = some ℓ := by
      have := gs_gAt (X := X) (G := G) (rd := rd) (g₀ := rst σ cy dec) rfl (4 * X.B - 1)
      rw [show 4 * X.B - 1 + 1 = 4 * X.B by omega] at this
      rw [hg', this, hGℓ]
    have hℓn := (hG ℓ hGℓ).1
    obtain ⟨hcl, hch⟩ := hcmp (by rw [hs, cnt_all hX.P_lt]) ℓ hgs
    rw [hnew, Nat.mod_eq_of_lt (hX.lo_lt ℓ hℓn)] at hcl
    rw [hnew, Nat.mod_eq_of_lt (hX.hi_lt ℓ hℓn)] at hch
    refine ⟨hboot, hbo, hcy, hs, by rw [hgs]; rfl, ?_, ?_⟩
    · rw [hcl]; intro h; rw [Nat.compare_eq_lt] at h; omega
    · rw [hch, Nat.compare_eq_lt]; exact hhi
  · right
    obtain ⟨t', ht'⟩ : ∃ t', ev rd (2 * X.B) = t' + 1 := ⟨ev rd (2 * X.B) - 1, by omega⟩
    have hbo : g'.bo = false := by
      cases hc : g'.bo
      · rfl
      · rw [hc] at hev; simp at hev; have := ev_lt rd (2 * X.B); omega
    have hevw' : ev w' (2 * X.B) = t' := by rw [hbo] at hev; simp at hev; omega
    rw [ht'] at htab
    obtain ⟨l, c, r, hF, hl, hc, hr⟩ := htab
    refine ⟨t', ht', hevw', .norm (decide (i = 0)) l c r, ?_, ?_⟩
    · refine ⟨hboot, hbo, hcy, ?_, ?_⟩
      · cases hz : g'.zi
        · have : od w' (2 * X.B) ≠ 0 := fun h => by rw [← hzi] at h; rw [hz] at h; simp at h
          simp [hnew ▸ this]
        · have : od w' (2 * X.B) = 0 := hzi.1 hz
          simp [← hnew, this]
      · rw [hσ]
        by_cases h0 : i = 0
        · simp only [h0, decide_true, if_true]; simp only [h0, if_true] at hF; exact hF
        · simp only [h0, decide_false, if_false, Bool.false_eq_true]; simp only [h0, if_false] at hF; exact hF
    · intro g'' hg''
      simp only [endOut, Set.mem_setOf_eq] at hg''
      rcases hg'' with rfl | rfl | ⟨hz, rfl⟩
      · exact ⟨c, false, false, i, rfl, by simp [hnew], by omega, hc⟩
      · exact ⟨r, true, false, i + 1, rfl, by simp [hnew], by omega, hr⟩
      · have hi0 : i ≠ 0 := by simpa using hz
        exact ⟨l, true, true, i - 1, rfl, by simp [hnew]; omega, by omega, hl hi0⟩

/-! ## The boot round -/

/-- The canonical operation of the boot round writing the cell index `i`. -/
def opB (i c : ℕ) : Op :=
  if c.testBit 0 then .bi (!c.testBit (X.e + 1) && i.testBit (c / 2)) else .bt (!c.testBit (X.e + 1))

theorem opOK_opB (i c : ℕ) (σ : S) (b : Bool) : X.opOK (X.opB i c) (g0 σ) b c := by
  unfold opB
  by_cases hc : c.testBit 0 = true
  · simp only [hc, if_true]
    refine ⟨rfl, hc, fun h => ?_⟩
    simp [h]
  · simp only [hc, if_false, Bool.false_eq_true]
    exact ⟨rfl, by simpa using hc, rfl⟩

theorem opEff_opB (i c : ℕ) (σ : S) : X.opEff (X.opB i c) (g0 σ) = g0 σ := by
  unfold opB; split_ifs <;> rfl

/-- The tape written by the boot round. -/
def wB (i : ℕ) (c : ℕ) : Bool := opW (X.opB i c)

theorem ev_wB (i : ℕ) : ev (X.wB i) (2 * X.B) = 2 ^ X.B - 1 := by
  have h := ev_boot (w := X.wB i) (B := X.B) (fun j hj => by
    simp only [wB, opB]
    have h0 : (2 * j).testBit 0 = false := by simp [Nat.testBit_zero]
    rw [h0]
    simp only [Bool.false_eq_true, if_false, opW]
    rw [testBit_top (e := X.e) (by have : 2 * j < 4 * X.B := by omega
                                   simpa [Spec.B, pow_add, mul_comm] using this)]
    simp only [Spec.B, pow_succ] at hj ⊢
    by_cases h : j < 2 ^ X.e
    · simp [h]; omega
    · simp [h]; omega) (2 * X.B) le_rfl
  rw [h, min_eq_right (by omega)]

theorem od_wB {i : ℕ} (hi : i < 2 ^ X.B) : od (X.wB i) (2 * X.B) = i := by
  have key : ∀ n ≤ 2 * X.B, od (X.wB i) n = i % 2 ^ min n X.B := by
    intro n
    induction n with
    | zero => simp [od, Nat.mod_one]
    | succ n ih =>
      intro hn
      rw [od_succ, ih (by omega)]
      have hbit : X.wB i (2 * n + 1) = (decide (n < X.B) && i.testBit n) := by
        simp only [wB, opB]
        have h1 : (2 * n + 1).testBit 0 = true := by simp [Nat.testBit_zero]
        rw [if_pos h1]
        simp only [opW]
        rw [testBit_top (e := X.e) (by have : 2 * n + 1 < 4 * X.B := by omega
                                       simpa [Spec.B, pow_add, mul_comm] using this)]
        have e2 : (2 * n + 1) / 2 = n := by omega
        rw [e2]
        simp only [Spec.B, pow_succ]
        by_cases h : n < 2 ^ X.e
        · simp [h]; omega
        · simp [h]; omega
      rw [hbit]
      by_cases h : n < X.B
      · rw [min_eq_left (by omega), min_eq_left (by omega)]
        simp only [h, decide_true, Bool.true_and]
        rw [mod_succ_toNat]
      · rw [min_eq_right (by omega), min_eq_right (by omega)]
        simp [h]
  rw [key _ le_rfl, min_eq_right (by omega), Nat.mod_eq_of_lt hi]

end Spec

end TT

end HardTR

end FOND
