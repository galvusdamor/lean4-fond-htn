import FondHtn.HardTR.TPT
import FondHtn.TOHard2.Main
import FondHtn.MPStrong.TR
/-!
# Tail-recursive MP strong plan existence is 2-EXPTIME-hard (CB22 Thm 5)

**`FOND.HardTR.hard_TR_mpStrong`**: `PlanExMP .strong FClass.TR` is 2-EXPTIME-hard; with
`FOND.strongMP_TR_mem`, **`FOND.HardTR.complete_TR_mpStrong`**: it is 2-EXPTIME-complete.

The reduction `FOND.HardTR.TI.red`: the tableau of a deterministic machine on the doubly
exponentially padded input is checked by the tableau transducer (`FondHtn/HardTR/Tab.lean`), whose
rounds are played by the two loops of a tail-recursive description (`TDesc.lean`); soundness
`TSound.lean`, completeness `TPlay.lean`, polynomial time `TPT.lean` and below.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

open TL TT TE TD TI TP HardMP HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime TOHard2 ATM TM

/-! ## The bits of the interval bounds -/

/-- The bits of `rA n p = 2 n + 2 + 2 ^ p`, without computing `2 ^ p` for large `p`. -/
def rAbit (n p j : ℕ) : Bool :=
  if n + 2 ≤ p then (decide (j = p) || (2 * n + 2).testBit j)
  else (2 * n + 2 + 2 ^ min p (n + 2)).testBit j

theorem rA_testBit (n p j : ℕ) : (rA n p).testBit j = rAbit n p j := by
  unfold rA rAbit
  split_ifs with h
  · have ha : 2 * n + 2 < 2 ^ p :=
      lt_of_lt_of_le (two_mul_add_lt_two_pow n) (Nat.pow_le_pow_right (by norm_num) h)
    rw [show 2 * n + 2 + 2 ^ p = 2 ^ p + (2 * n + 2) by ring]
    rcases lt_trichotomy j p with hj | rfl | hj
    · rw [Nat.testBit_two_pow_add_gt hj]; simp [hj.ne]
    · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha]; simp
    · have h1 : 2 ^ p + (2 * n + 2) < 2 ^ j := by
        have : 2 ^ (p + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        rw [pow_succ] at this; omega
      have h2 : 2 * n + 2 < 2 ^ j := by omega
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]; simp [hj.ne']
  · rw [min_eq_left (by omega)]

/-! ## The parameters of the source instance -/

section Src

variable {k : ℕ} (M : NTM (Fin k) (Option Bool)) (q e : Polynomial ℕ)

/-- The first `2 n + 2` letters of the padded input. -/
def pre (x : List Bool) : List Bool := (x.flatMap fun b => [b, b]) ++ [false, true]

/-- The code of the symbol of the interval `ℓ`. -/
def sgC (x : List Bool) (ℓ : ℕ) : ℕ :=
  if ℓ ≤ 2 * x.length + 1 then
    Nat.pair (if ℓ = 0 then M.init.val + 1 else 0) (((pre x).getI ℓ).toNat + 1)
  else Nat.pair 0 0

theorem length_pre (x : List Bool) : (pre x).length = 2 * x.length + 2 := by
  simp [pre, List.length_flatMap]; ring

variable {M}

theorem sgC_eq (hb : M.blank = none) (x : List Bool) (ℓ : ℕ) :
    sgC M x ℓ = cSym ((srcSpec M q x e).sg ℓ) := by
  have hpad : Cx.padExp2 q x = pre x ++ List.replicate (2 ^ 2 ^ q.eval x.length) true := by
    simp [Cx.padExp2, pairStr, pre]
  simp only [srcSpec, rowSpec, row0, sgC]
  by_cases hℓ : ℓ ≤ 2 * x.length + 1
  · have hlt : ℓ < (pre x).length := by rw [length_pre]; omega
    have hg : ((Cx.padExp2 q x).map some).getD ℓ M.blank = some ((pre x).getI ℓ) := by
      rw [hpad, List.map_append, List.getD_append _ _ _ _ (by simpa using hlt),
        List.getD_eq_getElem _ _ (by simpa using hlt)]
      simp [List.getI_eq_getElem _ hlt]
    rw [if_pos hℓ, rlo, if_pos hℓ, hg]
    by_cases h0 : ℓ = 0 <;> simp [h0, cSym]
  · have hA : (Cx.padExp2 q x).length ≤ rA x.length (2 ^ q.eval x.length) := by
      rw [hpad]; simp [length_pre, rA]
    have hg : ((Cx.padExp2 q x).map some).getD (rA x.length (2 ^ q.eval x.length)) M.blank = none := by
      rw [List.getD_eq_default _ _ (by simpa using hA), hb]
    have hA0 : rA x.length (2 ^ q.eval x.length) ≠ 0 := by
      simp [rA]
    rw [if_neg hℓ, rlo, if_neg hℓ, hg, if_neg hA0]
    rfl

/-- The special positions, without computing `2 ^ p` for large `p`. -/
def posL (x : List Bool) : List ℕ :=
  List.range (x.length + 2) ++
    (if x.length + 2 ≤ 2 ^ q.eval x.length then [2 ^ q.eval x.length]
      else if rAbit x.length (2 ^ q.eval x.length) (x.length + 2) then [x.length + 2] else []) ++
    [2 ^ e.eval x.length + 1]

theorem posL_eq (x : List Bool) : posL q e x = (srcSpec M q x e).P := by
  simp only [posL, srcSpec, rowSpec, rP, rext, rA_testBit]

theorem getI_nat (l : List ℕ) (s : ℕ) : l.getI s = l[s]?.getD 0 := by
  rw [← List.getD_default_eq_getI, List.getD_eq_getElem?_getD]; rfl

/-- The bit of the lower bound of the interval `ℓ` at the special position `s`. -/
def loC (x : List Bool) (ls : ℕ × ℕ) : Bool :=
  if ls.1 ≤ 2 * x.length + 1 then ls.1.testBit ((posL q e x).getI ls.2)
  else rAbit x.length (2 ^ q.eval x.length) ((posL q e x).getI ls.2)

/-- The bit of the upper bound of the interval `ℓ` at the special position `s`. -/
def hiC (x : List Bool) (ls : ℕ × ℕ) : Bool :=
  if ls.1 ≤ 2 * x.length then (ls.1 + 1).testBit ((posL q e x).getI ls.2)
  else if ls.1 = 2 * x.length + 1 then rAbit x.length (2 ^ q.eval x.length) ((posL q e x).getI ls.2)
  else decide ((posL q e x).getI ls.2 = 2 ^ e.eval x.length + 1)

theorem loC_eq (x : List Bool) (ls : ℕ × ℕ) :
    loC q e x ls = (srcSpec M q x e).kb (srcSpec M q x e).lo (some ls) := by
  obtain ⟨ℓ, s⟩ := ls
  simp only [loC, Spec.kb, ← posL_eq (M := M), List.getD_default_eq_getI]
  simp only [srcSpec, rowSpec, rlo]
  split_ifs <;> simp [rA_testBit, getI_nat]

theorem hiC_eq (x : List Bool) (ls : ℕ × ℕ) :
    hiC q e x ls = (srcSpec M q x e).kb (srcSpec M q x e).hi (some ls) := by
  obtain ⟨ℓ, s⟩ := ls
  simp only [hiC, Spec.kb, ← posL_eq (M := M), List.getD_default_eq_getI]
  simp only [srcSpec, rowSpec, rhi]
  split_ifs <;> simp [rA_testBit, Nat.testBit_two_pow, eq_comm, getI_nat]

/-! ## Polynomial time -/

theorem pt_rAbit {β : Type} [BEnc β] {n p pm j : β → ℕ} (hn : PT n) (hp : PT p) (hpm : PT pm)
    (hj : PT j) (he : ∀ b, pm b = 2 ^ min (p b) (n b + 2)) : PT fun b => rAbit (n b) (p b) (j b) :=
  (PT.ite (PT.le (PT.succ (PT.succ hn)) hp) (PT.or (PT.eq hj hp) (pt_testBit (PT.affine 2 2 hn) hj))
    (pt_testBit (PT.add (PT.affine 2 2 hn) hpm) hj)).of_eq fun b => by
      simp only [rAbit, he]

variable (M) in
/-- **The parameters of the source instance are computed in polynomial time.** -/
theorem hyp_src (hb : M.blank = none) :
    Hyp cSym (fun x => srcSpec M q x e) M.F (accSet M) := by
  obtain ⟨Ql, hQl, hQlen⟩ := PolyDom.exists_pt_polyLen q
  obtain ⟨El, hEl, hElen⟩ := PolyDom.exists_pt_polyLen e
  have hn : PT fun x : List Bool => x.length := PT.length PT.id
  have hp : PT fun x : List Bool => 2 ^ q.eval x.length :=
    (AcycHard.Sav.pt_pow2len hQl).of_eq fun x => by rw [hQlen]
  have hE2 : PT fun x : List Bool => 2 ^ e.eval x.length :=
    (AcycHard.Sav.pt_pow2len hEl).of_eq fun x => by rw [hElen]
  have hR2 : PT fun x : List Bool => List.range (x.length + 2) :=
    (PT.rangeLength (PT.append PT.id (PT.const [false, false]))).of_eq fun x => by simp
  have hlt : PT₂ fun (x : List Bool) (r : ℕ) => decide (r < 2 ^ q.eval x.length) :=
    PT.lt PT.snd (hp.comp PT.fst)
  have hpm : PT fun x : List Bool => 2 ^ min (2 ^ q.eval x.length) (x.length + 2) :=
    (PT.ofBits (PT.append (PT.map (g := fun _ _ => false) (PT.filter hR2 hlt)
      (PT.const false)) (PT.const [true]))).of_eq fun x => pow_min_eq _ _
  have hext : PT fun x : List Bool => rAbit x.length (2 ^ q.eval x.length) (x.length + 2) :=
    pt_rAbit hn hp hpm (PT.succ (PT.succ hn)) fun _ => rfl
  have hP : PT fun x => posL q e x :=
    PT.append (PT.append hR2 (PT.ite (PT.le (PT.succ (PT.succ hn)) hp) (PT.single hp)
      (PT.ite (PT.eq hext (PT.const true)) (PT.single (PT.succ (PT.succ hn))) PT.nil)))
      (PT.single (PT.succ hE2))
  have hpre : PT fun x => pre x :=
    PT.append (PT.flatMap PT.id (PT.cons PT.snd (PT.single PT.snd))) (PT.const _)
  have hbit : PT fun z : List Bool × ℕ => ((pre z.1).getI z.2).toNat :=
    (PT.cond (PT.getI (hpre.comp PT.fst) PT.snd) (PT.const 1) (PT.const 0)).of_eq fun z => by
      cases (pre z.1).getI z.2 <;> rfl
  have hsg : PT fun z : List Bool × ℕ => sgC M z.1 z.2 :=
    PT.ite (PT.le PT.snd (PT.affine 2 1 (hn.comp PT.fst)))
      (PT.natPair (PT.ite (PT.eq PT.snd (PT.const 0)) (PT.const _) (PT.const 0)) (PT.succ hbit))
      (PT.const _)
  have hj : PT fun z : List Bool × (ℕ × ℕ) => (posL q e z.1).getI z.2.2 :=
    PT.getI (hP.comp PT.fst) (PT.snd' PT.snd)
  have hrz : PT fun z : List Bool × (ℕ × ℕ) =>
      rAbit z.1.length (2 ^ q.eval z.1.length) ((posL q e z.1).getI z.2.2) :=
    pt_rAbit (hn.comp PT.fst) (hp.comp PT.fst) (hpm.comp PT.fst) hj fun _ => rfl
  have hlo : PT fun z : List Bool × (ℕ × ℕ) => loC q e z.1 z.2 :=
    PT.ite (PT.le (PT.fst' PT.snd) (PT.affine 2 1 (hn.comp PT.fst)))
      (pt_testBit (PT.fst' PT.snd) hj) hrz
  have hhi : PT fun z : List Bool × (ℕ × ℕ) => hiC q e z.1 z.2 :=
    PT.ite (PT.le (PT.fst' PT.snd) (PT.affine 2 0 (hn.comp PT.fst)))
      (pt_testBit (PT.succ (PT.fst' PT.snd)) hj)
      (PT.ite (PT.eq (PT.fst' PT.snd) (PT.affine 2 1 (hn.comp PT.fst))) hrz
        (PT.eq hj (PT.succ (hE2.comp PT.fst))))
  exact
  { m := (PT.rangeLength (PT.append hEl (PT.const [(), ()]))).of_eq fun x => by
      simp [srcSpec, rowSpec, mm, hElen]
    no := (PT.rangeLength (PT.append (PT.append PT.id PT.id) (PT.const [false, false, false]))).of_eq
      fun x => by simp [srcSpec, rowSpec]; ring_nf
    P := hP.of_eq fun x => posL_eq (M := M) q e x
    sg := hsg.of_eq fun z => sgC_eq q e hb z.1 z.2
    lo := hlo.of_eq fun z => loC_eq (M := M) q e z.1 z.2
    hi := hhi.of_eq fun z => hiC_eq (M := M) q e z.1 z.2
    F := fun _ => rfl
    acc := fun _ => rfl }

variable (M) in
/-- **The reduction is computed in polynomial time.** -/
theorem pt_red (hb : M.blank = none) : PT (red M q e) :=
  (pt_desc allSym (hyp_src M q e hb) (ensOf allSym) σI).of_eq fun _ => rfl

end Src

/-! ## Hardness -/

/-- **Tail-recursive strong method-based plan existence is 2-EXPTIME-hard** [CB22 Thm 5]. -/
theorem hard_TR_mpStrong : Cx.Hard Cx.EXPTIME2 (PlanExMP .strong FClass.TR) := by
  intro L hL
  obtain ⟨k, M, q, e, hb, -, hB, hLx⟩ := exptime2_tabWin_pow' hL
  have hf : PT (red M q e) := pt_red M q e hb
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hf)), fun x => ?_⟩
  show L x ↔ PlanExMP .strong FClass.TR (enc (red M q e x))
  rw [planExMP_enc_iff, MPCrit.Solvable]
  exact ⟨fun hx => ⟨valid _ _ _ _ _ _ cSym_inj, red_TR x, (red_iff hb hB hLx x).1 hx⟩,
    fun ⟨_, _, h⟩ => (red_iff hb hB hLx x).2 h⟩

/-- **Tail-recursive strong method-based plan existence is 2-EXPTIME-complete** [CB22 Thm 5]. -/
theorem complete_TR_mpStrong : Cx.Complete Cx.EXPTIME2 (PlanExMP .strong FClass.TR) :=
  ⟨strongMP_TR_mem, hard_TR_mpStrong⟩

end HardTR

end FOND
