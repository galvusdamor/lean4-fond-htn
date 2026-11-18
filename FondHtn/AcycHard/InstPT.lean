import FondHtn.AcycHard.InstNum
import FondHtn.TOHard2.PT
/-!
# The description of the Savitch instance is computed in polynomial time

**`FOND.AcycHard.Sav.pt_descOf`**: for polynomial-time lengths `P, E₁, E₂` of the input,
`w ↦ (instOf N P E₁ E₂ w).desc` is computed in polynomial time.  The proof uses the numeric
form of `FOND.AcycHard.Sav.Inst.acts_num` and `FOND.AcycHard.Sav.Inst.meths_num`; the
input-dependent options enter through their code quadruples.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

namespace Sav

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime HardMP TM TOHard2

variable {k : ℕ}

/-! ## Generic pieces -/

section Gen

variable {α : Type} [BEnc α]

theorem pt_setTn {f : α → List (Bool × ℕ)} (hf : PT f) : PT fun a => setTn (f a) := by
  unfold setTn
  have hR := PT.rangeLength hf
  exact PT.pair hR (PT.pair PT.nil (PT.map hR (PT.pair PT.snd (PT.getI (hf.comp PT.fst) PT.snd))))

theorem pt_pow2len {f : α → List Unit} (hf : PT f) : PT fun a => 2 ^ (f a).length :=
  (PT.ofBits (PT.append (PT.map (g := fun _ _ => false) hf (PT.const false)) (PT.const [true]))).of_eq
    fun x => by rw [List.map_const', natOfBits_pow]

theorem pt_cOq {q : α → ℕ × ℕ × ℕ × ℕ} (hq : PT q) : PT fun a => cOq (q a) :=
  PT.natPair (PT.fst' hq) (PT.natPair (PT.fst' (PT.snd' hq))
    (PT.natPair (PT.fst' (PT.snd' (PT.snd' hq))) (PT.snd' (PT.snd' (PT.snd' hq)))))

theorem pt_fT (i : ℕ) {x : α → ℕ} (hx : PT x) : PT fun a => fT i (x a) :=
  PT.natPair (PT.const 2) (PT.natPair (PT.const i) hx)

theorem pt_qPre {q : α → ℕ × ℕ × ℕ × ℕ} (hq : PT q) : PT fun a => qPre (q a) :=
  PT.cons (PT.const _) (PT.cons (pt_fT 0 (PT.fst' hq)) (PT.cons (pt_fT 1 (PT.fst' (PT.snd' hq)))
    (PT.single (pt_fT 2 (PT.fst' (PT.snd' (PT.snd' hq)))))))

theorem pt_qAct {q : α → ℕ × ℕ × ℕ × ℕ} (hq : PT q) : PT fun a => qAct (q a) :=
  PT.pair (PT.natPair (PT.const 8) (pt_cOq hq)) (PT.pair (pt_qPre hq) (PT.pair PT.nil
    (PT.single (PT.pair (PT.cons (PT.const _) (PT.single (pt_fT 0 (PT.snd' (PT.snd' (PT.snd' hq))))))
      (pt_qPre hq)))))

theorem pt_qFacts {q : α → ℕ × ℕ × ℕ × ℕ} (hq : PT q) : PT fun a => qFacts (q a) :=
  PT.cons (pt_fT 0 (PT.fst' hq)) (PT.cons (pt_fT 1 (PT.fst' (PT.snd' hq)))
    (PT.single (pt_fT 2 (PT.fst' (PT.snd' (PT.snd' hq))))))

theorem pt_qSB {q : α → ℕ × ℕ × ℕ × ℕ} (hq : PT q) : PT fun a => qSB (q a) :=
  PT.pair (PT.natPair (PT.const 2) (pt_cOq hq)) (PT.pair (PT.const false)
    (PT.natPair (PT.const 8) (pt_cOq hq)))

theorem pt_toRdAct {L : α → ℕ} (hL : PT fun a => List.range (L a + 2)) : PT fun a => toRdAct (L a) := by
  unfold toRdAct
  exact PT.pair (PT.const _) (PT.pair PT.nil (PT.pair PT.nil (PT.single (PT.pair (PT.const _)
    (PT.map hL (pt_fT 0 (PT.natPair (PT.const 0) PT.snd)))))))

theorem pt_methPw {cb j : α → ℕ} {l0 : α → List (Bool × ℕ)} (hcb : PT cb) (hj : PT j) (hl0 : PT l0) :
    PT fun a => methPw (cb a) (j a) (l0 a) := by
  unfold methPw
  have hp := PT.natPair (PT.const 0) (PT.natPair hcb (PT.subC hj 1))
  exact PT.pair (PT.natPair (PT.const 0) (PT.natPair hcb hj))
    (pt_seqTn (PT.ite (PT.eq hj (PT.const 0)) hl0
      (PT.cons (PT.pair (PT.const true) hp) (PT.single (PT.pair (PT.const true) hp)))))

theorem pt_methSpw {cs : α → ℕ} {it : α → Bool × ℕ} {j : α → ℕ} (hcs : PT cs) (hit : PT it) (hj : PT j) :
    PT fun a => methSpw (cs a) (it a) (j a) := by
  unfold methSpw
  have hp := PT.natPair (PT.const 5) (PT.natPair hcs (PT.subC hj 1))
  exact PT.pair (PT.natPair (PT.const 5) (PT.natPair hcs hj))
    (pt_setTn (PT.ite (PT.eq hj (PT.const 0)) (PT.single hit)
      (PT.cons (PT.pair (PT.const true) hp) (PT.single (PT.pair (PT.const true) hp)))))

theorem pt_bitsRange {B c : α → ℕ} (hB : PT fun a => List.range (B a)) (hc : PT c) :
    PT fun a => (List.range (B a)).filter fun j => (c a).testBit j :=
  PT.filter hB (pt_testBit (hc.comp PT.fst) PT.snd)

theorem pt_methPown {cb B c : α → ℕ} (hcb : PT cb) (hB : PT fun a => List.range (B a)) (hc : PT c) :
    PT fun a => methPown (cb a) (B a) (c a) := by
  unfold methPown
  exact PT.pair (PT.natPair (PT.const 1) hcb) (pt_seqTn (PT.map (pt_bitsRange hB hc)
    (PT.pair (PT.const true) (PT.natPair (PT.const 0) (PT.natPair (hcb.comp PT.fst) PT.snd)))))

theorem pt_methSpown {cs B c : α → ℕ} (hcs : PT cs) (hB : PT fun a => List.range (B a)) (hc : PT c) :
    PT fun a => methSpown (cs a) (B a) (c a) := by
  unfold methSpown
  exact PT.pair (PT.natPair (PT.const 6) hcs) (pt_setTn (PT.map (pt_bitsRange hB hc)
    (PT.pair (PT.const true) (PT.natPair (PT.const 5) (PT.natPair (hcs.comp PT.fst) PT.snd)))))

theorem pt_blkM (cb : ℕ) (l0 : List (Bool × ℕ)) {B c : α → ℕ} (hB : PT fun a => List.range (B a))
    (hc : PT c) : PT fun a => blkM cb l0 (B a) (c a) := by
  unfold blkM
  exact PT.append (PT.map hB (pt_methPw (PT.const cb) PT.snd (PT.const l0)))
    (PT.single (pt_methPown (PT.const cb) hB hc))

theorem pt_sbM {d : α → ℕ × (Bool × ℕ)} {B c : α → ℕ} (hd : PT d) (hB : PT fun a => List.range (B a))
    (hc : PT c) : PT fun a => sbM (d a) (B a) (c a) := by
  unfold sbM
  exact PT.append (PT.map hB (pt_methSpw (PT.fst' (hd.comp PT.fst)) (PT.snd' (hd.comp PT.fst)) PT.snd))
    (PT.single (pt_methSpown (PT.fst' hd) hB hc))

theorem pt_map_const {β γ : Type} [BEnc γ] (L : List β) {G : α → β → γ}
    (h : ∀ t ∈ L, PT fun a => G a t) : PT fun a => L.map (G a) :=
  (pt_flatMap_const L (G := fun a t => [G a t]) fun t ht => PT.single (h t ht)).of_eq fun a => by
    clear h
    induction L with
    | nil => rfl
    | cons t L ih => simp [ih]

end Gen

/-! ## The options of an input -/

theorem tri_two_mul : ∀ n, 2 * FSpec.tri n = n * (n - 1)
  | 0 => rfl
  | n + 1 => by
    simp only [FSpec.tri]
    rw [mul_add, tri_two_mul n]
    cases n with
    | zero => rfl
    | succ n => simp only [Nat.add_sub_cancel]; ring

theorem tri_eq (n : ℕ) : FSpec.tri n = n * (n - 1) / 2 := by
  rw [← tri_two_mul]; omega

variable (N : NTM (Fin k) (Option Bool))

/-- The code of the tape symbol of cell `i` of the initial configuration. -/
def cTS (w : List Bool) (i : ℕ) : ℕ := if i < w.length then (if w.getI i then 2 else 1) else codeTS N.blank

theorem codeTS_tape (w : List Bool) (i : ℕ) :
    codeTS ((N.initConfig (w.map some)).tape i) = cTS N w i := by
  simp only [NTM.initConfig, cTS]
  split_ifs with h h'
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
    rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ h] at h'
    simp [h', codeTS]
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
    rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ h] at h'
    simp at h'; simp [h', codeTS]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

/-- The code quadruple of an input option. -/
def quadI (w : List Bool) (σ : SymK k) (e : XK k) (i : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (Nat.pair 0 i, codeSym σ,
    Nat.pair (Nat.pair (cTS N w i) (if i = 0 then N.init.val + 1 else 0)) (Nat.pair (codeX e) (codeX e)) + 1,
    Nat.pair 0 (min (i + 1) (w.length + 1)))

theorem quad_optI (w : List Bool) (σ : SymK k) (e : XK k) (i : ℕ) :
    quad ((AS.inp i, σ, some (mk (N.initConfig (w.map some)) i, e, e), AS.inp (min (i + 1) (w.length + 1))) :
      OK k) = quadI N w σ e i := by
  simp only [quad, quadI, codeAS, codeSym, codeX, mk, codeTS_tape]
  congr 4
  simp only [NTM.initConfig]
  split_ifs <;> rfl

theorem quads_eq (P E₁ E₂ : ℕ) (w : List Bool) : (instOf N P E₁ E₂ w).opts.map quad =
    (List.range (w.length + 2)).flatMap (fun i => (allSyms k).flatMap fun σ => (accE N).map fun e =>
      quadI N w σ e i) ++ (optsC N).map quad := by
  simp only [instOf, optsI, List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
    quad_optI]

variable {N}

theorem pt_quadI (σ : SymK k) (e : XK k) : PT fun p : List Bool × ℕ => quadI N p.1 σ e p.2 := by
  unfold quadI
  have hi : PT fun p : List Bool × ℕ => p.2 := PT.snd
  have hw : PT fun p : List Bool × ℕ => p.1 := PT.fst
  refine PT.pair (PT.natPair (PT.const 0) hi) (PT.pair (PT.const _) (PT.pair ?_
    (PT.natPair (PT.const 0) (PT.ite (PT.le (PT.succ hi) (PT.succ (PT.length hw))) (PT.succ hi)
      (PT.succ (PT.length hw))) |>.of_eq fun p => by simp [min_def])))
  refine PT.succ (PT.natPair (PT.natPair ?_ (PT.ite (PT.eq hi (PT.const 0)) (PT.const _) (PT.const 0)))
    (PT.const _))
  unfold cTS
  exact PT.ite (PT.lt hi (PT.length hw)) (PT.ite (PT.eq (PT.getI hw hi) (PT.const true)) (PT.const 2)
    (PT.const 1)) (PT.const _)


theorem pt_quads {Pf E₁f E₂f : List Bool → ℕ} :
    PT fun w => (instOf N (Pf w) (E₁f w) (E₂f w) w).opts.map quad := by
  have hR : PT fun w : List Bool => List.range (w.length + 2) :=
    (PT.rangeLength (PT.append PT.id (PT.const [true, true]))).of_eq fun w => by simp
  have h : PT fun w : List Bool => (List.range (w.length + 2)).flatMap (fun i => (allSyms k).flatMap
      fun σ => (accE N).map fun e => quadI N w σ e i) ++ (optsC N).map quad := by
    refine PT.append (PT.flatMap hR ?_) (PT.const _)
    show PT fun p : List Bool × ℕ => (allSyms k).flatMap fun σ => (accE N).map fun e => quadI N p.1 σ e p.2
    exact pt_flatMap_const _ fun σ _ => pt_map_const _ fun e _ => pt_quadI σ e
  exact h.of_eq fun w => (quads_eq N _ _ _ w).symm
/-! ## The description -/

/-- **The description is computed in polynomial time.** -/
theorem pt_descOf {Pl E₁l E₂l : List Bool → List Unit} (hP : PT Pl) (h₁ : PT E₁l) (h₂ : PT E₂l) :
    PT fun w => (instOf N (Pl w).length (E₁l w).length (E₂l w).length w).desc := by
  set I : List Bool → Inst k := fun w => instOf N (Pl w).length (E₁l w).length (E₂l w).length w with hI
  have hS : PT fun w => (I w).S := pt_pow2len hP
  have hn : PT fun w => (I w).n := pt_pow2len h₁
  have hR : PT fun w => (I w).R := pt_pow2len h₂
  have hK : PT fun w => (I w).K :=
    PT.subC (PT.add (PT.add (PT.const k) (PT.length hP)) (PT.mul (PT.const 2) hS)) 1
  have hL2 : PT fun w => List.range ((I w).L + 2) :=
    (PT.rangeLength (PT.append PT.id (PT.const [true, true]))).of_eq fun w => by simp [hI, instOf]
  have hB : PT fun w => List.range (I w).B :=
    (PT.rangeLength (PT.append h₂ (PT.const [()]))).of_eq fun w => by simp [hI, instOf]
  have htri : PT fun w => FSpec.tri (I w).S :=
    (PT.divC (PT.mul hS (PT.subC hS 1)) two_pos).of_eq fun w => (tri_eq _).symm
  have hQ : PT fun w => (I w).opts.map quad := pt_quads
  have hsyms : ∀ w, (I w).syms = allSyms k := fun w => rfl
  have hacts : PT fun w => (I w).acts := by
    simp only [Inst.acts_num, hsyms]
    refine (PT.dedup (PT.append (PT.append (PT.append (PT.const (ctlA0 (k := k)))
      (PT.cons (pt_toRdAct hL2) (PT.const (ctlA1 (k := k)))))
      (PT.single (PT.pair (PT.const _) (PT.pair PT.nil (PT.pair PT.nil (PT.single (PT.pair
        (PT.append (PT.const _) (PT.flatMap (g := fun _ q => qFacts q) hQ (pt_qFacts PT.snd))) PT.nil)))))))
      (PT.append (PT.append (PT.const (symActs (allSyms k))) (PT.const (trActs (k := k))))
        (PT.map (g := fun _ q => qAct q) hQ (pt_qAct PT.snd))))).of_eq fun w => rfl
  have hB1 : PT fun p : List Bool × (ℕ × (Bool × ℕ)) => List.range (I p.1).B := hB.comp PT.fst
  have hn1 : PT fun p : List Bool × (ℕ × (Bool × ℕ)) => (I p.1).n := hn.comp PT.fst
  have hB2 : PT fun p : List Bool × (ℕ × ℕ × ℕ × ℕ) => List.range (I p.1).B := hB.comp PT.fst
  have hn2 : PT fun p : List Bool × (ℕ × ℕ × ℕ × ℕ) => (I p.1).n := hn.comp PT.fst
  have hmeths : PT fun w => (I w).cnList.map (I w).methOf := by
    simp only [Inst.meths_num, Inst.methOf_pool, hsyms]
    refine (PT.append (PT.append (PT.append
      (PT.append (PT.append (PT.append (PT.append (PT.append (PT.append
        (pt_blkM _ _ hB hS) (pt_blkM _ _ hB hS)) (pt_blkM _ _ hB htri)) (pt_blkM _ _ hB hS))
        (pt_blkM _ _ hB hK)) (pt_blkM _ _ hB hR)) (pt_blkM _ _ hB hS))
      (PT.const (Inst.I0.methOf .cellB :: (allSyms k).map fun τ => Inst.I0.methOf (.newc τ))))
      (PT.cons (PT.const _) (PT.append (PT.append (pt_sbM (PT.const _) hB hS)
        (PT.flatMap (g := fun w d => sbM d (I w).B (I w).n) (PT.const ((allSyms k).map fun τ => sbD (.fresh τ))) (pt_sbM PT.snd hB1 hn1)))
        (PT.flatMap (g := fun w q => sbM (qSB q) (I w).B (I w).n) hQ (pt_sbM (pt_qSB PT.snd) hB2 hn2)))))
      (PT.single (PT.pair (PT.const _) (pt_setTn (PT.cons (PT.const _) (PT.append (PT.const _)
        (PT.map (g := fun _ q => (true, Nat.pair 6 (Nat.pair 2 (cOq q)))) hQ (PT.pair (PT.const true) (PT.natPair (PT.const 6)
          (PT.natPair (PT.const 2) (pt_cOq PT.snd))))))))))).of_eq fun w => rfl
  refine (PT.pair (PT.pair hacts hmeths) (PT.const (Inst.initL (k := k), setTn (Inst.tnIL (k := k))))).of_eq fun w => ?_
  simp only [hI, Inst.desc]

end Sav

end AcycHard

end FOND
