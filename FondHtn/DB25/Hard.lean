import FondHtn.DB25.PTBuild
/-!
# [DB25, Thm. 4/5] (repaired route): regular strong OD plan existence is EXPSPACE-hard

**`FOND.strongOD_REGtn_expspaceHard`**: `PlanExFM strongOD REGtn` is EXPSPACE-hard (hence also
`PlanExFM strongOD REG`, `FOND.strongOD_REG_expspaceHard`).

**Deviation from [DB25].**  DB25 reduces from chosen-length planning games (Thm. 1), whose
hardness proof leaves the STRIPS gadgets unspecified, and then simulates games by regular
problems (Thm. 5, backup/restore networks).  Here we reduce **directly from exponential-space
nondeterministic Turing machines**:

* the planner's fixed decomposition word chooses, step by step, the transition and the carry
  pattern of the head counter (`FOND.DB.stepData`), so the machine run is fixed in advance and
  the same for all branches;
* nature chooses one tape cell `c` at the start; each block tracks the content of `c`
  (`FOND.DB.loopOps`), with the policy's choices checked by CNF gadgets (`FOND.DB.opPhases`);
* hence a strong OD solution exists iff some run exists that is consistent at every cell.

The gadgets use positive preconditions only (each Boolean register is a pair of facts).
-/

namespace FOND

namespace DB

open HTN HTN.Syn HTN.Syn.PolyDom PTime TM

/-! ## Direct forms of the block phases -/

theorem flatMap_single {β γ : Type} (l : List β) (f : β → γ) : l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The phases of the initial block. -/
def prePh (n : ℕ) (w : List Sym) (blank : Sym) : List (List FActDesc) :=
  (List.range n).map (fun b => [natA (cB b)]) ++
    (initChoices w).map (fun r => [setA r false, setA r true]) ++
    (phiInit n w blank).flatMap clausePhases

theorem blockPhases_preOps (n : ℕ) (w : List Sym) (blank : Sym) :
    blockPhases (preOps n w blank) = prePh n w blank := by
  simp [blockPhases, preOps, prePh, opPhases, List.flatMap_append, List.flatMap_map,
    flatMap_single (f := fun b => [natA (cB b)]),
    flatMap_single (f := fun r => [setA r false, setA r true])]

/-- The phases of a loop block. -/
def loopPh (n : ℕ) (d : TrD × HU) : List (List FActDesc) :=
  (stepChoices n).map (fun r => [setA r false, setA r true]) ++
    (phiStep n d.1).flatMap clausePhases ++
    [[cpA (tB 0) (lit (sB 0)) true, cpA (tB 0) (lit (sB 0)) false],
     [cpA (tB 1) (lit (sB 1)) true, cpA (tB 1) (lit (sB 1)) false],
     [updA d.1.1 (d.2.1.map hl) d.1.2.2.1 (d.2.2.map hl)]]

theorem blockPhases_loopOps (n : ℕ) (d : TrD × HU) : blockPhases (loopOps n d) = loopPh n d := by
  simp [blockPhases, loopOps, loopPh, opPhases, List.flatMap_append, List.flatMap_map,
    flatMap_single (f := fun r => [setA r false, setA r true])]

/-- The phases of a final block. -/
def finalPh (acc : ℕ) : List (List FActDesc) := [[updA acc [] acc []]]

theorem blockPhases_finalOps (acc : ℕ) : blockPhases (finalOps acc) = finalPh acc := by
  simp [blockPhases, finalOps, finalPh, opPhases]

theorem tmDesc_eq {k : ℕ} (N : NTM (Fin k) Sym) (n : ℕ) (w : List Sym) :
    tmDesc N n w = mkDesc (initList (regs n w) (fun _ => false) N.init.val) (prePh n w N.blank)
      ((stepData N n).map (loopPh n)) ((accList N).map finalPh) := by
  simp only [tmDesc, opDesc, blockPhases_preOps, List.map_map]
  have h1 : blockPhases ∘ loopOps n = loopPh n := funext fun d => blockPhases_loopOps n d
  have h2 : blockPhases ∘ finalOps = finalPh := funext fun a => blockPhases_finalOps a
  rw [h1, h2]

/-! ## The initial CNF with binary numerals -/

theorem lt_two_pow_iff (i n : ℕ) : i < 2 ^ n ↔ (bitsOfNat i).length ≤ n :=
  ⟨length_bits_le_of_lt, fun h => lt_of_lt_of_le (lt_two_pow_length_bits i)
    (Nat.pow_le_pow_right (by norm_num) h)⟩

/-- `phiInit` with the binary numerals of the library. -/
def phiInitB (n : ℕ) (w : List Sym) (blank : Sym) : List Clause :=
  ((List.range w.length).flatMap fun i =>
    if (bitsOfNat i).length ≤ n then (List.range n).map fun b =>
      [(gB i, false), (cB b, (bitsOfNat i).getI b)]
    else [[(gB i, false)]]) ++
  ((List.range w.length).flatMap fun i =>
    if (bitsOfNat i).length ≤ n then (List.range 2).map fun j =>
      (List.range n).map (fun b => (cB b, !(bitsOfNat i).getI b)) ++ [(sB j, ebit (w.getI i) j)]
    else []) ++
  ((List.range 2).map fun j =>
    (List.range w.length).map (fun i => (gB i, true)) ++ [(sB j, ebit blank j)])

theorem phiInit_eq (n : ℕ) (w : List Sym) (blank : Sym) : phiInit n w blank = phiInitB n w blank := by
  simp only [phiInit, phiInitB, Article.getI_bitsOfNat, lt_two_pow_iff]

/-! ## Polynomial time -/

section

variable {α : Type} [BEnc α]

theorem pt_ebit {γ : α → Sym} {j : α → ℕ} (hγ : PT γ) (hj : PT j) : PT fun a => ebit (γ a) (j a) := by
  unfold ebit
  exact PT.ite (PT.eq hj (PT.const 0)) (PT.isSome hγ) (PT.getD hγ (PT.const false))

theorem pt_reg (t : ℕ) {b : α → ℕ} (hb : PT b) : PT fun a => Nat.pair t (b a) :=
  PT.natPair (PT.const t) hb

theorem pt_phiStep {u : α → List Unit} {τ : α → TrD} (hu : PT u) (hτ : PT τ) :
    PT fun a => phiStep (u a).length (τ a) := by
  unfold phiStep cB hB sB tB dB
  have hR : PT fun a => List.range (u a).length := PT.rangeLength hu
  refine PT.append (PT.append (PT.append ?_ ?_) ?_) ?_
  · exact PT.flatMap hR (PT.cons (PT.cons (PT.pair (pt_reg 4 PT.snd) (PT.const false))
      (PT.cons (PT.pair (pt_reg 0 PT.snd) (PT.const true)) (PT.single (PT.pair (pt_reg 1 PT.snd)
        (PT.const true))))) (PT.single (PT.cons (PT.pair (pt_reg 4 PT.snd) (PT.const false))
          (PT.cons (PT.pair (pt_reg 0 PT.snd) (PT.const false)) (PT.single (PT.pair
            (pt_reg 1 PT.snd) (PT.const false)))))))
  · exact PT.map (PT.const (List.range 2)) (PT.append (PT.map (hR.comp PT.fst)
      (PT.pair (pt_reg 4 PT.snd) (PT.const true))) (PT.single (PT.pair (pt_reg 2 PT.snd)
        (pt_ebit (PT.fst.comp (PT.snd.comp (hτ.comp PT.fst))) PT.snd))))
  · exact PT.map (PT.const (List.range 2)) (PT.append (PT.map (hR.comp PT.fst)
      (PT.pair (pt_reg 4 PT.snd) (PT.const true))) (PT.single (PT.pair (pt_reg 3 PT.snd)
        (pt_ebit (PT.snd.comp (PT.snd.comp (PT.snd.comp (hτ.comp PT.fst)))) PT.snd))))
  · refine PT.flatMap hR (PT.flatMap (PT.const (List.range 2)) ?_)
    -- on `((a, b), j)`
    have hb : PT fun z : (α × ℕ) × ℕ => z.1.2 := PT.snd.comp PT.fst
    have hj : PT fun z : (α × ℕ) × ℕ => z.2 := PT.snd
    exact PT.cons (PT.cons (PT.pair (pt_reg 0 hb) (PT.const true)) (PT.cons (PT.pair (pt_reg 1 hb)
      (PT.const false)) (PT.cons (PT.pair (pt_reg 3 hj) (PT.const false)) (PT.single (PT.pair
        (pt_reg 2 hj) (PT.const true)))))) (PT.cons (PT.cons (PT.pair (pt_reg 0 hb)
      (PT.const true)) (PT.cons (PT.pair (pt_reg 1 hb) (PT.const false)) (PT.cons (PT.pair
        (pt_reg 3 hj) (PT.const true)) (PT.single (PT.pair (pt_reg 2 hj) (PT.const false))))))
      (PT.cons (PT.cons (PT.pair (pt_reg 0 hb) (PT.const false)) (PT.cons (PT.pair (pt_reg 1 hb)
        (PT.const true)) (PT.cons (PT.pair (pt_reg 3 hj) (PT.const false)) (PT.single (PT.pair
          (pt_reg 2 hj) (PT.const true)))))) (PT.single (PT.cons (PT.pair (pt_reg 0 hb)
        (PT.const false)) (PT.cons (PT.pair (pt_reg 1 hb) (PT.const true)) (PT.cons (PT.pair
          (pt_reg 3 hj) (PT.const true)) (PT.single (PT.pair (pt_reg 2 hj) (PT.const false)))))))))

theorem pt_phiInitB {u : α → List Unit} {w : α → List Sym} (blank : Sym) (hu : PT u) (hw : PT w) :
    PT fun a => phiInitB (u a).length (w a) blank := by
  unfold phiInitB cB sB gB
  have hR : PT fun a => List.range (u a).length := PT.rangeLength hu
  have hW : PT fun a => List.range (w a).length := PT.rangeLength hw
  have hlen : PT fun z : α × ℕ => decide ((bitsOfNat z.2).length ≤ (u z.1).length) :=
    PT.le (PT.length (PT.bits.comp PT.snd)) (PT.length (hu.comp PT.fst))
  refine PT.append (PT.append ?_ ?_) ?_
  · refine PT.flatMap hW (PT.ite hlen ?_ (PT.single (PT.single (PT.pair (pt_reg 5 PT.snd)
      (PT.const false)))))
    exact PT.map (hR.comp PT.fst) (PT.cons (PT.pair (pt_reg 5 (PT.snd.comp PT.fst))
      (PT.const false)) (PT.single (PT.pair (pt_reg 0 PT.snd)
        (PT.getI (PT.bits.comp (PT.snd.comp PT.fst)) PT.snd))))
  · refine PT.flatMap hW (PT.ite hlen ?_ PT.nil)
    refine PT.map (PT.const (List.range 2)) (PT.append ?_ (PT.single (PT.pair (pt_reg 2 PT.snd)
      (pt_ebit (PT.getI (hw.comp (PT.fst.comp PT.fst)) (PT.snd.comp PT.fst)) PT.snd))))
    exact PT.map (hR.comp (PT.fst.comp PT.fst)) (PT.pair (pt_reg 0 PT.snd)
      (PT.not (PT.getI (PT.bits.comp (PT.snd.comp (PT.fst.comp PT.fst))) PT.snd)))
  · exact PT.map (PT.const (List.range 2)) (PT.append (PT.map (hW.comp PT.fst)
      (PT.pair (pt_reg 5 PT.snd) (PT.const true))) (PT.single (PT.pair (pt_reg 2 PT.snd)
        (pt_ebit (PT.const blank) PT.snd))))

theorem pt_setPair {r : α → ℕ} (hr : PT r) :
    PT fun a => [setA (r a) false, setA (r a) true] :=
  PT.cons (pt_setA hr (PT.const false)) (PT.single (pt_setA hr (PT.const true)))

theorem pt_prePh {u : α → List Unit} {w : α → List Sym} (blank : Sym) (hu : PT u) (hw : PT w) :
    PT fun a => prePh (u a).length (w a) blank := by
  unfold prePh initChoices
  refine PT.append (PT.append (PT.map (PT.rangeLength hu) (PT.single (pt_natA (pt_reg 0 PT.snd))))
    (PT.map (PT.append (PT.const [sB 0, sB 1]) (PT.map (PT.rangeLength hw) (pt_reg 5 PT.snd)))
      (pt_setPair PT.snd))) ?_
  refine (PT.flatMap (g := fun _ C => clausePhases C) (pt_phiInitB blank hu hw)
    (pt_clausePhases PT.snd)).of_eq fun a => ?_
  rw [phiInit_eq]

theorem pt_loopPh {u : α → List Unit} {d : α → TrD × HU} (hu : PT u) (hd : PT d) :
    PT fun a => loopPh (u a).length (d a) := by
  unfold loopPh stepChoices
  have hhl : PT fun z : α × (ℕ × Bool) => hl z.2 :=
    PT.pair (pt_reg 1 (PT.fst.comp PT.snd)) (PT.snd.comp PT.snd)
  have hq : PT fun a => (d a).1.1 := PT.fst.comp (PT.fst.comp hd)
  have hq' : PT fun a => (d a).1.2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.fst.comp hd)))
  have hpre : PT fun a => (d a).2.1.map hl := PT.map (PT.fst.comp (PT.snd.comp hd)) hhl
  have hpost : PT fun a => (d a).2.2.map hl := PT.map (PT.snd.comp (PT.snd.comp hd)) hhl
  have hcp : ∀ j : ℕ, PT fun a : α => [cpA (tB j) (lit (sB j)) true, cpA (tB j) (lit (sB j)) false] :=
    fun j => PT.cons (pt_cpA_lit (PT.const _) (PT.const _) (PT.const true))
      (PT.single (pt_cpA_lit (PT.const _) (PT.const _) (PT.const false)))
  refine PT.append (PT.append (PT.map (PT.append (PT.const [tB 0, tB 1]) (PT.map
    (PT.rangeLength hu) (pt_reg 4 PT.snd))) (pt_setPair PT.snd))
    (PT.flatMap (g := fun _ C => clausePhases C) (pt_phiStep hu (PT.fst.comp hd))
      (pt_clausePhases PT.snd))) ?_
  exact PT.cons (hcp 0) (PT.cons (hcp 1) (PT.single (PT.single (pt_updA hq hq' hpre hpost))))

theorem pt_flatMap_const {β γ : Type} [BEnc γ] (L : List β) (F : β → α → List γ)
    (hF : ∀ t ∈ L, PT (F t)) : PT fun a => L.flatMap fun t => F t a := by
  induction L with
  | nil => exact PT.nil
  | cons t L ih =>
    exact (PT.append (hF t (by simp)) (ih fun t' ht' => hF t' (by simp [ht']))).of_eq
      fun a => by simp

theorem range_filter_lt : ∀ (n j : ℕ), j ≤ n → (List.range n).filter (fun i => decide (i < j)) =
    List.range j
  | 0, j, h => by obtain rfl : j = 0 := by omega
                  rfl
  | n + 1, j, h => by
    rcases Nat.lt_or_ge j (n + 1) with h' | h'
    · rw [List.range_succ, List.filter_append, range_filter_lt n j (by omega)]
      simp; omega
    · obtain rfl : j = n + 1 := by omega
      exact List.filter_eq_self.2 fun a ha => by simpa using List.mem_range.1 ha

/-- Ranges below `n`, computed from a list of length `n`. -/
theorem pt_rangeBelow {u : α → List Unit} {j : α → ℕ} (hu : PT u) (hj : PT j) :
    PT fun a => (List.range (u a).length).filter fun i => decide (i < j a) :=
  PT.filter (p := fun a i => decide (i < j a)) (PT.rangeLength hu) (PT.lt PT.snd (hj.comp PT.fst))

theorem pt_hus {u : α → List Unit} (hu : PT u) (m : Move) : PT fun a => hus (u a).length m := by
  -- on `(a, j)` with `j < n`
  have hR : ∀ v : Bool, PT fun z : α × ℕ =>
      ((List.range (u z.1).length).filter fun i => decide (i < z.2)).map (·, v) :=
    fun v => PT.map (pt_rangeBelow (hu.comp PT.fst) PT.snd) (PT.pair PT.snd (PT.const v))
  cases m with
  | stay => exact PT.const _
  | right =>
    refine (PT.map (g := fun a j => ((((List.range (u a).length).filter fun i => decide (i < j)).map
      (·, true)) ++ [(j, false)], (((List.range (u a).length).filter fun i => decide (i < j)).map
        (·, false)) ++ [(j, true)])) (PT.rangeLength hu) (PT.pair (PT.append (hR true)
          (PT.single (PT.pair PT.snd (PT.const false)))) (PT.append (hR false)
            (PT.single (PT.pair PT.snd (PT.const true)))))).of_eq fun a => ?_
    simp only [hus]
    refine List.map_congr_left fun j hj => ?_
    rw [range_filter_lt _ _ (by simp at hj; omega)]; rfl
  | left =>
    refine (PT.append (PT.map (g := fun a j => ((((List.range (u a).length).filter
      fun i => decide (i < j)).map (·, false)) ++ [(j, true)], (((List.range (u a).length).filter
        fun i => decide (i < j)).map (·, true)) ++ [(j, false)])) (PT.rangeLength hu)
          (PT.pair (PT.append (hR false) (PT.single (PT.pair PT.snd (PT.const true))))
            (PT.append (hR true) (PT.single (PT.pair PT.snd (PT.const false))))))
      (PT.single (PT.pair (PT.map (g := fun (_ : α) (i : ℕ) => (i, false)) (PT.rangeLength hu)
        (PT.pair PT.snd (PT.const false))) (PT.nil (β := ℕ × Bool))))).of_eq fun a => ?_
    simp only [hus]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [range_filter_lt _ _ (by simp at hj; omega)]; rfl

variable {k : ℕ} (N : NTM (Fin k) Sym)

theorem pt_stepData {u : α → List Unit} (hu : PT u) : PT fun a => stepData N (u a).length :=
  pt_flatMap_const (trsList N) (fun t a => (hus (u a).length t.2.2.2.2).map fun μ =>
    ((t.1.val, t.2.1, t.2.2.1.val, t.2.2.2.1), μ))
    fun t _ => PT.map (pt_hus hu _) (PT.pair (PT.const _) PT.snd)

theorem pt_regs {u : α → List Unit} {w : α → List Sym} (hu : PT u) (hw : PT w) :
    PT fun a => regs (u a).length (w a) := by
  unfold regs
  have hR := PT.rangeLength hu
  exact PT.append (PT.append (PT.append (PT.append (PT.map hR (pt_reg 0 PT.snd))
    (PT.map hR (pt_reg 1 PT.snd))) (PT.const _)) (PT.map hR (pt_reg 4 PT.snd)))
    (PT.map (PT.rangeLength hw) (pt_reg 5 PT.snd))

/-- **The encoding is computed in polynomial time.** -/
theorem pt_tmDesc {u : α → List Unit} {w : α → List Sym} (hu : PT u) (hw : PT w) :
    PT fun a => tmDesc N (u a).length (w a) := by
  refine (pt_mkDesc (PT.append (PT.map (g := fun (_ : α) v => lit v false) (pt_regs hu hw)
    (pt_lit PT.snd (PT.const false))) (PT.const _)) (pt_prePh N.blank hu hw)
    (PT.map (g := fun a d => loopPh (u a).length d) (pt_stepData N hu)
      (pt_loopPh (hu.comp PT.fst) PT.snd)) (PT.const _)).of_eq
      fun a => (tmDesc_eq N _ _).symm

end

end DB

open DB HTN HTN.Syn HTN.Syn.PolyDom PTime

/-- **[DB25, Thm. 4/5]: regular (in the sense of [CB21]) fixed-method strong OD plan existence is
EXPSPACE-hard.** -/
theorem strongOD_REGtn_expspaceHard : HTN.Cx.Hard HTN.Cx.EXPSPACE (PlanExFM .strongOD FClass.REGtn) := by
  intro L hL
  obtain ⟨k, N, p, hN⟩ := hL
  obtain ⟨g, hg, hglen⟩ := HTN.Article.exists_pt_polyLen p
  have hpt : PT fun x : List Bool => tmDesc N (g x).length (x.map some) :=
    pt_tmDesc N hg (PT.map PT.id (PT.some PT.snd))
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hpt)), fun x => ?_⟩
  show L x ↔ PlanExFM .strongOD FClass.REGtn (enc (tmDesc N (g x).length (x.map some)))
  rw [hN x, tmDesc_mem_iff, hglen]

/-- Regular problems in the sense of Bercher et al. contain them. -/
theorem strongOD_REG_expspaceHard : HTN.Cx.Hard HTN.Cx.EXPSPACE (PlanExFM .strongOD FClass.REG) := by
  intro L hL
  obtain ⟨k, N, p, hN⟩ := hL
  obtain ⟨g, hg, hglen⟩ := HTN.Article.exists_pt_polyLen p
  have hpt : PT fun x : List Bool => tmDesc N (g x).length (x.map some) :=
    pt_tmDesc N hg (PT.map PT.id (PT.some PT.snd))
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hpt)), fun x => ?_⟩
  show L x ↔ PlanExFM .strongOD FClass.REG (enc (tmDesc N (g x).length (x.map some)))
  rw [hN x, planExFM_enc_iff, hglen, ← tmDesc_strongOD_iff N]
  exact ⟨fun h => ⟨tmDesc_valid N _ _, (tmDesc_REGtn N _ _).1, h⟩, fun h => h.2.2⟩



end FOND
