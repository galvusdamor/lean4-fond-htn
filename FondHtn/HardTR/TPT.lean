import FondHtn.HardTR.TInst
import FondHtn.AcycHard.InstPT
/-!
# CB22 Thm 5: the description is computed in polynomial time

Generic part: for a family `Xf : α → Spec S` of transducer parameters whose numeric data
(`e`, the special positions `P`, the number of intervals `no`, the codes of the interval symbols
and the bits of the interval bounds at the special positions) are computed in polynomial time,
and whose game (`F`, `acc`) is fixed, `a ↦ desc cS (Xf a) allS (opsOf …) ens σ₀` is computed in
polynomial time (`FOND.HardTR.TP.pt_desc`).
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TP

open TL TT TE TD TI HardMP HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime TOHard2

variable {α : Type} [BEnc α]

/-! ## Literals and codes -/

theorem pt_pos (b : Bool) {f : α → ℕ} (hf : PT f) : PT fun a => pos (f a) b := by
  cases b
  · exact PT.nil.of_eq fun a => rfl
  · exact (PT.single hf).of_eq fun a => rfl

theorem pt_neg (b : Bool) {f : α → ℕ} (hf : PT f) : PT fun a => neg (f a) b := by
  cases b
  · exact (PT.single hf).of_eq fun a => rfl
  · exact PT.nil.of_eq fun a => rfl

theorem pt_chk {c : α → Prop} [DecidablePred c] (hc : PT fun a => decide (c a)) :
    PT fun a => chk (c a) :=
  (PT.ite hc PT.nil (PT.const [fNo])).of_eq fun a => by
    unfold chk; by_cases h : c a <;> simp [h]

theorem pt_fPh_wb {k : α → ℕ} (hk : PT k) : PT fun a => fPh (.wb (k a)) :=
  PT.natPair (PT.const 0) (PT.natPair (PT.const 0) hk)

theorem pt_fPh_rb {k : α → ℕ} (hk : PT k) : PT fun a => fPh (.rb (k a)) :=
  PT.natPair (PT.const 0) (PT.natPair (PT.const 2) hk)

theorem pt_fC {k : α → ℕ} (hk : PT k) : PT fun a => fC (k a) := PT.natPair (PT.const 1) hk

theorem pt_fSg {k : α → ℕ} (hk : PT k) : PT fun a => fSg (k a) := PT.natPair (PT.const 3) hk

theorem pt_fGs_some {k : α → ℕ} (hk : PT k) : PT fun a => fGs (some (k a)) :=
  PT.natPair (PT.const 4) (PT.succ hk)

theorem pt_fSc {k : α → ℕ} (hk : PT k) : PT fun a => fSc (k a) := PT.natPair (PT.const 7) hk

theorem pt_fCs {k : α → ℕ} (hk : PT fun a => List.range (k a)) : PT fun a => (List.range (k a)).map fC :=
  PT.map (g := fun _ j => fC j) hk (pt_fC PT.snd)

/-! ## The simple actions -/

section Fam

variable {S : Type} (cS : S → ℕ) (allS : List S) {Xf : α → Spec S}

/-- The described action of an action of the machine. -/
noncomputable abbrev FA (X : Spec S) (a : Act Op (En S)) : FActDesc :=
  toFAct (nmA cS a) (aspec cS X allS a)

/-- `range k` for `k ≤ m`, computed from `range m`. -/
theorem pt_rangeLt {m k : α → ℕ} (hm : PT fun a => List.range (m a)) (hk : PT k) :
    PT fun a => (List.range (m a)).filter fun j => decide (j < k a) :=
  PT.filter hm (PT.lt PT.snd (hk.comp PT.fst))

theorem pt_A_wb (p b : Bool) (hm : PT fun a => List.range (mm (Xf a))) :
    PT fun q : α × ℕ => FA cS allS (Xf q.1) (.wb p q.2 b) := by
  have hmq : PT fun q : α × ℕ => mm (Xf q.1) := (pt_of_range hm).comp PT.fst
  have hnext : PT fun q : α × ℕ => fPh ((Xf q.1).mach.nextWb q.2) :=
    (PT.ite (PT.lt (PT.succ PT.snd) hmq) (pt_fPh_wb (PT.succ PT.snd)) (PT.const (fPh .rv))).of_eq
      fun q => by unfold Mach.nextWb; simp only [Spec.mach, mm]; split_ifs <;> rfl
  refine pt_toFAct (PT.natPair (PT.const 0) (PT.natPair (PT.const _) PT.snd)) ?_
  exact PT.pair (PT.append (PT.append (PT.append (PT.single (pt_fPh_wb PT.snd))
    (pt_pos p (PT.const _))) (pt_pos b (pt_fC PT.snd))) (pt_chk (PT.lt PT.snd hmq)))
    (PT.pair (PT.append (pt_neg p (PT.const _)) (pt_neg b (pt_fC PT.snd)))
      (PT.pair (PT.single (PT.pair (PT.single hnext) (PT.single (pt_fPh_wb PT.snd))))
        (PT.pair PT.nil PT.nil)))

theorem pt_A_rb (p b : Bool) : PT fun q : α × ℕ => FA cS allS (Xf q.1) (.rb p q.2 b) := by
  have hnext : PT fun q : α × ℕ => fPh (Mach.nextRb q.2) :=
    (PT.ite (PT.eq PT.snd (PT.const 0)) (PT.const (fPh .op)) (pt_fPh_rb (PT.pred PT.snd))).of_eq
      fun q => by unfold Mach.nextRb; split_ifs <;> rfl
  refine pt_toFAct (PT.natPair (PT.const 2) (PT.natPair (PT.const _) PT.snd)) ?_
  exact PT.pair (PT.append (PT.append (PT.single (pt_fPh_rb PT.snd))
    (pt_pos (!p) (PT.const _))) (pt_pos b (pt_fC PT.snd)))
    (PT.pair (PT.append (pt_neg (!p) (PT.const _)) (pt_neg b (pt_fC PT.snd)))
      (PT.pair (PT.single (PT.pair (PT.single hnext) (PT.single (pt_fPh_rb PT.snd))))
        (PT.pair PT.nil PT.nil)))

/-- The increment, with `range k` computed from `range m` (valid for `k < m`). -/
noncomputable def incA (X : Spec S) (p : Bool) (k : ℕ) : FActDesc :=
  toFAct (nmA cS (.inc p k))
    ([fPh .inc] ++ pos (fB 0) p ++ ((List.range (mm X)).filter fun j => decide (j < k)).map fC ++
        chk (k < mm X),
      neg (fB 0) p ++ [fC k],
      [([fPh (.wb 0), fC k], [fPh .inc] ++ ((List.range (mm X)).filter fun j => decide (j < k)).map fC)],
      [], [])

theorem incA_eq (X : Spec S) (p : Bool) {k : ℕ} (hk : k < mm X) :
    incA cS X p k = FA cS allS X (.inc p k) := by
  simp only [incA, FA, aspec, range_filter_lt hk.le]

theorem pt_A_inc (p : Bool) (hm : PT fun a => List.range (mm (Xf a))) :
    PT fun q : α × ℕ => incA cS (Xf q.1) p q.2 := by
  have hmq : PT fun q : α × ℕ => mm (Xf q.1) := (pt_of_range hm).comp PT.fst
  have hr := PT.map (g := fun _ j => fC j) (pt_rangeLt (hm.comp PT.fst) PT.snd) (pt_fC PT.snd)
  refine pt_toFAct (PT.natPair (PT.const 4) (PT.natPair (PT.const _) PT.snd)) ?_
  exact PT.pair (PT.append (PT.append (PT.append (PT.single (PT.const _)) (pt_pos p (PT.const _))) hr)
    (pt_chk (PT.lt PT.snd hmq)))
    (PT.pair (PT.append (pt_neg p (PT.const _)) (PT.single (pt_fC PT.snd)))
      (PT.pair (PT.single (PT.pair (PT.cons (PT.const _) (PT.single (pt_fC PT.snd)))
        (PT.append (PT.single (PT.const _)) hr))) (PT.pair PT.nil PT.nil)))

theorem pt_A_rv (p γ : Bool) (hm : PT fun a => List.range (mm (Xf a))) :
    PT fun a => FA cS allS (Xf a) (.rv p γ) := by
  refine pt_toFAct (PT.const _) ?_
  exact PT.pair (PT.append (PT.single (PT.const _)) (pt_pos (!p) (PT.const _)))
    (PT.pair (pt_neg (!p) (PT.const _)) (PT.pair (PT.single (PT.pair
      (PT.append (PT.single (pt_fPh_rb (PT.pred (pt_of_range hm)))) (pt_pos γ (PT.const _)))
      (PT.append (PT.single (PT.const _)) (pt_neg γ (PT.const _))))) (PT.pair PT.nil PT.nil)))

theorem pt_A_wrap (p : Bool) (hm : PT fun a => List.range (mm (Xf a))) :
    PT fun a => FA cS allS (Xf a) (.wrap p) := by
  refine pt_toFAct (PT.const _) ?_
  exact PT.pair (PT.append (PT.append (PT.single (PT.const _)) (pt_pos p (PT.const _))) (pt_fCs hm))
    (PT.pair (pt_neg p (PT.const _)) (PT.pair (PT.single (PT.pair (PT.single (PT.const _))
      (PT.append (PT.single (PT.const _)) (pt_fCs hm)))) (PT.pair PT.nil PT.nil)))

theorem pt_A_nrd (p : Bool) : PT fun a => FA cS allS (Xf a) (.nrd p) :=
  (PT.const (toFAct (nmA cS (.nrd p)) ([fPh .rv] ++ pos (fB 0) p ++ [fB 2], neg (fB 0) p,
    [([fPh .op], [fPh .rv, fB 1])], [], []))).of_eq fun _ => rfl

theorem pt_A_dr (p : Bool) : PT fun a => FA cS allS (Xf a) (.dr p) :=
  (PT.const (toFAct (nmA cS (.dr p)) ([fPh .drain], [], [([], [])], [], []))).of_eq fun _ => rfl

theorem pt_A_fin (hP : PT fun a => (Xf a).P) : PT fun a => FA cS allS (Xf a) .fin := by
  refine pt_toFAct (PT.const _) ?_
  exact PT.pair (PT.cons (PT.const _) (PT.cons (PT.const _) (PT.cons (pt_fSc (PT.length hP))
    (PT.single (PT.const _))))) (PT.pair (PT.const _) (PT.pair (PT.const _) (PT.pair PT.nil PT.nil)))

/-! ## The operations -/

theorem pt_A_op {β : Type} [BEnc β] (p : Bool) {Xq : β → Spec S} {oq : β → Op}
    (hs : PT fun q => opSpec cS (Xq q) (oq q)) (hc : PT fun q => codeOp (oq q)) :
    PT fun q => FA cS allS (Xq q) (.op p (oq q)) := by
  refine pt_toFAct (PT.natPair (PT.const 3) (PT.natPair (PT.const _) hc)) ?_
  exact PT.pair (PT.append (PT.append (PT.single (PT.const _)) (pt_pos p (PT.const _))) (PT.fst' hs))
    (PT.pair (PT.append (pt_neg p (PT.const _)) (PT.fst' (PT.snd' hs)))
      (PT.pair (PT.single (PT.pair (PT.append (PT.single (PT.const _)) (PT.fst' (PT.snd' (PT.snd' hs))))
        (PT.append (PT.single (PT.const _)) (PT.snd' (PT.snd' (PT.snd' hs)))))) (PT.pair PT.nil PT.nil)))

theorem pt_gsCodes (hno : PT fun a => List.range (Xf a).no) : PT fun a => gsCodes (Xf a) :=
  PT.cons (PT.const _) (PT.map (g := fun _ ℓ => fGs (some ℓ)) hno (pt_fGs_some PT.snd))

theorem pt_scCodes (hP : PT fun a => (Xf a).P) : PT fun a => scCodes (Xf a) := by
  have h : PT fun a => List.range ((Xf a).P.length + 1) :=
    (PT.rangeLength (PT.cons (PT.const 0) hP)).of_eq fun a => by simp
  exact PT.map (g := fun _ s => fSc s) h (pt_fSc PT.snd)

theorem pt_opS_tn (b w : Bool) : PT fun a => opSpec cS (Xf a) (.t none b w) :=
  (PT.const (pos (fB 1) b ++ pos (fB 3) (xor b w) ++ [],
    [fB 2, fC 0] ++ neg (fB 1) b ++ neg (fB 3) (xor b w) ++ [], [],
    (if b then [fB 3] else []) ++ [])).of_eq fun _ => rfl

theorem pt_opS_ts (b w : Bool) (hm : PT fun a => List.range (mm (Xf a)))
    (hno : PT fun a => List.range (Xf a).no) (hsg : PT fun q : α × ℕ => cS ((Xf q.1).sg q.2)) :
    PT fun q : α × ℕ => opSpec cS (Xf q.1) (.t (some q.2) b w) := by
  have hnoq : PT fun q : α × ℕ => (Xf q.1).no := (pt_of_range hno).comp PT.fst
  show PT fun q : α × ℕ => (pos (fB 1) b ++ pos (fB 3) (xor b w) ++
      (fSg (cS ((Xf q.1).sg q.2)) :: chk (q.2 < (Xf q.1).no)),
    [fB 2, fC 0] ++ neg (fB 1) b ++ neg (fB 3) (xor b w) ++ (List.range (mm (Xf q.1))).map fC,
    [fGs (some q.2)], (if b then [fB 3] else []) ++ gsCodes (Xf q.1))
  exact PT.pair (PT.append (PT.const _) (PT.cons (pt_fSg hsg) (pt_chk (PT.lt PT.snd hnoq))))
    (PT.pair (PT.append (PT.const _) (pt_fCs (hm.comp PT.fst)))
      (PT.pair (PT.single (pt_fGs_some PT.snd)) (PT.append (PT.const _) ((pt_gsCodes hno).comp PT.fst))))

theorem pt_opS_in (dec b w : Bool) : PT fun a => opSpec cS (Xf a) (.i dec b w none) :=
  (PT.const (pos (fB 1) b ++ [fC 0] ++ pos (fB 4) (xor b w) ++ pos (fB 5) dec ++ [],
    [fB 2] ++ neg (fB 1) b ++ neg (fB 4) (xor b w) ++ neg (fB 5) dec ++ [],
    (if w = false then [] else [fCl (if w then .gt else .lt)]) ++
      (if w = false then [] else [fCh (if w then .gt else .lt)]) ++ [],
    (if (if dec then !b else b) then [] else [fB 4]) ++ (if w then [fB 6] else []) ++
      (if w = false then [] else clCodes) ++ (if w = false then [] else chCodes) ++ [])).of_eq
    fun _ => rfl

theorem pt_opS_is (dec b w : Bool) (hm : PT fun a => List.range (mm (Xf a)))
    (hP : PT fun a => (Xf a).P)
    (hlo : PT fun q : α × (ℕ × ℕ) => (Xf q.1).kb (Xf q.1).lo (some q.2))
    (hhi : PT fun q : α × (ℕ × ℕ) => (Xf q.1).kb (Xf q.1).hi (some q.2)) :
    PT fun q : α × (ℕ × ℕ) => opSpec cS (Xf q.1) (.i dec b w (some q.2)) := by
  have hPq : PT fun q : α × (ℕ × ℕ) => (Xf q.1).P := hP.comp PT.fst
  have hmq : PT fun q : α × (ℕ × ℕ) => List.range (mm (Xf q.1)) := hm.comp PT.fst
  have hsp : PT fun q : α × (ℕ × ℕ) => spA (Xf q.1) q.2.2 :=
    (PT.affine 2 1 (PT.getI hPq (PT.snd' PT.snd))).of_eq fun q => by
      simp only [spA, ← List.getD_default_eq_getI]; rfl
  have hon : PT fun q : α × (ℕ × ℕ) => ((List.range (mm (Xf q.1))).filter
      fun j => (spA (Xf q.1) q.2.2).testBit j).map fC :=
    PT.map (g := fun _ j => fC j) (PT.filter hmq (pt_testBit (hsp.comp PT.fst) PT.snd)) (pt_fC PT.snd)
  have hoff : PT fun q : α × (ℕ × ℕ) => ((List.range (mm (Xf q.1))).filter
      fun j => !(spA (Xf q.1) q.2.2).testBit j).map fC :=
    PT.map (g := fun _ j => fC j) (PT.filter hmq (PT.not (pt_testBit (hsp.comp PT.fst) PT.snd)))
      (pt_fC PT.snd)
  have hl : PT fun q : α × (ℕ × ℕ) => decide (w = (Xf q.1).kb (Xf q.1).lo (some q.2)) :=
    PT.eq (PT.const w) hlo
  have hh : PT fun q : α × (ℕ × ℕ) => decide (w = (Xf q.1).kb (Xf q.1).hi (some q.2)) :=
    PT.eq (PT.const w) hhi
  show PT fun q : α × (ℕ × ℕ) =>
    (pos (fB 1) b ++ [fC 0] ++ pos (fB 4) (xor b w) ++ pos (fB 5) dec ++
        (fGs (some q.2.1) :: fSc q.2.2 :: chk (q.2.2 < (Xf q.1).P.length) ++
          ((List.range (mm (Xf q.1))).filter fun j => (spA (Xf q.1) q.2.2).testBit j).map fC),
      [fB 2] ++ neg (fB 1) b ++ neg (fB 4) (xor b w) ++ neg (fB 5) dec ++
        ((List.range (mm (Xf q.1))).filter fun j => !(spA (Xf q.1) q.2.2).testBit j).map fC,
      (if w = (Xf q.1).kb (Xf q.1).lo (some q.2) then [] else [fCl (if w then .gt else .lt)]) ++
        (if w = (Xf q.1).kb (Xf q.1).hi (some q.2) then [] else [fCh (if w then .gt else .lt)]) ++
        [fSc (q.2.2 + 1)],
      (if (if dec then !b else b) then [] else [fB 4]) ++ (if w then [fB 6] else []) ++
        (if w = (Xf q.1).kb (Xf q.1).lo (some q.2) then [] else clCodes) ++
        (if w = (Xf q.1).kb (Xf q.1).hi (some q.2) then [] else chCodes) ++ [fSc q.2.2])
  exact PT.pair (PT.append (PT.const _) (PT.cons (pt_fGs_some (PT.fst' PT.snd))
      (PT.cons (pt_fSc (PT.snd' PT.snd)) (PT.append (pt_chk (PT.lt (PT.snd' PT.snd) (PT.length hPq)))
        hon))))
    (PT.pair (PT.append (PT.const _) hoff)
      (PT.pair (PT.append (PT.append (PT.ite hl PT.nil (PT.const _)) (PT.ite hh PT.nil (PT.const _)))
        (PT.single (pt_fSc (PT.succ (PT.snd' PT.snd)))))
        (PT.append (PT.append (PT.append (PT.const _) (PT.ite hl PT.nil (PT.const _)))
          (PT.ite hh PT.nil (PT.const _))) (PT.single (pt_fSc (PT.snd' PT.snd))))))

theorem pt_opS_bt (w : Bool) (hm : PT fun a => List.range (mm (Xf a))) :
    PT fun a => opSpec cS (Xf a) (.bt w) := by
  have he : PT fun a => fC ((Xf a).e + 1) :=
    (pt_fC (PT.pred (pt_of_range hm))).of_eq fun a => by simp [mm]
  exact PT.pair (PT.append (PT.const _) (pt_pos (!w) he))
    (PT.pair (PT.append (PT.const _) (pt_neg (!w) he)) (PT.pair PT.nil PT.nil))

theorem pt_opS_bi (w : Bool) (hm : PT fun a => List.range (mm (Xf a))) :
    PT fun a => opSpec cS (Xf a) (.bi w) := by
  have he : PT fun a => fC ((Xf a).e + 1) :=
    (pt_fC (PT.pred (pt_of_range hm))).of_eq fun a => by simp [mm]
  show PT fun a => ([fB 2, fC 0], if w then [fC ((Xf a).e + 1)] else [], ([] : List ℕ), ([] : List ℕ))
  cases w
  · exact (PT.const (([fB 2, fC 0], [], [], []) : List ℕ × List ℕ × List ℕ × List ℕ)).of_eq fun _ => rfl
  · exact PT.pair (PT.const _) (PT.pair (PT.single he) (PT.const _))

/-- **Over all operations**: a list-valued function of the operations, computed in polynomial
time on each shape, is computed in polynomial time on the whole list `opsOf`. -/
theorem pt_ops {γ : Type} [BEnc γ] {G : α → Op → List γ}
    (hno : PT fun a => List.range (Xf a).no) (hP : PT fun a => (Xf a).P)
    (h1 : ∀ b w, PT fun a => G a (.t none b w))
    (h2 : ∀ b w, PT fun q : α × ℕ => G q.1 (.t (some q.2) b w))
    (h3 : ∀ dec b w, PT fun a => G a (.i dec b w none))
    (h4 : ∀ dec b w, PT fun q : α × (ℕ × ℕ) => G q.1 (.i dec b w (some q.2)))
    (h5 : ∀ w, PT fun a => G a (.bt w)) (h6 : ∀ w, PT fun a => G a (.bi w)) :
    PT fun a => (opsOf (Xf a).no (Xf a).P.length).flatMap (G a) := by
  have hB : ∀ {β : Type} [BEnc β] {H : β → Bool → Bool → List γ}, (∀ b w, PT fun x => H x b w) →
      PT fun x => [false, true].flatMap fun b => [false, true].flatMap fun w => H x b w :=
    fun h => pt_flatMap_const _ fun b _ => pt_flatMap_const _ fun w _ => h b w
  have hB3 : ∀ {β : Type} [BEnc β] {H : β → Bool → Bool → Bool → List γ},
      (∀ d b w, PT fun x => H x d b w) →
      PT fun x => [false, true].flatMap fun d => [false, true].flatMap fun b =>
        [false, true].flatMap fun w => H x d b w :=
    fun h => pt_flatMap_const _ fun d _ => pt_flatMap_const _ fun b _ => pt_flatMap_const _ fun w _ => h d b w
  have hL : PT fun q : α × ℕ => List.range (Xf q.1).P.length := (PT.rangeLength hP).comp PT.fst
  have e4 := PT.flatMap (g := fun (q : α × ℕ) (s : ℕ) => [false, true].flatMap fun d =>
      [false, true].flatMap fun b => [false, true].flatMap fun w => G q.1 (.i d b w (some (q.2, s))))
    hL (hB3 fun d b w => (h4 d b w).comp (PT.pair (PT.fst.comp PT.fst)
      (PT.pair (PT.snd.comp PT.fst) PT.snd)))
  have hE := PT.append (PT.append (PT.append (PT.append (hB h1)
    (PT.flatMap (g := fun a ℓ => [false, true].flatMap fun b => [false, true].flatMap fun w =>
      G a (.t (some ℓ) b w)) hno (hB h2)))
    (hB3 h3)) (PT.flatMap (g := fun a ℓ => (List.range (Xf a).P.length).flatMap fun s =>
      [false, true].flatMap fun d => [false, true].flatMap fun b => [false, true].flatMap fun w =>
        G a (.i d b w (some (ℓ, s)))) hno e4))
    (PT.append (PT.append (PT.append (h5 false) (h5 true)) (h6 false)) (h6 true))
  refine hE.of_eq fun a => ?_
  simp only [opsOf, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatMap_assoc,
    List.flatMap_map, List.map_cons, List.map_nil, List.append_nil, List.append_assoc,
    List.cons_append, List.nil_append]

/-! ## The round ends -/

/-- The outcomes of a round end (independent of the parameters). -/
def endOuts : En S → List (S × Bool × Bool)
  | .boot σ => [(σ, false, false)]
  | .norm z l c r => [(c, false, false), (r, true, false)] ++ (if z then [] else [(l, true, true)])

theorem endSpec_outs (X : Spec S) (e : En S) : (endSpec cS X e).2.2 = endOuts e := by
  cases e <;> rfl

theorem pt_rstEff (hno : PT fun a => List.range (Xf a).no) (hP : PT fun a => (Xf a).P)
    (σ : S) (cy dec : Bool) : PT fun a => rstEff cS (Xf a) allS σ cy dec :=
  PT.pair (PT.const _) (PT.append (PT.append (PT.append (PT.append (PT.append (PT.append (PT.const _)
    (pt_gsCodes hno)) (PT.const _)) (PT.const _)) (pt_scCodes hP)) (PT.const _)) (PT.const _))

theorem pt_A_rend (hno : PT fun a => List.range (Xf a).no) (hP : PT fun a => (Xf a).P)
    {F₀ : Option S → S → S → S} {acc₀ : Set S} (hF : ∀ a, (Xf a).F = F₀)
    (hacc : ∀ a, (Xf a).acc = acc₀) (p : Bool) (e : En S) :
    PT fun a => FA cS allS (Xf a) (.rend p e) := by
  have h1 : PT fun a => (endSpec cS (Xf a) e).1 := by
    cases e with
    | boot σ =>
      exact (PT.const ([fB 2] ++ chk (σ ∈ acc₀))).of_eq fun a => by simp only [endSpec, hacc]
    | norm z l c r =>
      exact (PT.const (pos (fB 6) z ++ [fSg (cS (F₀ (if z then none else some l) c r))])).of_eq
        fun a => by simp only [endSpec, hF]
  have h2 : PT fun a => (endSpec cS (Xf a) e).2.1 := by
    cases e with
    | boot σ => exact PT.nil.of_eq fun a => rfl
    | norm z l c r => exact (PT.const ([fB 2, fB 3, fB 4] ++ neg (fB 6) z)).of_eq fun a => rfl
  have h3 : PT fun a => (endSpec cS (Xf a) e).2.2.map fun q =>
      ([fPh (.wb 0)] ++ pos (fB 0) (!p) ++ (rstEff cS (Xf a) allS q.1 q.2.1 q.2.2).1,
        [fPh .fin] ++ neg (fB 0) (!p) ++ (rstEff cS (Xf a) allS q.1 q.2.1 q.2.2).2) := by
    refine (AcycHard.Sav.pt_map_const (endOuts e) (G := fun a q =>
      ([fPh (.wb 0)] ++ pos (fB 0) (!p) ++ (rstEff cS (Xf a) allS q.1 q.2.1 q.2.2).1,
        [fPh .fin] ++ neg (fB 0) (!p) ++ (rstEff cS (Xf a) allS q.1 q.2.1 q.2.2).2))
      fun q _ => ?_).of_eq fun a => by rw [endSpec_outs]
    exact PT.pair (PT.append (PT.const _) (PT.fst' (pt_rstEff cS allS hno hP _ _ _)))
      (PT.append (PT.const _) (PT.snd' (pt_rstEff cS allS hno hP _ _ _)))
  refine pt_toFAct (PT.const _) ?_
  exact PT.pair (PT.append (PT.const _) h1) (PT.pair (PT.append (PT.const _) h2)
    (PT.pair h3 (PT.pair PT.nil PT.nil)))

/-! ## All actions -/

/-- The parameters of the family, computed in polynomial time. -/
structure Hyp (Xf : α → Spec S) (F₀ : Option S → S → S → S) (acc₀ : Set S) : Prop where
  m : PT fun a => List.range (mm (Xf a))
  no : PT fun a => List.range (Xf a).no
  P : PT fun a => (Xf a).P
  sg : PT fun q : α × ℕ => cS ((Xf q.1).sg q.2)
  lo : PT fun q : α × (ℕ × ℕ) => (Xf q.1).kb (Xf q.1).lo (some q.2)
  hi : PT fun q : α × (ℕ × ℕ) => (Xf q.1).kb (Xf q.1).hi (some q.2)
  F : ∀ a, (Xf a).F = F₀
  acc : ∀ a, (Xf a).acc = acc₀

variable {cS} {F₀ : Option S → S → S → S} {acc₀ : Set S}

theorem pt_opsA (H : Hyp cS Xf F₀ acc₀) (p : Bool) :
    PT fun a => (opsOf (Xf a).no (Xf a).P.length).map fun o => FA cS allS (Xf a) (.op p o) := by
  refine (pt_ops (G := fun a o => [FA cS allS (Xf a) (.op p o)]) H.no H.P
    (fun b w => PT.single (pt_A_op cS allS p (pt_opS_tn cS b w) (PT.const _)))
    (fun b w => PT.single (pt_A_op cS allS p (pt_opS_ts cS b w (H.m) (H.no) H.sg)
      (PT.natPair (PT.const 0) (PT.natPair (PT.succ PT.snd) (PT.const _)))))
    (fun d b w => PT.single (pt_A_op cS allS p (pt_opS_in cS d b w) (PT.const _)))
    (fun d b w => PT.single (pt_A_op cS allS p (pt_opS_is cS d b w H.m H.P H.lo H.hi)
      (PT.natPair (PT.const 1) (PT.natPair (PT.const _)
        (PT.succ (PT.natPair (PT.fst' PT.snd) (PT.snd' PT.snd)))))))
    (fun w => PT.single (pt_A_op cS allS p (pt_opS_bt cS w H.m) (PT.const _)))
    (fun w => PT.single (pt_A_op cS allS p (pt_opS_bi cS w H.m) (PT.const _)))).of_eq
    fun a => List.map_eq_flatMap.symm

theorem pt_actsPA (H : Hyp cS Xf F₀ acc₀) (ens : List (En S)) (p : Bool) :
    PT fun a => (actsP (Xf a) (opsOf (Xf a).no (Xf a).P.length) ens p).map (FA cS allS (Xf a)) := by
  have hk : PT fun a => (List.range (mm (Xf a))).flatMap fun k =>
      [FA cS allS (Xf a) (.wb p k false), FA cS allS (Xf a) (.wb p k true),
        FA cS allS (Xf a) (.rb p k false), FA cS allS (Xf a) (.rb p k true), incA cS (Xf a) p k] :=
    PT.flatMap H.m (PT.cons (pt_A_wb cS allS p false H.m) (PT.cons (pt_A_wb cS allS p true H.m)
      (PT.cons (pt_A_rb cS allS p false) (PT.cons (pt_A_rb cS allS p true)
        (PT.single (pt_A_inc cS p H.m))))))
  have hE := PT.append (PT.append (PT.append hk (PT.cons (pt_A_rv cS allS p false H.m)
    (PT.cons (pt_A_rv cS allS p true H.m) (PT.cons (pt_A_wrap cS allS p H.m)
      (PT.cons (pt_A_nrd cS allS (Xf := Xf) p) (PT.single (pt_A_dr cS allS (Xf := Xf) p)))))))
    (pt_opsA allS H p))
    (AcycHard.Sav.pt_map_const ens fun e _ => pt_A_rend cS allS H.no H.P H.F H.acc p e)
  refine hE.of_eq fun a => ?_
  simp only [actsP, List.map_append, List.map_flatMap, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def]
  congr 3
  refine List.flatMap_congr fun k hk => ?_
  rw [incA_eq cS allS _ p (List.mem_range.1 hk)]

theorem pt_actsA (H : Hyp cS Xf F₀ acc₀) (ens : List (En S)) :
    PT fun a => ((TD.acts (Xf a) (opsOf (Xf a).no (Xf a).P.length) ens).map
      (FA cS allS (Xf a))).dedup := by
  refine PT.dedup ((PT.append (PT.append (pt_actsPA allS H ens true) (pt_actsPA allS H ens false))
    (PT.single (pt_A_fin cS allS H.P))).of_eq fun a => ?_)
  simp [TD.acts, List.map_append]

end Fam

end TP

end HardTR

end FOND
