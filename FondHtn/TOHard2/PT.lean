import FondHtn.TOHard2.Red
import FondHtn.HardMP.PT
/-!
# The description is computed in polynomial time

For a family of parameters `P : α → Par` whose fields are computed in polynomial time,
`FOND.TOHard2.pt_desc` shows that `a ↦ desc (P a)` is.  The digit types never need an encoding:
the automata are constant, so their transitions are unfolded (`FOND.TOHard2.pt_flatMap_const`).
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime HardMP

variable {α : Type} [BEnc α]

/-! ## Generic helpers -/

theorem pt_flatMap_const {β γ : Type} [BEnc γ] (L : List β) {G : α → β → List γ}
    (h : ∀ t ∈ L, PT fun a => G a t) : PT fun a => L.flatMap (G a) := by
  induction L with
  | nil => exact (PT.const []).of_eq fun a => by simp
  | cons t L ih =>
    simp only [List.flatMap_cons]
    exact PT.append (h t (by simp)) (ih fun t ht => h t (by simp [ht]))

theorem pt_ite_const {β : Type} [BEnc β] (c : Prop) [Decidable c] {f g : α → β} (hf : PT f) (hg : PT g) :
    PT fun a => if c then f a else g a := by
  by_cases h : c
  · exact hf.of_eq fun a => by simp [h]
  · exact hg.of_eq fun a => by simp [h]

theorem pt_testBit {e r : α → ℕ} (he : PT e) (hr : PT r) : PT fun a => (e a).testBit (r a) :=
  (PT.getI (PT.bits.comp he) hr).of_eq fun a => getI_bitsOfNat _ _

theorem pt_iN {t p : α → ℕ} (ht : PT t) (hp : PT p) : PT fun a => iN (t a) (p a) := PT.natPair ht hp

theorem pt_fChk {r : α → ℕ} (hr : PT r) : PT fun a => fChk (r a) := (PT.affine 2 8 hr).of_eq fun a => rfl
theorem pt_fCtr {r : α → ℕ} (hr : PT r) : PT fun a => fCtr (r a) := (PT.affine 2 9 hr).of_eq fun a => rfl

theorem pt_syms {p : α → List (ℕ × List ASpec)} (hp : PT p) : PT fun a => syms (p a) :=
  PT.map hp (PT.pair (PT.const false) (PT.fst.comp PT.snd))

theorem range_filter_lt : ∀ {b j : ℕ}, j ≤ b → (List.range b).filter (fun r => decide (r < j)) = List.range j := by
  intro b
  induction b with
  | zero => intro j hj; obtain rfl : j = 0 := by omega
            rfl
  | succ b ih =>
    intro j hj
    rcases Nat.lt_or_ge b j with h | h
    · obtain rfl : j = b + 1 := by omega
      rw [List.filter_eq_self.2 (fun r hr => by simp at hr; simp; omega)]
    · rw [List.range_succ, List.filter_append, ih h]
      simp; omega

theorem pt_of_range {b : α → ℕ} (hr : PT fun a => List.range (b a)) : PT b :=
  (PT.length hr).of_eq fun a => by simp

/-! ## Instructions -/

theorem pt_tst {alts : α → List (List ℕ × List ℕ)} (h : PT alts) : PT fun a => tst (alts a) :=
  PT.map h (PT.pair (PT.fst.comp PT.snd) (PT.pair (PT.snd.comp PT.snd) (PT.const (noeff, [], []))))

section B

variable {b : α → ℕ} (hr : PT fun a => List.range (b a))
include hr

theorem pt_eqLits {e : α → ℕ} (he : PT e) : PT fun a => eqLits (b a) (e a) := by
  unfold eqLits
  exact PT.pair (PT.map (PT.filter hr (pt_testBit (he.comp PT.fst) PT.snd)) (pt_fChk PT.snd))
    (PT.map (PT.filter hr (PT.not (pt_testBit (he.comp PT.fst) PT.snd))) (pt_fChk PT.snd))

theorem pt_neLits {e : α → ℕ} (he : PT e) : PT fun a => neLits (b a) (e a) := by
  unfold neLits
  exact PT.map hr (PT.ite (pt_testBit (he.comp PT.fst) PT.snd |>.of_eq fun _ => by simp)
    (PT.pair PT.nil (PT.single (pt_fChk PT.snd))) (PT.pair (PT.single (pt_fChk PT.snd)) PT.nil))

theorem pt_incI : PT fun a => incI (b a) := by
  -- the ranges below `j < b` are filters of the range below `b`
  have hg : PT fun a => (List.range (b a)).map (fun j =>
      ((((List.range (b a)).filter fun r => decide (r < j)).map fCtr, [fCtr j],
        [([fCtr j], ((List.range (b a)).filter fun r => decide (r < j)).map fCtr)], [], []) :
        ASpec)) := by
    have hf : PT fun q : α × ℕ => ((List.range (b q.1)).filter fun r => decide (r < q.2)).map fCtr :=
      PT.map (PT.filter (hr.comp PT.fst) (PT.lt PT.snd (PT.snd.comp PT.fst))) (pt_fCtr PT.snd)
    exact PT.map hr (PT.pair hf (PT.pair (PT.single (pt_fCtr PT.snd)) (PT.pair
      (PT.single (PT.pair (PT.single (pt_fCtr PT.snd)) hf)) (PT.const ([], [])))))
  have hlast : PT fun a => ((((List.range (b a)).map fCtr, [], [([0], (List.range (b a)).map fCtr)],
      [], []) : ASpec)) :=
    PT.pair (PT.map hr (pt_fCtr PT.snd)) (PT.pair PT.nil (PT.pair (PT.single (PT.pair (PT.const [0])
      (PT.map hr (pt_fCtr PT.snd)))) (PT.const ([], []))))
  refine (PT.pair (PT.const (iN 2 0)) (PT.append hg (PT.single hlast))).of_eq fun a => ?_
  unfold incI
  congr 2
  refine List.map_congr_left fun j hj => ?_
  rw [range_filter_lt (List.mem_range.1 hj).le]

theorem pt_cmps : PT fun a => (List.range (b a)).map cmpI := by
  unfold cmpI
  exact PT.map hr (PT.pair (pt_iN (PT.const 1) PT.snd) (PT.cons
    (PT.pair (PT.cons (pt_fCtr PT.snd) (PT.single (pt_fChk PT.snd))) (PT.const ([], noeff, [], [])))
    (PT.cons (PT.pair PT.nil (PT.pair (PT.cons (pt_fCtr PT.snd) (PT.single (pt_fChk PT.snd)))
      (PT.const (noeff, [], []))))
    (PT.cons (PT.pair (PT.single (pt_fCtr PT.snd)) (PT.pair (PT.single (pt_fChk PT.snd))
      (PT.const ([([], [1])], [], []))))
    (PT.single (PT.pair (PT.single (pt_fChk PT.snd)) (PT.pair (PT.single (pt_fCtr PT.snd))
      (PT.const ([([], [1])], [], [])))))))))

theorem pt_pickChks : PT fun a => (List.range (b a)).map pickChkI := by
  unfold pickChkI
  exact PT.map hr (PT.pair (pt_iN (PT.const 12) PT.snd) (PT.single (PT.pair PT.nil (PT.pair PT.nil
    (PT.pair (PT.cons (PT.pair (PT.single (pt_fChk PT.snd)) PT.nil)
      (PT.single (PT.pair PT.nil (PT.single (pt_fChk PT.snd))))) (PT.const ([], [])))))))

section CS

variable {cs : α → List (List ℕ)} (hcs : PT cs)
include hcs

theorem pt_actP_ce {k : α → ℕ} (hk : PT k) : PT fun a => actP (b a) (cs a) (.ce (k a)) := by
  simp only [actP, ceAI, ceBI]
  have hks : PT fun a => (cs a).getI (k a) := PT.getI hcs hk
  refine PT.cons (PT.pair (pt_iN (PT.const 7) hk) (pt_tst (PT.append (PT.const _) (PT.map hks
    (PT.pair (PT.cons (PT.const 1) (PT.cons (PT.const 3)
      (PT.fst.comp (pt_eqLits (hr.comp PT.fst) PT.snd))))
      (PT.snd.comp (pt_eqLits (hr.comp PT.fst) PT.snd))))))) ?_
  refine PT.map (PT.rangeLength hks) (PT.pair (pt_iN (PT.const 8) (PT.natPair (hk.comp PT.fst) PT.snd))
    (pt_tst (PT.append (PT.const _) (pt_neLits (hr.comp PT.fst) (PT.getI (hks.comp PT.fst) PT.snd)))))

theorem pt_actP_cw {k : α → ℕ} (hk : PT k) : PT fun a => actP (b a) (cs a) (.cw (k a)) := by
  simp only [actP, cwBI]
  have hks : PT fun a => (cs a).getI (k a) := PT.getI hcs hk
  refine PT.cons (PT.const _) ?_
  refine PT.map (PT.rangeLength hks) (PT.pair (pt_iN (PT.const 10) (PT.natPair (hk.comp PT.fst) PT.snd))
    (pt_tst (PT.cons (PT.const _) (pt_neLits (hr.comp PT.fst) (PT.getI (hks.comp PT.fst) PT.snd)))))

theorem pt_actP_cv {k : α → ℕ} (hk : PT k) : PT fun a => actP (b a) (cs a) (.cv (k a)) := by
  simp only [actP, cvI]
  have hks : PT fun a => (cs a).getI (k a) := PT.getI hcs hk
  exact PT.single (PT.pair (pt_iN (PT.const 11) hk) (pt_tst (PT.cons (PT.const _) (PT.map hks
    (PT.pair (PT.cons (PT.const 1) (PT.fst.comp (pt_eqLits (hr.comp PT.fst) PT.snd)))
      (PT.cons (PT.const 3) (PT.snd.comp (pt_eqLits (hr.comp PT.fst) PT.snd))))))))

theorem pt_actP (a : AT) : PT fun x => actP (b x) (cs x) a := by
  cases a with
  | ce k => exact pt_actP_ce hr hcs (PT.const k)
  | cw k => exact pt_actP_cw hr hcs (PT.const k)
  | cv k => exact pt_actP_cv hr hcs (PT.const k)
  | _ => exact PT.const _

theorem pt_block (a : AT) : PT fun x => block (b x) (cs x) a := by
  unfold block
  exact PT.append (PT.append (PT.cons (PT.const setEQ) (pt_cmps hr |>.of_eq fun _ => rfl))
    (pt_actP hr hcs a)) (PT.single (pt_incI hr))

end CS

end B

/-! ## Names -/

theorem pt_KN {x : α → ℕ} (hx : PT x) : PT fun a => KN (x a) := PT.natPair (PT.const 1) hx
theorem pt_subN {k j : α → ℕ} (hk : PT k) (hj : PT j) : PT fun a => subN (k a) (j a) :=
  PT.natPair (PT.const 2) (PT.natPair hk hj)
theorem pt_chN (A : Comp) {y : α → ℕ} (hy : PT y) : PT fun a => chN A (y a) :=
  PT.natPair (PT.const 4) (PT.natPair (PT.const _) hy)
theorem pt_lamN (A : Comp) {σ y : α → ℕ} (hσ : PT σ) (hy : PT y) : PT fun a => lamN A (σ a) (y a) :=
  PT.natPair (PT.const 5) (PT.natPair (PT.const _) (PT.natPair hσ hy))

/-! ## Methods -/

theorem pt_modeBody (m : ℕ) {x : α → ℕ} (hx : PT x) : PT fun a => modeBody m (x a) :=
  (PT.cons (PT.const _) (PT.single (PT.pair (PT.const true)
    (pt_chN _ (pt_chN (modeI m) (pt_KN hx)))))).of_eq fun a => (modeBody_eq m (x a)).symm


section Par

variable {P : α → Par} (hr : PT fun a => List.range (P a).b) (hcs : PT fun a => (P a).cs)
include hr hcs

theorem pt_lamMeths (A : Comp) {y : α → ℕ} (hy : PT y) : PT fun a => lamMeths (P a) A (y a) := by
  unfold lamMeths
  refine pt_flatMap_const _ fun t _ => PT.cons (PT.pair (pt_lamN A (PT.const _) hy)
    (PT.cons (PT.pair (PT.const true) (pt_lamN A (PT.const _) hy)) (pt_syms (pt_block hr hcs t.2.1))))
    (pt_ite_const _ (PT.single (PT.pair (pt_lamN A (PT.const _) hy)
      (PT.cons (PT.pair (PT.const true) hy) (pt_syms (pt_block hr hcs t.2.1))))) (PT.const _))

theorem pt_chMeths (A : Comp) {y : α → ℕ} (hy : PT y) : PT fun a => chMeths (P a) A (y a) := by
  unfold chMeths chBody
  exact PT.cons (PT.pair (pt_chN A hy) (PT.cons (PT.pair (PT.const true) (pt_lamN A (PT.const _) hy))
    (PT.const _))) (pt_lamMeths hr hcs A hy)

theorem pt_modeChMeths {x : α → ℕ} (hx : PT x) : PT fun a => modeChMeths (P a) (x a) := by
  unfold modeChMeths
  have hK := pt_KN hx
  exact PT.append (PT.append (PT.append (PT.append (PT.append
    (pt_chMeths hr hcs _ (pt_chN _ hK)) (pt_chMeths hr hcs _ hK))
    (pt_chMeths hr hcs _ (pt_chN _ hK))) (pt_chMeths hr hcs _ hK))
    (pt_chMeths hr hcs _ (pt_chN _ hK))) (pt_chMeths hr hcs _ hK)

theorem pt_pickChksP : PT fun a => pickChks (P a) := pt_pickChks hr

theorem pt_bbBody : PT fun a => bbBody (P a) := by
  unfold bbBody
  exact pt_syms (PT.append (pt_pickChksP hr hcs) (PT.const _))

theorem pt_prefBody {c : α → ℕ} (hc : PT c) : PT fun a => prefBody (P a) (c a) := by
  unfold prefBody
  exact pt_syms (PT.append (PT.append (pt_pickChksP hr hcs) (PT.const _))
    (pt_actP_ce hr hcs (PT.add (PT.const 2) hc)))

section Fields

variable (hmid : PT fun a => (P a).mid) (hlft : PT fun a => (P a).lft) (hrgt : PT fun a => (P a).rgt)
  (hacc : PT fun a => (P a).acc) (hbase : PT fun a => (P a).baseU)
  (htrue : PT fun a => (P a).codeTrue) (hnone : PT fun a => (P a).codeNone)
include hmid hlft hrgt hacc hbase htrue hnone

theorem pt_predCodes : PT fun a => predCodes (P a) := by
  unfold predCodes
  exact PT.append (PT.append
    (PT.flatMap hmid (PT.cons (PT.fst.comp (PT.snd.comp PT.snd)) (PT.cons
      (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))) (PT.single (PT.snd.comp (PT.snd.comp
        (PT.snd.comp PT.snd)))))))
    (PT.flatMap hlft (PT.cons (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.single (PT.snd.comp (PT.snd.comp PT.snd))))))
    (PT.flatMap hrgt (PT.cons (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.single (PT.snd.comp (PT.snd.comp PT.snd)))))

theorem pt_allChMeths : PT fun a => allChMeths (P a) := by
  unfold allChMeths
  have hbb : PT fun _ : α => bbN := PT.const _
  refine PT.append (PT.append (PT.flatMap (pt_predCodes hr hcs hmid hlft hrgt hacc hbase htrue hnone)
    (pt_modeChMeths (hr.comp PT.fst) (hcs.comp PT.fst) PT.snd)) ?_) ?_
  · exact PT.append (PT.append (PT.append (pt_chMeths hr hcs _ (pt_chN _ hbb)) (pt_chMeths hr hcs _ hbb))
      (pt_chMeths hr hcs _ (pt_chN _ hbb))) (pt_chMeths hr hcs _ hbb)
  · exact PT.flatMap hacc (PT.append
      (pt_chMeths (hr.comp PT.fst) (hcs.comp PT.fst) _ (pt_chN _ (pt_KN PT.snd)))
      (pt_chMeths (hr.comp PT.fst) (hcs.comp PT.fst) _ (pt_KN PT.snd)))

theorem pt_rootMeths : PT fun a => rootMeths (P a) := by
  unfold rootMeths
  exact PT.map hacc (PT.pair (PT.const _) (PT.cons (PT.pair (PT.const true)
    (pt_chN _ (pt_chN _ (pt_KN PT.snd)))) (PT.const _)))

theorem pt_kMeths : PT fun a => kMeths (P a) := by
  unfold kMeths
  refine PT.append (PT.append (PT.append (PT.append ?_ ?_) ?_) ?_) ?_
  · exact PT.map (PT.rangeLength hmid) (PT.pair (pt_KN (PT.fst.comp (PT.getI (hmid.comp PT.fst) PT.snd)))
      (PT.cons (PT.const _) (PT.single (PT.pair (PT.const true) (pt_subN (PT.const 0) PT.snd)))))
  · exact PT.map (PT.rangeLength hlft) (PT.pair (pt_KN (PT.fst.comp (PT.getI (hlft.comp PT.fst) PT.snd)))
      (PT.cons (PT.const _) (PT.single (PT.pair (PT.const true) (pt_subN (PT.const 1) PT.snd)))))
  · exact PT.map (PT.rangeLength hrgt) (PT.pair (pt_KN (PT.fst.comp (PT.getI (hrgt.comp PT.fst) PT.snd)))
      (PT.cons (PT.const _) (PT.single (PT.pair (PT.const true) (pt_subN (PT.const 2) PT.snd)))))
  · exact PT.map (PT.rangeLength hbase) (PT.pair (pt_KN (PT.getI (hbase.comp PT.fst) PT.snd))
      (pt_prefBody (hr.comp PT.fst) (hcs.comp PT.fst) PT.snd))
  · exact PT.cons (PT.pair (pt_KN htrue) (PT.const _)) (PT.single (PT.pair (pt_KN hnone) (PT.const _)))

theorem pt_subMeths : PT fun a => subMeths (P a) := by
  unfold subMeths
  have hq : ∀ {β : Type} [BEnc β] [Inhabited β] {L : α → List β}, PT L →
      PT fun q : α × ℕ => (L q.1).getI q.2 := fun hL => PT.getI (hL.comp PT.fst) PT.snd
  refine PT.append (PT.append ?_ ?_) ?_
  · have h := hq hmid
    exact PT.flatMap (PT.rangeLength hmid) (PT.cons (PT.pair (pt_subN (PT.const 0) PT.snd)
      (pt_modeBody 0 (PT.fst.comp (PT.snd.comp h)))) (PT.cons (PT.pair (pt_subN (PT.const 0) PT.snd)
      (pt_modeBody 1 (PT.fst.comp (PT.snd.comp (PT.snd.comp h))))) (PT.single (PT.pair
        (pt_subN (PT.const 0) PT.snd) (pt_modeBody 2 (PT.snd.comp (PT.snd.comp (PT.snd.comp h))))))))
  · have h := hq hlft
    exact PT.flatMap (PT.rangeLength hlft) (PT.cons (PT.pair (pt_subN (PT.const 1) PT.snd)
      (PT.append (pt_modeBody 1 (PT.fst.comp (PT.snd.comp h))) (PT.const _)))
      (PT.single (PT.pair (pt_subN (PT.const 1) PT.snd)
      (PT.append (pt_modeBody 2 (PT.snd.comp (PT.snd.comp h))) (PT.const _)))))
  · have h := hq hrgt
    exact PT.flatMap (PT.rangeLength hrgt) (PT.cons (PT.pair (pt_subN (PT.const 2) PT.snd)
      (PT.append (pt_modeBody 0 (PT.fst.comp (PT.snd.comp h))) (PT.const _)))
      (PT.single (PT.pair (pt_subN (PT.const 2) PT.snd)
      (PT.append (pt_modeBody 1 (PT.snd.comp (PT.snd.comp h))) (PT.const _)))))

theorem pt_meths : PT fun a => meths (P a) := by
  unfold meths
  exact PT.append (PT.append (PT.append (PT.append
    (pt_rootMeths hr hcs hmid hlft hrgt hacc hbase htrue hnone)
    (pt_kMeths hr hcs hmid hlft hrgt hacc hbase htrue hnone))
    (pt_subMeths hr hcs hmid hlft hrgt hacc hbase htrue hnone))
    (PT.single (PT.pair (PT.const _) (pt_bbBody hr hcs))))
    (pt_allChMeths hr hcs hmid hlft hrgt hacc hbase htrue hnone)

end Fields

theorem pt_insRaw : PT fun a => insRaw (P a) := by
  unfold insRaw
  refine PT.append (PT.append (PT.append (PT.cons (PT.const _) (PT.cons (pt_incI hr) (PT.const _)))
    (pt_cmps hr)) (pt_pickChksP hr hcs)) ?_
  exact PT.flatMap (PT.rangeLength hcs) (PT.append (PT.append
    (pt_actP_ce (hr.comp PT.fst) (hcs.comp PT.fst) PT.snd)
    (pt_actP_cw (hr.comp PT.fst) (hcs.comp PT.fst) PT.snd))
    (pt_actP_cv (hr.comp PT.fst) (hcs.comp PT.fst) PT.snd))

end Par

/-! ## The compiled description -/

theorem pt_symL {q : α → Bool × ℕ} (hq : PT q) : PT fun a => symL (q a) :=
  (PT.pair (PT.const true) (PT.add (PT.affine 2 0 (PT.snd.comp hq))
    (PT.cond (PT.fst.comp hq) (PT.const 1) (PT.const 0)))).of_eq fun a => by
      simp only [symL]; cases (q a).1 <;> simp

theorem pt_compile {G : α → Gram} (hI : PT fun a => (G a).insL) (hM : PT fun a => (G a).methL)
    (init : List ℕ) (root : List (Bool × ℕ)) : PT fun a => compile (G a) init root := by
  unfold compile actsG insMeths ntMeths
  refine PT.pair (PT.pair ?_ (PT.append ?_ ?_)) (PT.const _)
  · exact PT.flatMap hI (PT.map (PT.rangeLength (PT.snd.comp PT.snd))
      (pt_toFAct (PT.natPair (PT.fst.comp (PT.snd.comp PT.fst)) PT.snd)
        (PT.getI (PT.snd.comp (PT.snd.comp PT.fst)) PT.snd)))
  · exact PT.flatMap hI (PT.map (PT.rangeLength (PT.snd.comp PT.snd))
      (HardMP.pt_meth (PT.affine 2 0 (PT.fst.comp (PT.snd.comp PT.fst)) |>.of_eq fun _ => by ring)
        (PT.single (PT.pair (PT.const false) (PT.natPair (PT.fst.comp (PT.snd.comp PT.fst)) PT.snd)))))
  · exact PT.map hM (HardMP.pt_meth (PT.affine 2 1 (PT.fst.comp PT.snd))
      (PT.map (PT.snd.comp PT.snd) (pt_symL PT.snd)))

/-- **The description is computed in polynomial time.** -/
theorem pt_desc {P : α → Par} (hr : PT fun a => List.range (P a).b) (hcs : PT fun a => (P a).cs)
    (hmid : PT fun a => (P a).mid) (hlft : PT fun a => (P a).lft) (hrgt : PT fun a => (P a).rgt)
    (hacc : PT fun a => (P a).acc) (hbase : PT fun a => (P a).baseU)
    (htrue : PT fun a => (P a).codeTrue) (hnone : PT fun a => (P a).codeNone) :
    PT fun a => desc (P a) := by
  unfold desc
  refine pt_compile ?_ ?_ _ _
  · exact (@PT.dedup _ _ _ _ decEqInsP _ (pt_insRaw hr hcs)).of_eq fun a => (gram_insL (P a)).symm
  · exact (pt_meths hr hcs hmid hlft hrgt hacc hbase htrue hnone).of_eq fun a => (gram_methL (P a)).symm

end TOHard2

end FOND
