import HtnComplexity.Article.TOHardDesc
import HtnComplexity.PT.DivMod
/-!
# The tableau-checking problem is computed in polynomial time

`HTN.Article.pt_tabDesc`: the description `HTN.Article.TabData.desc` is a polynomial-time function
of its data, when the number of bits `B` and the prefix length `c₁` are given in unary (as the
lengths of lists).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom PTime

variable {α : Type} [BEnc α]

theorem pt_seqTn {f : α → List (Bool × ℕ)} (hf : PT f) : PT fun a => seqTn (f a) := by
  unfold seqTn
  have hR := PT.rangeLength hf
  refine PT.pair hR (PT.pair ?_ ?_)
  · exact PT.flatMap hR (PT.map (PT.filter (hR.comp PT.fst) (PT.lt (PT.snd.comp PT.fst) PT.snd))
      (PT.pair (PT.snd.comp PT.fst) PT.snd))
  · exact PT.map hR (PT.pair PT.snd (PT.getI (hf.comp PT.fst) PT.snd))

theorem pt_meth {c : α → ℕ} {b : α → List (Bool × ℕ)} (hc : PT c) (hb : PT b) :
    PT fun a => meth (c a) (b a) :=
  PT.pair hc (pt_seqTn hb)

theorem pt_aN (k : ℕ) {p : α → ℕ} (hp : PT p) : PT fun a => aN k (p a) :=
  (PT.affine 16 k hp).of_eq fun a => by unfold aN; ring

theorem pt_cN (k : ℕ) {p : α → ℕ} (hp : PT p) : PT fun a => cN k (p a) :=
  (PT.affine 8 k hp).of_eq fun a => by unfold cN; ring

theorem pt_tF {p : α → ℕ} (hp : PT p) : PT fun a => tF (p a) :=
  (PT.affine 2 0 hp).of_eq fun a => by unfold tF; ring

theorem pt_iF {p : α → ℕ} (hp : PT p) : PT fun a => iF (p a) :=
  (PT.affine 2 1 hp).of_eq fun a => by unfold iF; ring

theorem pt_bit {c m : α → ℕ} (hc : PT c) (hm : PT m) : PT fun a => bit (c a) (m a) :=
  PT.getI (PT.bits.comp hc) hm

section Acts

variable {L : α → List Unit} (hL : PT L)
include hL

theorem pt_eqPos {c : α → ℕ} (hc : PT c) : PT fun a => eqPos (L a).length (c a) :=
  PT.map (PT.filter (PT.rangeLength hL) (pt_bit (hc.comp PT.fst) PT.snd)) (pt_iF PT.snd)

theorem pt_eqNeg {c : α → ℕ} (hc : PT c) : PT fun a => eqNeg (L a).length (c a) :=
  PT.map (PT.filter (PT.rangeLength hL) (PT.not (pt_bit (hc.comp PT.fst) PT.snd))) (pt_iF PT.snd)

theorem pt_abPos {c j : α → ℕ} (hc : PT c) (hj : PT j) : PT fun a => abPos (L a).length (c a) (j a) :=
  PT.map (PT.filter (PT.rangeLength hL) (PT.and (PT.lt (hj.comp PT.fst) PT.snd)
    (pt_bit (hc.comp PT.fst) PT.snd))) (pt_iF PT.snd)

theorem pt_abNeg {c j : α → ℕ} (hc : PT c) (hj : PT j) : PT fun a => abNeg (L a).length (c a) (j a) :=
  PT.map (PT.filter (PT.rangeLength hL) (PT.and (PT.lt (hj.comp PT.fst) PT.snd)
    (PT.not (pt_bit (hc.comp PT.fst) PT.snd)))) (pt_iF PT.snd)

theorem pt_tabActOf {c₁ c₂ n : α → ℕ} (hc₁ : PT c₁) (hc₂ : PT c₂) (hn : PT n) :
    PT fun a => actOf (L a).length (c₁ a) (c₂ a) (n a) := by
  have hm : PT fun a => n a % 16 := PT.modC hn (by norm_num)
  have hp : PT fun a => n a / 16 := PT.divC hn (by norm_num)
  have h0 : PT fun _ : α => ([] : List ℕ) := PT.const []
  unfold actOf
  refine PT.ite (PT.eq hm (PT.const 0)) (PT.pair hn (PT.pair h0 (PT.pair (PT.single hp)
    (PT.pair (PT.single hp) h0)))) ?_
  refine PT.ite (PT.eq hm (PT.const 1)) (PT.pair hn (PT.pair (PT.single hp) (PT.pair h0
    (PT.pair h0 (PT.single hp))))) ?_
  refine PT.ite (PT.eq hm (PT.const 3)) (PT.pair hn (PT.pair (pt_eqPos hL hp) (PT.pair
    (pt_eqNeg hL hp) (PT.pair h0 h0)))) ?_
  refine PT.ite (PT.eq hm (PT.const 4)) (PT.pair hn (PT.pair h0 (PT.pair
    (PT.map (PT.rangeLength hL) (pt_tF PT.snd)) (PT.pair h0 h0)))) ?_
  refine PT.ite (PT.eq hm (PT.const 5)) (PT.pair hn (PT.pair (PT.cons (pt_iF hp)
    (pt_abPos hL hc₁ hp)) (PT.pair (pt_abNeg hL hc₁ hp) (PT.pair h0 h0)))) ?_
  refine PT.ite (PT.eq hm (PT.const 6)) (PT.pair hn (PT.pair (PT.cons (pt_iF hp)
    (pt_abPos hL hc₂ hp)) (PT.pair (pt_abNeg hL hc₂ hp) (PT.pair h0 h0)))) ?_
  refine PT.ite (PT.eq hm (PT.const 7)) (PT.pair hn (PT.pair (pt_abPos hL hc₂ hp) (PT.pair
    (PT.cons (pt_iF hp) (pt_abNeg hL hc₂ hp)) (PT.pair h0 h0)))) ?_
  exact PT.pair hn (PT.pair h0 (PT.pair h0 (PT.pair h0 h0)))

theorem pt_actNames {L₁ : α → List Unit} (hL₁ : PT L₁) {c₂ mx : α → ℕ} (hc₂ : PT c₂) (hmx : PT mx) :
    PT fun a => actNames (L a).length (L₁ a).length (c₂ a) (mx a) := by
  unfold actNames
  have hR2 : PT fun a => List.range (2 * (L a).length) :=
    (PT.rangeLength (PT.append hL hL)).of_eq fun a => by simp [two_mul]
  refine PT.append (PT.append (PT.append ?_ (PT.const _)) ?_) ?_
  · exact PT.flatMap hR2 (PT.cons (pt_aN 0 PT.snd) (PT.single (pt_aN 1 PT.snd)))
  · exact PT.map (PT.append (PT.rangeLength hL₁) (PT.cons (PT.length hL₁) (PT.cons hc₂
      (PT.single hmx)))) (pt_aN 3 PT.snd)
  · exact PT.flatMap (PT.rangeLength hL) (PT.cons (pt_aN 5 PT.snd) (PT.cons (pt_aN 6 PT.snd)
      (PT.single (pt_aN 7 PT.snd))))

theorem pt_acts {L₁ : α → List Unit} (hL₁ : PT L₁) {c₂ mx : α → ℕ} (hc₂ : PT c₂) (hmx : PT mx) :
    PT fun a => acts (L a).length (L₁ a).length (c₂ a) (mx a) :=
  PT.map (PT.dedup (pt_actNames hL hL₁ hc₂ hmx))
    (pt_tabActOf (L := fun q : α × ℕ => L q.1) (hL.comp PT.fst) ((PT.length hL₁).comp PT.fst)
      (hc₂.comp PT.fst) PT.snd)

end Acts

section Meths

variable {L : α → List Unit} (hL : PT L)
include hL

theorem pt_ctrMethods : PT fun a => ctrMethods (L a).length := by
  unfold ctrMethods
  have hj : PT fun q : α × ℕ => q.2 := PT.snd
  have hj1 : PT fun q : α × ℕ => q.2 + 1 := PT.succ hj
  have lab : ∀ {b : Bool} {f : α × ℕ → ℕ}, PT f → PT fun q => (b, f q) := fun hf =>
    PT.pair (PT.const _) hf
  refine PT.flatMap (PT.rangeLength hL) ?_
  refine PT.cons (pt_meth (pt_cN 0 hj) (PT.single (lab (pt_aN 0 (pt_tF hj))))) ?_
  refine PT.cons (pt_meth (pt_cN 0 hj) (PT.cons (lab (pt_aN 1 (pt_tF hj)))
    (PT.single (lab (pt_cN 0 hj1))))) ?_
  refine PT.cons (pt_meth (pt_cN 1 hj) (PT.single (lab (pt_aN 1 (pt_tF hj))))) ?_
  refine PT.cons (pt_meth (pt_cN 1 hj) (PT.cons (lab (pt_aN 0 (pt_tF hj)))
    (PT.single (lab (pt_cN 1 hj1))))) ?_
  refine PT.cons (pt_meth (pt_cN 2 hj) (PT.single (lab (pt_aN 0 (pt_iF hj))))) ?_
  refine PT.cons (pt_meth (pt_cN 2 hj) (PT.cons (lab (pt_aN 1 (pt_iF hj)))
    (PT.single (lab (pt_cN 2 hj1))))) ?_
  refine PT.cons (pt_meth (pt_cN 3 hj) (PT.single (lab (pt_aN 1 (pt_iF hj))))) ?_
  refine PT.cons (pt_meth (pt_cN 3 hj) (PT.cons (lab (pt_aN 0 (pt_iF hj)))
    (PT.single (lab (pt_cN 3 hj1))))) ?_
  refine PT.cons (pt_meth (pt_cN 4 hj) (PT.single (lab (PT.const noopN)))) ?_
  exact PT.single (pt_meth (pt_cN 4 hj) (PT.single (lab (pt_aN 0 (pt_iF hj)))))

theorem pt_geNames {c : α → ℕ} (hc : PT c) (k : ℕ) :
    PT fun a => geNames (L a).length (c a) (aN k) :=
  PT.cons (pt_aN 3 hc) (PT.map (PT.filter (PT.rangeLength hL) (PT.not (pt_bit (hc.comp PT.fst)
    PT.snd))) (pt_aN k PT.snd))

theorem pt_ltNames {c : α → ℕ} (hc : PT c) : PT fun a => ltNames (L a).length (c a) :=
  PT.map (PT.filter (PT.rangeLength hL) (pt_bit (hc.comp PT.fst) PT.snd)) (pt_aN 7 PT.snd)

theorem pt_rootBody {acc : α → ℕ} (ha : PT acc) : PT fun x => rootBody (L x).length (acc x) :=
  PT.append (PT.map (PT.rangeLength hL) (PT.pair (PT.const true) (pt_cN 4 PT.snd)))
    (PT.single (PT.pair (PT.const true) (pt_cN 5 ha)))

end Meths

theorem pt_stepMethods {mx : α → ℕ} {mid : α → List (ℕ × ℕ × ℕ × ℕ)} {lft rgt : α → List (ℕ × ℕ × ℕ)}
    (hmx : PT mx) (hmid : PT mid) (hlft : PT lft) (hrgt : PT rgt) :
    PT fun a => stepMethods (mx a) (mid a) (lft a) (rgt a) := by
  unfold stepMethods
  have lab : ∀ {β : Type} [BEnc β] {b : Bool} {f : β → ℕ}, PT f → PT fun q => (b, f q) :=
    fun hf => PT.pair (PT.const _) hf
  refine PT.append (PT.append ?_ ?_) ?_
  · refine PT.map hmid (pt_meth (pt_cN 5 (PT.fst.comp PT.snd)) ?_)
    unfold midBody
    have hq := PT.snd (α := α) (β := ℕ × ℕ × ℕ × ℕ)
    exact PT.cons (PT.const _) (PT.cons (PT.const _) (PT.cons (lab (pt_cN 5 (PT.fst' (PT.snd' hq))))
      (PT.cons (PT.const _) (PT.cons (lab (pt_cN 5 (PT.fst' (PT.snd' (PT.snd' hq)))))
        (PT.cons (PT.const _) (PT.cons (lab (pt_cN 5 (PT.snd' (PT.snd' (PT.snd' hq)))))
          (PT.cons (PT.const _) (PT.single (PT.const _)))))))))
  · refine PT.map hlft (pt_meth (pt_cN 5 (PT.fst.comp PT.snd)) ?_)
    unfold lftBody
    have hq := PT.snd (α := α) (β := ℕ × ℕ × ℕ)
    exact PT.cons (PT.const _) (PT.cons (PT.const _) (PT.cons (lab (pt_cN 5 (PT.fst' (PT.snd' hq))))
      (PT.cons (PT.const _) (PT.cons (lab (pt_cN 5 (PT.snd' (PT.snd' hq))))
        (PT.cons (PT.const _) (PT.single (PT.const _)))))))
  · refine PT.map hrgt (pt_meth (pt_cN 5 (PT.fst.comp PT.snd)) ?_)
    unfold rgtBody
    have hq := PT.snd (α := α) (β := ℕ × ℕ × ℕ)
    exact PT.cons (lab (pt_aN 3 (hmx.comp PT.fst))) (PT.cons (PT.const _) (PT.cons (PT.const _)
      (PT.cons (lab (pt_cN 5 (PT.fst' (PT.snd' hq)))) (PT.cons (PT.const _)
        (PT.cons (lab (pt_cN 5 (PT.snd' (PT.snd' hq)))) (PT.single (PT.const _)))))))

/-- **The description is computed in polynomial time from its data.** -/
theorem pt_tabDesc {L L₁ : α → List Unit} {c₂ mx codeTrue codeNone : α → ℕ}
    {baseU acc : α → List ℕ} {mid : α → List (ℕ × ℕ × ℕ × ℕ)} {lft rgt : α → List (ℕ × ℕ × ℕ)}
    (hL : PT L) (hL₁ : PT L₁) (hc₂ : PT c₂) (hmx : PT mx) (hT : PT codeTrue) (hN : PT codeNone)
    (hb : PT baseU) (hacc : PT acc) (hmid : PT mid) (hlft : PT lft) (hrgt : PT rgt) :
    PT fun a => (TabData.mk (L a).length (L₁ a).length (c₂ a) (baseU a) (codeTrue a) (codeNone a)
      (mid a) (lft a) (rgt a) (acc a) (mx a)).desc := by
  unfold TabData.desc TabData.methods
  simp only
  have lab : ∀ {β : Type} [BEnc β] {b : Bool} {f : β → ℕ}, PT f → PT fun q => (b, f q) :=
    fun hf => PT.pair (PT.const _) hf
  refine PT.pair (PT.pair (pt_acts hL hL₁ hc₂ hmx) ?_) (PT.pair (PT.map (PT.rangeLength hL)
    (pt_tF PT.snd)) (PT.pair (PT.const _) (PT.pair (PT.const _) (PT.const _))))
  refine PT.append (PT.append (PT.append (pt_ctrMethods hL) (pt_stepMethods hmx hmid hlft hrgt))
    ?_) ?_
  · unfold baseMethods
    refine PT.append (PT.append ?_ ?_) ?_
    · exact PT.map (PT.rangeLength hL₁) (pt_meth (pt_cN 5 (PT.getI (hb.comp PT.fst) PT.snd))
        (PT.cons (PT.const _) (PT.single (lab (pt_aN 3 PT.snd)))))
    · refine PT.flatMap (pt_geNames hL (PT.length hL₁) 5) ?_
      exact PT.map (pt_ltNames hL hc₂ |>.comp PT.fst) (pt_meth (pt_cN 5 (hT.comp (PT.fst.comp PT.fst)))
        (PT.cons (PT.const _) (PT.cons (lab (PT.snd.comp PT.fst)) (PT.single (lab PT.snd)))))
    · exact PT.map (pt_geNames hL hc₂ 6) (pt_meth (pt_cN 5 (hN.comp PT.fst))
        (PT.cons (PT.const _) (PT.single (lab PT.snd))))
  · unfold rootMethods
    exact PT.map hacc (pt_meth (PT.const _) (pt_rootBody (L := fun q : α × ℕ => L q.1)
      (hL.comp PT.fst) PT.snd))

end Article

end HTN
