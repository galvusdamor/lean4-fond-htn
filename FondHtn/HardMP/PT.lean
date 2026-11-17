import FondHtn.HardMP.Desc
import HtnComplexity.Article.TOHardPT
import HtnComplexity.Article.TODPPT
import HtnComplexity.Article.TreeCertPT
import HtnComplexity.Article.MostlyAcycPT
import HtnComplexity.Article.RunCheck
/-!
# The descriptions of the reductions are computed in polynomial time

`FOND.HardMP.pt_descA`, `FOND.HardMP.pt_descR`.
-/

namespace FOND

namespace HardMP

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime

variable {α : Type} [BEnc α]

/-! ## Encoding -/

theorem pt_fact {f : α → ℕ} (hf : PT f) : PT fun a => fact (f a) :=
  (PT.affine 2 0 hf).of_eq fun a => by simp [fact]

theorem pt_curF {x : α → Option (Bool × ℕ)} (hx : PT x) : PT fun a => curF (x a) := by
  have hg : PT fun a => (x a).getD (false, 0) := PT.getD hx (PT.const _)
  have hb : PT fun a => bif ((x a).getD (false, 0)).1 then 1 else 0 :=
    PT.cond (PT.fst.comp hg) (PT.const 1) (PT.const 0)
  have h := PT.cond (PT.isSome hx)
    (PT.affine 2 3 (PT.add (PT.affine 2 0 (PT.snd.comp hg)) hb)) (PT.const 1)
  refine h.of_eq fun a => ?_
  rcases x a with _ | ⟨b, n⟩
  · rfl
  · cases b <;> simp [curF]

theorem pt_toFAct0 : PT fun q : ℕ × ASpec => toFAct q.1 q.2 := by
  unfold toFAct
  have hs : PT fun q : ℕ × ASpec => q.2 := PT.snd
  have hcp := PT.map (g := fun _ x => curF x) (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hs))))
    (pt_curF PT.snd)
  have hcn := PT.map (g := fun _ x => curF x) (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hs))))
    (pt_curF PT.snd)
  refine PT.pair PT.fst (PT.pair (PT.append (PT.map (PT.fst.comp hs) (pt_fact PT.snd)) hcp)
    (PT.pair (PT.map (PT.fst.comp (PT.snd.comp hs)) (pt_fact PT.snd)) ?_))
  refine PT.map (PT.fst.comp (PT.snd.comp (PT.snd.comp hs))) ?_
  refine PT.pair (PT.append (PT.map (PT.fst.comp PT.snd) (pt_fact PT.snd)) (hcn.comp PT.fst))
    (PT.append (PT.map (PT.snd.comp PT.snd) (pt_fact PT.snd)) ?_)
  exact PT.cond (PT.isEmpty (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (hs.comp PT.fst))))))
    PT.nil (hcp.comp PT.fst)

theorem pt_toFAct {nm : α → ℕ} {s : α → ASpec} (hn : PT nm) (hs : PT s) :
    PT fun a => toFAct (nm a) (s a) := pt_toFAct0.comp (PT.pair hn hs)

theorem pt_guessI {f : α → ℕ} (hf : PT f) : PT fun a => guessI (f a) := by
  unfold guessI
  exact PT.cons (PT.pair PT.nil (PT.pair PT.nil (PT.pair (PT.single (PT.pair (PT.single hf) PT.nil))
      (PT.const _)))) (PT.single (PT.pair PT.nil (PT.pair PT.nil (PT.pair
      (PT.single (PT.pair PT.nil (PT.single hf))) (PT.const _)))))

theorem pt_eqI {f g : α → ℕ} (hf : PT f) (hg : PT g) : PT fun a => eqI (f a) (g a) := by
  unfold eqI
  exact PT.cons (PT.pair (PT.cons hf (PT.single hg)) (PT.const _))
    (PT.single (PT.pair PT.nil (PT.pair (PT.cons hf (PT.single hg)) (PT.const _))))

theorem pt_ccpI {s f g : α → ℕ} (hs : PT s) (hf : PT f) (hg : PT g) :
    PT fun a => ccpI (s a) (f a) (g a) := by
  unfold ccpI
  exact PT.cons (PT.pair PT.nil (PT.pair (PT.single hs) (PT.const _)))
    (PT.cons (PT.pair (PT.cons hs (PT.single hf)) (PT.pair PT.nil (PT.pair
      (PT.single (PT.pair (PT.single hg) PT.nil)) (PT.const _))))
    (PT.single (PT.pair (PT.single hs) (PT.pair (PT.single hf) (PT.pair
      (PT.single (PT.pair PT.nil (PT.single hg))) (PT.const _))))))

theorem pt_ccurI {s : α → ℕ} {h y : α → Option (Bool × ℕ)} (hs : PT s) (hh : PT h) (hy : PT y) :
    PT fun a => ccurI (s a) (h a) (y a) := by
  unfold ccurI
  exact PT.cons (PT.pair PT.nil (PT.pair (PT.single hs) (PT.const _)))
    (PT.single (PT.pair (PT.single hs) (PT.pair PT.nil (PT.pair (PT.const _)
      (PT.pair (PT.single hh) (PT.single hy))))))

theorem pt_chkI {pre neg : α → List ℕ} {cp : α → List (Option (Bool × ℕ))} (hp : PT pre)
    (hn : PT neg) (hc : PT cp) : PT fun a => chkI (pre a) (neg a) (cp a) := by
  unfold chkI
  exact PT.single (PT.pair hp (PT.pair hn (PT.pair (PT.const _) (PT.pair hc PT.nil))))

theorem pt_setI {d : α → ℕ} (hd : PT d) : PT fun a => setI (d a) := by
  unfold setI
  exact PT.single (PT.pair PT.nil (PT.pair PT.nil (PT.pair (PT.single (PT.pair (PT.single hd) PT.nil))
    (PT.const _))))

theorem pt_fSel {i : α → ℕ} (hi : PT i) : PT fun a => fSel (i a) :=
  (PT.affine 2 1 hi).of_eq fun a => by simp [fSel]

theorem pt_fSlot {k j : α → ℕ} (hk : PT k) (hj : PT j) : PT fun a => fSlot (k a) (j a) :=
  (PT.affine 2 2 (PT.natPair hk hj)).of_eq fun a => by simp [fSlot]

theorem pt_pickI {L : α → List (Bool × ℕ)} (hL : PT L) :
    PT fun a => pickI fSel (L a).length := by
  unfold pickI
  have hR := PT.rangeLength hL
  exact PT.single (PT.pair PT.nil (PT.pair PT.nil (PT.pair
    (PT.map hR (PT.pair (PT.single (pt_fSel PT.snd)) (PT.map (hR.comp PT.fst) (pt_fSel PT.snd))))
    (PT.const _))))

section Rounds

variable {L : α → List ℕ} (hL : PT L)
include hL

theorem pt_slotFields {ks : α → List ℕ} (hks : PT ks) :
    PT fun a => slotFields (L a).length (ks a) := by
  unfold slotFields
  exact PT.flatMap hks (PT.map (PT.rangeLength (hL.comp PT.fst))
    (pt_fSlot (PT.snd.comp PT.fst) PT.snd))

theorem pt_cpPairs {src dst : α → ℕ} (hs : PT src) (hd : PT dst) :
    PT fun a => cpPairs (L a).length (src a) (dst a) := by
  unfold cpPairs
  exact PT.map (PT.rangeLength hL) (PT.pair (pt_fSlot (hs.comp PT.fst) PT.snd)
    (pt_fSlot (hd.comp PT.fst) PT.snd))

theorem pt_childPairs {i : α → ℕ} (hi : PT i) : PT fun a => childPairs (L a).length (i a) := by
  unfold childPairs
  exact PT.append (pt_cpPairs hL (PT.affine 1 2 hi |>.of_eq fun a => by ring) (PT.const 0))
    (pt_cpPairs hL (PT.affine 1 3 hi |>.of_eq fun a => by ring) (PT.const 1))

theorem pt_progM {h : α → Option (Bool × ℕ)} {bs : α → List (Bool × ℕ)} (hh : PT h) (hbs : PT bs) :
    PT fun a => progM (L a).length (h a) (bs a) := by
  unfold progM
  have hR := PT.rangeLength hbs
  have hR1 : PT fun a => List.range ((bs a).length + 1) :=
    (PT.rangeLength (PT.append hbs (PT.const [default]))).of_eq fun a => by simp
  have hk : PT fun a => (bs a).length := PT.length hbs
  refine PT.append (PT.append (PT.append (PT.append ?_ ?_) ?_) ?_) ?_
  · exact PT.single (pt_chkI PT.nil PT.nil (PT.single hh))
  · exact PT.map (pt_slotFields hL (PT.map hR1 (PT.affine 1 2 PT.snd |>.of_eq fun a => by ring)))
      (pt_guessI PT.snd)
  · exact PT.map (pt_cpPairs hL (PT.const 0) (PT.const 2))
      (pt_eqI (PT.fst.comp PT.snd) (PT.snd.comp PT.snd))
  · exact PT.map (pt_cpPairs hL (PT.affine 1 2 hk |>.of_eq fun a => by ring) (PT.const 1))
      (pt_eqI (PT.fst.comp PT.snd) (PT.snd.comp PT.snd))
  · refine PT.cond (PT.isEmpty hbs) (PT.single (pt_setI (PT.const fDone))) ?_
    refine PT.append (PT.append (PT.single (pt_pickI hbs)) ?_) ?_
    · exact PT.flatMap hR (PT.map (pt_childPairs (hL.comp PT.fst) PT.snd)
        (pt_ccpI (pt_fSel (PT.snd.comp PT.fst)) (PT.fst.comp PT.snd) (PT.snd.comp PT.snd)))
    · exact PT.map hR (pt_ccurI (pt_fSel PT.snd) (hh.comp PT.fst)
        (PT.some (PT.getI (hbs.comp PT.fst) PT.snd)))

end Rounds

theorem pt_bitI {V : α → List ℕ} {act : α → ActDesc} {j : α → ℕ} (hV : PT V) (hact : PT act)
    (hj : PT j) : PT fun a => bitI (V a) (act a) (j a) := by
  unfold bitI
  have hf := PT.getI hV hj
  exact PT.cond (PT.elem (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hact)))) hf)
    (pt_chkI (PT.single (pt_fSlot (PT.const 1) hj)) PT.nil PT.nil)
    (PT.cond (PT.elem (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hact)))) hf)
      (pt_chkI PT.nil (PT.single (pt_fSlot (PT.const 1) hj)) PT.nil)
      (pt_eqI (pt_fSlot (PT.const 0) hj) (pt_fSlot (PT.const 1) hj)))

theorem pt_chkA {V : α → List ℕ} {act : α → ActDesc} {x : α → ℕ} (hV : PT V) (hact : PT act)
    (hx : PT x) : PT fun a => chkA (V a) (act a) (x a) := by
  unfold chkA
  have hR := PT.rangeLength hV
  have hsel : ∀ {sel : ActDesc → List ℕ}, PT sel →
      PT fun a => ((List.range (V a).length).filter fun j => decide ((V a).getI j ∈ sel (act a))).map
        (fSlot 0) := fun hsel =>
    PT.map (PT.filter hR (PT.elem (hsel.comp (hact.comp PT.fst)) (PT.getI (hV.comp PT.fst) PT.snd)))
      (pt_fSlot (PT.const 0) PT.snd)
  refine PT.cond (PT.all (PT.fst.comp (PT.snd.comp hact)) (PT.elem (hV.comp PT.fst) PT.snd)) ?_ PT.nil
  exact PT.single (PT.pair (hsel (PT.fst.comp PT.snd)) (PT.pair (hsel (PT.fst.comp (PT.snd.comp PT.snd)))
    (PT.pair (PT.const _) (PT.pair (PT.single (PT.some (PT.pair (PT.const false) hx))) PT.nil))))

theorem pt_progA : PT fun q : ProbDesc × ℕ => progA q.1 q.2 := by
  unfold progA
  have hV := pt_pfacts.comp (PT.fst (α := ProbDesc) (β := ℕ))
  have hact : PT fun q : ProbDesc × ℕ => actDescOf q.1 q.2 := pt_actDescOf
  exact PT.append (PT.map (PT.rangeLength hV) (pt_bitI (hV.comp PT.fst) (hact.comp PT.fst) PT.snd))
    (PT.single (pt_chkA hV hact PT.snd))

theorem pt_bodyOf {t : α → TnDesc} (ht : PT t) : PT fun a => bodyOf (t a) := by
  unfold bodyOf
  exact PT.map (pt_lin ht) (pt_lblOf (ht.comp PT.fst) PT.snd)

theorem pt_rules : PT rules := by
  unfold rules
  have hV := pt_pfacts
  refine PT.append (PT.append (PT.cons (PT.const _) (PT.single (pt_progM hV (PT.const none)
    (pt_bodyOf (PT.fst.comp (PT.snd.comp PT.snd)))))) ?_) ?_
  · exact PT.map (PT.snd.comp PT.fst) (pt_progM (hV.comp PT.fst)
      (PT.some (PT.pair (PT.const true) (PT.fst.comp PT.snd))) (pt_bodyOf (PT.snd.comp PT.snd)))
  · exact PT.map pt_numsOf pt_progA

theorem pt_goalI : PT goalI := by
  unfold goalI
  have hV := pt_pfacts
  have hR := PT.rangeLength hV
  have hsel : ∀ {sel : ProbDesc → List ℕ}, PT sel →
      PT fun p => ((List.range (pfacts p).length).filter fun j =>
        decide ((pfacts p).getI j ∈ sel p)).map (fSlot 1) := fun hsel =>
    PT.map (PT.filter hR (PT.elem (hsel.comp PT.fst) (PT.getI (hV.comp PT.fst) PT.snd)))
      (pt_fSlot (PT.const 1) PT.snd)
  have hgp : PT fun p : ProbDesc => p.goalPos := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hgn : PT fun p : ProbDesc => p.goalNeg := PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))
  exact PT.cond (PT.all hgp (PT.elem (hV.comp PT.fst) PT.snd)) (pt_chkI (hsel hgp) (hsel hgn) PT.nil)
    PT.nil

theorem pt_progInit : PT progInit := by
  unfold progInit
  exact PT.append (PT.map (PT.map (PT.rangeLength pt_pfacts) (pt_fSlot (PT.const 1) PT.snd))
    (pt_guessI PT.snd)) (PT.single pt_goalI)

/-! ## The descriptions -/

theorem pt_cN {r pc : α → ℕ} (hr : PT r) (hp : PT pc) : PT fun a => cN (r a) (pc a) :=
  (PT.affine 2 2 (PT.natPair hr hp)).of_eq fun a => by simp [cN]

theorem pt_aN {r pc alt : α → ℕ} (hr : PT r) (hp : PT pc) (hal : PT alt) :
    PT fun a => aN (r a) (pc a) (alt a) :=
  (PT.succ (PT.natPair hr (PT.natPair hp hal))).of_eq fun a => by simp [aN]

theorem pt_clkN {j : α → ℕ} (hj : PT j) : PT fun a => clkN (j a) :=
  (PT.affine 2 1 hj).of_eq fun a => by simp [clkN]

theorem pt_meth {c : α → ℕ} {b : α → List (Bool × ℕ)} (hc : PT c) (hb : PT b) :
    PT fun a => meth (c a) (b a) :=
  PT.pair hc (pt_seqTn hb)

theorem pt_prgs : PT prgs := PT.cons pt_progInit pt_rules

section P

variable {P : α → List (List (List ASpec))} (hP : PT P)
include hP

theorem pt_acts : PT fun a => acts (P a) := by
  unfold acts
  refine PT.cons (PT.const _) ?_
  have hPr : PT fun q : α × ℕ => (P q.1).getI q.2 := PT.getI (hP.comp PT.fst) PT.snd
  refine PT.flatMap (PT.rangeLength hP) (PT.flatMap (PT.rangeLength hPr) ?_)
  have hI : PT fun q : (α × ℕ) × ℕ => ((P q.1.1).getI q.1.2).getI q.2 :=
    PT.getI (hPr.comp PT.fst) PT.snd
  refine PT.map (PT.rangeLength hI) ?_
  exact pt_toFAct (pt_aN (PT.snd.comp (PT.fst.comp PT.fst)) (PT.snd.comp PT.fst) PT.snd)
    (PT.getI (hI.comp PT.fst) PT.snd)

theorem pt_chainMeths {ex : α → List (Bool × ℕ)} (hex : PT ex) :
    PT fun a => chainMeths (P a) (ex a) := by
  unfold chainMeths
  have hPr : PT fun q : α × ℕ => (P q.1).getI q.2 := PT.getI (hP.comp PT.fst) PT.snd
  refine PT.flatMap (PT.rangeLength hP) (PT.append ?_ (PT.single (pt_meth
    (pt_cN PT.snd (PT.length hPr)) (hex.comp PT.fst))))
  refine PT.flatMap (PT.rangeLength hPr) ?_
  have hI : PT fun q : (α × ℕ) × ℕ => ((P q.1.1).getI q.1.2).getI q.2 :=
    PT.getI (hPr.comp PT.fst) PT.snd
  have hr : PT fun q : ((α × ℕ) × ℕ) × ℕ => q.1.1.2 := PT.snd.comp (PT.fst.comp PT.fst)
  have hpc : PT fun q : ((α × ℕ) × ℕ) × ℕ => q.1.2 := PT.snd.comp PT.fst
  exact PT.map (PT.rangeLength hI) (pt_meth (pt_cN hr hpc) (PT.cons
    (PT.pair (PT.const false) (pt_aN hr hpc PT.snd))
    (PT.single (PT.pair (PT.const true) (pt_cN hr (PT.succ hpc))))))

theorem pt_roundMeths : PT fun a => roundMeths (P a) := by
  unfold roundMeths
  exact (PT.map (g := fun _ r => meth roundN [(true, cN (r + 1) 0)]) (PT.rangeLength (PT.tail hP))
    (pt_meth (PT.const roundN)
    (PT.single (PT.pair (PT.const true) (pt_cN (PT.succ PT.snd) (PT.const 0)))))).of_eq
    fun a => by simp

end P

theorem pt_rangeNclk : PT fun p : ProbDesc => List.range (Nclk p) := by
  have h := PT.rangeLength (PT.append (PT.append (PT.append (PT.append pt_pfacts pt_pfacts) pt_numsOf)
    pt_numsOf) (PT.const [0, 0]))
  exact h.of_eq fun p => by simp [Nclk]; ring_nf

theorem pt_Nclk : PT Nclk := (PT.length pt_rangeNclk).of_eq fun p => by simp

theorem pt_clockMeths : PT fun p : ProbDesc => clockMeths (Nclk p) := by
  unfold clockMeths
  exact PT.cons (PT.const _) (PT.map pt_rangeNclk (pt_meth (pt_clkN (PT.succ PT.snd))
    (PT.cons (PT.pair (PT.const true) (pt_clkN PT.snd)) (PT.single (PT.pair (PT.const true)
      (pt_clkN PT.snd))))))

theorem pt_initFacts : PT initFacts := by
  unfold initFacts
  exact PT.cons (PT.const _) (PT.map (PT.filter (PT.rangeLength pt_pfacts)
    (PT.elem (PT.fst.comp (PT.snd.comp PT.fst)) (PT.getI (pt_pfacts.comp PT.fst) PT.snd)))
    (pt_fact (pt_fSlot (PT.const 0) PT.snd)))

/-- **The acyclic description is computed in polynomial time.** -/
theorem pt_descA : PT descA := by
  unfold descA
  exact PT.pair (PT.pair (pt_acts pt_prgs) (PT.append (PT.append (pt_chainMeths pt_prgs PT.nil)
    (pt_roundMeths pt_prgs)) pt_clockMeths)) (PT.pair pt_initFacts (pt_seqTn (PT.cons (PT.const _)
      (PT.cons (PT.pair (PT.const true) (pt_clkN pt_Nclk)) (PT.const _)))))

/-- **The regular description is computed in polynomial time.** -/
theorem pt_descR : PT descR := by
  unfold descR
  exact PT.pair (PT.pair (pt_acts pt_prgs) (PT.append (PT.append
    (pt_chainMeths pt_prgs (PT.const _)) (pt_roundMeths pt_prgs)) (PT.const _)))
    (PT.pair pt_initFacts (PT.const _))

end HardMP

end FOND
