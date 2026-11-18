import FondHtn.AcycHard.InstMach
/-!
# The description in numeric form

The description `FOND.AcycHard.Sav.Inst.desc` rewritten with numeric building blocks only
(codes, ranges, bit filters, the code quadruples `quad` of the options), as a preparation of the
polynomial-time proof: `FOND.AcycHard.Sav.Inst.acts_num`, `FOND.AcycHard.Sav.Inst.meths_num`.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

namespace Sav

open HTN HTN.Syn HTN.Article HardMP

variable {k : ℕ}

/-! ## Options as quadruples of codes -/

/-- The codes of the components of an option. -/
def quad (o : OK k) : ℕ × ℕ × ℕ × ℕ := (codeAS o.1, codeSym o.2.1, codeSym o.2.2.1, codeAS o.2.2.2)

def cOq (q : ℕ × ℕ × ℕ × ℕ) : ℕ := Nat.pair q.1 (Nat.pair q.2.1 (Nat.pair q.2.2.1 q.2.2.2))

theorem codeO_eq (o : OK k) : codeO o = cOq (quad o) := rfl

/-- The code of a data fact `st`, `rd`, `wr` (`i = 0, 1, 2`). -/
def fT (i x : ℕ) : ℕ := Nat.pair 2 (Nat.pair i x)

def qPre (q : ℕ × ℕ × ℕ × ℕ) : List ℕ := [Nat.pair 0 4, fT 0 q.1, fT 1 q.2.1, fT 2 q.2.2.1]

/-- The action of an option. -/
def qAct (q : ℕ × ℕ × ℕ × ℕ) : FActDesc :=
  (Nat.pair 8 (cOq q), qPre q, [], [([Nat.pair 1 4, fT 0 q.2.2.2], qPre q)])

theorem Inst.actOf_opt (o : OK k) : Inst.actOf (nP (.opt o)) (poolLists (.opt o)) = qAct (quad o) := rfl

/-- The facts the refill adds for an option. -/
def qFacts (q : ℕ × ℕ × ℕ × ℕ) : List ℕ := [fT 0 q.1, fT 1 q.2.1, fT 2 q.2.2.1]

/-- The pool chain data of an option: the code and the label of its single item. -/
def qSB (q : ℕ × ℕ × ℕ × ℕ) : ℕ × (Bool × ℕ) := (Nat.pair 2 (cOq q), (false, Nat.pair 8 (cOq q)))

/-! ## Actions -/

/-- The input-dependent control action. -/
def toRdAct (L : ℕ) : FActDesc :=
  (nC (.plain .toRd), [], [], [([fT 0 (Nat.pair 1 0)], (List.range (L + 2)).map fun i => fT 0 (Nat.pair 0 i))])

def ctlA0 : List FActDesc :=
  (gates.flatMap fun g => [CI.opn g, CI.cls g]).map fun x => Inst.actOf (k := k) (nC x) (ctlLists 0 x)

def ctlA1 : List FActDesc :=
  [Pl.half, .halfChk, .acc].map fun p => Inst.actOf (k := k) (nC (.plain p)) (ctlLists 0 (.plain p))

def gateCodes : List ℕ := gates.map fun g => codeTok (k := k) (.op g)

def symActs (syms : List (SymK k)) : List FActDesc :=
  syms.flatMap fun τ => [Inst.actOf (nP (.init τ)) (poolLists (.init τ)), Inst.actOf (nP (.fin τ)) (poolLists (.fin τ))]

def trActs : List FActDesc :=
  [Inst.actOf (nP (k := k) .tick) (poolLists (k := k) .tick), Inst.actOf (nP (k := k) .res) (poolLists (k := k) .res)]

/-! ## Methods -/

def methPw (cb j : ℕ) (l0 : List (Bool × ℕ)) : MethodDesc :=
  (Nat.pair 0 (Nat.pair cb j),
    seqTn (if j = 0 then l0 else [(true, Nat.pair 0 (Nat.pair cb (j - 1))), (true, Nat.pair 0 (Nat.pair cb (j - 1)))]))

def methPown (cb B c : ℕ) : MethodDesc :=
  (Nat.pair 1 cb, seqTn (((List.range B).filter fun j => c.testBit j).map fun j => (true, Nat.pair 0 (Nat.pair cb j))))

def methSpw (cs : ℕ) (it0 : Bool × ℕ) (j : ℕ) : MethodDesc :=
  (Nat.pair 5 (Nat.pair cs j),
    setTn (if j = 0 then [it0] else [(true, Nat.pair 5 (Nat.pair cs (j - 1))), (true, Nat.pair 5 (Nat.pair cs (j - 1)))]))

def methSpown (cs B c : ℕ) : MethodDesc :=
  (Nat.pair 6 cs, setTn (((List.range B).filter fun j => c.testBit j).map fun j => (true, Nat.pair 5 (Nat.pair cs j))))

/-- The methods of a pool chain kind. -/
def sbM (d : ℕ × (Bool × ℕ)) (B c : ℕ) : List MethodDesc :=
  (List.range B).map (methSpw d.1 d.2) ++ [methSpown d.1 B c]

/-- The methods of a block. -/
def blkM (cb : ℕ) (l0 : List (Bool × ℕ)) (B c : ℕ) : List MethodDesc :=
  (List.range B).map (fun j => methPw cb j l0) ++ [methPown cb B c]

/-- The labels of a block. -/
def blkLabs (b : Blk) : List (Bool × ℕ) := ((blkItems (k := k) b).map itemCode).map toLabB

/-- The data of a pool chain kind. -/
def sbD (s : SB k) : ℕ × (Bool × ℕ) := (codeSB s, toLabB (itemCode (sbItem s)))

theorem sbD_opt (o : OK k) : sbD (.opt o) = qSB (quad o) := rfl

namespace Inst

variable (I : Inst k)

theorem methOf_pw (b : Blk) (j : ℕ) : I.methOf (.pw b j) = methPw (codeBlk b) j (blkLabs (k := k) b) := by
  cases j <;> rfl

theorem methOf_pown (b : Blk) : I.methOf (.pown b) = methPown (codeBlk b) I.B (I.cnt b) := by
  simp only [methOf, methPown, isSetCN, labs, bodyCN, List.map_map, codeCN]
  rfl

theorem methOf_spw (s : SB k) (j : ℕ) : I.methOf (.spw s j) = methSpw (sbD s).1 (sbD s).2 j := by
  cases j <;> rfl

theorem methOf_spown (s : SB k) : I.methOf (.spown s) = methSpown (sbD s).1 I.B (I.cntS s) := by
  simp only [methOf, methSpown, isSetCN, labs, bodyCN, List.map_map, codeCN, sbD]
  rfl

/-- The constant methods. -/
def I0 : Inst k := ⟨0, 0, 0, 0, 0, 0, [], []⟩

theorem methOf_cellB : I.methOf .cellB = (I0 (k := k)).methOf .cellB := rfl
theorem methOf_newc (τ : SymK k) : I.methOf (.newc τ) = (I0 (k := k)).methOf (.newc τ) := rfl
theorem methOf_ctl : I.methOf .ctl = (I0 (k := k)).methOf .ctl := rfl

theorem methOf_pool : I.methOf .pool = (Nat.pair 7 0, setTn ((true, Nat.pair 6 (codeSB (k := k) .blank)) ::
    I.syms.map (fun τ => (true, Nat.pair 6 (codeSB (.fresh τ)))) ++
    (I.opts.map quad).map fun q => (true, Nat.pair 6 (Nat.pair 2 (cOq q))))) := by
  simp only [methOf, isSetCN, ite_true, labs, bodyCN, List.map_cons, List.map_append, List.map_map]
  rfl

/-- **The actions in numeric form.** -/
theorem acts_num : I.acts = (ctlA0 (k := k) ++ toRdAct I.L :: ctlA1 (k := k) ++
    [(nC .refill, [], [], [(gateCodes (k := k) ++ (I.opts.map quad).flatMap qFacts, [])])] ++
    (symActs I.syms ++ trActs (k := k) ++ (I.opts.map quad).map qAct)).dedup := by
  unfold acts
  congr 1
  have h1 : ciList.map (fun x => Inst.actOf (k := k) (nC x) (ctlLists I.L x)) = ctlA0 (k := k) ++ toRdAct I.L :: ctlA1 (k := k) := by
    have ht : Inst.actOf (k := k) (nC (.plain .toRd)) (ctlLists I.L (.plain .toRd)) = toRdAct I.L := by
      simp only [Inst.actOf, ctlLists, ppL, peL, Inst.encL, toRdAct, List.map_cons, List.map_nil,
        List.map_map]
      rfl
    simp only [ciList, pls, gates, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, ctlA0, ctlA1, List.cons_append, List.nil_append, List.append_nil, ht]
    rfl
  have h2 : I.refillAct = (nC .refill, [], [], [(gateCodes (k := k) ++ (I.opts.map quad).flatMap qFacts, [])]) := by
    have e : encL I.fullL = gateCodes (k := k) ++ (I.opts.map quad).flatMap qFacts := by
      rw [encL, fullL, List.map_append, List.map_map, List.map_flatMap, List.flatMap_map]
      rfl
    simp only [refillAct, e]
  have h3 : I.paList.map (fun a => Inst.actOf (nP a) (poolLists a)) =
      symActs I.syms ++ trActs (k := k) ++ (I.opts.map quad).map qAct := by
    simp only [paList, List.map_append, List.map_flatMap, List.map_map, symActs, trActs]
    simp only [List.map_cons, List.map_nil, Function.comp_def, Inst.actOf_opt]
  rw [h1, h2, h3]

/-- **The methods in numeric form.** -/
theorem meths_num : I.cnList.map I.methOf =
    (blkM (codeBlk .WT) (blkLabs (k := k) .WT) I.B I.S ++ blkM (codeBlk .WR) (blkLabs (k := k) .WR) I.B I.S ++
      blkM (codeBlk .PRE) (blkLabs (k := k) .PRE) I.B (FSpec.tri I.S) ++
      blkM (codeBlk .STEP) (blkLabs (k := k) .STEP) I.B I.S ++
      blkM (codeBlk .ROUND) (blkLabs (k := k) .ROUND) I.B I.K ++
      blkM (codeBlk .REF) (blkLabs (k := k) .REF) I.B I.R ++ blkM (codeBlk .TR) (blkLabs (k := k) .TR) I.B I.S) ++
    ((I0 (k := k)).methOf .cellB :: I.syms.map (fun τ => (I0 (k := k)).methOf (.newc τ))) ++
    ((I0 (k := k)).methOf .ctl :: (sbM (sbD (k := k) .blank) I.B I.S ++
      (I.syms.map fun τ => sbD (.fresh τ)).flatMap (fun d => sbM d I.B I.n) ++
      (I.opts.map quad).flatMap (fun q => sbM (qSB q) I.B I.n))) ++
    [I.methOf .pool] := by
  have hb : ∀ b, ((List.range I.B).map (CN.pw (k := k) b) ++ [CN.pown b]).map I.methOf =
      blkM (codeBlk b) (blkLabs (k := k) b) I.B (I.cnt b) := by
    intro b
    simp only [List.map_append, List.map_map, Function.comp_def, methOf_pw, List.map_cons, List.map_nil,
      methOf_pown, blkM]
  have hs : ∀ s, ((List.range I.B).map (CN.spw (k := k) s) ++ [CN.spown s]).map I.methOf =
      sbM (sbD s) I.B (I.cntS s) := by
    intro s
    simp only [List.map_append, List.map_map, Function.comp_def, methOf_spw, List.map_cons, List.map_nil,
      methOf_spown, sbM]
  simp only [cnList, List.map_append, List.map_flatMap, blks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_cons, List.map_nil, hb, sbs, List.flatMap_append, hs, List.flatMap_map,
    methOf_cellB, methOf_newc, methOf_ctl, List.map_map, Function.comp_def]
  simp only [cnt, cntS, sbD_opt, List.append_assoc, List.cons_append]

end Inst

end Sav

end AcycHard

end FOND
