import FondHtn.FairSigma.Rank
import FondHtn.MP.Fair
import HtnComplexity.Computable.Marking
/-!
# Fair strong cyclic MP plan existence is in `Σ¹₁`

**`FOND.FS.fairMP_sigma11`**: `PlanExMPFair FClass.UNRES` is in `Σ¹₁`, in Kleene normal form
(`FOND.FS.Sigma11`): there is a computable `R` such that `w` is in the language iff some
`f : ℕ → ℕ` passes `R` on all its finite prefixes.

The function `f` encodes, for every description-level configuration of the fair game, its
membership in the winning set and its attractor rank (`FOND.FS.exists_chk_iff`); the check
`FOND.FS.sigCheck` decodes the description, tests it, and checks the local conditions on the
configurations whose codes (and successor codes) lie in the prefix.  It is polynomial-time in
the length of the prefix and the input, hence computable.
-/

namespace FOND

namespace FS

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS

/-- **`Σ¹₁` in Kleene normal form**: `w ∈ L` iff some `f : ℕ → ℕ` satisfies the computable
relation `R` on every finite prefix. -/
def Sigma11 (L : Cx.Language) : Prop :=
  ∃ R : List Bool × List ℕ → Bool, Computable R ∧
    ∀ w, L w ↔ ∃ f : ℕ → ℕ, ∀ n, R (w, (List.range n).map f) = true

/-- The configurations of the fair game on descriptions. -/
abbrev Nd : Type := ℕ × GNode

/-- The successors of a configuration. -/
def succL (p : FProbDesc) (c : Nd) : List Nd := (nodeSuccs p c.2).map fun g => (c.1, g)

/-- The code of a configuration: its encoding, read as a binary numeral with a final `1`. -/
def codeN (c : Nd) : ℕ := natOfBits (enc c ++ [true])

/-- Decoding a code. -/
def decN (k : ℕ) : Nd := (BDec.decR ((bitsOfNat k).reverse.tail.reverse)).1

/-- The initial configuration. -/
def c0 (p : FProbDesc) : Nd := (0, ((false, 0), initF p))

/-- Decoding a description. -/
def decP (w : List Bool) : FProbDesc := (BDec.decR w).1

/-- **The check.** -/
def sigCheck (x : List Bool × List ℕ) : Bool :=
  (decP x.1).validB && decide (enc (decP x.1) = x.1) &&
    chk gAcc gUni (decP x.1) (succL (decP x.1)) codeN decN (c0 (decP x.1)) x.2

theorem decN_codeN (c : Nd) : decN (codeN c) = c := by
  simp only [decN, codeN, bitsOfNat_natOfBits_append_true, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.tail_cons,
    List.reverse_reverse]
  have := BDec.decR_enc c []
  simpa using congrArg Prod.fst this

theorem decP_enc (p : FProbDesc) : decP (enc p) = p := by
  have := BDec.decR_enc p []
  simpa [decP] using congrArg Prod.fst this

theorem gStep_iff (p : FProbDesc) (c c' : Nd) : gStep (p, c, c') = true ↔ c' ∈ succL p c := by
  obtain ⟨b, g⟩ := c
  obtain ⟨b', g'⟩ := c'
  simp only [gStep, Bool.and_eq_true, decide_eq_true_eq, succL, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨g', h, rfl, rfl⟩
  · rintro ⟨g'', h, rfl, rfl⟩; exact ⟨rfl, h⟩

/-- **The language as prefix checks.** -/
theorem planExMPFair_iff_sigCheck (w : List Bool) :
    PlanExMPFair FClass.UNRES w ↔ ∃ f : ℕ → ℕ, ∀ n, sigCheck (w, (List.range n).map f) = true := by
  have key : ∀ p : FProbDesc, p.Valid → (p.toProblem.MPStrongCyclicFairSolvable ↔
      ∃ f : ℕ → ℕ, ∀ n, chk gAcc gUni p (succL p) codeN decN (c0 p) ((List.range n).map f) = true) :=
    fun p hp => by
      rw [fair_iff_uWin hp, uWin_iff_loc, exists_chk_iff gStep (gStep_iff p) codeN decN decN_codeN]
      rfl
  simp only [sigCheck, Bool.and_eq_true, decide_eq_true_eq, FProbDesc.validB_iff]
  constructor
  · rintro ⟨p, rfl, hp, -, hs⟩
    obtain ⟨f, hf⟩ := (key p hp).1 hs
    exact ⟨f, fun n => ⟨⟨by rw [decP_enc]; exact hp, by rw [decP_enc]⟩, by rw [decP_enc]; exact hf n⟩⟩
  · rintro ⟨f, hf⟩
    obtain ⟨⟨hp, he⟩, -⟩ := hf 0
    exact ⟨decP w, he, hp, trivial, (key _ hp).2 ⟨f, fun n => (hf n).2⟩⟩

/-! ## The check is polynomial-time -/

theorem pt_codeN : PT codeN :=
  (PT.ofBits (PT.append BDec.pt_encL (PT.const [true]))).of_eq fun _ => rfl

theorem pt_decN : PT decN :=
  (PT.fst.comp (BDec.pt_decR.comp (PT.reverse (PT.tail (PT.reverse PT.bits))))).of_eq fun _ => rfl

theorem pt_decP : PT decP := (PT.fst.comp BDec.pt_decR).of_eq fun _ => rfl

theorem pt_c0 : PT c0 := (PT.pair (PT.const 0) (PT.pair (PT.const _) pt_initF)).of_eq fun _ => rfl

theorem pt_succL : PT fun x : FProbDesc × Nd => succL x.1 x.2 := by
  have h1 : PT fun x : FProbDesc × Nd => nodeSuccs x.1 x.2.2 :=
    pt_nodeSuccs.comp (PT.pair PT.fst (PT.snd.comp PT.snd))
  have h2 : PT₂ fun (x : FProbDesc × Nd) (g : GNode) => ((x.2.1, g) : Nd) :=
    PT.pair (PT.fst.comp (PT.snd.comp PT.fst)) PT.snd
  exact (PT.map h1 h2).of_eq fun _ => rfl

/-- A lookup, as a function of a context. -/
theorem pt_look {ξ : Type} [BEnc ξ] {l : ξ → List ℕ} {c : ξ → Nd} (hl : PT l) (hc : PT c) :
    PT fun x => look codeN (l x) (c x) :=
  (PT.getI hl (pt_codeN.comp hc)).of_eq fun _ => rfl

theorem pt_locB : PT fun y : FProbDesc × List ℕ × Nd =>
    locB gAcc gUni y.1 (succL y.1) codeN y.2.1 y.2.2 := by
  have hp : PT fun y : FProbDesc × List ℕ × Nd => y.1 := PT.fst
  have hl : PT fun y : FProbDesc × List ℕ × Nd => y.2.1 := PT.fst.comp PT.snd
  have hc : PT fun y : FProbDesc × List ℕ × Nd => y.2.2 := PT.snd.comp PT.snd
  have hv := pt_look hl hc
  have hS : PT fun y : FProbDesc × List ℕ × Nd => succL y.1 y.2.2 := pt_succL.comp (PT.pair hp hc)
  -- in the context `(y, c')`
  have hl' : PT fun z : (FProbDesc × List ℕ × Nd) × Nd => z.1.2.1 := hl.comp PT.fst
  have hv' : PT fun z : (FProbDesc × List ℕ × Nd) × Nd => look codeN z.1.2.1 z.2 := pt_look hl' PT.snd
  have hvc : PT fun z : (FProbDesc × List ℕ × Nd) × Nd => look codeN z.1.2.1 z.1.2.2 :=
    hv.comp PT.fst
  have two : 0 < 2 := by norm_num
  have hx' : PT fun z : (FProbDesc × List ℕ × Nd) × Nd => look codeN z.1.2.1 z.2 % 2 == 1 :=
    PT.beq (PT.modC hv' two) (PT.const 1)
  have hpos' : PT fun z : (FProbDesc × List ℕ × Nd) × Nd => decide (0 < look codeN z.1.2.1 z.2 / 2) :=
    PT.lt (PT.const 0) (PT.divC hv' two)
  have hle' : PT fun z : (FProbDesc × List ℕ × Nd) × Nd =>
      decide (look codeN z.1.2.1 z.2 / 2 ≤ look codeN z.1.2.1 z.1.2.2 / 2 - 1) :=
    PT.le (PT.divC hv' two) (PT.subC (PT.divC hvc two) 1)
  have hacc : PT fun y : FProbDesc × List ℕ × Nd => gAcc (y.1, y.2.2) := pt_gAcc.comp (PT.pair hp hc)
  have huni : PT fun y : FProbDesc × List ℕ × Nd => gUni (y.1, y.2.2) := pt_gUni.comp (PT.pair hp hc)
  unfold locB
  refine PT.and (PT.or (PT.not (PT.beq (PT.modC hv two) (PT.const 1)))
    (PT.not (PT.beq (PT.divC hv two) (PT.const 0)))) ?_
  refine PT.or (PT.or (PT.or (PT.beq (PT.divC hv two) (PT.const 0)) hacc)
    (PT.and (PT.not huni) (PT.any hS (PT.and (PT.and hx' hpos') hle')))) ?_
  exact PT.and (PT.and huni (PT.all hS hx')) (PT.any hS (PT.and hpos' hle'))

theorem pt_chk : PT fun x : FProbDesc × List ℕ =>
    chk gAcc gUni x.1 (succL x.1) codeN decN (c0 x.1) x.2 := by
  have hp : PT fun x : FProbDesc × List ℕ => x.1 := PT.fst
  have hl : PT fun x : FProbDesc × List ℕ => x.2 := PT.snd
  have hc0 : PT fun x : FProbDesc × List ℕ => c0 x.1 := pt_c0.comp hp
  -- in the context `(x, k)`
  have hk : PT fun z : (FProbDesc × List ℕ) × ℕ => decN z.2 := pt_decN.comp PT.snd
  have hS : PT fun z : (FProbDesc × List ℕ) × ℕ => succL z.1.1 (decN z.2) :=
    pt_succL.comp (PT.pair (hp.comp PT.fst) hk)
  have hlen : PT fun w : ((FProbDesc × List ℕ) × ℕ) × Nd => w.1.1.2.length :=
    PT.length (hl.comp (PT.fst.comp PT.fst))
  have hloc : PT fun z : (FProbDesc × List ℕ) × ℕ =>
      locB gAcc gUni z.1.1 (succL z.1.1) codeN z.1.2 (decN z.2) :=
    pt_locB.comp (PT.pair (hp.comp PT.fst) (PT.pair (hl.comp PT.fst) hk))
  unfold chk
  refine PT.and (PT.or (PT.not (PT.lt (pt_codeN.comp hc0) (PT.length hl)))
    (PT.beq (PT.modC (pt_look hl hc0) (by norm_num)) (PT.const 1))) ?_
  refine PT.all (PT.rangeLength hl) (PT.or (PT.not (PT.and (PT.eq (pt_codeN.comp hk) PT.snd)
    (PT.all hS (PT.lt (pt_codeN.comp PT.snd) hlen)))) hloc)

theorem pt_sigCheck : PT sigCheck := by
  have hp : PT fun x : List Bool × List ℕ => decP x.1 := pt_decP.comp PT.fst
  have h1 : PT fun x : List Bool × List ℕ => (decP x.1).validB := FProbDesc.pt_validB.comp hp
  have he : PT fun x : List Bool × List ℕ => (enc (decP x.1) : List Bool) := BDec.pt_encL.comp hp
  have h2 : PT fun x : List Bool × List ℕ => decide (enc (decP x.1) = x.1) := PT.eq he PT.fst
  have hpair : PT fun x : List Bool × List ℕ => ((decP x.1, x.2) : FProbDesc × List ℕ) :=
    PT.pair hp PT.snd
  have h3 := pt_chk.comp hpair
  simp only at h3
  exact PT.and (PT.and h1 h2) h3

theorem computable_sigCheck : Computable sigCheck := by
  obtain ⟨F, hF, hFe⟩ := pt_sigCheck
  have hc : Computable fun x : List Bool × List ℕ => (F (enc x)).headI :=
    Primrec.list_headI.to_comp.comp ((polyTimeFun_of_uc hF).computable.comp PEnc.primrec_enc.to_comp)
  refine hc.of_eq fun x => ?_
  rw [hFe]; rfl

/-- **Fair strong cyclic method-based plan existence is in `Σ¹₁`** (unrestricted problems). -/
theorem fairMP_sigma11 : Sigma11 (PlanExMPFair FClass.UNRES) :=
  ⟨sigCheck, computable_sigCheck, planExMPFair_iff_sigCheck⟩

end FS

end FOND
