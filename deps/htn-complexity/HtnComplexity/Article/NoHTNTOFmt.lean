import HtnComplexity.Article.NoHTNTOExec
import HtnComplexity.Logspace.Check
/-!
# Problem descriptions as located codes

The format `HTN.Article.NoHTNTO.fProb` of problem descriptions: its code is the code `enc` of
`HtnComplexity/Article/PlanEx.lean` (`HTN.Article.NoHTNTO.enc_fProb`).  The parts of a
description written at the start of the input are located by closed terms
(`HTN.Article.NoHTNTO.locTn`, …), and the parts of a task network relative to its location.
-/

namespace HTN

namespace Article

namespace NoHTNTO

open Cx Cx.LTerm Syn Syn.PolyDom Logspace

/-! ### Formats -/

/-- Lists of numbers. -/
abbrev fNL : Fmt := .list .nat
/-- Action descriptions. -/
abbrev fAct : Fmt := .pair .nat (.pair fNL (.pair fNL (.pair fNL fNL)))
/-- Ordering pairs. -/
abbrev fOrd : Fmt := .list (.pair .nat .nat)
/-- Labels. -/
abbrev fLbl : Fmt := .list (.pair .nat (.pair .bool .nat))
/-- Task network descriptions. -/
abbrev fTn : Fmt := .pair fNL (.pair fOrd fLbl)
/-- Method descriptions. -/
abbrev fMeth : Fmt := .pair .nat fTn
/-- **Problem descriptions.** -/
abbrev fProb : Fmt := .pair (.pair (.list fAct) (.list fMeth)) (.pair fNL (.pair fTn (.pair fNL fNL)))

theorem fenc_nat : Fmt.enc .nat = (enc : ℕ → List Bool) := rfl

theorem fenc_bool : Fmt.enc .bool = (enc : Bool → List Bool) := rfl

theorem fenc_list {F : Fmt} [BEnc F.ty] (h : Fmt.enc F = enc) : Fmt.enc (.list F) = enc :=
  funext fun l => by rw [Fmt.enc_list, h, enc_list]

theorem fenc_pair {F G : Fmt} [BEnc F.ty] [BEnc G.ty] (hF : Fmt.enc F = enc) (hG : Fmt.enc G = enc) :
    Fmt.enc (.pair F G) = enc :=
  funext fun ab => by rw [show ab = (ab.1, ab.2) from rfl, Fmt.enc_pair, hF, hG, enc_prod]

theorem fenc_NL : Fmt.enc fNL = (enc : List ℕ → List Bool) := fenc_list fenc_nat

theorem fenc_tn : Fmt.enc fTn = (enc : TnDesc → List Bool) :=
  fenc_pair fenc_NL (fenc_pair (fenc_list (fenc_pair fenc_nat fenc_nat))
    (fenc_list (fenc_pair fenc_nat (fenc_pair fenc_bool fenc_nat))))

/-- **The code of a description is its code as a value of `fProb`.** -/
theorem enc_fProb : Fmt.enc fProb = (enc : ProbDesc → List Bool) :=
  fenc_pair (fenc_pair (fenc_list (fenc_pair fenc_nat (fenc_pair fenc_NL (fenc_pair fenc_NL
    (fenc_pair fenc_NL fenc_NL))))) (fenc_list (fenc_pair fenc_nat fenc_tn)))
    (fenc_pair fenc_NL (fenc_pair fenc_tn (fenc_pair fenc_NL fenc_NL)))

/-! ### Pairs -/

variable {y : List Bool} {M : ℕ}

theorem At.p1 {d q : ℕ} {F G : Fmt} {ab : (Fmt.pair F G).ty} (h : At y d q (.pair F G) ab) :
    At y d q F ab.1 := (LocS.append.1 h).1

theorem At.p2 (hM : y.length + 2 ≤ M) {F G : Fmt} {d : ℕ} {P : LTerm} {env : List ℕ}
    {ab : (Fmt.pair F G).ty} (h : At y d (eval y M env P) (.pair F G) ab) :
    At y d (eval y M env (sndT F d P)) G ab.2 :=
  At.snd (a := ab.1) (b := ab.2) hM h

theorem at_input (y : List Bool) : LocS y 0 0 y := by
  intro k hk
  simp [rd, hk, List.getD_eq_getElem?_getD]

/-! ### Locations of the parts of a description -/

/-- The methods. -/
def locMeths : LTerm := sndT (.list fAct) 0 (.lit 0)
/-- The instance. -/
def locInst : LTerm := sndT (.pair (.list fAct) (.list fMeth)) 0 (.lit 0)
/-- The initial task network. -/
def locTn : LTerm := sndT fNL 0 locInst
/-- `g⁺`. -/
def locGP : LTerm := sndT fTn 0 locTn
/-- `g⁻`. -/
def locGN : LTerm := sndT fNL 0 locGP

/-- The ordering pairs of the task network at `(d, T)`. -/
def ordLoc (d : ℕ) (T : LTerm) : LTerm := sndT fNL d T
/-- The labels of the task network at `(d, T)`. -/
def lblLoc (d : ℕ) (T : LTerm) : LTerm := sndT fOrd d (ordLoc d T)

section Parts

variable (hM : y.length + 2 ≤ M) {p : ProbDesc} (hp : At y 0 0 fProb p) (env : List ℕ)
include hM hp

theorem at_acts : At y 0 (eval y M env (.lit 0)) (.list fAct) p.actions := At.p1 (At.p1 hp)

theorem at_meths : At y 0 (eval y M env locMeths) (.list fMeth) p.methods :=
  At.p2 hM (P := .lit 0) (env := env) (At.p1 hp)

theorem at_inst : At y 0 (eval y M env locInst) (.pair fNL (.pair fTn (.pair fNL fNL))) p.2 :=
  At.p2 hM (P := .lit 0) (env := env) hp

theorem at_init : At y 0 (eval y M env locInst) fNL p.init := At.p1 (at_inst hM hp env)

theorem at_tn : At y 0 (eval y M env locTn) fTn p.tnI := At.p1 (At.p2 hM (at_inst hM hp env))

theorem at_gP : At y 0 (eval y M env locGP) fNL p.goalPos :=
  At.p1 (At.p2 hM (At.p2 hM (at_inst hM hp env)))

theorem at_gN : At y 0 (eval y M env locGN) fNL p.goalNeg :=
  At.p2 hM (At.p2 hM (At.p2 hM (at_inst hM hp env)))

end Parts

section Tn

variable (hM : y.length + 2 ≤ M) {d : ℕ} {T : LTerm} {env : List ℕ} {t : TnDesc}
  (ht : At y d (eval y M env T) fTn t)
include hM ht

theorem at_ids : At y d (eval y M env T) fNL t.ids := At.p1 ht

theorem at_ord : At y d (eval y M env (ordLoc d T)) fOrd t.ordList := At.p1 (At.p2 hM ht)

theorem at_lbl : At y d (eval y M env (lblLoc d T)) fLbl t.lbl := At.p2 hM (At.p2 hM ht)

end Tn

/-! ### Membership of a pair -/

/-- **The pair of the numbers at `(dx, X)` and `(dz, Z)` is in the list of pairs at `(d, O)`.** -/
def pairMemT (dx : ℕ) (X : LTerm) (dz : ℕ) (Z : LTerm) (d : ℕ) (O : LTerm) : LTerm :=
  exE d O (and (natEqT dx (lift 2 X) (d + 1) (entryT d (lift 2 O) (.var 1)))
    (natEqT dz (lift 2 Z) (d + 1) (sndT .nat (d + 1) (entryT d (lift 2 O) (.var 1)))))

theorem eval_pairMemT (hM : y.length + 2 ≤ M) {dx dz d : ℕ} {X Z O : LTerm} {env : List ℕ} {x z : ℕ}
    {l : List (ℕ × ℕ)} (hx : At y dx (eval y M env X) .nat x) (hz : At y dz (eval y M env Z) .nat z)
    (hO : At y d (eval y M env O) fOrd l) :
    eval y M env (pairMemT dx X dz Z d O) ≠ 0 ↔ (x, z) ∈ l := by
  rw [pairMemT, eval_exE hM hO, List.mem_iff_getElem]
  refine exists_congr fun i => ⟨fun ⟨hi, he⟩ => ⟨hi, ?_⟩, fun ⟨hi, he⟩ => ⟨hi, ?_⟩⟩
  · have he1 := At.entry2 hM hO hi 0
    rw [eval_and, eval_natEqT hM (hx.lift2 0 i) (At.p1 he1), eval_natEqT hM (hz.lift2 0 i) (At.p2 hM he1)] at he
    by_cases h1 : x = l[i].1 <;> by_cases h2 : z = l[i].2 <;> simp_all [Prod.ext_iff]
  · have he1 := At.entry2 hM hO hi 0
    rw [eval_and, eval_natEqT hM (hx.lift2 0 i) (At.p1 he1), eval_natEqT hM (hz.lift2 0 i) (At.p2 hM he1)]
    rw [he]; simp

end NoHTNTO

end Article

end HTN
