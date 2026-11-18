import FondHtn.HardTR.EncOut
import FondHtn.HardTR.WTrans
import FondHtn.HardTR.NetY
import FondHtn.HardTR.Lang
import FondHtn.AcycHard.InstDesc
/-!
# CB22 Thm 5, P1/P2: the description of the two-loop encoding of the tableau transducer

`FOND.HardTR.TD.desc`: actions are the encoded actions of the machine (`TE.aspec`), methods are
the productions of the grammar `TL.Gen` (`seqTn`/`setTn` bodies), the initial network is the
single task `main`, the initial state encodes the boot record.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TD

open TL TT TE HardMP HTN HTN.Syn HTN.Article AcycHard.Sav

variable {S : Type}

/-! ## Names -/

def codeSp : Option (ℕ × ℕ) → ℕ
  | none => 0
  | some (ℓ, s) => Nat.pair ℓ s + 1

def codeOG : Option ℕ → ℕ
  | none => 0
  | some ℓ => ℓ + 1

def codeOp : Op → ℕ
  | .t gs b w => Nat.pair 0 (Nat.pair (codeOG gs) (2 * b.toNat + w.toNat))
  | .i dec b w sp => Nat.pair 1 (Nat.pair (4 * dec.toNat + 2 * b.toNat + w.toNat) (codeSp sp))
  | .bt w => Nat.pair 2 w.toNat
  | .bi w => Nat.pair 3 w.toNat

variable (cS : S → ℕ)

def codeEn : En S → ℕ
  | .boot σ => Nat.pair 0 (cS σ)
  | .norm z l c r => Nat.pair 1 (Nat.pair z.toNat (Nat.pair (cS l) (Nat.pair (cS c) (cS r))))

/-- The names of the actions. -/
def nmA : Act Op (En S) → ℕ
  | .wb p k b => Nat.pair 0 (Nat.pair (2 * p.toNat + b.toNat) k)
  | .rv p γ => Nat.pair 1 (2 * p.toNat + γ.toNat)
  | .rb p k b => Nat.pair 2 (Nat.pair (2 * p.toNat + b.toNat) k)
  | .op p o => Nat.pair 3 (Nat.pair p.toNat (codeOp o))
  | .inc p k => Nat.pair 4 (Nat.pair p.toNat k)
  | .wrap p => Nat.pair 5 p.toNat
  | .rend p e => Nat.pair 6 (Nat.pair p.toNat (codeEn cS e))
  | .nrd p => Nat.pair 7 p.toNat
  | .dr p => Nat.pair 8 p.toNat
  | .fin => Nat.pair 9 0

/-- The names of the compound tasks. -/
def nmN : Nt → ℕ
  | .main => Nat.pair 0 0
  | .loop p => Nat.pair 1 p.toNat
  | .block p => Nat.pair 2 p.toNat
  | .tree p k => Nat.pair 3 (Nat.pair p.toNat k)
  | .bit p k => Nat.pair 4 (Nat.pair p.toNat k)
  | .core p => Nat.pair 5 p.toNat
  | .incT p => Nat.pair 6 p.toNat
  | .rvT p γ => Nat.pair 7 (2 * p.toNat + γ.toNat)
  | .rbT p k b => Nat.pair 8 (Nat.pair (2 * p.toNat + b.toNat) k)
  | .reT p => Nat.pair 9 p.toNat
  | .finT => Nat.pair 10 0

/-! ## The description -/

variable (X : Spec S) (allS : List S) (ops : List Op) (ens : List (En S))

/-- An action label. -/
def lA (a : Act Op (En S)) : Bool × ℕ := (false, nmA cS a)

/-- A compound label. -/
def lN (y : Nt) : Bool × ℕ := (true, nmN y)

/-- The actions of the loop `p`. -/
def actsP (p : Bool) : List (Act Op (En S)) :=
  (List.range (mm X)).flatMap (fun k => [.wb p k false, .wb p k true, .rb p k false, .rb p k true, .inc p k]) ++
    [.rv p false, .rv p true, .wrap p, .nrd p, .dr p] ++ ops.map (.op p) ++ ens.map (.rend p)

/-- **All actions.** -/
def acts : List (Act Op (En S)) := actsP X ops ens true ++ actsP X ops ens false ++ [Act.fin]

/-- The methods of the loop `p`. -/
def methsP (p : Bool) : List MethodDesc :=
  [(nmN (.loop p), seqTn [lN (.block p), lN (.loop p)]), (nmN (.loop p), seqTn []),
    (nmN (.block p), setTn [lN (.tree p (mm X)), lN (.reT p)]),
    (nmN (.tree p 0), seqTn [lN (.bit p 0)]), (nmN (.bit p (mm X)), seqTn [lN (.core p)]),
    (nmN (.incT p), seqTn [lA cS (.wrap p)])] ++
  (List.range (mm X)).flatMap (fun k =>
    [(nmN (.tree p (k + 1)), setTn [lN (.tree p k), lN (.tree p k)]),
      (nmN (.incT p), seqTn [lA cS (.inc p k)])] ++
    [false, true].flatMap fun b =>
      [(nmN (.bit p k), seqTn [lA cS (.wb p k b), lN (.bit p (k + 1)), lN (.rbT p k b)]),
        (nmN (.rbT p k b), seqTn [lA cS (.rb p k b)]), (nmN (.rbT p k b), seqTn [lA cS (.dr p)])]) ++
  ops.flatMap (fun o =>
    [(nmN (.core p), seqTn [lA cS (.op p o), lN (.incT p), lN (.rvT p (Spec.opW o))]),
      (nmN (.core p), seqTn [lA cS (.nrd p), lA cS (.op p o), lN (.incT p), lN (.rvT p (Spec.opW o))])]) ++
  [false, true].flatMap (fun γ =>
    [(nmN (.rvT p γ), seqTn [lA cS (.rv p γ)]), (nmN (.rvT p γ), seqTn [lA cS (.dr p)])]) ++
  ens.map (fun e => (nmN (.reT p), seqTn [lA cS (.rend p e)])) ++
  [(nmN (.reT p), seqTn [lA cS (.dr p)])]

/-- **All methods.** -/
def meths : List MethodDesc :=
  (nmN .main, setTn [lN (.loop true), lN (.loop false), lN .finT]) ::
    (nmN .finT, seqTn [lA cS .fin]) :: methsP cS X ops ens true ++ methsP cS X ops ens false

/-- The fields of the boot record (writer `true`, claim `σ₀`). -/
def bootFields (σ₀ : S) : List ℕ :=
  [fPh (.wb 0), fB 0, fB 2, fSg (cS σ₀), fB 3, fB 6, fGs none, fCl .eq, fCh .eq, fSc 0]

/-- The boot record. -/
def r₀ (σ₀ : S) : Rec (Ctl S) := ⟨.wb 0, 0, true, false, g0 σ₀⟩

/-- **The description.** -/
noncomputable def desc (σ₀ : S) : FProbDesc :=
  ((((acts X ops ens).map fun a => toFAct (nmA cS a) (aspec cS X allS a)).dedup, meths cS X ops ens),
    (curF none :: (bootFields cS σ₀).map fact, seqTn [lN .main]))

end TD

end HardTR

end FOND
