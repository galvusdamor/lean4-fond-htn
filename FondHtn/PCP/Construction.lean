import FondHtn.PCP.ChainTn
import FondHtn.PCP.Words
import FondHtn.PCP.Chains4
import FondHtn.Lang.Desc
/-!
# The FOND problem of a two-stack machine

For a two-stack machine `M` and initial stacks `s₁, s₂`, `FOND.PCP.desc M s₁ s₂` is a FOND
description with four chains (`doc/notes_pcp_check.md`):

* chain `A` (control): `init`, then the word `aw c₀ c_f mid` (each letter an action `nA ℓ`),
  then `fin`;
* chain `B`: blocks `blk (u, t, v)` (actions `nB ℓ`), then `endB`;
* supply chains `S₁`, `S₂`: any number of `cheat₁`, `cheat₂`.

Facts: `fr m` (mode `m` free), `pd m c` (mode `m` pending character `c`), `ok m` (cheats of
mode `m` enabled), `dB` (chain `B` finished).
-/

namespace FOND

namespace PCP

open HTN HTN.Syn HTN.Article HTN.Undec

/-! ## Codes -/

def codeC : Ch → ℕ
  | .stk a => 3 * a
  | .st q => 3 * q + 1
  | .sep => 2

theorem codeC_inj : Function.Injective codeC := by
  intro x y h
  cases x <;> cases y <;> simp only [codeC] at h <;> first | rfl | omega | (congr 1; omega)

def codeO : Option Ch → ℕ
  | none => 0
  | some c => codeC c + 1

theorem codeO_inj : Function.Injective codeO := by
  intro x y h
  cases x <;> cases y <;> simp only [codeO] at h
  · rfl
  · omega
  · omega
  · rename_i a b; rw [codeC_inj (show codeC a = codeC b by omega)]

def codeL (ℓ : Letter) : ℕ := Nat.pair (codeO ℓ.1) (codeO ℓ.2)

theorem codeL_inj : Function.Injective codeL := by
  intro x y h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 h
  exact Prod.ext (codeO_inj h1) (codeO_inj h2)

/-- Action names. -/
def nInit : ℕ := 0
def nFin : ℕ := 1
def nEnd : ℕ := 2
def nCheat (m : ℕ) : ℕ := m + 2
def nA (ℓ : Letter) : ℕ := Nat.pair 5 (codeL ℓ)
def nB (ℓ : Letter) : ℕ := Nat.pair 6 (codeL ℓ)

theorem nA_inj : Function.Injective nA := fun x y h =>
  codeL_inj (Nat.pair_eq_pair.1 h).2
theorem nB_inj : Function.Injective nB := fun x y h =>
  codeL_inj (Nat.pair_eq_pair.1 h).2
theorem nA_ne_nB (x y : Letter) : nA x ≠ nB y := fun h => by
  have := (Nat.pair_eq_pair.1 h).1; omega
theorem five_le_nA (ℓ : Letter) : 5 ≤ nA ℓ := Nat.left_le_pair _ _
theorem five_le_nB (ℓ : Letter) : 6 ≤ nB ℓ := Nat.left_le_pair _ _

/-- Facts. -/
def fr (m : ℕ) : ℕ := Nat.pair 0 m
def pd (m : ℕ) (c : Ch) : ℕ := Nat.pair 1 (Nat.pair m (codeC c))
def ok (m : ℕ) : ℕ := Nat.pair 2 m
def dB : ℕ := Nat.pair 3 0

/-! ## The alphabet -/

variable (M : TSM) (s₁ s₂ : List ℕ)

/-- The stack symbols. -/
def syms : List ℕ := s₁ ++ s₂ ++ M.trans.flatMap fun t => t.pop :: t.push
/-- The control states. -/
def sts : List ℕ := M.start :: M.acc :: M.trans.flatMap fun t => [t.src, t.tgt]
/-- The characters. -/
def chars : List Ch := (( syms M s₁ s₂).map Ch.stk ++ (sts M).map Ch.st ++ [Ch.sep]).dedup
/-- The letters. -/
def letters : List Letter :=
  (chars M s₁ s₂).flatMap fun c => [(none, some c), (some c, some c), (some c, none)]

/-! ## Actions -/

/-- Mode `m` part of a letter of `A` (the leading chain): precondition and deletion. -/
def preA (m : ℕ) : Option Ch → List ℕ
  | none => []
  | some _ => [fr m]
def addA (m : ℕ) : Option Ch → List ℕ
  | none => []
  | some c => [pd m c]
/-- Mode `m` part of a letter of `B` (the following chain). -/
def preB (m : ℕ) : Option Ch → List ℕ
  | none => []
  | some c => [pd m c]
def addB (m : ℕ) : Option Ch → List ℕ
  | none => []
  | some _ => [fr m]

def actA (ℓ : Letter) : FActDesc :=
  (nA ℓ, preA 1 ℓ.1 ++ preA 2 ℓ.2, [], [(addA 1 ℓ.1 ++ addA 2 ℓ.2, preA 1 ℓ.1 ++ preA 2 ℓ.2)])
def actB (ℓ : Letter) : FActDesc :=
  (nB ℓ, preB 1 ℓ.1 ++ preB 2 ℓ.2, [], [(addB 1 ℓ.1 ++ addB 2 ℓ.2, preB 1 ℓ.1 ++ preB 2 ℓ.2)])
def actInit : FActDesc := (nInit, [], [], [([fr 1, ok 2], []), ([fr 2, ok 1], [])])
def actFin : FActDesc := (nFin, [fr 1, fr 2, dB], [], [([ok 1, ok 2], [])])
def actEnd : FActDesc := (nEnd, [], [], [([dB], [])])
def actCheat (m : ℕ) : FActDesc :=
  (nCheat m, [ok m], [], [(fr m :: (chars M s₁ s₂).map (pd m), [])])

def actions : List FActDesc :=
  [actInit, actFin, actEnd, actCheat M s₁ s₂ 1, actCheat M s₁ s₂ 2] ++
    (letters M s₁ s₂).map actA ++ (letters M s₁ s₂).map actB

/-! ## Methods -/

/-- The initial and final configurations. -/
def c₀ : Cfg := ⟨M.start, s₁, s₂⟩
def cf : Cfg := ⟨M.acc, [], []⟩

/-- The letters of a rule. -/
def ruleW (t : Tr) : List ℕ := (only1 (rhs t) ++ only2 (lhs t)).map nB
/-- A stack symbol of `B`, visible in both modes. -/
def symB (a : ℕ) : ℕ := nB (some (Ch.stk a), some (Ch.stk a))

/-- Compound names: `A₀ = 0`, `A_mid = 1`, `B_U = 2`, `B_V = 3`, `B_E = 4`, `S₁ = 5`, `S₂ = 6`. -/
def triples : List (ℕ × List ℕ × Option ℕ) :=
  [(0, nInit :: (only2 (encC (c₀ M s₁ s₂) ++ [Ch.sep])).map nA, some 1),
    (1, (only1 (encC (cf M) ++ [Ch.sep])).map nA ++ [nFin], none),
    (3, [nB (some Ch.sep, some Ch.sep)], some 4),
    (4, [nEnd], none),
    (5, [nCheat 1], some 5), (5, [], none), (6, [nCheat 2], some 6), (6, [], none)] ++
  (chars M s₁ s₂).map (fun c => (1, [nA (some c, some c)], some 1)) ++
  (syms M s₁ s₂).map (fun a => (2, [symB a], some 2)) ++
  (syms M s₁ s₂).map (fun a => (3, [symB a], some 3)) ++
  (syms M s₁ s₂).map (fun a => (4, [symB a], some 2)) ++
  M.trans.map (fun t => (2, ruleW t, some 3)) ++
  M.trans.map (fun t => (4, ruleW t, some 3))

def methods : List MethodDesc := (triples M s₁ s₂).map fun q => (q.1, chainTn q.2.1 q.2.2)

/-- The initial task network: the four roots, unordered. -/
def tnI : TnDesc := ([0, 1, 2, 3], [], [(0, true, 0), (1, true, 2), (2, true, 5), (3, true, 6)])

/-- The roots. -/
def root : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 5
  | _ => 6

/-- **The description.** -/
def desc : FProbDesc := ((actions M s₁ s₂, methods M s₁ s₂), ([], tnI))

end PCP

end FOND
