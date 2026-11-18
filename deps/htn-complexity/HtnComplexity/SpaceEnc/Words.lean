import HtnComplexity.SpaceEnc.Defs
/-!
# The words of the encoding

A *chain word* of parity `p` is the refinement of one leaf `Tree p 0` of the binary tree of a
block:

`ws p · wb p 0 x₀ e₀ ⋯ wb p (m-1) x e · rd · core · incw · rv p val · rb p (m-1) x ⋯ rb p 0 x₀`.

It is described by its *chain data* `HTN.SpaceEnc.CD` (the address bits `x`, the comparison bits
`e`, the optional input read `rd`, the core action, the increment action and the stored symbol
`val`).  A *round end word* is a single head move action, the *finish word* starts with `fin q`.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type}

/-- The chain data of a chain word. -/
structure CD (Q Γ : Type) where
  /-- The address bits. -/
  x : ℕ → Bool
  /-- The comparison bits (address bit equals head bit). -/
  e : ℕ → Bool
  /-- The input read (round `0` only). -/
  rd : List (Act Q Γ)
  /-- The core action (`cp` or `tr`). -/
  core : Act Q Γ
  /-- The increment action (`inc` or `wrap`). -/
  incw : Act Q Γ
  /-- The stored symbol. -/
  val : Γ

/-- The address checks `wb p k ⋯ wb p (k + j - 1)` of a chain word. -/
def wbsL (p : Bool) (k j : ℕ) (cd : CD Q Γ) : List (Act Q Γ) :=
  (List.range' k j).map fun i => .wb p i (cd.x i) (cd.e i)

/-- The address checks `rb p (k + j - 1) ⋯ rb p k` of a tail. -/
def rbsL (p : Bool) (k j : ℕ) (x : ℕ → Bool) : List (Act Q Γ) :=
  ((List.range' k j).map fun i => .rb p i (x i)).reverse

/-- The middle of a chain word. -/
def midL (p : Bool) (cd : CD Q Γ) : List (Act Q Γ) := cd.rd ++ [cd.core, cd.incw, .rv p cd.val]

/-- The refinement of `Bit p k`: the part of a chain word after the first `k` address checks
(without the matching `k` last address checks). -/
def bitL (m : ℕ) (p : Bool) (k : ℕ) (cd : CD Q Γ) : List (Act Q Γ) :=
  wbsL p k (m - k) cd ++ midL p cd ++ rbsL p k (m - k) cd.x

/-- **A chain word.** -/
def chainW (m : ℕ) (p : Bool) (cd : CD Q Γ) : List (Act Q Γ) := .ws p :: bitL m p 0 cd

/-- **A tail**: the stored symbol `g` at the address `x`. -/
def tailW (m : ℕ) (p : Bool) (x : ℕ → Bool) (g : Γ) : List (Act Q Γ) := .rv p g :: rbsL p 0 m x

/-- The head move actions. -/
def IsHAct (h : Act Q Γ) : Prop :=
  ∃ p, (∃ k, h = .hinc p k) ∨ (∃ k, h = .hdec p k) ∨ h = .hdec0 p ∨ h = .hstay p

section Valid

variable [Fintype Q] [Fintype Γ] (m n' : ℕ) (N : NTM Q Γ)

/-- **The chain data allowed by the methods** for the parity `p`. -/
def ValidCD (p : Bool) (cd : CD Q Γ) : Prop :=
  (cd.rd = [] ∨ (p = true ∧ (cd.rd = [.rblank] ∨ ∃ i b, i < n' ∧ cd.rd = [.ri i b]))) ∧
  ((∃ g, cd.core = .cp p g ∧ cd.val = g) ∨
    (∃ d ∈ transL N, cd.core = .tr p d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 ∧
      cd.val = d.2.2.2.1)) ∧
  ((∃ k < m, cd.incw = .inc p k) ∨ cd.incw = .wrap p)

/-- **A word of a loop**: a chain word or a round end word. -/
def LoopW (v : List (Act Q Γ)) : Prop :=
  (∃ p cd, ValidCD m n' N p cd ∧ v = chainW m p cd) ∨ (∃ h, IsHAct h ∧ v = [h])

/-- **A finish word.** -/
def FinW (v : List (Act Q Γ)) : Prop := ∃ q ∈ accL N, ∃ rest, v = .fin q :: rest

end Valid

/-! ### Unfolding -/

theorem wbsL_succ (p : Bool) (k j : ℕ) (cd : CD Q Γ) :
    wbsL p k (j + 1) cd = .wb p k (cd.x k) (cd.e k) :: wbsL p (k + 1) j cd := by
  simp [wbsL, List.range'_succ]

theorem rbsL_succ (p : Bool) (k j : ℕ) (x : ℕ → Bool) :
    rbsL p k (j + 1) x = (rbsL p (k + 1) j x : List (Act Q Γ)) ++ [.rb p k (x k)] := by
  simp [rbsL, List.range'_succ]

theorem bitL_of_lt {m : ℕ} (p : Bool) {k : ℕ} (hk : k < m) (cd : CD Q Γ) :
    bitL m p k cd = .wb p k (cd.x k) (cd.e k) :: bitL m p (k + 1) cd ++ [.rb p k (cd.x k)] := by
  obtain ⟨j, hj⟩ : ∃ j, m - k = j + 1 := ⟨m - k - 1, by omega⟩
  have hj' : m - (k + 1) = j := by omega
  simp [bitL, hj, hj', wbsL_succ, rbsL_succ]

theorem bitL_self (m : ℕ) (p : Bool) (cd : CD Q Γ) : bitL m p m cd = midL p cd := by
  simp [bitL, wbsL, rbsL]

end SpaceEnc

end HTN
