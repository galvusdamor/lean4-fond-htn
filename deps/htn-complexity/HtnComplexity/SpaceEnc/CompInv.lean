import HtnComplexity.SpaceEnc.CompBasic
/-!
# Completeness of the encoding: the phases of the planned run

The world of the planned run is described phase by phase, as in the soundness proof, but with
the remaining words known exactly:

* `CP0 k c` (program counter `0`, position `c` of round `k`), `CPW k c j` (address checks),
  `CPR k c j` (reading the stored tail of position `c`), `CPC k c` (core action), `CPI k c`
  (increment), `CPE k` (head move), `CFin` (the accepting configuration reached), `CD1 S`,
  `CD2 S c j` (draining the stored tails of the positions `S` after `fin`);
* `HTN.SpaceEnc.CInv` — their disjunction.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ}

section Defs

variable [Fintype Q] [Fintype Γ] {S : ℕ} {c₀ : Config Q Γ} (R : RunSeq N S c₀) (m n' : ℕ) (w : List Bool)

/-- The unstarted chain words of round `k` from position `c₀` on. -/
noncomputable def Mfr (k c₀ : ℕ) : Multiset (List (Act Q Γ)) :=
  ((List.range' c₀ (2 ^ m - c₀)).map fun c' => chainW m (parR k) (cdOf R m n' w k c') :
    List (List (Act Q Γ)))

/-- **The writer's blocks** in round `k` at position `c`: the unstarted chain words from `c₀`
on, the head move, the stored tails of the positions `< c` and the words `X` in progress;
then the future blocks. -/
def WB (k c₀ c : ℕ) (X : Multiset (List (Act Q Γ))) (bsp : List (List (List (Act Q Γ)))) :
    Prop :=
  ∃ E cur, bsp = E ++ cur :: futB R m n' w (parR k) (k + 1) ∧ AllE E ∧
    msOf cur = Mfr R m n' w k c₀ + {[hOf R k]} +
      tails m (parR k) (R.cf (k + 1)).tape (List.range c) + X

/-- **The reader's blocks** in round `k`: in round `0` only future blocks, later the current
block holds the words `RC`. -/
def RB (k : ℕ) (RC : Multiset (List (Act Q Γ))) (bsq : List (List (List (Act Q Γ)))) : Prop :=
  ∃ E L, bsq = E ++ L ∧ AllE E ∧ (k = 0 → L = futB R m n' w (!parR k) (k + 1)) ∧
    (k ≠ 0 → ∃ cur, L = cur :: futB R m n' w (!parR k) (k + 1) ∧ msOf cur = RC)

/-- The record of round `k` at position `c`. -/
def CFS (k c pc : ℕ) (done : Prop) (fs : FS Q Γ) : Prop :=
  fs.pc = pc ∧ fs.cnt = c ∧ fs.hd = (R.cf k).head ∧ fs.par = parR k ∧
    fs.first = decide (k = 0) ∧
    (done → fs.st = (R.tr k).1 ∧ fs.mv = some (R.tr k).2.2) ∧
    (¬ done → fs.st = (R.cf k).state ∧ fs.mv = none)

/-- The tails of the reader in round `k` from position `c` on. -/
def RT (k c : ℕ) : Multiset (List (Act Q Γ)) :=
  tails m (!parR k) (R.cf k).tape (List.range' c (2 ^ m - c))

/-- Phase `CP0 k c`. -/
def CP0 (k c : ℕ) (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  k < R.r ∧ c < 2 ^ m ∧ ∃ fs, wd.s = enc m w fs ∧ CFS R k c 0 ((R.cf k).head < c) fs ∧
    fs.eqv = true ∧ (k = 0 → fs.u = min c n') ∧
    WB R m n' w k c c 0 (wd.bs (parR k)) ∧ RB R m n' w k (RT R m k c) (wd.bs (!parR k)) ∧
    wd.φ = phiOf R m

/-- Phase `CPW k c j`. -/
def CPW (k c j : ℕ) (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  k < R.r ∧ c < 2 ^ m ∧ j ≤ m ∧ ∃ fs, wd.s = enc m w fs ∧
    CFS R k c (j + 1) ((R.cf k).head < c) fs ∧
    fs.eqv = decide (∀ i < j, c.testBit i = (R.cf k).head.testBit i) ∧
    (k = 0 → fs.u = min c n') ∧
    WB R m n' w k (c + 1) c {wipW m (parR k) j (cdOf R m n' w k c)} (wd.bs (parR k)) ∧
    RB R m n' w k (RT R m k c) (wd.bs (!parR k)) ∧ wd.φ = phiOf R m

/-- Phase `CPR k c j`. -/
def CPR (k c j : ℕ) (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  k < R.r ∧ k ≠ 0 ∧ c < 2 ^ m ∧ j ≤ m ∧ ∃ fs, wd.s = enc m w fs ∧
    CFS R k c (m + 2 + j) ((R.cf k).head < c) fs ∧
    fs.eqv = decide (∀ i < m, c.testBit i = (R.cf k).head.testBit i) ∧
    fs.sym = some ((R.cf k).tape c) ∧
    WB R m n' w k (c + 1) c {wipW m (parR k) m (cdOf R m n' w k c)} (wd.bs (parR k)) ∧
    RB R m n' w k (RT R m k (c + 1) +
      Multiset.filter (· ≠ []) {rbsL (!parR k) 0 (m - j) (bitsOf c)}) (wd.bs (!parR k)) ∧
    wd.φ = phiOf R m

/-- The word in progress after the input read, at the core action. -/
def coreW (cd : CD Q Γ) (p : Bool) (m : ℕ) : List (Act Q Γ) :=
  cd.core :: cd.incw :: .rv p cd.val :: rbsL p 0 m cd.x

/-- Phase `CPC k c`. -/
def CPC (k c : ℕ) (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  k < R.r ∧ c < 2 ^ m ∧ ∃ fs, wd.s = enc m w fs ∧
    CFS R k c (2 * m + 2) ((R.cf k).head < c) fs ∧
    fs.eqv = decide (∀ i < m, c.testBit i = (R.cf k).head.testBit i) ∧
    fs.sym = some ((R.cf k).tape c) ∧ (k = 0 → fs.u = min (c + 1) n') ∧
    WB R m n' w k (c + 1) c {coreW (cdOf R m n' w k c) (parR k) m} (wd.bs (parR k)) ∧
    RB R m n' w k (RT R m k (c + 1)) (wd.bs (!parR k)) ∧ wd.φ = phiOf R m

/-- Phase `CPI k c`. -/
def CPI (k c : ℕ) (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  k < R.r ∧ c < 2 ^ m ∧ ∃ fs, wd.s = enc m w fs ∧
    CFS R k c (2 * m + 3) ((R.cf k).head < c + 1) fs ∧ (k = 0 → fs.u = min (c + 1) n') ∧
    WB R m n' w k (c + 1) c {((coreW (cdOf R m n' w k c) (parR k) m).drop 1)} (wd.bs (parR k)) ∧
    RB R m n' w k (RT R m k (c + 1)) (wd.bs (!parR k)) ∧ wd.φ = phiOf R m

/-- Phase `CPE k`. -/
def CPE (k : ℕ) (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  k < R.r ∧ ∃ fs, wd.s = enc m w fs ∧ CFS R k 0 (2 * m + 4) True fs ∧ fs.eqv = true ∧
    WB R m n' w k (2 ^ m) (2 ^ m) 0 (wd.bs (parR k)) ∧ RB R m n' w k 0 (wd.bs (!parR k)) ∧
    wd.φ = phiOf R m

/-- Phase `CFin`: the accepting configuration has been reached. -/
def CFin (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  ∃ fs, wd.s = enc m w fs ∧ fs.pc = 0 ∧ fs.cnt = 0 ∧ fs.st = (R.cf R.r).state ∧
    AllE (wd.bs (parR R.r)) ∧ (R.r = 0 → AllE (wd.bs (!parR R.r))) ∧
    (R.r ≠ 0 → ∃ E cur, wd.bs (!parR R.r) = E ++ [cur] ∧ AllE E ∧
      msOf cur = tails m (!parR R.r) (R.cf R.r).tape (List.range' 0 (2 ^ m))) ∧
    wd.φ = phiOf R m

/-- The facts that stay true while draining. -/
def DrainSt (s : Set (Fct Q Γ)) (pcv : ℕ) : Prop :=
  Fct.drain ∈ s ∧ Fct.par true ∈ s ∧ Fct.par false ∈ s ∧ (∀ k < m, ∀ x, Fct.cb k x ∈ s) ∧
    Fct.pc pcv ∈ s

/-- Phase `CD1 S`: draining, the tails of the positions `S` remain. -/
def CD1 (S : List ℕ) (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  (∃ q E L, wd.bs q = E ++ L ∧ AllE E ∧ AllE (wd.bs (!q)) ∧
    ((L = [] ∧ S = []) ∨ ∃ cur, L = [cur] ∧ msOf cur = tails m q (R.cf R.r).tape S)) ∧
    DrainSt m wd.s (m + 1) ∧ wd.φ = List.replicate S.length .drn

/-- Phase `CD2 S c j`: draining, the tail of position `c` is being read. -/
def CD2 (S : List ℕ) (c j : ℕ) (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  (∃ q E cur, wd.bs q = E ++ [cur] ∧ AllE E ∧ AllE (wd.bs (!q)) ∧
    msOf cur = tails m q (R.cf R.r).tape S +
      Multiset.filter (· ≠ []) {rbsL q 0 (m - j) (bitsOf c)}) ∧
    j ≤ m ∧ DrainSt m wd.s (m + 2 + j) ∧ wd.φ = List.replicate (S.length + 1) .drn

/-- **The invariant of the planned run.** -/
def CInv (wd : World (Fct Q Γ) (Act Q Γ)) : Prop :=
  (∃ k c, CP0 R m n' w k c wd) ∨ (∃ k c j, CPW R m n' w k c j wd) ∨
    (∃ k c j, CPR R m n' w k c j wd) ∨ (∃ k c, CPC R m n' w k c wd) ∨
    (∃ k c, CPI R m n' w k c wd) ∨ (∃ k, CPE R m n' w k wd) ∨ CFin R m w wd ∨
    (∃ S, CD1 R m S wd) ∨ (∃ S c j, CD2 R m S c j wd)

end Defs

#check @WB

/-! ### Making a step -/

section Step

variable {δ : ActionModel (Fct Q Γ) (Act Q Γ)}

theorem wstep_loop {wd : World (Fct Q Γ) (Act Q Γ)} {q : Bool}
    {E rest : List (List (List (Act Q Γ)))} {bl : List (List (Act Q Γ))} {i : ℕ}
    {a : Act Q Γ} {t : List (Act Q Γ)} (hbq : wd.bs q = E ++ bl :: rest) (hE : AllE E)
    (hi : bl[i]? = some (a :: t)) (happ : δ.Applicable a wd.s) :
    WStep δ wd ⟨δ.transition a wd.s, Function.update wd.bs q (bl.set i t :: rest), wd.φ⟩ :=
  ⟨a, happ, rfl, Or.inl ⟨q, E, bl, rest, i, t, hbq, hE, hi, rfl, rfl⟩⟩

theorem wstep_phi {wd : World (Fct Q Γ) (Act Q Γ)} {a : Act Q Γ} {φ' : List (Act Q Γ)}
    (hφ : wd.φ = a :: φ') (happ : δ.Applicable a wd.s) :
    WStep δ wd ⟨δ.transition a wd.s, wd.bs, φ'⟩ :=
  ⟨a, happ, rfl, Or.inr ⟨hφ, rfl⟩⟩

end Step

theorem exists_get_of_mem_msOf {α : Type*} {bl : List (List α)} {v : List α} (h : v ∈ msOf bl) :
    ∃ i : ℕ, bl[i]? = some v := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (mem_msOf.1 h).1
  exact ⟨i, by simp [hi]⟩

end SpaceEnc

end HTN
