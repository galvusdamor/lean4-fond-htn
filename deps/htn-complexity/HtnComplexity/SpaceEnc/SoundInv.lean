import HtnComplexity.SpaceEnc.BlockYield
import HtnComplexity.SpaceEnc.FactState
/-!
# Soundness of the encoding: the invariant

The soundness proof reads an executable refinement action by action.  The world consists of the
fact state (a record `HTN.SpaceEnc.FS`), the remaining words of the two loops (block lists, one
per parity, `bs : Bool → List (List (List Act))`) and the remaining finish word `φ`.  This file
defines

* `HTN.SpaceEnc.G` — the symmetric form of `HTN.SpaceEnc.Gen`, and its step lemma `g_step`;
* `HTN.SpaceEnc.locate`, `HTN.SpaceEnc.locateF` — the block from which a step takes its action;
* `HTN.SpaceEnc.pcNeed`, `HTN.SpaceEnc.pc_of_app` — the program counter an action needs;
* `HTN.SpaceEnc.tl`, `HTN.SpaceEnc.tails` — stored tails;
* the phase invariants `InvP0`, `InvPW`, `InvPR`, `InvPC`, `InvPI`, `InvPE` of one round.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type}

/-! ### The symmetric three-process interleaving -/

section G

variable {α : Type*}

/-- `G bs φ z`: `z` interleaves a concatenation of interleavings of the blocks `bs true`, one of
the blocks `bs false`, and the word `φ`. -/
def G (bs : Bool → List (List (List α))) (φ : List α) (z : List α) : Prop :=
  Gen (bs true) (bs false) φ z

/-- All blocks of a list are entirely consumed. -/
def AllE (bs : List (List (List α))) : Prop := ∀ b ∈ bs, AllEmpty b

theorem g_step {bs : Bool → List (List (List α))} {φ : List α} {a : α} {z : List α}
    (h : G bs φ (a :: z)) :
    (∃ q E bl rest i t, bs q = E ++ bl :: rest ∧ AllE E ∧ bl[i]? = some (a :: t) ∧
        G (Function.update bs q (bl.set i t :: rest)) φ z) ∨
      (∃ φ', φ = a :: φ' ∧ G bs φ' z) := by
  rcases gen_cons h with ⟨e, bl, rest, i, t, h1, h2, h3, h4⟩ |
    ⟨e, bl, rest, i, t, h1, h2, h3, h4⟩ | ⟨φ', h1, h2⟩
  · refine Or.inl ⟨true, e, bl, rest, i, t, h1, h2, h3, ?_⟩
    simpa [G, Function.update] using h4
  · refine Or.inl ⟨false, e, bl, rest, i, t, h1, h2, h3, ?_⟩
    simpa [G, Function.update] using h4
  · exact Or.inr ⟨φ', h1, h2⟩

theorem g_nil {bs : Bool → List (List (List α))} {φ : List α} (h : G bs φ []) : φ = [] :=
  gen_nil h

theorem not_allEmpty_of_get {bl : List (List α)} {i : ℕ} {v : List α} (h : bl[i]? = some v)
    (hv : v ≠ []) : ¬ AllEmpty bl := fun hA => hv (hA v (List.mem_of_getElem? h))

theorem allE_append {E E' : List (List (List α))} (h : AllE E) (h' : AllE E') : AllE (E ++ E') := by
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact h b hb
  · exact h' b hb

/-- The first block that is not entirely consumed is determined. -/
theorem first_block {e E : List (List (List α))} {bl : List (List α)}
    {rest L : List (List (List α))} (h : e ++ bl :: rest = E ++ L) (he : AllE e) (hE : AllE E)
    (hbl : ¬ AllEmpty bl) : ∃ E₂, L = E₂ ++ bl :: rest ∧ AllE E₂ := by
  induction E generalizing e with
  | nil => exact ⟨e, h.symm, he⟩
  | cons b E ih =>
    rcases e with _ | ⟨b', e⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact absurd (hE _ (List.mem_cons_self ..)) hbl
    · simp only [List.cons_append, List.cons.injEq] at h
      exact ih h.2 (fun x hx => he x (List.mem_cons_of_mem _ hx))
        (fun x hx => hE x (List.mem_cons_of_mem _ hx))

end G

/-! ### Fresh blocks -/

section Fresh

variable [Fintype Q] [Fintype Γ] {m n' : ℕ} {N : NTM Q Γ}

theorem FreshBlock.not_allEmpty {p : Bool} {bl : List (List (Act Q Γ))}
    (h : FreshBlock m n' N p bl) : ¬ AllEmpty bl := by
  obtain ⟨cds, a, -, -, -, rfl⟩ := h
  intro hA
  have := hA [a] (by simp)
  simp at this

theorem FreshBlock.mem {p : Bool} {bl : List (List (Act Q Γ))} (h : FreshBlock m n' N p bl)
    {v : List (Act Q Γ)} (hv : v ∈ bl) :
    (∃ cd, ValidCD m n' N p cd ∧ v = chainW m p cd) ∨ (∃ a, IsHActP p a ∧ v = [a]) := by
  obtain ⟨cds, a, hv', -, ha, rfl⟩ := h
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hv
  rcases hv with ⟨cd, hcd, rfl⟩ | rfl
  · exact Or.inl ⟨cd, hv' cd hcd, rfl⟩
  · exact Or.inr ⟨a, ha, rfl⟩

/-- **Locating the block of a step** among the blocks `E ++ cur :: F` (`E` consumed, `F`
fresh): it is `cur`, or `cur` is consumed and it is the first block of `F`. -/
theorem locate {p : Bool} {bs E F e rest : List (List (List (Act Q Γ)))}
    {cur bl : List (List (Act Q Γ))} (h1 : bs = E ++ cur :: F) (hE : AllE E)
    (hF : ∀ b ∈ F, FreshBlock m n' N p b) (h2 : bs = e ++ bl :: rest) (he : AllE e)
    (hbl : ¬ AllEmpty bl) :
    (bl = cur ∧ rest = F) ∨ (AllEmpty cur ∧ F = bl :: rest) := by
  obtain ⟨E₂, hL, hE₂⟩ := first_block (h2.symm.trans h1) he hE hbl
  rcases E₂ with _ | ⟨b, E₂⟩
  · simp only [List.nil_append, List.cons.injEq] at hL
    exact Or.inl ⟨hL.1.symm, hL.2.symm⟩
  · simp only [List.cons_append, List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    refine Or.inr ⟨hE₂ _ (List.mem_cons_self ..), ?_⟩
    rcases E₂ with _ | ⟨b', E₂⟩
    · rfl
    · exact absurd (hE₂ b' (by simp)) (hF b' (by simp)).not_allEmpty

/-- **Locating the block of a step** among the blocks `E ++ F` (`E` consumed, `F` fresh). -/
theorem locateF {p : Bool} {bs E F e rest : List (List (List (Act Q Γ)))}
    {bl : List (List (Act Q Γ))} (h1 : bs = E ++ F) (hE : AllE E)
    (hF : ∀ b ∈ F, FreshBlock m n' N p b) (h2 : bs = e ++ bl :: rest) (he : AllE e)
    (hbl : ¬ AllEmpty bl) : F = bl :: rest := by
  obtain ⟨E₂, hL, hE₂⟩ := first_block (h2.symm.trans h1) he hE hbl
  rcases E₂ with _ | ⟨b', E₂⟩
  · exact hL
  · exact absurd (hE₂ b' (by simp)) (hF b' (by rw [hL]; simp)).not_allEmpty

end Fresh

/-! ### The program counter an action needs -/

/-- The value of the program counter at which an action is applicable. -/
def pcNeed (m : ℕ) : Act Q Γ → ℕ
  | .boot => 0
  | .ws _ => 0
  | .wb _ k _ _ => k + 1
  | .rb _ k _ => 2 * m + 1 - k
  | .rv _ _ => m + 1
  | .ri _ _ => m + 1
  | .rblank => m + 1
  | .cp _ _ => 2 * m + 2
  | .tr _ _ _ _ _ _ => 2 * m + 2
  | .inc _ _ => 2 * m + 3
  | .wrap _ => 2 * m + 3
  | .hinc _ _ => 2 * m + 4
  | .hdec _ _ => 2 * m + 4
  | .hdec0 _ => 2 * m + 4
  | .hstay _ => 2 * m + 4
  | .fin _ => 0
  | .drn => 2 * m + 2

section App

variable [Fintype Γ] {m n' : ℕ} {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool} {fs : FS Q Γ}

/-- **An applicable action needs the current program counter.** -/
theorem pc_of_app {a : Act Q Γ} (h : (am m n' ι N).Applicable a (enc m w fs)) :
    fs.pc = pcNeed m a := by
  cases a with
  | boot => exact absurd h (app_boot m n' ι N w fs)
  | drn => exact absurd h (app_drn m n' ι N w fs)
  | ws => exact ((app_ws m n' ι N w fs).1 h).1
  | wb => exact ((app_wb m n' ι N w fs).1 h).1
  | rb => exact ((app_rb m n' ι N w fs).1 h).1
  | rv => exact ((app_rv m n' ι N w fs).1 h).1
  | ri => exact ((app_ri m n' ι N w fs).1 h).1
  | rblank => exact ((app_rblank m n' ι N w fs).1 h).1
  | cp => exact ((app_cp m n' ι N w fs).1 h).1
  | tr => exact ((app_tr m n' ι N w fs).1 h).1
  | inc => exact ((app_inc m n' ι N w fs).1 h).1
  | wrap => exact ((app_wrap m n' ι N w fs).1 h).1
  | hinc => exact ((app_hinc m n' ι N w fs).1 h).1
  | hdec => exact ((app_hdec m n' ι N w fs).1 h).1
  | hdec0 => exact ((app_hdec0 m n' ι N w fs).1 h).1
  | hstay => exact ((app_hstay m n' ι N w fs).1 h).1
  | fin => exact ((app_fin m n' ι N w fs).1 h).1

/-- A head move of parity `p` needs the parity `p`. -/
theorem par_of_app_h {p : Bool} {a : Act Q Γ} (ha : IsHActP p a)
    (h : (am m n' ι N).Applicable a (enc m w fs)) : fs.par = p := by
  rcases ha with ⟨k, rfl⟩ | ⟨k, rfl⟩ | rfl | rfl
  · exact ((app_hinc m n' ι N w fs).1 h).2.1
  · exact ((app_hdec m n' ι N w fs).1 h).2.1
  · exact ((app_hdec0 m n' ι N w fs).1 h).2.1
  · exact ((app_hstay m n' ι N w fs).1 h).2.1

omit [Fintype Γ] in
theorem pcNeed_h {p : Bool} {a : Act Q Γ} (ha : IsHActP p a) : pcNeed m a = 2 * m + 4 := by
  rcases ha with ⟨k, rfl⟩ | ⟨k, rfl⟩ | rfl | rfl <;> rfl

end App

/-! ### Tails -/

/-- The bits of a position. -/
def bitsOf (c : ℕ) : ℕ → Bool := fun k => c.testBit k

/-- **The stored tail** of parity `p` for the position `c` with the symbol `g`. -/
def tl (m : ℕ) (p : Bool) (c : ℕ) (g : Γ) : List (Act Q Γ) := tailW m p (bitsOf c) g

/-- The tails of parity `p` of the positions `s`, with the symbols `f`. -/
def tails (m : ℕ) (p : Bool) (f : ℕ → Γ) (s : List ℕ) : Multiset (List (Act Q Γ)) :=
  ((s.map fun c => tl m p c (f c) : List (List (Act Q Γ))) : Multiset (List (Act Q Γ)))

/-- **The word in progress** after `k` address checks: the remaining checks, the middle and all
`m` read checks. -/
def wipW (m : ℕ) (p : Bool) (k : ℕ) (cd : CD Q Γ) : List (Act Q Γ) :=
  wbsL p k (m - k) cd ++ midL p cd ++ rbsL p 0 m cd.x

theorem tl_ne_nil (m : ℕ) (p : Bool) (c : ℕ) (g : Γ) : (tl m p c g : List (Act Q Γ)) ≠ [] := by
  simp [tl, tailW]

theorem chainW_ne_nil (m : ℕ) (p : Bool) (cd : CD Q Γ) : (chainW m p cd : List (Act Q Γ)) ≠ [] := by
  simp [chainW]

/-! ### Runs of the machine in bounded space -/

section Run

variable {N : NTM Q Γ}

theorem reachesSpace_head_lt {S : ℕ} : ∀ {r : ℕ} {c d : Config Q Γ}, N.ReachesSpace S r c d →
    d.head < S
  | 0, _, _, h => by obtain ⟨rfl, h⟩ := h; exact h
  | r + 1, _, _, h => by obtain ⟨-, e, -, h⟩ := h; exact reachesSpace_head_lt h

theorem reachesSpace_snoc {S : ℕ} : ∀ {r : ℕ} {c d e : Config Q Γ}, N.ReachesSpace S r c d →
    N.Step d e → e.head < S → N.ReachesSpace S (r + 1) c e
  | 0, _, _, _, h, hs, he => by
    obtain ⟨rfl, h⟩ := h
    exact ⟨h, _, hs, rfl, he⟩
  | r + 1, _, _, _, h, hs, he => by
    obtain ⟨h0, d', hd', h⟩ := h
    exact ⟨h0, d', hd', reachesSpace_snoc h hs he⟩

end Run

/-! ### The phase invariants -/

section Inv

variable [Fintype Q] [Fintype Γ] (m n' : ℕ) (ι : Bool → Γ) (N : NTM Q Γ) (w : List Bool)

/-- The ghost run: `cfg` is reachable in space `2 ^ m`; in round `0` it is the initial
configuration and the writer is the loop `A`. -/
def Run (cfg : Config Q Γ) (first p : Bool) : Prop :=
  (∃ r, N.ReachesSpace (2 ^ m) r (N.initConfig (w.map ι)) cfg) ∧
    (first = true → cfg = N.initConfig (w.map ι) ∧ p = true)

/-- The blocks `bs` are `E ++ cur :: F` with `E` consumed, `cur` satisfying `P` and `F` fresh. -/
def Blocks (p : Bool) (bs : List (List (List (Act Q Γ)))) (P : List (List (Act Q Γ)) → Prop) :
    Prop :=
  ∃ E cur F, bs = E ++ cur :: F ∧ AllE E ∧ P cur ∧ ∀ b ∈ F, FreshBlock m n' N p b

/-- The blocks `bs` are `E ++ F` with `E` consumed and `F` fresh. -/
def BlocksF (p : Bool) (bs : List (List (List (Act Q Γ)))) : Prop :=
  ∃ E F, bs = E ++ F ∧ AllE E ∧ ∀ b ∈ F, FreshBlock m n' N p b

/-- **The current block of the writer** at position `c`: the unstarted chain words, the head
move word, the tails of the positions `< c` (symbols `nv`) and the words `X` in progress. -/
def WCur (p : Bool) (c : ℕ) (nv : ℕ → Γ) (X : Multiset (List (Act Q Γ)))
    (cur : List (List (Act Q Γ))) : Prop :=
  ∃ (Fr : Multiset (CD Q Γ)) (h : Act Q Γ), (∀ cd ∈ Fr, ValidCD m n' N p cd) ∧
    Multiset.card Fr + c + Multiset.card X = 2 ^ m ∧ IsHActP p h ∧
    msOf cur = Fr.map (chainW m p) + {[h]} + tails m p nv (List.range c) + X

/-- **The reader at position `c`**: in round `0` all its blocks are fresh; otherwise its current
block holds the tails of the positions `c, …, 2 ^ m - 1` with the symbols of the tape. -/
def Reader (p : Bool) (cfg : Config Q Γ) (first : Bool) (c : ℕ)
    (bs : List (List (List (Act Q Γ)))) : Prop :=
  (first = true → ∀ b ∈ bs, FreshBlock m n' N (!p) b) ∧
    (first = false → Blocks m n' N (!p) bs fun cur =>
      msOf cur = tails m (!p) cfg.tape (List.range' c (2 ^ m - c)))

/-- The fixed part of the record during a round. -/
def FSok (p : Bool) (cfg : Config Q Γ) (first : Bool) (c : ℕ) (fs : FS Q Γ) : Prop :=
  fs.par = p ∧ fs.hd = cfg.head ∧ fs.first = first ∧ fs.cnt = c

/-- The new symbols written so far agree with the tape away from the head. -/
def NVok (cfg : Config Q Γ) (nv : ℕ → Γ) (c : ℕ) : Prop :=
  ∀ c' < c, c' ≠ cfg.head → nv c' = cfg.tape c'

/-- The transition status: after the head position (`done`), a transition of the machine has
been chosen, writing `nv head`; before, the state is unchanged and no move is pending. -/
def Stat (fs : FS Q Γ) (cfg : Config Q Γ) (nv : ℕ → Γ) (done : Prop) : Prop :=
  (done → ∃ μ, fs.mv = some μ ∧ (fs.st, nv cfg.head, μ) ∈ N.step cfg.state (cfg.tape cfg.head)) ∧
    (¬ done → fs.st = cfg.state ∧ fs.mv = none)

/-- **Phase `P0`**: program counter `0`, about to start the chain word of position `c`. -/
def InvP0 (p : Bool) (cfg : Config Q Γ) (first : Bool) (c : ℕ) (nv : ℕ → Γ) (fs : FS Q Γ)
    (bs : Bool → List (List (List (Act Q Γ)))) (φ : List (Act Q Γ)) : Prop :=
  Run m ι N w cfg first p ∧ FSok p cfg first c fs ∧ fs.pc = 0 ∧ fs.eqv = true ∧ c < 2 ^ m ∧
    (first = true → fs.u = min c n') ∧ NVok cfg nv c ∧ Stat N fs cfg nv (cfg.head < c) ∧
    FinW N φ ∧
    (c = 0 → BlocksF m n' N p (bs p)) ∧ (0 < c → Blocks m n' N p (bs p) (WCur m n' N p c nv 0)) ∧
    Reader m n' N p cfg first c (bs (!p))

/-- The chain data of the word in progress, after `k` address checks at position `c`. -/
def CDok (p : Bool) (cfg : Config Q Γ) (c k : ℕ) (cd : CD Q Γ) : Prop :=
  ValidCD m n' N p cd ∧ ∀ i < k, cd.x i = c.testBit i ∧ cd.e i = (c.testBit i == cfg.head.testBit i)

/-- **Phase `PW k`**: program counter `k + 1`, `k` address checks of the word in progress done. -/
def InvPW (p : Bool) (cfg : Config Q Γ) (first : Bool) (c k : ℕ) (nv : ℕ → Γ) (fs : FS Q Γ)
    (bs : Bool → List (List (List (Act Q Γ)))) (φ : List (Act Q Γ)) : Prop :=
  Run m ι N w cfg first p ∧ FSok p cfg first c fs ∧ fs.pc = k + 1 ∧ k ≤ m ∧ c < 2 ^ m ∧
    (first = true → fs.u = min c n') ∧ NVok cfg nv c ∧ Stat N fs cfg nv (cfg.head < c) ∧
    FinW N φ ∧
    fs.eqv = decide (∀ i < k, c.testBit i = cfg.head.testBit i) ∧
    (∃ cd, CDok m n' N p cfg c k cd ∧ Blocks m n' N p (bs p) (WCur m n' N p c nv {wipW m p k cd})) ∧
    Reader m n' N p cfg first c (bs (!p))

/-- **Phase `PR j`**: the tail of position `c'` is being read, `j` of its address checks done. -/
def InvPR (p : Bool) (cfg : Config Q Γ) (c j : ℕ) (nv : ℕ → Γ) (fs : FS Q Γ)
    (bs : Bool → List (List (List (Act Q Γ)))) (φ : List (Act Q Γ)) : Prop :=
  Run m ι N w cfg false p ∧ FSok p cfg false c fs ∧ fs.pc = m + 2 + j ∧ j ≤ m ∧ c < 2 ^ m ∧
    NVok cfg nv c ∧ Stat N fs cfg nv (cfg.head < c) ∧ FinW N φ ∧
    fs.eqv = decide (∀ i < m, c.testBit i = cfg.head.testBit i) ∧
    (∃ cd, CDok m n' N p cfg c m cd ∧ Blocks m n' N p (bs p) (WCur m n' N p c nv {wipW m p m cd})) ∧
    ∃ c', c ≤ c' ∧ c' < 2 ^ m ∧ (∀ i, m - j ≤ i → i < m → c'.testBit i = c.testBit i) ∧
      fs.sym = some (cfg.tape c') ∧
      Blocks m n' N (!p) (bs (!p)) fun cur =>
        msOf cur + {tl m (!p) c' (cfg.tape c')} =
          tails m (!p) cfg.tape (List.range' c (2 ^ m - c)) +
            Multiset.filter (· ≠ []) {rbsL (!p) 0 (m - j) (bitsOf c')}

/-- **Phase `PC`**: program counter `2m + 2`, the symbol of position `c` has been read. -/
def InvPC (p : Bool) (cfg : Config Q Γ) (first : Bool) (c : ℕ) (nv : ℕ → Γ) (fs : FS Q Γ)
    (bs : Bool → List (List (List (Act Q Γ)))) (φ : List (Act Q Γ)) : Prop :=
  Run m ι N w cfg first p ∧ FSok p cfg first c fs ∧ fs.pc = 2 * m + 2 ∧ c < 2 ^ m ∧
    (first = true → fs.u = min (c + 1) n') ∧ NVok cfg nv c ∧ Stat N fs cfg nv (cfg.head < c) ∧
    FinW N φ ∧ fs.sym = some (cfg.tape c) ∧
    fs.eqv = decide (∀ i < m, c.testBit i = cfg.head.testBit i) ∧
    (∃ cd rd, ValidCD m n' N p cd ∧ (∀ i < m, cd.x i = c.testBit i) ∧
      (rd = [] ∨ rd = [.rblank] ∨ ∃ i b, rd = [.ri i b]) ∧
      Blocks m n' N p (bs p)
        (WCur m n' N p c nv {rd ++ [cd.core, cd.incw, .rv p cd.val] ++ rbsL p 0 m cd.x})) ∧
    Reader m n' N p cfg first (c + 1) (bs (!p))

/-- **Phase `PI`**: program counter `2m + 3`, the symbol of position `c` has been written. -/
def InvPI (p : Bool) (cfg : Config Q Γ) (first : Bool) (c : ℕ) (nv : ℕ → Γ) (fs : FS Q Γ)
    (bs : Bool → List (List (List (Act Q Γ)))) (φ : List (Act Q Γ)) : Prop :=
  Run m ι N w cfg first p ∧ FSok p cfg first c fs ∧ fs.pc = 2 * m + 3 ∧ c < 2 ^ m ∧
    (first = true → fs.u = min (c + 1) n') ∧ NVok cfg nv (c + 1) ∧
    Stat N fs cfg nv (cfg.head < c + 1) ∧ FinW N φ ∧
    (∃ incw, ((∃ k < m, incw = .inc p k) ∨ incw = .wrap p) ∧
      Blocks m n' N p (bs p)
        (WCur m n' N p c nv {incw :: .rv p (nv c) :: rbsL p 0 m (bitsOf c)})) ∧
    Reader m n' N p cfg first (c + 1) (bs (!p))

/-- **Phase `PE`**: program counter `2m + 4`, the round is over, the head is to be moved. -/
def InvPE (p : Bool) (cfg : Config Q Γ) (first : Bool) (nv : ℕ → Γ) (fs : FS Q Γ)
    (bs : Bool → List (List (List (Act Q Γ)))) (φ : List (Act Q Γ)) : Prop :=
  Run m ι N w cfg first p ∧ FSok p cfg first 0 fs ∧ fs.pc = 2 * m + 4 ∧ fs.eqv = true ∧
    NVok cfg nv (2 ^ m) ∧ Stat N fs cfg nv True ∧ FinW N φ ∧
    Blocks m n' N p (bs p) (WCur m n' N p (2 ^ m) nv 0) ∧
    Reader m n' N p cfg first (2 ^ m) (bs (!p))

/-- **The invariant**: one of the phases. -/
def Inv (fs : FS Q Γ) (bs : Bool → List (List (List (Act Q Γ)))) (φ : List (Act Q Γ)) : Prop :=
  ∃ p cfg first nv, (∃ c, InvP0 m n' ι N w p cfg first c nv fs bs φ) ∨
    (∃ c k, InvPW m n' ι N w p cfg first c k nv fs bs φ) ∨
    (first = false ∧ ∃ c j, InvPR m n' ι N w p cfg c j nv fs bs φ) ∨
    (∃ c, InvPC m n' ι N w p cfg first c nv fs bs φ) ∨
    (∃ c, InvPI m n' ι N w p cfg first c nv fs bs φ) ∨
    InvPE m n' ι N w p cfg first nv fs bs φ

end Inv

end SpaceEnc

end HTN
