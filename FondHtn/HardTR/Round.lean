import FondHtn.HardTR.WGame
/-!
# CB22 Thm 5, P2 (abstract part): the round lemma of the two-loop block machine

The encoding stores a tape of `W = 2 ^ m` bits in the network: two tail-recursive loops `A`
(`true`) and `B` (`false`) write, alternately, one *block* per round.  A block consists of `W`
*chain words* and one *round-end word*.  A chain word of parity `p` is

`wb p 0 x₀ ⋯ wb p (m-1) x_{m-1} · [nrd p] · op p o · (inc p k | wrap p) · rv p γ' ·
  rb p (m-1) x_{m-1} ⋯ rb p 0 x₀`

with `γ' = opW o`: its address `x` is checked against the round counter when the word is written
(`wb`) and again when its *tail* `rv p γ' · rb …` is read in the next round by the other loop;
the tail stores the bit `γ'` of the cell `x` meanwhile.  The *transducer action* `op p o` reads the
bit of the cell (put into the state by `rv`), the address (the counter) and a finite control `g`
(an abstract type `G`), and writes `opW o`.  The round-end word is a single action `rend p e`
whose outcomes (nature) change the control; a separate *finish thread* holds the action `fin`
that ends the game.  The optional `nrd p` replaces reading in the first (boot) round, where there
is no tape yet.  The tail actions can alternatively be drained by `dr p` after `fin`.

**Design (deviation from `doc/notes_cb22_thm5_progress.md`).**  Soundness is not argued on task
networks but on the *configuration game* `FOND.HardTR.NWin` of a labelled transition system whose
configurations are **multisets of thread states** (`FOND.HardTR.TL.Th`), one multiset per loop
(the words of the current block that are not finished; `0` = the loop may start a new block),
plus the pending finish thread.  `FondHtn/HardTR/WGame.lean` reduces the progression game to it
once the refinements of the initial network are over-approximated by the language of this
transition system.  Since threads of the same loop with the same remaining word are
indistinguishable, the forcing argument ("the counter and the address checks force one word per
address and round") is *local*: at every step of a round the set of configurations consistent
with the history is a singleton (or, while an address is being read, a set indexed by the
candidate cell).

Main results (with `W = 2 ^ m`, `0 < m`):

* **`FOND.HardTR.TL.Mach.round_sound`** — from the start of a round (writer `ρ`, the tape `w`
  stored in the tails of the other loop, control `g`), a winning configuration game yields a
  relational transducer run `SRun w w' 0 g g'` producing the new tape `w'`, and then either the
  finish condition `finOK g'` or a round-end action `e` with `endOK e g'` all of whose outcomes
  `g''` win the next round (writer `!ρ`, tape `w'`).
* **`FOND.HardTR.TL.Mach.boot_sound`** — the same for the boot round (no tape, every read bit is
  `false`).
-/

namespace FOND

namespace HardTR

namespace TL

/-! ## The machine -/

/-- The phases of a position of a round (the program counter). -/
inductive Ph
  | wb (k : ℕ)
  | rv
  | rb (k : ℕ)
  | op
  | inc
  | fin
  | drain
  deriving DecidableEq

/-- The (abstract) states: phase, round counter, writing loop, last read bit, finite control. -/
structure Rec (G : Type) where
  ph : Ph
  c : ℕ
  par : Bool
  sym : Bool
  g : G

/-- The actions.  All but `fin` carry the parity of the loop they belong to. -/
inductive Act (Op En : Type)
  | wb (p : Bool) (k : ℕ) (b : Bool)
  | rv (p : Bool) (γ : Bool)
  | rb (p : Bool) (k : ℕ) (b : Bool)
  | op (p : Bool) (o : Op)
  | inc (p : Bool) (k : ℕ)
  | wrap (p : Bool)
  | rend (p : Bool) (e : En)
  | nrd (p : Bool)
  | dr (p : Bool)
  | fin

/-- The loop of an action (`none` for the finish action). -/
def Act.ap {Op En : Type} : Act Op En → Option Bool
  | .wb p _ _ => some p
  | .rv p _ => some p
  | .rb p _ _ => some p
  | .op p _ => some p
  | .inc p _ => some p
  | .wrap p => some p
  | .rend p _ => some p
  | .nrd p => some p
  | .dr p => some p
  | .fin => none

/-- The thread states.  `hd k a`: the first `k` address bits `a` written; `nb a`: after `nrd`;
`ic a γ`: after `op` (writing `γ`); `tv a γ`: the stored tail; `tb k a`: the tail after reading
the value and the address bits above `k`; `re`: the round-end word. -/
inductive Th
  | hd (k a : ℕ)
  | nb (a : ℕ)
  | ic (a : ℕ) (γ : Bool)
  | tv (a : ℕ) (γ : Bool)
  | tb (k a : ℕ)
  | re
  deriving DecidableEq

/-- The parameters: the number of address bits, the transducer and the round-end gadget. -/
structure Mach (G Op En : Type) where
  m : ℕ
  opOK : Op → G → Bool → ℕ → Prop
  opEff : Op → G → G
  opW : Op → Bool
  endOK : En → G → Prop
  endOut : En → G → Set G
  finOK : G → Prop
  boot : G → Prop
  endNe : ∀ e g, endOK e g → (endOut e g).Nonempty

variable {G Op En : Type} (M : Mach G Op En)

namespace Mach

/-- The number of cells. -/
abbrev W : ℕ := 2 ^ M.m

/-- The phase after `wb k`. -/
def nextWb (k : ℕ) : Ph := if k + 1 < M.m then .wb (k + 1) else .rv

/-- The phase after `rb k`. -/
def nextRb (k : ℕ) : Ph := if k = 0 then .op else .rb (k - 1)

/-- Applicability. -/
def app : Act Op En → Rec G → Prop
  | .wb p k b, r => r.ph = .wb k ∧ r.par = p ∧ r.c.testBit k = b
  | .rv p _, r => r.ph = .rv ∧ r.par = !p
  | .rb p k b, r => r.ph = .rb k ∧ r.par = !p ∧ r.c.testBit k = b
  | .op p o, r => r.ph = .op ∧ r.par = p ∧ M.opOK o r.g r.sym r.c
  | .inc p k, r => r.ph = .inc ∧ r.par = p ∧ k < M.m ∧ r.c.testBit k = false ∧
      ∀ j < k, r.c.testBit j = true
  | .wrap p, r => r.ph = .inc ∧ r.par = p ∧ ∀ j < M.m, r.c.testBit j = true
  | .rend p e, r => r.ph = .fin ∧ r.par = p ∧ M.endOK e r.g
  | .nrd p, r => r.ph = .rv ∧ r.par = p ∧ M.boot r.g
  | .dr _, r => r.ph = .drain
  | .fin, r => r.ph = .fin ∧ M.finOK r.g

/-- The outcomes. -/
def outs : Act Op En → Rec G → Set (Rec G)
  | .wb _ k _, r => {{ r with ph := M.nextWb k }}
  | .rv _ γ, r => {{ r with ph := .rb (M.m - 1), sym := γ }}
  | .rb _ k _, r => {{ r with ph := nextRb k }}
  | .op _ o, r => {{ r with ph := .inc, g := M.opEff o r.g }}
  | .inc _ _, r => {{ r with ph := .wb 0, c := r.c + 1 }}
  | .wrap _, r => {{ r with ph := .fin, c := 0 }}
  | .rend p e, r => {r' | ∃ g' ∈ M.endOut e r.g, r' = { r with ph := .wb 0, par := !p, g := g' }}
  | .nrd _, r => {{ r with ph := .op, sym := false }}
  | .dr _, r => {r}
  | .fin, r => {{ r with ph := .drain }}

theorem outs_nonempty (a : Act Op En) (r : Rec G) (h : M.app a r) : (M.outs a r).Nonempty := by
  cases a with
  | rend p e =>
    obtain ⟨g', hg'⟩ := M.endNe e r.g h.2.2
    exact ⟨_, g', hg', rfl⟩
  | dr p => exact ⟨r, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- The tail after `rb k`. -/
def tbNext (k a : ℕ) : Option Th := if k = 0 then none else some (.tb (k - 1) a)

/-- **The thread automaton**: `thStep q a r` — the thread in state `q` performs `a` and continues
in `r` (`none`: finished). -/
def thStep : Th → Act Op En → Option Th → Prop
  | .hd k a, .wb _ k' b, r => k' = k ∧ k < M.m ∧ r = some (.hd (k + 1) (a + if b then 2 ^ k else 0))
  | .hd k a, .op _ o, r => k = M.m ∧ r = some (.ic a (M.opW o))
  | .hd k a, .nrd _, r => k = M.m ∧ r = some (.nb a)
  | .nb a, .op _ o, r => r = some (.ic a (M.opW o))
  | .ic a γ, .inc _ _, r => r = some (.tv a γ)
  | .ic a γ, .wrap _, r => r = some (.tv a γ)
  | .tv a γ, .rv _ γ', r => γ' = γ ∧ r = some (.tb (M.m - 1) a)
  | .tv a _, .dr _, r => r = some (.tb (M.m - 1) a)
  | .tb k a, .rb _ k' b, r => k' = k ∧ b = a.testBit k ∧ r = tbNext k a
  | .tb k a, .dr _, r => r = tbNext k a
  | .re, .rend _ _, r => r = none
  | .re, .dr _, r => r = none
  | _, _, _ => False

end Mach

/-! ## Multisets of threads given by index functions -/

/-- The multiset of the threads `f i`, `i < N`. -/
def fm (f : ℕ → Option Th) (N : ℕ) : Multiset Th := ((List.range N).filterMap f : List Th)

/-- An optional thread as a multiset. -/
def optM (r : Option Th) : Multiset Th := (r.toList : Multiset Th)

theorem mem_fm {f : ℕ → Option Th} {N : ℕ} {q : Th} : q ∈ fm f N ↔ ∃ i < N, f i = some q := by
  simp [fm]

theorem fm_update {f : ℕ → Option Th} {N i : ℕ} (hi : i < N) (r : Option Th) :
    fm (Function.update f i r) N = fm (Function.update f i none) N + optM r := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [fm, List.range_succ, List.filterMap_append, ← Multiset.coe_add] at ih ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [ih h]
      have hN : N ≠ i := by omega
      simp only [List.filterMap_cons, List.filterMap_nil, Function.update_of_ne hN, add_assoc,
        add_comm (optM r)]
    · have hfun : ∀ r', (List.range i).filterMap (Function.update f i r') =
          (List.range i).filterMap f := by
        intro r'
        refine List.filterMap_congr fun j hj => ?_
        rw [Function.update_of_ne (by simp at hj; omega)]
      rw [hfun, hfun]
      cases r <;> simp [optM]

theorem fm_erase {f : ℕ → Option Th} {N i : ℕ} (hi : i < N) {q : Th} (hq : f i = some q)
    (r : Option Th) : (fm f N).erase q + optM r = fm (Function.update f i r) N := by
  have h1 : fm f N = q ::ₘ fm (Function.update f i none) N := by
    have := fm_update (f := f) hi (some q)
    rw [← hq, Function.update_eq_self] at this
    rw [this, hq]
    simp [optM, add_comm]
  rw [h1, Multiset.erase_cons_head, fm_update hi r]

theorem fm_ne_zero {f : ℕ → Option Th} {N i : ℕ} (hi : i < N) {q : Th} (hq : f i = some q) :
    fm f N ≠ 0 := by
  intro h
  have : q ∈ fm f N := mem_fm.2 ⟨i, hi, hq⟩
  rw [h] at this
  exact Multiset.notMem_zero q this

theorem fm_congr {f f' : ℕ → Option Th} {N : ℕ} (h : ∀ i < N, f i = f' i) : fm f N = fm f' N := by
  unfold fm
  congr 1
  exact List.filterMap_congr fun j hj => h j (List.mem_range.1 hj)

/-! ## Configurations -/

/-- A configuration: the threads of the two loops and whether the finish thread is pending. -/
structure Cfg where
  cm : Bool → Multiset Th
  fp : Bool

namespace Mach

/-- A step of one of the threads of a multiset. -/
def stepT (S : Multiset Th) (a : Act Op En) (S' : Multiset Th) : Prop :=
  ∃ q ∈ S, ∃ r, M.thStep q a r ∧ S' = S.erase q + optM r

/-- The writer's threads at position `c` of a round: the tails of the words of addresses `< c`
(storing `w'`), fresh words, and the round-end word (index `W`). -/
def wF (w' : ℕ → Bool) (c : ℕ) : ℕ → Option Th := fun i =>
  if i < c then some (.tv i (w' i)) else if i < M.W then some (.hd 0 0)
  else if i = M.W then some .re else none

/-- The reader's threads at position `c`: the stored tails of the addresses `≥ c`. -/
def rF (w : ℕ → Bool) (c : ℕ) : ℕ → Option Th := fun i =>
  if i < c then none else if i < M.W then some (.tv i (w i)) else none

/-- A fresh block. -/
def block : Multiset Th := fm (M.wF (fun _ => false) 0) (M.W + 1)

/-- A step of a loop: a step of one of its threads, or, when all threads are finished, the first
step of a fresh block. -/
def stepC (S : Multiset Th) (a : Act Op En) (S' : Multiset Th) : Prop :=
  M.stepT S a S' ∨ (S = 0 ∧ M.stepT M.block a S')

/-- The step relation of configurations. -/
def cstep (C : Cfg) (a : Act Op En) (C' : Cfg) : Prop :=
  match a.ap with
  | some p => M.stepC (C.cm p) a (C'.cm p) ∧ C'.cm (!p) = C.cm (!p) ∧ C'.fp = C.fp
  | none => C.fp = true ∧ C'.fp = false ∧ C'.cm = C.cm

/-- **The transition system of the encoding.** -/
def lts : LTS Cfg (Act Op En) where
  step := M.cstep
  acc C := C.cm true = 0 ∧ C.cm false = 0 ∧ C.fp = false

/-- The configuration game. -/
abbrev Win (X : Set Cfg) (r : Rec G) : Prop := NWin M.app M.outs M.lts X r

end Mach

/-- The configuration with writer threads `S` (loop `ρ`), reader threads `T`, finish pending. -/
def cfg (ρ : Bool) (S T : Multiset Th) : Cfg := ⟨fun q => if q = ρ then S else T, true⟩

@[simp] theorem cfg_cm_self (ρ : Bool) (S T : Multiset Th) : (cfg ρ S T).cm ρ = S := by
  simp [cfg]

@[simp] theorem cfg_cm_not (ρ : Bool) (S T : Multiset Th) : (cfg ρ S T).cm (!ρ) = T := by
  simp [cfg]

@[simp] theorem cfg_fp (ρ : Bool) (S T : Multiset Th) : (cfg ρ S T).fp = true := rfl

theorem cfg_eq {ρ : Bool} {S T : Multiset Th} {C : Cfg} (h1 : C.cm ρ = S) (h2 : C.cm (!ρ) = T)
    (h3 : C.fp = true) : C = cfg ρ S T := by
  obtain ⟨cm, fp⟩ := C
  simp only at h1 h2 h3
  subst h3
  congr 1
  funext q
  by_cases hq : q = ρ
  · subst hq; simp [h1]
  · have : q = !ρ := by cases q <;> cases ρ <;> simp_all
    subst this; simp [h2]

namespace Mach

variable {M}

/-- A non-accepting configuration game must make a move. -/
theorem Win.move {X : Set Cfg} {r : Rec G} (h : M.Win X r) (hX : ∀ C ∈ X, C.fp = true) :
    ∃ a, M.app a r ∧ ∀ r' ∈ M.outs a r, M.Win (M.lts.post X a) r' := by
  cases h with
  | nil h =>
    obtain ⟨C, hC, -, -, hf⟩ := h
    rw [hX C hC] at hf
    exact absurd hf (by simp)
  | step a ha h => exact ⟨a, ha, h⟩

theorem Win.false_of_empty {r : Rec G} (h : M.Win ∅ r) : False :=
  NWin.false_of_empty (fun a s ha => M.outs_nonempty a s ha) h

/-- The successors of a set of configurations under an action of the loop `p`. -/
theorem mem_post_some {X : Set Cfg} {C' : Cfg} {a : Act Op En} {p : Bool} (hp : a.ap = some p)
    (h : C' ∈ M.lts.post X a) : ∃ C ∈ X,
    M.stepC (C.cm p) a (C'.cm p) ∧ C'.cm (!p) = C.cm (!p) ∧ C'.fp = C.fp := by
  obtain ⟨C₀, hC₀, h⟩ := h
  have h' : M.cstep C₀ a C' := h
  unfold cstep at h'
  rw [hp] at h'
  exact ⟨C₀, hC₀, h'⟩

/-- A game whose configurations all satisfy `P` (and lie in `Y`) — or are absent. -/
theorem Win.cond {X Y : Set Cfg} {r : Rec G} {P : Prop} (h : M.Win X r)
    (hX : ∀ C ∈ X, P ∧ C ∈ Y) : P ∧ M.Win Y r := by
  by_cases hP : P
  · exact ⟨hP, h.mono fun C hC => (hX C hC).2⟩
  · exfalso
    have : X = ∅ := Set.eq_empty_of_forall_notMem fun C hC => hP (hX C hC).1
    subst this
    exact h.false_of_empty

theorem stepC_of_ne {S S' : Multiset Th} {a : Act Op En} (hS : S ≠ 0) :
    M.stepC S a S' ↔ M.stepT S a S' := by
  unfold stepC; simp [hS]

theorem stepC_zero {S' : Multiset Th} {a : Act Op En} :
    M.stepC 0 a S' ↔ M.stepT M.block a S' := by
  unfold stepC stepT
  simp

/-! ## Bits -/

theorem mod_two_pow_succ' (c k : ℕ) :
    c % 2 ^ (k + 1) = c % 2 ^ k + if c.testBit k then 2 ^ k else 0 := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_two_eq_zero_or_one (c / 2 ^ k)
  rcases this with h | h <;> simp [h]

theorem eq_of_testBit_lt {a c m : ℕ} (ha : a < 2 ^ m) (hc : c < 2 ^ m)
    (h : ∀ j < m, a.testBit j = c.testBit j) : a = c := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < m
  · exact h j hj
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-! ## Locating the stepping thread -/

theorem mem_wcomp {w' : ℕ → Bool} {c : ℕ} {cur q : Th}
    (hq : q ∈ fm (Function.update (M.wF w' c) c (some cur)) (M.W + 1)) :
    q = cur ∨ (∃ i, q = .tv i (w' i)) ∨ q = .hd 0 0 ∨ q = .re := by
  obtain ⟨i, -, hi⟩ := mem_fm.1 hq
  by_cases hic : i = c
  · subst hic; simp at hi; exact Or.inl hi.symm
  · rw [Function.update_of_ne hic] at hi
    unfold wF at hi
    split_ifs at hi <;> simp at hi <;> subst hi <;> simp

theorem mem_rcomp {w : ℕ → Bool} {c a : ℕ} {st q : Th}
    (hq : q ∈ fm (Function.update (M.rF w c) a (some st)) (M.W + 1)) :
    q = st ∨ ∃ i, c ≤ i ∧ i < M.W ∧ q = .tv i (w i) := by
  obtain ⟨i, -, hi⟩ := mem_fm.1 hq
  by_cases hia : i = a
  · subst hia; simp at hi; exact Or.inl hi.symm
  · rw [Function.update_of_ne hia] at hi
    unfold rF at hi
    split_ifs at hi with h1 h2 <;> simp at hi
    exact Or.inr ⟨i, by omega, h2, hi.symm⟩

theorem mem_rF {w : ℕ → Bool} {c : ℕ} {q : Th} (hq : q ∈ fm (M.rF w c) (M.W + 1)) :
    ∃ i, c ≤ i ∧ i < M.W ∧ q = .tv i (w i) := by
  obtain ⟨i, -, hi⟩ := mem_fm.1 hq
  unfold rF at hi
  split_ifs at hi with h1 h2 <;> simp at hi
  exact ⟨i, by omega, h2, hi.symm⟩

theorem wF_self {w' : ℕ → Bool} {c : ℕ} (hc : c < M.W) : M.wF w' c c = some (.hd 0 0) := by
  simp [wF, hc]

theorem update_wF_ne_zero {w' : ℕ → Bool} {c : ℕ} (hc : c < M.W) (cur : Th) :
    fm (Function.update (M.wF w' c) c (some cur)) (M.W + 1) ≠ 0 :=
  fm_ne_zero (i := c) (q := cur) (by omega) (by simp)

/-! ## The writer's phases -/

/-- **One address bit of the word in progress** (`wb ρ k`). -/
theorem win_wb {ρ : Bool} {c k : ℕ} {w' : ℕ → Bool} {S T : Multiset Th} {y : Bool} {g : G}
    (hc : c < M.W) (hk : k < M.m)
    (hS : ∀ a S', M.stepC S a S' ↔
      M.stepT (fm (Function.update (M.wF w' c) c (some (.hd k (c % 2 ^ k)))) (M.W + 1)) a S')
    (h : M.Win {cfg ρ S T} ⟨.wb k, c, ρ, y, g⟩) :
    M.Win {cfg ρ (fm (Function.update (M.wF w' c) c (some (.hd (k + 1) (c % 2 ^ (k + 1)))))
      (M.W + 1)) T} ⟨M.nextWb k, c, ρ, y, g⟩ := by
  obtain ⟨a, ha, hw⟩ := h.move (by simp)
  cases a <;> simp [app] at ha
  case wb p k' b =>
  obtain ⟨rfl, rfl, rfl⟩ := ha
  refine (hw _ rfl).mono ?_
  intro C' hC'
  obtain ⟨C, rfl, hst, hrest, hfp⟩ := mem_post_some (p := ρ) rfl hC'
  rw [cfg_cm_self, hS] at hst
  obtain ⟨q, hq, r, hth, hS'⟩ := hst
  have hqe : q = .hd k (c % 2 ^ k) := by
    rcases mem_wcomp hq with rfl | ⟨i, rfl⟩ | rfl | rfl <;> simp [thStep] at hth
    · rfl
    · obtain ⟨rfl, -⟩ := hth; simp [Nat.mod_one]
  subst hqe
  simp only [thStep, true_and] at hth
  obtain ⟨-, rfl⟩ := hth
  rw [fm_erase (i := c) (by omega) (by simp), Function.update_idem, ← mod_two_pow_succ'] at hS'
  refine Set.mem_singleton_iff.2 (cfg_eq hS' ?_ hfp)
  rw [hrest]; simp

/-- **The address of the word in progress**: from the start of a position to the reading phase,
`m` address bits (the first one may start a fresh block). -/
theorem win_wbs {ρ : Bool} {c : ℕ} {w' : ℕ → Bool} {S T : Multiset Th} {y : Bool} {g : G}
    (hm : 0 < M.m) (hc : c < M.W)
    (hS : ∀ a S', M.stepC S a S' ↔ M.stepT (fm (M.wF w' c) (M.W + 1)) a S')
    (h : M.Win {cfg ρ S T} ⟨.wb 0, c, ρ, y, g⟩) :
    M.Win {cfg ρ (fm (Function.update (M.wF w' c) c (some (.hd M.m c))) (M.W + 1)) T}
      ⟨.rv, c, ρ, y, g⟩ := by
  have key : ∀ k, 1 ≤ k → k ≤ M.m →
      M.Win {cfg ρ (fm (Function.update (M.wF w' c) c (some (.hd k (c % 2 ^ k)))) (M.W + 1)) T}
        ⟨M.nextWb (k - 1), c, ρ, y, g⟩ := by
    intro k hk1 hkm
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · refine win_wb hc hm ?_ h
        intro a S'
        rw [hS]
        have : Function.update (M.wF w' c) c (some (.hd 0 (c % 2 ^ 0))) = M.wF w' c := by
          rw [pow_zero, Nat.mod_one, ← wF_self hc, Function.update_eq_self]
        rw [this]
      · have h' := ih hk (by omega)
        have hph : M.nextWb (k - 1) = .wb k := by
          unfold nextWb; rw [if_pos (by omega)]; congr 1; omega
        rw [hph] at h'
        have hS2 : ∀ a S', M.stepC (fm (Function.update (M.wF w' c) c
            (some (.hd k (c % 2 ^ k)))) (M.W + 1)) a S' ↔ M.stepT (fm (Function.update (M.wF w' c)
            c (some (.hd k (c % 2 ^ k)))) (M.W + 1)) a S' :=
          fun a S' => stepC_of_ne (update_wF_ne_zero hc _)
        simpa using win_wb hc (by omega) hS2 h'
  have := key M.m hm le_rfl
  have hph : M.nextWb (M.m - 1) = .rv := by unfold nextWb; rw [if_neg (by omega)]
  rwa [hph, Nat.mod_eq_of_lt hc] at this

/-- **The transducer action** of the word in progress. -/
theorem win_op {ρ : Bool} {c : ℕ} {w' : ℕ → Bool} {T : Multiset Th} {y : Bool} {g : G}
    {cur : Th} (hm : 0 < M.m) (hc : c < M.W) (hcur : cur = .hd M.m c ∨ cur = .nb c)
    (h : M.Win {cfg ρ (fm (Function.update (M.wF w' c) c (some cur)) (M.W + 1)) T}
      ⟨.op, c, ρ, y, g⟩) :
    ∃ o, M.opOK o g y c ∧ M.Win {cfg ρ (fm (Function.update (M.wF w' c) c
      (some (.ic c (M.opW o)))) (M.W + 1)) T} ⟨.inc, c, ρ, y, M.opEff o g⟩ := by
  obtain ⟨a, ha, hw⟩ := h.move (by simp)
  cases a <;> simp [app] at ha
  case op p o =>
  obtain ⟨rfl, hok⟩ := ha
  refine ⟨o, hok, (hw _ rfl).mono ?_⟩
  intro C' hC'
  obtain ⟨C, rfl, hst, hrest, hfp⟩ := mem_post_some (p := ρ) rfl hC'
  rw [cfg_cm_self, stepC_of_ne (update_wF_ne_zero hc _)] at hst
  obtain ⟨q, hq, r, hth, hS'⟩ := hst
  have hqe : q = cur := by
    rcases mem_wcomp hq with rfl | ⟨i, rfl⟩ | rfl | rfl <;> simp [thStep] at hth
    · rfl
    · omega
  subst hqe
  have hr : r = some (.ic c (M.opW o)) := by
    rcases hcur with rfl | rfl <;> simp [thStep] at hth <;> exact hth
  subst hr
  rw [fm_erase (i := c) (by omega) (by simp), Function.update_idem] at hS'
  refine Set.mem_singleton_iff.2 (cfg_eq hS' ?_ hfp)
  rw [hrest]; simp

theorem wF_inc {w' : ℕ → Bool} {c : ℕ} {γ : Bool} (hc : c < M.W) :
    fm (Function.update (M.wF w' c) c (some (.tv c γ))) (M.W + 1) =
      fm (M.wF (Function.update w' c γ) (c + 1)) (M.W + 1) := by
  refine fm_congr fun i _ => ?_
  by_cases hic : i = c
  · subst hic; simp [wF]
  · rw [Function.update_of_ne hic]
    unfold wF
    rw [Function.update_of_ne hic]
    by_cases h1 : i < c
    · simp [h1, show i < c + 1 by omega]
    · simp [h1, show ¬ i < c + 1 by omega]

/-- **The counter increment** ends the position: the next position, or the end of the round. -/
theorem win_inc {ρ : Bool} {c : ℕ} {w' : ℕ → Bool} {T : Multiset Th} {y γ : Bool} {g : G}
    (hc : c < M.W)
    (h : M.Win {cfg ρ (fm (Function.update (M.wF w' c) c (some (.ic c γ))) (M.W + 1)) T}
      ⟨.inc, c, ρ, y, g⟩) :
    M.Win {cfg ρ (fm (M.wF (Function.update w' c γ) (c + 1)) (M.W + 1)) T}
      (if c + 1 < M.W then ⟨.wb 0, c + 1, ρ, y, g⟩ else ⟨.fin, 0, ρ, y, g⟩) := by
  obtain ⟨a, ha, hw⟩ := h.move (by simp)
  have hpost : ∀ a', (∃ k, a' = .inc ρ k) ∨ a' = .wrap ρ →
      M.lts.post {cfg ρ (fm (Function.update (M.wF w' c) c (some (.ic c γ))) (M.W + 1)) T} a' ⊆
      {cfg ρ (fm (M.wF (Function.update w' c γ) (c + 1)) (M.W + 1)) T} := by
    intro a' ha' C' hC'
    have hap : a'.ap = some ρ := by rcases ha' with ⟨k, rfl⟩ | rfl <;> rfl
    obtain ⟨C, rfl, hst, hrest, hfp⟩ := mem_post_some hap hC'
    rw [cfg_cm_self, stepC_of_ne (update_wF_ne_zero hc _)] at hst
    obtain ⟨q, hq, r, hth, hS'⟩ := hst
    have hqe : q = .ic c γ := by
      rcases mem_wcomp hq with rfl | ⟨i, rfl⟩ | rfl | rfl
      · rfl
      all_goals rcases ha' with ⟨k, rfl⟩ | rfl <;> simp [thStep] at hth
    subst hqe
    have hr : r = some (.tv c γ) := by rcases ha' with ⟨k, rfl⟩ | rfl <;> simpa [thStep] using hth
    rw [hr, fm_erase (i := c) (by omega) (by simp), Function.update_idem,
      wF_inc hc] at hS'
    exact Set.mem_singleton_iff.2 (cfg_eq hS' (by rw [hrest]; simp) hfp)
  cases a <;> simp [app] at ha
  case inc p k =>
    obtain ⟨rfl, hk, hbk, hlow⟩ := ha
    have hlt : c + 1 < M.W := by
      have hne : c ≠ 2 ^ M.m - 1 := by
        rintro rfl
        rw [Nat.testBit_two_pow_sub_one] at hbk
        simp [hk] at hbk
      have : 2 ^ M.m - 1 < 2 ^ M.m := by have := Nat.one_le_two_pow (n := M.m); omega
      simp only [W] at hc ⊢
      omega
    rw [if_pos hlt]
    exact (hw _ rfl).mono (hpost _ (Or.inl ⟨k, rfl⟩))
  case wrap p =>
    obtain ⟨rfl, hall⟩ := ha
    have hc1 : c = 2 ^ M.m - 1 := by
      refine eq_of_testBit_lt (m := M.m) hc (by have := Nat.one_le_two_pow (n := M.m); omega) ?_
      intro j hj
      rw [hall j hj, Nat.testBit_two_pow_sub_one]; simp [hj]
    have hnlt : ¬ c + 1 < M.W := by
      simp only [W]; have := Nat.one_le_two_pow (n := M.m); omega
    rw [if_neg hnlt]
    exact (hw _ rfl).mono (hpost _ (Or.inr rfl))

/-! ## The reader's phases -/

theorem rF_ne_zero {w : ℕ → Bool} {c a : ℕ} (ha : a < M.W) (st : Th) :
    fm (Function.update (M.rF w c) a (some st)) (M.W + 1) ≠ 0 :=
  fm_ne_zero (i := a) (q := st) (by omega) (by simp)

/-- The configurations while the address of the cell being read is checked: the candidate cell
`a` agrees with the counter `c` on the bits above `k`. -/
def Yrb (ρ : Bool) (S : Multiset Th) (w : ℕ → Bool) (c : ℕ) (γ : Bool) (k : ℕ) : Set Cfg :=
  {C | ∃ a, c ≤ a ∧ a < M.W ∧ w a = γ ∧ (∀ j, k < j → j < M.m → a.testBit j = c.testBit j) ∧
    C = cfg ρ S (fm (Function.update (M.rF w c) a (some (.tb k a))) (M.W + 1))}

/-- **Reading the value** of a stored tail (`rv`). -/
theorem win_rv {ρ : Bool} {c : ℕ} {w : ℕ → Bool} {S : Multiset Th} {y : Bool} {g : G}
    (hc : c < M.W) (hnb : ¬ M.boot g)
    (h : M.Win {cfg ρ S (fm (M.rF w c) (M.W + 1))} ⟨.rv, c, ρ, y, g⟩) :
    ∃ γ, M.Win (M.Yrb ρ S w c γ (M.m - 1)) ⟨.rb (M.m - 1), c, ρ, γ, g⟩ := by
  obtain ⟨a, ha, hw⟩ := h.move (by simp)
  cases a <;> simp [app] at ha
  case nrd p => exact absurd ha.2 hnb
  case rv p γ =>
  have hp : p = !ρ := by revert ha; cases p <;> cases ρ <;> simp
  subst hp
  refine ⟨γ, (hw _ rfl).mono ?_⟩
  intro C' hC'
  obtain ⟨C, rfl, hst, hrest, hfp⟩ := mem_post_some (p := !ρ) rfl hC'
  have hne : fm (M.rF w c) (M.W + 1) ≠ 0 :=
    fm_ne_zero (i := c) (q := .tv c (w c)) (by omega) (by simp [rF, hc])
  rw [cfg_cm_not, stepC_of_ne hne] at hst
  obtain ⟨q, hq, r, hth, hS'⟩ := hst
  obtain ⟨i, hci, hiW, rfl⟩ := mem_rF hq
  simp only [thStep] at hth
  obtain ⟨rfl, rfl⟩ := hth
  rw [fm_erase (i := i) (by omega) (by simp [rF, hiW, show ¬ i < c by omega])] at hS'
  exact ⟨i, hci, hiW, rfl, fun j hj hjm => by omega, cfg_eq (by simpa using hrest) hS' hfp⟩

/-- **Checking one address bit** of the tail being read (`rb k`, `k ≥ 1`). -/
theorem win_rb_succ {ρ : Bool} {c k : ℕ} {w : ℕ → Bool} {S : Multiset Th} {γ : Bool} {g : G}
    (h : M.Win (M.Yrb ρ S w c γ (k + 1)) ⟨.rb (k + 1), c, ρ, γ, g⟩) :
    M.Win (M.Yrb ρ S w c γ k) ⟨.rb k, c, ρ, γ, g⟩ := by
  obtain ⟨a, ha, hw⟩ := h.move (by rintro C ⟨a, -, -, -, -, rfl⟩; rfl)
  cases a <;> simp [app] at ha
  case rb p k' b =>
  obtain ⟨rfl, hp, rfl⟩ := ha
  have hp' : p = !ρ := by revert hp; cases p <;> cases ρ <;> simp
  subst hp'
  have hph : nextRb (k + 1) = .rb k := by simp [nextRb]
  refine (hw _ rfl).mono ?_
  intro C' hC'
  obtain ⟨C, ⟨a, hca, haW, hwa, hbits, rfl⟩, hst, hrest, hfp⟩ := mem_post_some (p := !ρ) rfl hC'
  rw [cfg_cm_not, stepC_of_ne (rF_ne_zero haW _)] at hst
  obtain ⟨q, hq, r, hth, hS'⟩ := hst
  rcases mem_rcomp hq with rfl | ⟨i, -, -, rfl⟩
  · simp only [thStep, true_and] at hth
    obtain ⟨hb, rfl⟩ := hth
    rw [fm_erase (i := a) (by omega) (by simp), Function.update_idem] at hS'
    simp only [tbNext, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero k)] at hS'
    refine ⟨a, hca, haW, hwa, fun j hj hjm => ?_, cfg_eq ?_ hS' hfp⟩
    · rcases Nat.lt_or_ge (k + 1) j with h1 | h1
      · exact hbits j h1 hjm
      · have : j = k + 1 := by omega
        subst this; exact hb.symm
    · simpa using hrest
  · simp [thStep] at hth

theorem rF_succ {w : ℕ → Bool} {c : ℕ} :
    fm (Function.update (M.rF w c) c none) (M.W + 1) = fm (M.rF w (c + 1)) (M.W + 1) := by
  refine fm_congr fun i _ => ?_
  by_cases hic : i = c
  · subst hic; simp [rF]
  · rw [Function.update_of_ne hic]
    unfold rF
    by_cases h1 : i < c
    · simp [h1, show i < c + 1 by omega]
    · simp [h1, show ¬ i < c + 1 by omega]

/-- **The last address bit** of the tail being read: the tail is the one of the cell `c`. -/
theorem win_rb_zero {ρ : Bool} {c : ℕ} {w : ℕ → Bool} {S : Multiset Th} {γ : Bool} {g : G}
    (hc : c < M.W) (h : M.Win (M.Yrb ρ S w c γ 0) ⟨.rb 0, c, ρ, γ, g⟩) :
    w c = γ ∧ M.Win {cfg ρ S (fm (M.rF w (c + 1)) (M.W + 1))} ⟨.op, c, ρ, γ, g⟩ := by
  obtain ⟨a, ha, hw⟩ := h.move (by rintro C ⟨a, -, -, -, -, rfl⟩; rfl)
  cases a <;> simp [app] at ha
  case rb p k' b =>
  obtain ⟨rfl, hp, rfl⟩ := ha
  have hp' : p = !ρ := by revert hp; cases p <;> cases ρ <;> simp
  subst hp'
  refine (hw _ rfl).cond ?_
  intro C' hC'
  obtain ⟨C, ⟨a, hca, haW, hwa, hbits, rfl⟩, hst, hrest, hfp⟩ := mem_post_some (p := !ρ) rfl hC'
  rw [cfg_cm_not, stepC_of_ne (rF_ne_zero haW _)] at hst
  obtain ⟨q, hq, r, hth, hS'⟩ := hst
  rcases mem_rcomp hq with rfl | ⟨i, -, -, rfl⟩
  · simp only [thStep, true_and] at hth
    obtain ⟨hb, rfl⟩ := hth
    have hac : a = c := by
      refine eq_of_testBit_lt (m := M.m) haW hc fun j hj => ?_
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact hb.symm
      · exact hbits j hj0 hj
    subst hac
    rw [fm_erase (i := a) (by omega) (by simp), Function.update_idem] at hS'
    simp only [tbNext, ↓reduceIte, rF_succ] at hS'
    exact ⟨hwa, Set.mem_singleton_iff.2 (cfg_eq (by simpa using hrest) hS' hfp)⟩
  · simp [thStep] at hth

/-- **Reading a cell** (normal rounds): the value read is the stored bit `w c`. -/
theorem win_read {ρ : Bool} {c : ℕ} {w : ℕ → Bool} {S : Multiset Th} {y : Bool} {g : G}
    (hm : 0 < M.m) (hc : c < M.W) (hnb : ¬ M.boot g)
    (h : M.Win {cfg ρ S (fm (M.rF w c) (M.W + 1))} ⟨.rv, c, ρ, y, g⟩) :
    M.Win {cfg ρ S (fm (M.rF w (c + 1)) (M.W + 1))} ⟨.op, c, ρ, w c, g⟩ := by
  obtain ⟨γ, h1⟩ := win_rv hc hnb h
  have key : ∀ k, k < M.m → ∀ {γ : Bool}, M.Win (M.Yrb ρ S w c γ k) ⟨.rb k, c, ρ, γ, g⟩ →
      M.Win (M.Yrb ρ S w c γ 0) ⟨.rb 0, c, ρ, γ, g⟩ := by
    intro k
    induction k with
    | zero => exact fun _ _ h => h
    | succ k ih => exact fun hk _ h => ih (by omega) (win_rb_succ h)
  obtain ⟨rfl, h2⟩ := win_rb_zero hc (key _ (by omega) h1)
  exact h2

/-- **Not reading** (the boot round): `nrd`. -/
theorem win_nrd {ρ : Bool} {c : ℕ} {w' : ℕ → Bool} {y : Bool} {g : G} (hm : 0 < M.m)
    (hc : c < M.W)
    (h : M.Win {cfg ρ (fm (Function.update (M.wF w' c) c (some (.hd M.m c))) (M.W + 1)) 0}
      ⟨.rv, c, ρ, y, g⟩) :
    M.Win {cfg ρ (fm (Function.update (M.wF w' c) c (some (.nb c))) (M.W + 1)) 0}
      ⟨.op, c, ρ, false, g⟩ := by
  obtain ⟨a, ha, hw⟩ := h.move (by simp)
  cases a <;> simp [app] at ha
  case rv p γ =>
    have hp : p = !ρ := by revert ha; cases p <;> cases ρ <;> simp
    subst hp
    exfalso
    refine ((hw _ rfl).cond (P := False) (Y := ∅) ?_).1
    intro C' hC'
    obtain ⟨C, rfl, hst, -, -⟩ := mem_post_some (p := !ρ) rfl hC'
    rw [cfg_cm_not, stepC_zero] at hst
    obtain ⟨q, hq, r, hth, -⟩ := hst
    obtain ⟨i, -, hi⟩ := mem_fm.1 hq
    unfold wF at hi
    split_ifs at hi with h1 <;> simp at hi <;> subst hi <;> simp [thStep] at hth
    exact absurd h1 (Nat.not_lt_zero _)
  case nrd p =>
  obtain ⟨rfl, -⟩ := ha
  refine (hw _ rfl).mono ?_
  intro C' hC'
  obtain ⟨C, rfl, hst, hrest, hfp⟩ := mem_post_some (p := ρ) rfl hC'
  rw [cfg_cm_self, stepC_of_ne (update_wF_ne_zero hc _)] at hst
  obtain ⟨q, hq, r, hth, hS'⟩ := hst
  have hqe : q = .hd M.m c := by
    rcases mem_wcomp hq with rfl | ⟨i, rfl⟩ | rfl | rfl <;> simp [thStep] at hth
    · rfl
    · omega
  subst hqe
  simp only [thStep, true_and] at hth
  subst hth
  rw [fm_erase (i := c) (by omega) (by simp), Function.update_idem] at hS'
  refine Set.mem_singleton_iff.2 (cfg_eq hS' ?_ hfp)
  rw [hrest]; simp

/-! ## Positions and the sweep -/

/-- **A relational run of the transducer** from the position `c` with control `g` to the end of
the round with control `g'`: at each cell `c` an operation `o` with `opOK o g (rd c) c` (`rd` the
read tape), writing `w' c = opW o`. -/
inductive SRun (M : Mach G Op En) (rd w' : ℕ → Bool) : ℕ → G → G → Prop
  | done {g : G} : SRun M rd w' M.W g g
  | step {c : ℕ} {g g' : G} {o : Op} (hc : c < M.W) (hok : M.opOK o g (rd c) c)
      (hw : w' c = M.opW o) (h : SRun M rd w' (c + 1) (M.opEff o g) g') : SRun M rd w' c g g'

/-- The writer's threads at the start of position `c` (a fresh block at `c = 0`). -/
def WStart (w' : ℕ → Bool) (c : ℕ) (S : Multiset Th) : Prop :=
  ∀ a S', M.stepC S a S' ↔ M.stepT (fm (M.wF w' c) (M.W + 1)) a S'

theorem wStart_fm {w' : ℕ → Bool} {c : ℕ} (hc : c ≤ M.W) :
    M.WStart w' c (fm (M.wF w' c) (M.W + 1)) :=
  fun _ _ => stepC_of_ne (fm_ne_zero (i := M.W) (q := .re) (by omega)
    (by simp [wF, show ¬ M.W < c by omega]))

theorem wStart_zero {w' : ℕ → Bool} : M.WStart w' 0 0 := by
  intro a S'
  rw [stepC_zero]
  have : M.block = fm (M.wF w' 0) (M.W + 1) := fm_congr fun i _ => by simp [wF]
  rw [this]

/-- **A position of a normal round.** -/
theorem win_pos {ρ : Bool} {c : ℕ} {w w' : ℕ → Bool} {S : Multiset Th} {y : Bool} {g : G}
    (hm : 0 < M.m) (hc : c < M.W) (hnb : ¬ M.boot g) (hS : M.WStart w' c S)
    (h : M.Win {cfg ρ S (fm (M.rF w c) (M.W + 1))} ⟨.wb 0, c, ρ, y, g⟩) :
    ∃ o, M.opOK o g (w c) c ∧ M.Win {cfg ρ (fm (M.wF (Function.update w' c (M.opW o)) (c + 1))
      (M.W + 1)) (fm (M.rF w (c + 1)) (M.W + 1))}
      (if c + 1 < M.W then ⟨.wb 0, c + 1, ρ, w c, M.opEff o g⟩
        else ⟨.fin, 0, ρ, w c, M.opEff o g⟩) := by
  have h1 := win_wbs hm hc hS h
  have h2 := win_read hm hc hnb h1
  obtain ⟨o, hok, h3⟩ := win_op hm hc (Or.inl rfl) h2
  exact ⟨o, hok, win_inc hc h3⟩

/-- **A position of the boot round.** -/
theorem win_pos_boot {ρ : Bool} {c : ℕ} {w' : ℕ → Bool} {S : Multiset Th} {y : Bool} {g : G}
    (hm : 0 < M.m) (hc : c < M.W) (hS : M.WStart w' c S)
    (h : M.Win {cfg ρ S 0} ⟨.wb 0, c, ρ, y, g⟩) :
    ∃ o, M.opOK o g false c ∧ M.Win {cfg ρ (fm (M.wF (Function.update w' c (M.opW o)) (c + 1))
      (M.W + 1)) 0}
      (if c + 1 < M.W then ⟨.wb 0, c + 1, ρ, false, M.opEff o g⟩
        else ⟨.fin, 0, ρ, false, M.opEff o g⟩) := by
  have h1 := win_wbs hm hc hS h
  have h2 := win_nrd hm hc h1
  obtain ⟨o, hok, h3⟩ := win_op hm hc (Or.inr rfl) h2
  exact ⟨o, hok, win_inc hc h3⟩

/-- **The sweep**, abstractly: a position lemma for the reader threads `R c`, the read tape `rd`
and an invariant `J` of the control gives a run of the transducer over the whole round. -/
theorem sweep {ρ : Bool} {rd : ℕ → Bool} {R : ℕ → Multiset Th} {J : G → Prop}
    (hpos : ∀ c < M.W, ∀ (w' : ℕ → Bool) (S : Multiset Th) (y : Bool) (g : G), J g →
      M.WStart w' c S → M.Win {cfg ρ S (R c)} ⟨.wb 0, c, ρ, y, g⟩ →
      ∃ o y', M.opOK o g (rd c) c ∧ J (M.opEff o g) ∧
        M.Win {cfg ρ (fm (M.wF (Function.update w' c (M.opW o)) (c + 1)) (M.W + 1)) (R (c + 1))}
          (if c + 1 < M.W then ⟨.wb 0, c + 1, ρ, y', M.opEff o g⟩
            else ⟨.fin, 0, ρ, y', M.opEff o g⟩)) :
    ∀ n c, c + n + 1 = M.W → ∀ (w' : ℕ → Bool) (S : Multiset Th) (y : Bool) (g : G), J g →
      M.WStart w' c S → M.Win {cfg ρ S (R c)} ⟨.wb 0, c, ρ, y, g⟩ →
      ∃ w'' g' y', (∀ i < c, w'' i = w' i) ∧ SRun M rd w'' c g g' ∧
        M.Win {cfg ρ (fm (M.wF w'' M.W) (M.W + 1)) (R M.W)} ⟨.fin, 0, ρ, y', g'⟩ := by
  intro n
  induction n with
  | zero =>
    intro c hcn w' S y g hJ hS h
    obtain ⟨o, y', hok, -, h'⟩ := hpos c (by omega) w' S y g hJ hS h
    rw [if_neg (by omega), show c + 1 = M.W by omega] at h'
    refine ⟨Function.update w' c (M.opW o), _, y', fun i hi => ?_, ?_, h'⟩
    · rw [Function.update_of_ne (by omega)]
    · refine SRun.step (by omega) hok (by simp) ?_
      rw [show c + 1 = M.W by omega]
      exact SRun.done
  | succ n ih =>
    intro c hcn w' S y g hJ hS h
    obtain ⟨o, y', hok, hJ', h'⟩ := hpos c (by omega) w' S y g hJ hS h
    rw [if_pos (by omega)] at h'
    obtain ⟨w'', g', y'', hw'', hrun, hfin⟩ :=
      ih (c + 1) (by omega) _ _ _ _ hJ' (wStart_fm (by omega)) h'
    refine ⟨w'', g', y'', fun i hi => ?_, SRun.step (by omega) hok ?_ hrun, hfin⟩
    · rw [hw'' i (by omega), Function.update_of_ne (by omega)]
    · rw [hw'' c (by omega)]; simp

/-! ## The end of a round and the round lemmas -/

/-- The start of a round: the writer `ρ` has no threads (it starts a fresh block), the reader
holds the tails of the tape `w`. -/
def start (ρ : Bool) (w : ℕ → Bool) : Cfg := cfg ρ 0 (fm (M.rF w 0) (M.W + 1))

theorem rF_W {w : ℕ → Bool} : fm (M.rF w M.W) (M.W + 1) = 0 := by
  have : fm (M.rF w M.W) (M.W + 1) = fm (fun _ => none) (M.W + 1) :=
    fm_congr fun i _ => by
      unfold rF
      split_ifs <;> rfl
  rw [this]; simp [fm]

/-- **The end of a round**: `fin`, or a round-end action all of whose outcomes start the next
round (writer `!ρ`, tape `w'`). -/
theorem win_end {ρ : Bool} {w' : ℕ → Bool} {y : Bool} {g : G}
    (h : M.Win {cfg ρ (fm (M.wF w' M.W) (M.W + 1)) 0} ⟨.fin, 0, ρ, y, g⟩) :
    M.finOK g ∨ ∃ e, M.endOK e g ∧
      ∀ g' ∈ M.endOut e g, M.Win {M.start (!ρ) w'} ⟨.wb 0, 0, !ρ, y, g'⟩ := by
  obtain ⟨a, ha, hw⟩ := h.move (by simp)
  cases a <;> simp [app] at ha
  case fin => exact Or.inl ha
  case rend p e =>
  obtain ⟨rfl, hok⟩ := ha
  refine Or.inr ⟨e, hok, fun g' hg' => (hw _ ⟨g', hg', rfl⟩).mono ?_⟩
  intro C' hC'
  obtain ⟨C, rfl, hst, hrest, hfp⟩ := mem_post_some (p := ρ) rfl hC'
  have hne : fm (M.wF w' M.W) (M.W + 1) ≠ 0 :=
    fm_ne_zero (i := M.W) (q := .re) (by omega) (by simp [wF])
  rw [cfg_cm_self, stepC_of_ne hne] at hst
  obtain ⟨q, hq, r, hth, hS'⟩ := hst
  obtain ⟨i, hi, hfi⟩ := mem_fm.1 hq
  have hiW : i = M.W := by
    by_contra hne'
    unfold wF at hfi
    rw [if_pos (by omega)] at hfi
    simp at hfi; subst hfi; simp [thStep] at hth
  subst hiW
  simp only [wF, lt_irrefl, if_false, if_true, Option.some.injEq] at hfi
  subst hfi
  simp only [thStep] at hth
  subst hth
  rw [fm_erase (i := M.W) (by omega) (by simp [wF])] at hS'
  have hS2 : fm (Function.update (M.wF w' M.W) M.W none) (M.W + 1) = fm (M.rF w' 0) (M.W + 1) :=
    fm_congr fun i hi => by
      by_cases hiW : i = M.W
      · subst hiW; simp [rF]
      · rw [Function.update_of_ne hiW]; simp [wF, rF, show i < M.W by omega]
  rw [hS2] at hS'
  refine Set.mem_singleton_iff.2 (cfg_eq (ρ := !ρ) ?_ (by simpa using hS') hfp)
  rw [hrest]; simp

/-- **The round lemma (soundness), normal rounds.**  If the game is won at the start of a round
(writer `ρ`, tape `w` stored in the tails of the other loop, control `g` not in boot mode), then
the transducer has a run producing a tape `w'` and ending with control `g'`, and either the
finish condition holds for `g'`, or some round-end action `e` is possible for `g'` and every
outcome `g''` wins the next round (writer `!ρ`, tape `w'`). -/
theorem round_sound {ρ : Bool} {w : ℕ → Bool} {y : Bool} {g : G} (hm : 0 < M.m)
    (hboot : ∀ o g, M.boot (M.opEff o g) ↔ M.boot g) (hnb : ¬ M.boot g)
    (h : M.Win {M.start ρ w} ⟨.wb 0, 0, ρ, y, g⟩) :
    ∃ w' g' y', SRun M w w' 0 g g' ∧ (M.finOK g' ∨ ∃ e, M.endOK e g' ∧
      ∀ g'' ∈ M.endOut e g', M.Win {M.start (!ρ) w'} ⟨.wb 0, 0, !ρ, y', g''⟩) := by
  have hpos : ∀ c < M.W, ∀ (w' : ℕ → Bool) (S : Multiset Th) (y : Bool) (g : G),
      ¬ M.boot g → M.WStart w' c S → M.Win {cfg ρ S (fm (M.rF w c) (M.W + 1))}
        ⟨.wb 0, c, ρ, y, g⟩ →
      ∃ o y', M.opOK o g (w c) c ∧ ¬ M.boot (M.opEff o g) ∧
        M.Win {cfg ρ (fm (M.wF (Function.update w' c (M.opW o)) (c + 1)) (M.W + 1))
          (fm (M.rF w (c + 1)) (M.W + 1))}
          (if c + 1 < M.W then ⟨.wb 0, c + 1, ρ, y', M.opEff o g⟩
            else ⟨.fin, 0, ρ, y', M.opEff o g⟩) := by
    intro c hc w' S y g hJ hS h
    obtain ⟨o, hok, h'⟩ := win_pos hm hc hJ hS h
    exact ⟨o, w c, hok, by rwa [hboot], h'⟩
  have hW : 0 + (M.W - 1) + 1 = M.W := by
    have := Nat.one_le_two_pow (n := M.m); simp only [W]; omega
  obtain ⟨w', g', y', -, hrun, hfin⟩ :=
    sweep (R := fun c => fm (M.rF w c) (M.W + 1)) hpos _ 0 hW (fun _ => false) 0 y g hnb
      wStart_zero h
  simp only [rF_W] at hfin
  exact ⟨w', g', y', hrun, win_end hfin⟩

/-- **The round lemma (soundness), the boot round**: no tape is read (every read bit is
`false`); the reader loop has no threads. -/
theorem boot_sound {ρ : Bool} {y : Bool} {g : G} (hm : 0 < M.m)
    (h : M.Win {cfg ρ 0 0} ⟨.wb 0, 0, ρ, y, g⟩) :
    ∃ w' g' y', SRun M (fun _ => false) w' 0 g g' ∧ (M.finOK g' ∨ ∃ e, M.endOK e g' ∧
      ∀ g'' ∈ M.endOut e g', M.Win {M.start (!ρ) w'} ⟨.wb 0, 0, !ρ, y', g''⟩) := by
  have hpos : ∀ c < M.W, ∀ (w' : ℕ → Bool) (S : Multiset Th) (y : Bool) (g : G),
      True → M.WStart w' c S → M.Win {cfg ρ S 0} ⟨.wb 0, c, ρ, y, g⟩ →
      ∃ o y', M.opOK o g false c ∧ True ∧
        M.Win {cfg ρ (fm (M.wF (Function.update w' c (M.opW o)) (c + 1)) (M.W + 1)) 0}
          (if c + 1 < M.W then ⟨.wb 0, c + 1, ρ, y', M.opEff o g⟩
            else ⟨.fin, 0, ρ, y', M.opEff o g⟩) := by
    intro c hc w' S y g _ hS h
    obtain ⟨o, hok, h'⟩ := win_pos_boot hm hc hS h
    exact ⟨o, false, hok, trivial, h'⟩
  have hW : 0 + (M.W - 1) + 1 = M.W := by
    have := Nat.one_le_two_pow (n := M.m); simp only [W]; omega
  obtain ⟨w', g', y', -, hrun, hfin⟩ :=
    sweep (R := fun _ => 0) (J := fun _ => True) hpos _ 0 hW (fun _ => false) 0 y g trivial
      wStart_zero h
  exact ⟨w', g', y', hrun, win_end hfin⟩

end Mach

end TL

end HardTR

end FOND
