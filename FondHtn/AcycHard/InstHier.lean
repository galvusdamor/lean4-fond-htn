import FondHtn.AcycHard.InstEnc
import FondHtn.AcycHard.HierGame
/-!
# The hierarchy of the Savitch instance

Compound names (`FOND.AcycHard.Sav.CN`): powers of blocks by binary doubling (`pw b j` has the
expansion `blockᵇ^(2^j)`, `pown b` the expansion `blockᵇ^(cnt b)`), the cells, the control root
and, set-kind, multiplicities by doubling (`spw`, `spown`) and the pool root.  The hierarchy
specification `FOND.AcycHard.Sav.Inst.hs` and the expansions of the roots.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

namespace Sav

open HTN TM

/-- The blocks that are repeated. -/
inductive Blk
  | WT
  | WR
  | PRE
  | STEP
  | ROUND
  | REF
  | TR
  deriving DecidableEq

/-- The chains of the pool that are repeated. -/
inductive SB (k : ℕ)
  | blank
  | fresh (τ : SymK k)
  | opt (o : OK k)

/-- **The compound names.** -/
inductive CN (k : ℕ)
  | pw (b : Blk) (j : ℕ)
  | pown (b : Blk)
  | cellB
  | newc (τ : SymK k)
  | ctl
  | spw (s : SB k) (j : ℕ)
  | spown (s : SB k)
  | pool

variable {k : ℕ}

/-- **The data of an instance**: cells `S`, rounds `K + 1`, refills `R`, supply `n`, bits `B`,
input length `L`, the symbols and the options. -/
structure Inst (k : ℕ) where
  S : ℕ
  K : ℕ
  R : ℕ
  n : ℕ
  B : ℕ
  L : ℕ
  syms : List (SymK k)
  opts : List (OK k)

namespace Inst

variable (I : Inst k)

/-- The repetitions of the blocks. -/
def cnt : Blk → ℕ
  | .WT => I.S
  | .WR => I.S
  | .PRE => FSpec.tri I.S
  | .STEP => I.S
  | .ROUND => I.K
  | .REF => I.R
  | .TR => I.S

/-- The multiplicities of the pool chains. -/
def cntS : SB k → ℕ
  | .blank => I.S
  | .fresh _ => I.n
  | .opt _ => I.n

end Inst

/-- The items of a block. -/
def blkItems : Blk → List (ℕ ⊕ CN k)
  | .WT => [.inl (nC (.opn .T)), .inl (nC (.cls .T))]
  | .WR => [.inl (nC (.opn .R)), .inl (nC (.cls .R))]
  | .PRE => [.inl (nC (.opn .T)), .inl (nC (.cls .T)), .inl (nC (.opn .R)), .inl (nC (.cls .R))]
  | .STEP => [.inr (.pown .WT), .inr (.pown .WR), .inl (nC (.opn .F)), .inl (nC (.cls .F)),
      .inl (nC (.opn .I)), .inl (nC (.cls .I)), .inl (nC (.opn .U)), .inl (nC (.cls .U))]
  | .ROUND => [.inr (.pown .STEP), .inl (nC (.plain .half))]
  | .REF => [.inl (nC .refill)]
  | .TR => [.inl (nP (k := k) .tick), .inl (nP (k := k) .res)]

/-- The item of a pool chain. -/
def sbItem : SB k → ℕ ⊕ CN k
  | .blank => .inr .cellB
  | .fresh τ => .inr (.newc τ)
  | .opt o => .inl (nP (.opt o))

namespace Inst

variable (I : Inst k)

/-- **The bodies.** -/
def bodyCN : CN k → List (ℕ ⊕ CN k)
  | .pw b 0 => blkItems b
  | .pw b (j + 1) => [.inr (.pw b j), .inr (.pw b j)]
  | .pown b => ((List.range I.B).filter fun j => (I.cnt b).testBit j).map fun j => .inr (.pw b j)
  | .cellB => [.inr (.pown .TR), .inl (nP (k := k) (.fin none))]
  | .newc τ => [.inl (nP (.init τ)), .inr (.pown .TR), .inl (nP (.fin τ))]
  | .ctl => [.inr (.pown .PRE), .inr (.pown .STEP), .inl (nC (.plain .toRd)), .inr (.pown .ROUND),
      .inr (.pown .STEP), .inl (nC (.plain .halfChk)), .inr (.pown .STEP), .inl (nC (.plain .acc)),
      .inr (.pown .REF)]
  | .spw s 0 => [sbItem s]
  | .spw s (j + 1) => [.inr (.spw s j), .inr (.spw s j)]
  | .spown s => ((List.range I.B).filter fun j => (I.cntS s).testBit j).map fun j => .inr (.spw s j)
  | .pool => (.inr (.spown .blank) :: I.syms.map fun τ => .inr (.spown (.fresh τ))) ++
      I.opts.map fun o => .inr (.spown (.opt o))

end Inst

/-- Set-kind names. -/
def isSetCN : CN k → Bool
  | .spw _ _ => true
  | .spown _ => true
  | .pool => true
  | _ => false

/-- Offsets of the ranks. -/
def offB (B : ℕ) : Blk → ℕ
  | .STEP => B + 1
  | .ROUND => 2 * B + 2
  | _ => 0

def offS (B : ℕ) : SB k → ℕ
  | .opt _ => 0
  | _ => B + 2

/-- **The ranks.** -/
def rkCN (B : ℕ) : CN k → ℕ
  | .pw b j => offB B b + j + 1
  | .pown b => offB B b + B + 1
  | .cellB => B + 2
  | .newc _ => B + 2
  | .ctl => 3 * B + 4
  | .spw s j => offS B s + j + 1
  | .spown s => offS B s + B + 1
  | .pool => 2 * B + 4

theorem rk_lt_CN (I : Inst k) (x y : CN k) (h : Sum.inr y ∈ I.bodyCN x) : rkCN I.B y < rkCN I.B x := by
  cases x with
  | pw b j =>
    cases j with
    | zero => cases b <;> simp [Inst.bodyCN, blkItems] at h <;> rcases h with rfl | rfl <;>
        simp [rkCN, offB] <;> omega
    | succ j => simp [Inst.bodyCN] at h; subst h; simp [rkCN]
  | pown b =>
    simp only [Inst.bodyCN, List.mem_map, List.mem_filter, List.mem_range, Sum.inr.injEq] at h
    obtain ⟨j, ⟨hj, -⟩, rfl⟩ := h
    simp [rkCN]; omega
  | cellB => simp [Inst.bodyCN] at h; subst h; simp [rkCN, offB]
  | newc τ => simp [Inst.bodyCN] at h; subst h; simp [rkCN, offB]
  | ctl => simp [Inst.bodyCN] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rkCN, offB] <;> omega
  | spw s j =>
    cases j with
    | zero => cases s <;> simp [Inst.bodyCN, sbItem] at h <;> subst h <;> simp [rkCN, offS]
    | succ j => simp [Inst.bodyCN] at h; subst h; simp [rkCN]
  | spown s =>
    simp only [Inst.bodyCN, List.mem_map, List.mem_filter, List.mem_range, Sum.inr.injEq] at h
    obtain ⟨j, ⟨hj, -⟩, rfl⟩ := h
    simp [rkCN]; omega
  | pool =>
    simp only [Inst.bodyCN, List.mem_append, List.mem_cons, List.mem_map, Sum.inr.injEq] at h
    rcases h with (rfl | ⟨τ, -, rfl⟩) | ⟨o, -, rfl⟩ <;> simp [rkCN, offS] <;> omega

theorem seq_items_CN (I : Inst k) (x y : CN k) (hx : isSetCN x = false) (h : Sum.inr y ∈ I.bodyCN x) :
    isSetCN y = false := by
  cases x with
  | pw b j =>
    cases j with
    | zero => cases b <;> simp [Inst.bodyCN, blkItems] at h <;> rcases h with rfl | rfl <;> rfl
    | succ j => simp [Inst.bodyCN] at h; subst h; rfl
  | pown b =>
    simp only [Inst.bodyCN, List.mem_map, Sum.inr.injEq] at h
    obtain ⟨j, -, rfl⟩ := h; rfl
  | cellB => simp [Inst.bodyCN] at h; subst h; rfl
  | newc τ => simp [Inst.bodyCN] at h; subst h; rfl
  | ctl => simp [Inst.bodyCN] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  | spw s j => simp [isSetCN] at hx
  | spown s => simp [isSetCN] at hx
  | pool => simp [isSetCN] at hx

/-! ## Codes of the compound names -/

def codeBlk : Blk → ℕ
  | .WT => 0
  | .WR => 1
  | .PRE => 2
  | .STEP => 3
  | .ROUND => 4
  | .REF => 5
  | .TR => 6

def codeSB : SB k → ℕ
  | .blank => Nat.pair 0 0
  | .fresh τ => Nat.pair 1 (codeSym τ)
  | .opt o => Nat.pair 2 (codeO o)

def codeCN : CN k → ℕ
  | .pw b j => Nat.pair 0 (Nat.pair (codeBlk b) j)
  | .pown b => Nat.pair 1 (codeBlk b)
  | .cellB => Nat.pair 2 0
  | .newc τ => Nat.pair 3 (codeSym τ)
  | .ctl => Nat.pair 4 0
  | .spw s j => Nat.pair 5 (Nat.pair (codeSB s) j)
  | .spown s => Nat.pair 6 (codeSB s)
  | .pool => Nat.pair 7 0

theorem codeBlk_inj : Function.Injective codeBlk := by
  intro a b h; cases a <;> cases b <;> simp_all [codeBlk]

theorem codeSB_inj : Function.Injective (codeSB (k := k)) := by
  intro a b h
  rcases a with _ | a | a <;> rcases b with _ | b | b <;>
    simp only [codeSB, Nat.pair_eq_pair] at h <;> (try omega)
  · rfl
  · rw [codeSym_inj h.2]
  · rw [codeO_inj h.2]

theorem codeCN_inj : Function.Injective (codeCN (k := k)) := by
  intro a b h
  rcases a with ⟨a, i⟩ | a | _ | a | _ | ⟨a, i⟩ | a | _ <;>
    rcases b with ⟨b, j⟩ | b | _ | b | _ | ⟨b, j⟩ | b | _ <;>
    simp only [codeCN, Nat.pair_eq_pair] at h <;> (try omega)
  · rw [codeBlk_inj h.2.1, h.2.2]
  · rw [codeBlk_inj h.2]
  · rfl
  · rw [codeSym_inj h.2]
  · rfl
  · rw [codeSB_inj h.2.1, h.2.2]
  · rw [codeSB_inj h.2]
  · rfl

/-! ## The hierarchy specification on numbers -/

open Classical in
/-- Decoding of compound names. -/
noncomputable def decCN (c : ℕ) : Option (CN k) :=
  if h : ∃ x : CN k, codeCN x = c then some (Classical.choose h) else none

theorem decCN_code (x : CN k) : decCN (codeCN x) = some x := by
  have h : ∃ y : CN k, codeCN y = codeCN x := ⟨x, rfl⟩
  rw [decCN, dif_pos h]
  exact congrArg some (codeCN_inj (Classical.choose_spec h))

theorem decCN_some {c : ℕ} {x : CN k} (h : decCN c = some x) : c = codeCN x := by
  unfold decCN at h
  split_ifs at h with h'
  · cases h; exact (Classical.choose_spec h').symm

/-- An item with coded compound names. -/
def itemCode : ℕ ⊕ CN k → ℕ ⊕ ℕ := Sum.map id codeCN

namespace Inst

variable (I : Inst k)

/-- **The hierarchy specification.** -/
noncomputable def hs : HSpec ℕ ℕ where
  body c := match decCN (k := k) c with
    | some x => (I.bodyCN x).map itemCode
    | none => []
  isSet c := match decCN (k := k) c with
    | some x => isSetCN x
    | none => false
  rk c := match decCN (k := k) c with
    | some x => rkCN I.B x
    | none => 0
  rk_lt c d h := by
    cases hc : decCN (k := k) c with
    | none => simp [hc] at h
    | some x =>
      simp only [hc, List.mem_map] at h
      obtain ⟨y, hy, he⟩ := h
      rcases y with a | y
      · simp [itemCode] at he
      · simp only [itemCode, Sum.map_inr, Sum.inr.injEq] at he
        subst he
        simp only [decCN_code]
        exact rk_lt_CN I x y hy
  seq_items c hc d h := by
    cases hc' : decCN (k := k) c with
    | none => simp [hc'] at h
    | some x =>
      simp only [hc'] at hc h
      simp only [List.mem_map] at h
      obtain ⟨y, hy, he⟩ := h
      rcases y with a | y
      · simp [itemCode] at he
      · simp only [itemCode, Sum.map_inr, Sum.inr.injEq] at he
        subst he
        simp only [decCN_code]
        exact seq_items_CN I x y hc hy

theorem hs_body (x : CN k) : I.hs.body (codeCN x) = (I.bodyCN x).map itemCode := by
  simp [hs, decCN_code]

theorem hs_isSet (x : CN k) : I.hs.isSet (codeCN x) = isSetCN x := by
  simp [hs, decCN_code]

end Inst

/-! ## Repetitions -/

/-- `m` copies of a list, concatenated. -/
def rep {α : Type} (l : List α) (m : ℕ) : List α := (List.replicate m l).flatten

theorem rep_add {α : Type} (l : List α) (a b : ℕ) : rep l (a + b) = rep l a ++ rep l b := by
  simp only [rep, List.replicate_add, List.flatten_append]

theorem rep_zero {α : Type} (l : List α) : rep l 0 = [] := rfl
theorem rep_one {α : Type} (l : List α) : rep l 1 = l := by simp [rep]

theorem rep_map {α β : Type} (f : α → β) (l : List α) (m : ℕ) : (rep l m).map f = rep (l.map f) m := by
  simp [rep, List.map_flatten, List.map_replicate]

theorem flatMap_rep_pow {α : Type} (E : List α) :
    ∀ ls : List ℕ, ls.flatMap (fun j => rep E (2 ^ j)) = rep E (ls.map (2 ^ ·)).sum := by
  intro ls
  induction ls with
  | nil => rfl
  | cons j ls ih => simp only [List.flatMap_cons, ih, List.map_cons, List.sum_cons, rep_add]

theorem sum_bits : ∀ (B n : ℕ), n < 2 ^ B →
    (((List.range B).filter fun j => n.testBit j).map (2 ^ ·)).sum = n := by
  intro B
  induction B with
  | zero => intro n h; simp at h; subst h; rfl
  | succ B ih =>
    intro n hn
    have hlow : (((List.range B).filter fun j => n.testBit j).map (2 ^ ·)).sum = n % 2 ^ B := by
      rw [← ih (n % 2 ^ B) (Nat.mod_lt _ (Nat.two_pow_pos B))]
      congr 2
      refine List.filter_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow, decide_eq_true (List.mem_range.1 hj), Bool.true_and]
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, hlow]
    have hdiv : n / 2 ^ B < 2 := Nat.div_lt_of_lt_mul (by rw [pow_succ] at hn; linarith)
    have hdm := Nat.div_add_mod n (2 ^ B)
    have hq : n / 2 ^ B % 2 = n / 2 ^ B := Nat.mod_eq_of_lt hdiv
    by_cases hb : n.testBit B = true
    · have h1 : n / 2 ^ B = 1 := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, hq] at hb; exact hb
      simp [hb]; rw [h1, mul_one] at hdm; omega
    · have h1 : n / 2 ^ B = 0 := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, hq] at hb; omega
      simp [hb]; rw [h1, mul_zero] at hdm; omega

theorem nsmul_add_pow {α : Type} (E : Multiset α) :
    ∀ ls : List ℕ, (ls.map fun j => 2 ^ j • E).sum = (ls.map (2 ^ ·)).sum • E := by
  intro ls
  induction ls with
  | nil => simp
  | cons j ls ih => simp only [List.map_cons, List.sum_cons, ih, add_nsmul]

/-! ## Expansions -/

namespace Inst

variable (I : Inst k)

/-- The expansion of a block. -/
noncomputable def blkE (b : Blk) : List ℕ := ((blkItems (k := k) b).map itemCode).flatMap I.hs.exI

theorem exI_inl_list (l : List ℕ) : (l.map Sum.inl).flatMap I.hs.exI = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, HSpec.exI_inl, ih]

theorem exI_code (x : CN k) : I.hs.exI (.inr (codeCN x)) = ((I.bodyCN x).map itemCode).flatMap I.hs.exI := by
  rw [HSpec.exI_inr, hs_body]

theorem exI_pw (b : Blk) : ∀ j, I.hs.exI (.inr (codeCN (k := k) (.pw b j))) = rep (I.blkE b) (2 ^ j) := by
  intro j
  induction j with
  | zero => rw [exI_code]; simp [bodyCN, blkE, rep_one]
  | succ j ih =>
    rw [exI_code]
    simp only [bodyCN, List.map_cons, List.map_nil, itemCode, Sum.map_inr, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [show (Sum.inr (codeCN (CN.pw b j)) : ℕ ⊕ ℕ) = .inr (codeCN (.pw b j)) from rfl, ih,
      ← rep_add, pow_succ, mul_two]

theorem exI_pown (b : Blk) (hb : I.cnt b < 2 ^ I.B) :
    I.hs.exI (.inr (codeCN (k := k) (.pown b))) = rep (I.blkE b) (I.cnt b) := by
  rw [exI_code]
  simp only [bodyCN, List.map_map]
  rw [List.flatMap_map]
  have : ∀ j, (I.hs.exI ∘ itemCode ∘ fun j => (Sum.inr (CN.pw b j) : ℕ ⊕ CN k)) j =
      rep (I.blkE b) (2 ^ j) := fun j => exI_pw I b j
  simp only [Function.comp_def] at this
  simp only [Function.comp_def, itemCode, Sum.map_inr] at *
  rw [List.flatMap_congr (fun j _ => this j), flatMap_rep_pow, sum_bits _ _ hb]

end Inst

/-! ## The window programs as repetitions -/

theorem expand_append {G P : Type} (a b : List (AcycHard.WI G P)) :
    WSys.expand (a ++ b) = WSys.expand a ++ WSys.expand b := by
  induction a with
  | nil => rfl
  | cons w a ih => cases w <;> simp [WSys.expand, ih]

theorem expand_rep {G P : Type} (l : List (AcycHard.WI G P)) : ∀ m, WSys.expand (rep l m) = rep (WSys.expand l) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [show m + 1 = 1 + m by omega, rep_add, rep_add, expand_append, ih, rep_one, rep_one]

theorem replicate_rep {α : Type} (x : α) (m : ℕ) : List.replicate m x = rep [x] m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, show m + 1 = 1 + m by omega, rep_add, rep_one, ← ih]; rfl

theorem preW_eq {P : Type} : ∀ m, FSpec.preW (P := P) m = rep [.win .T, .win .R] m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [FSpec.preW, show m + 1 = 1 + m by omega, rep_add, rep_one, ih]; rfl

section Prog

variable {Sym O D P : Type} [DecidableEq Sym] [DecidableEq O] (X : FSpec Sym O D P)

theorem expandQ_append (a b : List (Option P)) : X.expandQ (a ++ b) = X.expandQ a ++ X.expandQ b := by
  induction a with
  | nil => rfl
  | cons x a ih => cases x <;> simp [FSpec.expandQ, ih]

theorem expandQ_replicate : ∀ m, X.expandQ (List.replicate m none) = rep (FSpec.stepW X.S) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, show m + 1 = 1 + m by omega, rep_add, rep_one, ← ih]; rfl

theorem stepW_eq (n : ℕ) : FSpec.stepW (P := P) n =
    rep [.win .T] n ++ rep [.win .R] n ++ [.win .F, .win .I, .win .U] := by
  rw [FSpec.stepW, replicate_rep, replicate_rep, List.append_assoc]

end Prog

/-- The window program of the rounds. -/
theorem expandQ_rnd (X : FSpec (SymK k) (OK k) (DK k) Pl) (S : ℕ) : ∀ K, X.expandQ (rnd S K) =
    rep (X.expandQ (sweep S ++ [some .half])) K ++
      X.expandQ (sweep S ++ [some .halfChk] ++ sweep S ++ [some .acc]) := by
  intro K
  induction K with
  | zero => simp [rnd, rep_zero]
  | succ K ih =>
    rw [rnd, expandQ_append, ih, show K + 1 = 1 + K by omega, rep_add, rep_one]
    simp only [List.append_assoc]

/-! ## The expansion of the control root -/

namespace Inst

variable (I : Inst k)

theorem blkE_inl (b : Blk) (l : List ℕ) (h : (blkItems (k := k) b) = l.map Sum.inl) : I.blkE b = l := by
  rw [blkE, h, List.map_map]
  exact I.exI_inl_list l

theorem blkE_WT : I.blkE .WT = [nC (.opn .T), nC (.cls .T)] := I.blkE_inl _ _ rfl
theorem blkE_WR : I.blkE .WR = [nC (.opn .R), nC (.cls .R)] := I.blkE_inl _ _ rfl
theorem blkE_PRE : I.blkE .PRE = [nC (.opn .T), nC (.cls .T), nC (.opn .R), nC (.cls .R)] :=
  I.blkE_inl _ _ rfl
theorem blkE_REF : I.blkE .REF = [nC .refill] := I.blkE_inl _ _ rfl
theorem blkE_TR : I.blkE .TR = [nP (k := k) .tick, nP (k := k) .res] := I.blkE_inl _ _ rfl

variable (hcnt : ∀ b, I.cnt b < 2 ^ I.B)
include hcnt

theorem blkE_STEP : I.blkE .STEP = rep [nC (.opn .T), nC (.cls .T)] I.S ++
    rep [nC (.opn .R), nC (.cls .R)] I.S ++
    [nC (.opn .F), nC (.cls .F), nC (.opn .I), nC (.cls .I), nC (.opn .U), nC (.cls .U)] := by
  simp only [blkE, blkItems, List.map_cons, List.map_nil, itemCode, Sum.map_inr, Sum.map_inl,
    id, List.flatMap_cons, List.flatMap_nil, HSpec.exI_inl]
  rw [I.exI_pown .WT (hcnt _), I.exI_pown .WR (hcnt _), blkE_WT, blkE_WR]
  simp [cnt, List.append_assoc]

theorem blkE_ROUND : I.blkE .ROUND = rep (I.blkE .STEP) I.S ++ [nC (.plain .half)] := by
  conv_lhs => rw [blkE]
  simp only [blkItems, List.map_cons, List.map_nil, itemCode, Sum.map_inr, Sum.map_inl,
    id, List.flatMap_cons, List.flatMap_nil, HSpec.exI_inl]
  rw [show (Sum.inr (codeCN (CN.pown Blk.STEP)) : ℕ ⊕ ℕ) = .inr (codeCN (k := k) (.pown .STEP)) from rfl,
    I.exI_pown .STEP (hcnt _)]
  simp [cnt]

/-- **The expansion of the control root** is the expanded window program with the refills. -/
theorem exI_ctl : I.hs.exI (.inr (codeCN (k := k) .ctl)) =
    (WSys.expand (FSpec.preW (FSpec.tri I.S) ++ (spec (Q := Fin k) (Γ := Option Bool) I.L I.S).expandQ
      (prog I.S I.K)) ++ List.replicate I.R CI.refill).map nC := by
  rw [exI_code]
  simp only [bodyCN, List.map_cons, List.map_nil, itemCode, Sum.map_inr, Sum.map_inl, id,
    List.flatMap_cons, List.flatMap_nil, HSpec.exI_inl, List.append_nil]
  have e := fun b => I.exI_pown b (hcnt b)
  simp only [itemCode, Sum.map_inr] at e
  simp only [e]
  rw [prog, expandQ_append, expandQ_append, sweep, expandQ_replicate, expandQ_rnd, expandQ_append,
    expandQ_append, expandQ_append, expandQ_append, sweep, expandQ_replicate, preW_eq]
  simp only [spec, autSpec, FSpec.expandQ, expand_append, expand_rep, List.map_append, rep_map,
    WSys.expand, replicate_rep, stepW_eq, blkE_PRE, blkE_REF, blkE_STEP I hcnt, blkE_ROUND I hcnt, cnt,
    List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

end Inst

/-! ## The expansion of the pool root -/

theorem cellR_rep {Sym O : Type} (τ : Sym) :
    ∀ m, FSpec.cellR (O := O) τ m = rep [PA.tick, PA.res] m ++ [PA.fin τ] := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [FSpec.cellR, ih, show m + 1 = 1 + m by omega, rep_add, rep_one]; rfl

namespace Inst

variable (I : Inst k)

/-- The fixed window system of the instance. -/
abbrev X0 : FSpec (SymK k) (OK k) (DK k) Pl := spec (Q := Fin k) (Γ := Option Bool) I.L I.S

/-- The chain of a pool item. -/
def sbChain : SB k → List (PA (SymK k) (OK k))
  | .blank => FSpec.cellR none I.S
  | .fresh τ => I.X0.newCell τ
  | .opt o => [.opt o]

/-- The supply. -/
def supply : Multiset (List (PA (SymK k) (OK k))) :=
  (I.syms.map fun τ => I.n • ({I.X0.newCell τ} : Multiset _)).sum +
    (I.opts.map fun o => I.n • ({[PA.opt o]} : Multiset _)).sum

variable (hcnt : ∀ b, I.cnt b < 2 ^ I.B)
include hcnt

theorem exI_TR : I.hs.exI (.inr (codeCN (k := k) (.pown .TR))) = (rep [PA.tick, PA.res] I.S).map (nP (k := k)) := by
  rw [I.exI_pown .TR (hcnt _), blkE_TR, rep_map]; rfl

theorem exI_sb (s : SB k) : I.hs.exI (itemCode (sbItem s)) = (I.sbChain s).map nP := by
  cases s with
  | blank =>
    simp only [sbItem, itemCode, Sum.map_inr]
    rw [exI_code]
    simp only [bodyCN, List.map_cons, List.map_nil, itemCode, Sum.map_inr, Sum.map_inl, id,
      List.flatMap_cons, List.flatMap_nil, HSpec.exI_inl, List.append_nil]
    rw [show (Sum.inr (codeCN (CN.pown Blk.TR)) : ℕ ⊕ ℕ) = .inr (codeCN (k := k) (.pown .TR)) from rfl,
      I.exI_TR hcnt]
    simp [sbChain, cellR_rep]
  | fresh τ =>
    simp only [sbItem, itemCode, Sum.map_inr]
    rw [exI_code]
    simp only [bodyCN, List.map_cons, List.map_nil, itemCode, Sum.map_inr, Sum.map_inl, id,
      List.flatMap_cons, List.flatMap_nil, HSpec.exI_inl, List.append_nil]
    rw [show (Sum.inr (codeCN (CN.pown Blk.TR)) : ℕ ⊕ ℕ) = .inr (codeCN (k := k) (.pown .TR)) from rfl,
      I.exI_TR hcnt]
    simp [sbChain, FSpec.newCell, cellR_rep, X0, spec, autSpec]
  | opt o => simp [sbItem, itemCode, HSpec.exI_inl, sbChain]

theorem sbChain_ne (s : SB k) : I.sbChain s ≠ [] := by
  cases s <;> simp [sbChain, FSpec.newCell, cellR_rep]

theorem exMI_sb (s : SB k) : I.hs.exMI (itemCode (sbItem s)) = {(I.sbChain s).map nP} := by
  rw [HSpec.exMI_nonset, I.exI_sb hcnt, HSpec.filt, if_neg (by simpa using I.sbChain_ne hcnt s)]
  intro c hc
  cases s with
  | blank => simp only [sbItem, itemCode, Sum.map_inr, Sum.inr.injEq] at hc; subst hc
             rw [hs_isSet]; rfl
  | fresh τ => simp only [sbItem, itemCode, Sum.map_inr, Sum.inr.injEq] at hc; subst hc
               rw [hs_isSet]; rfl
  | opt o => simp [sbItem, itemCode] at hc

theorem exMI_spw (s : SB k) : ∀ j, I.hs.exMI (.inr (codeCN (k := k) (.spw s j))) =
    2 ^ j • ({(I.sbChain s).map nP} : Multiset _) := by
  intro j
  induction j with
  | zero =>
    rw [HSpec.exMI_set (H := I.hs) (c := codeCN (.spw s 0)) (by rw [hs_isSet]; rfl), hs_body]
    simp [bodyCN, I.exMI_sb hcnt]
  | succ j ih =>
    rw [HSpec.exMI_set (H := I.hs) (c := codeCN (.spw s (j+1))) (by rw [hs_isSet]; rfl), hs_body]
    simp only [bodyCN, List.map_cons, List.map_nil, itemCode, Sum.map_inr, List.sum_cons,
      List.sum_nil, add_zero]
    rw [show (Sum.inr (codeCN (CN.spw s j)) : ℕ ⊕ ℕ) = .inr (codeCN (k := k) (.spw s j)) from rfl,
      ih, ← add_nsmul, pow_succ, mul_two]

theorem exMI_spown (s : SB k) (hsb : I.cntS s < 2 ^ I.B) :
    I.hs.exMI (.inr (codeCN (k := k) (.spown s))) = I.cntS s • ({(I.sbChain s).map nP} : Multiset _) := by
  rw [HSpec.exMI_set (H := I.hs) (c := codeCN (.spown s)) (by rw [hs_isSet]; rfl), hs_body]
  simp only [bodyCN, List.map_map]
  have : ∀ j, (I.hs.exMI ∘ itemCode ∘ fun j => (Sum.inr (CN.spw s j) : ℕ ⊕ CN k)) j =
      2 ^ j • ({(I.sbChain s).map nP} : Multiset _) := fun j => I.exMI_spw hcnt s j
  rw [List.map_congr_left (fun j _ => this j), nsmul_add_pow, sum_bits _ _ hsb]

/-- **The expansion of the pool root**: `S` blank cells and the supply. -/
theorem exMI_pool (hS : I.S < 2 ^ I.B) (hn : I.n < 2 ^ I.B) :
    I.hs.exMI (.inr (codeCN (k := k) .pool)) =
      (FSpec.liveR (Multiset.replicate I.S (none, I.S)) + I.supply).map (List.map nP) := by
  rw [HSpec.exMI_set (H := I.hs) (c := codeCN (.pool)) (by rw [hs_isSet]; rfl), hs_body]
  simp only [bodyCN, List.map_cons, List.map_append, List.map_map, List.sum_cons, List.sum_append]
  have h1 : ∀ s : SB k, I.cntS s < 2 ^ I.B := fun s => by cases s <;> assumption
  rw [show itemCode (Sum.inr (CN.spown (k := k) SB.blank)) = .inr (codeCN (.spown .blank)) from rfl,
    I.exMI_spown hcnt _ (h1 _)]
  have e1 : ∀ τ, (I.hs.exMI ∘ itemCode ∘ fun τ => (Sum.inr (CN.spown (SB.fresh τ)) : ℕ ⊕ CN k)) τ =
      I.n • ({(I.X0.newCell τ).map nP} : Multiset _) := fun τ => I.exMI_spown hcnt _ (h1 _)
  have e2 : ∀ o, (I.hs.exMI ∘ itemCode ∘ fun o => (Sum.inr (CN.spown (SB.opt o)) : ℕ ⊕ CN k)) o =
      I.n • ({[nP (PA.opt o)]} : Multiset _) := fun o => I.exMI_spown hcnt _ (h1 _)
  rw [List.map_congr_left (fun τ _ => e1 τ), List.map_congr_left (fun o _ => e2 o)]
  have hm : ∀ {β : Type} (l : List β) (g : β → Multiset (List (PA (SymK k) (OK k)))),
      (l.map g).sum.map (List.map nP) = (l.map fun x => (g x).map (List.map nP)).sum := by
    intro β l g
    induction l with
    | nil => simp
    | cons x l ih => simp [ih]
  simp only [supply, FSpec.liveR, Multiset.map_add, hm, Multiset.map_nsmul, Multiset.map_singleton,
    Multiset.map_replicate, Multiset.map_map, Function.comp_def, sbChain, cntS,
    ← Multiset.nsmul_singleton, List.map_cons, List.map_nil, add_assoc]

end Inst

end Sav

end AcycHard

end FOND
