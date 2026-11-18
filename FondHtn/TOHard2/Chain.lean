import FondHtn.TOHard2.State
/-!
# Verification chains

A *verification chain* runs over all `2 ^ b` digits of a number.  It is a straight-line program
of *blocks*, one per digit `d`, followed by `FOND.TOHard2.finI`:

`block a = [setEQ, cmp 0, …, cmp (b - 1)] ++ act a ++ [inc]`

* `setEQ`, `cmp r` recompute `EQ` = "the counter equals the challenged index";
* `act a` (`FOND.TOHard2.actP`) acts on a register only if `EQ` holds: the *atomic digit type*
  `a : FOND.TOHard2.AT` relates the input digit and the output digit
  (`FOND.TOHard2.AT.rho`);
* `inc` increments the counter; the overflow after `2 ^ b` blocks is required by `fin`.

**The chain lemma** (`FOND.TOHard2.wp_chain`): from a state with a clean counter, the chain over
the digit types `as` succeeds iff `as` has exactly `2 ^ b` entries, the digit type at the
challenged index `c` accepts the register's value and the state with the transformed register
(and clean counter) satisfies the postcondition.
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HardMP

/-- **Atomic digit types.** -/
inductive AT
  /-- No action. -/
  | id
  /-- The register must be `0` and becomes `1`. -/
  | f01 (rg : Bool)
  /-- The register must be `1` and becomes `0`. -/
  | f10 (rg : Bool)
  /-- The cell digit must be `β`. -/
  | bit (β : Bool)
  /-- The cell digit equals the digit of constant `k`. -/
  | ce (k : ℕ)
  /-- The cell digit is `1`, the digit of constant `k` is `0`. -/
  | cw (k : ℕ)
  /-- The cell digit is `0`, the digit of constant `k` is `1`. -/
  | cv (k : ℕ)
  deriving DecidableEq

namespace AT

/-- The register an atomic type acts on. -/
def reg : AT → Bool
  | f01 rg => rg
  | f10 rg => rg
  | _ => false

/-- The relation of an atomic type at digit `d`, for the constants `cs` (lists of set digits):
the output digit for the input digit `z`, if any. -/
def rho (cs : List (List ℕ)) : AT → ℕ → Bool → Option Bool
  | id, _, z => some z
  | f01 _, _, z => if z = false then some true else none
  | f10 _, _, z => if z = true then some false else none
  | bit β, _, z => if z = β then some z else none
  | ce k, d, z => if z = decide (d ∈ cs.getI k) then some z else none
  | cw k, d, z => if z = true ∧ d ∉ cs.getI k then some z else none
  | cv k, d, z => if z = false ∧ d ∈ cs.getI k then some z else none

/-- The relation is injective in the input. -/
theorem rho_inj {cs : List (List ℕ)} {a : AT} {d : ℕ} {z z' v : Bool}
    (h : a.rho cs d z = some v) (h' : a.rho cs d z' = some v) : z = z' := by
  cases a <;> simp only [rho] at h h' <;> (try split_ifs at h h') <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at h h') <;> (try subst h) <;> (try subst h') <;>
    first | rfl | (cases z <;> cases z' <;> simp_all)

end AT

/-- The program of an atomic type (`b` bits of digit indices, constants `cs`). -/
def actP (b : ℕ) (cs : List (List ℕ)) : AT → List (ℕ × List ASpec)
  | .id => []
  | .f01 rg => [f01I rg]
  | .f10 rg => [f10I rg]
  | .bit β => [bitI β]
  | .ce k => ceAI b k (cs.getI k) ::
      (List.range (cs.getI k).length).map fun j => ceBI b k j ((cs.getI k).getI j)
  | .cw k => cwAI :: (List.range (cs.getI k).length).map fun j => cwBI b k j ((cs.getI k).getI j)
  | .cv k => [cvI b k (cs.getI k)]

/-- The comparisons of the counter with the challenged index. -/
def cmps (b : ℕ) : List (ℕ × List ASpec) := (List.range b).map cmpI

/-- **The block of a digit.** -/
def block (b : ℕ) (cs : List (List ℕ)) (a : AT) : List (ℕ × List ASpec) :=
  setEQ :: cmps b ++ actP b cs a ++ [incI b]

/-- The blocks of a list of digit types. -/
def blocks (b : ℕ) (cs : List (List ℕ)) (as : List AT) : List (ℕ × List ASpec) :=
  as.flatMap (block b cs)

/-- **The chain**: the blocks and the final check. -/
def chain (b : ℕ) (cs : List (List ℕ)) (as : List AT) : List (ℕ × List ASpec) :=
  blocks b cs as ++ [finI]

@[simp] theorem blocks_nil (b : ℕ) (cs : List (List ℕ)) : blocks b cs [] = [] := rfl
@[simp] theorem blocks_cons (b : ℕ) (cs : List (List ℕ)) (a : AT) (as : List AT) :
    blocks b cs (a :: as) = block b cs a ++ blocks b cs as := rfl

/-! ## Semantics of the parts -/

theorem St.setReg_reg (s : St) (rg : Bool) : s.setReg rg (s.reg rg) = s := by
  cases rg <;> rfl

@[simp] theorem St.reg_false (s : St) : s.reg false = s.ib := rfl
@[simp] theorem St.reg_true (s : St) : s.reg true = s.tb := rfl
@[simp] theorem St.setReg_false_ib (s : St) : s.setReg false s.ib = s := rfl
@[simp] theorem St.setReg_true_tb (s : St) : s.setReg true s.tb = s := rfl

/-- A program of tests. -/
theorem wpP_tests {l : List ℕ} {F : ℕ → List ASpec} {Q : ℕ → Prop} {s : St}
    (h : ∀ x ∈ l, ∀ Ψ : Set Cfg, s.cfg ∈ wpI (F x) Ψ ↔ Q x ∧ s.cfg ∈ Ψ) {Ψ : Set Cfg} :
    s.cfg ∈ wpP (l.map F) Ψ ↔ (∀ x ∈ l, Q x) ∧ s.cfg ∈ Ψ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, wpP_cons, h x (by simp), ih fun i hi => h i (by simp [hi])]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem inss_map (l : List ℕ) (f : ℕ → ℕ × List ASpec) : inss (l.map f) = l.map fun x => (f x).2 := by
  simp [inss, Function.comp_def]

section Act

variable {b : ℕ} {cs : List (List ℕ)} (hcs : ∀ k, ∀ e ∈ cs.getI k, e < 2 ^ b)
include hcs

/-- **The program of an atomic type.** -/
theorem wp_act (a : AT) {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpP (inss (actP b cs a)) Ψ ↔
      if s.eq then ∃ v, a.rho cs (s.chkV b) (s.reg a.reg) = some v ∧ (s.setReg a.reg v).cfg ∈ Ψ
      else s.cfg ∈ Ψ := by
  cases a with
  | id =>
    simp only [actP, inss_nil, wpP_nil, AT.rho, Option.some.injEq, exists_eq_left', AT.reg,
      St.setReg_reg, ite_self]
  | f01 rg =>
    simp only [actP, inss_cons, inss_nil, wpP_cons, wpP_nil, wp_f01, AT.rho, AT.reg]
    split_ifs with h1 h2 <;> simp_all
  | f10 rg =>
    simp only [actP, inss_cons, inss_nil, wpP_cons, wpP_nil, wp_f10, AT.rho, AT.reg]
    split_ifs with h1 h2 <;> simp_all
  | bit β =>
    simp only [actP, inss_cons, inss_nil, wpP_cons, wpP_nil, wp_bit, AT.rho, AT.reg]
    cases heq : s.eq
    · simp
    · constructor
      · rintro ⟨h1, h2⟩; exact ⟨s.ib, by simp [St.reg, h1 rfl], by
          rw [show s.setReg false s.ib = s from St.setReg_reg s false]; exact h2⟩
      · rintro ⟨v, hv, h⟩
        simp only [St.reg, Bool.false_eq_true, if_false] at hv
        split_ifs at hv with h'
        cases hv
        exact ⟨fun _ => h', by rwa [show s.setReg false s.ib = s from St.setReg_reg s false] at h⟩
  | ce k =>
    have hks := hcs k
    simp only [actP, inss_cons, wpP_cons, AT.rho, AT.reg, inss_map, St.reg_false]
    rw [wp_ceA hks, wpP_tests (Q := fun j => s.eq = true → s.ib = false → s.chkV b ≠ (cs.getI k).getI j)
      fun j hj Ψ' => wp_ceB (hks _ (getI_memS (List.mem_range.1 hj)))]
    cases heq : s.eq
    · simp
    · simp only [true_implies, forall_const, if_true]
      have key : ((s.ib = true → s.chkV b ∈ cs.getI k) ∧
          ∀ j ∈ List.range (cs.getI k).length, s.ib = false → s.chkV b ≠ (cs.getI k).getI j) ↔
          s.ib = decide (s.chkV b ∈ cs.getI k) := by
        constructor
        · rintro ⟨h1, h2⟩
          cases hib : s.ib
          · symm; rw [decide_eq_false_iff_not]; intro hm
            obtain ⟨j, hj, hje⟩ := exists_getI_of_mem hm
            exact h2 j (List.mem_range.2 hj) hib hje.symm
          · symm; rw [decide_eq_true_iff]; exact h1 hib
        · intro h
          refine ⟨fun hib => by rw [hib] at h; exact of_decide_eq_true h.symm, fun j hj hib hje => ?_⟩
          rw [hib] at h
          have := of_decide_eq_false h.symm
          exact this (hje ▸ getI_memS (List.mem_range.1 hj))
      rw [← and_assoc, key]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨s.ib, by rw [if_pos h1], by rwa [St.setReg_false_ib]⟩
      · rintro ⟨v, hv, h⟩
        split_ifs at hv with h1
        cases hv
        exact ⟨h1, by rwa [St.setReg_false_ib] at h⟩
  | cw k =>
    have hks := hcs k
    simp only [actP, inss_cons, wpP_cons, AT.rho, AT.reg, inss_map, St.reg_false]
    rw [wp_cwA, wpP_tests (Q := fun j => s.eq = true → s.chkV b ≠ (cs.getI k).getI j)
      fun j hj Ψ' => wp_cwB (hks _ (getI_memS (List.mem_range.1 hj)))]
    cases heq : s.eq
    · simp
    · simp only [true_implies, forall_const, if_true]
      have key : (s.ib = true ∧ ∀ j ∈ List.range (cs.getI k).length, s.chkV b ≠ (cs.getI k).getI j) ↔
          (s.ib = true ∧ s.chkV b ∉ cs.getI k) := by
        refine and_congr_right fun _ => ⟨fun h hm => ?_, fun h j hj hje => h (hje ▸ getI_memS (List.mem_range.1 hj))⟩
        obtain ⟨j, hj, hje⟩ := exists_getI_of_mem hm
        exact h j (List.mem_range.2 hj) hje.symm
      rw [← and_assoc, key]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨s.ib, by rw [if_pos h1], by rwa [St.setReg_false_ib]⟩
      · rintro ⟨v, hv, h⟩
        split_ifs at hv with h1
        cases hv
        exact ⟨h1, by rwa [St.setReg_false_ib] at h⟩
  | cv k =>
    have hks := hcs k
    simp only [actP, inss_cons, inss_nil, wpP_cons, wpP_nil, AT.rho, AT.reg, St.reg_false]
    rw [wp_cv hks]
    cases heq : s.eq
    · simp
    · simp only [true_implies, if_true]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨s.ib, by rw [if_pos h1], by rwa [St.setReg_false_ib]⟩
      · rintro ⟨v, hv, h⟩
        split_ifs at hv with h1
        cases hv
        exact ⟨h1, by rwa [St.setReg_false_ib] at h⟩

end Act

/-! ## The counter -/

theorem wp_cmps_list (l : List ℕ) : ∀ {Ψ : Set Cfg} {s : St},
    s.cfg ∈ wpP (inss (l.map cmpI)) Ψ ↔
      { s with eq := s.eq && decide (∀ r ∈ l, s.ctr r = s.chk r) }.cfg ∈ Ψ := by
  induction l with
  | nil => intro Ψ s; simp
  | cons r l ih =>
    intro Ψ s
    rw [List.map_cons, inss_cons, wpP_cons, wp_cmp]
    by_cases hr : s.ctr r = s.chk r
    · rw [if_pos hr, ih]; simp [hr]
    · rw [if_neg hr, ih]; simp [hr]

theorem decide_cmps {b k : ℕ} (hk : k < 2 ^ b) (g : ℕ → Bool) :
    decide (∀ r ∈ List.range b, k.testBit r = g r) = decide (k = ofB g b) := by
  rw [decide_eq_decide]
  simp only [List.mem_range]
  rw [eq_comm, ofB_eq_iff hk]
  exact ⟨fun h r hr => (h r hr).symm, fun h r hr => (h r hr).symm⟩

theorem ofB_false (n : ℕ) : ofB (fun _ => false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ofB_succ_false rfl, ih]

theorem incF_testBit {k j : ℕ} (h1 : ∀ r < j, k.testBit r = true) (h2 : k.testBit j = false) :
    incF k.testBit j = (k + 1).testBit := by
  set g := incF k.testBit j with hg
  have hgj : g j = true := by simp [hg, incF]
  have hlow : ∀ r < j, g r = false := fun r hr => by simp [hg, incF, hr]
  have hhigh : ∀ r, j < r → g r = k.testBit r := fun r hr => by
    simp [hg, incF, show ¬ r < j by omega, show r ≠ j by omega]
  have key : ∀ m, ofB g (j + 1 + m) = ofB k.testBit (j + 1 + m) + 1 := by
    intro m
    induction m with
    | zero =>
      rw [Nat.add_zero, ofB_succ_true hgj, ofB_succ_false h2, ofB_congr (g' := fun _ => false) hlow,
        ofB_false]
      have := ofB_all_true h1; omega
    | succ m ih =>
      rw [← Nat.add_assoc, ofB_succ, ofB_succ, hhigh _ (by omega), ih]; ring
  obtain ⟨N, hN⟩ : ∃ N, N = j + 1 + k := ⟨_, rfl⟩
  have hkN : k + 1 < 2 ^ N := by
    have := Nat.lt_two_pow_self (n := N); omega
  have hgN : ofB g N = k + 1 := by
    rw [hN, key, ofB_testBit (by rw [← hN]; omega)]
  funext r
  by_cases hr : r < N
  · rw [← hgN, testBit_ofB_of_lt _ hr]
  · rw [hhigh r (by omega), Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : k < 2 ^ N)
      (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hkN (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem all_ones_iff {b k : ℕ} (hk : k < 2 ^ b) : (∀ r < b, k.testBit r = true) ↔ k + 1 = 2 ^ b := by
  constructor
  · intro h
    have := ofB_all_true h
    rwa [ofB_testBit hk] at this
  · intro h r hr
    have h' : ofB k.testBit b + 1 = 2 ^ b := by rw [ofB_testBit hk]; exact h
    by_contra hne
    have : ofB k.testBit b + 2 ^ r ≤ 2 ^ b - 1 := by
      have hsplit : ∀ (g : ℕ → Bool) (n : ℕ), r < n → g r = false → ofB g n + 2 ^ r ≤ 2 ^ n - 1 := by
        intro g n
        induction n with
        | zero => intro h; omega
        | succ n ih =>
          intro hrn hgr
          have h2n := ofB_lt g n
          rw [ofB_succ, pow_succ]
          by_cases hrn' : r = n
          · subst hrn'; rw [hgr]; simp; omega
          · have := ih (by omega) hgr
            have : 2 ^ r < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
            cases g n <;> simp <;> omega
      exact hsplit _ _ hr (by simpa using hne)
    have : 0 < 2 ^ r := Nat.two_pow_pos r
    omega

theorem exists_carry {b k : ℕ} (hk : k + 1 < 2 ^ b) :
    ∃ j < b, (∀ r < j, k.testBit r = true) ∧ k.testBit j = false := by
  have hex : ∃ j, j < b ∧ k.testBit j = false := by
    by_contra h
    push_neg at h
    have := (all_ones_iff (b := b) (k := k) (by omega)).1 fun r hr => by simpa using h r hr
    omega
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun r hr => ?_, (Nat.find_spec hex).2⟩
  have := Nat.find_min hex hr
  push_neg at this
  have hrb : r < b := lt_trans hr (Nat.find_spec hex).1
  simpa using this hrb

/-- **The increment on a counter holding `k`.** -/
theorem wp_incCtr {b k : ℕ} (hk : k < 2 ^ b) {Ψ : Set Cfg} {s : St} (hs : s.ctr = k.testBit) :
    s.cfg ∈ wpI (incI b).2 Ψ ↔
      if k + 1 < 2 ^ b then { s with ctr := (k + 1).testBit }.cfg ∈ Ψ
      else { s with ctr := fun _ => false, ov := true }.cfg ∈ Ψ := by
  rw [wp_inc, hs]
  have hclr : clrF k.testBit b = fun _ => false := by
    funext r; simp only [clrF]
    split_ifs with h
    · rfl
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [hclr]
  split_ifs with h
  · constructor
    · rintro (⟨j, hj, h1, h2, h3⟩ | ⟨h1, -⟩)
      · rwa [incF_testBit h1 h2] at h3
      · have := (all_ones_iff hk).1 h1; omega
    · intro h3
      obtain ⟨j, hj, h1, h2⟩ := exists_carry h
      exact Or.inl ⟨j, hj, h1, h2, by rwa [incF_testBit h1 h2]⟩
  · have hall : ∀ r < b, k.testBit r = true := (all_ones_iff hk).2 (by omega)
    constructor
    · rintro (⟨j, hj, h1, h2, h3⟩ | ⟨h1, h3⟩)
      · rw [hall j hj] at h2; exact absurd h2 (by simp)
      · exact h3
    · intro h3; exact Or.inr ⟨hall, h3⟩

/-! ## Blocks and chains -/

/-- The state after a block at digit `k` (`e`: the digit was the challenged one). -/
def nxt (b k : ℕ) (e : Bool) (s : St) : St :=
  if k + 1 < 2 ^ b then { s with ctr := (k + 1).testBit, eq := e }
  else { s with ctr := fun _ => false, ov := true, eq := e }

/-- The state after a chain: clean counter. -/
def fn (s : St) : St := { s with ctr := fun _ => false, ov := false, eq := false }

theorem chkV_setReg (s : St) (rg v : Bool) (b : ℕ) : (s.setReg rg v).chkV b = s.chkV b := by
  cases rg <;> rfl

section Blocks

variable {b : ℕ} {cs : List (List ℕ)} (hcs : ∀ k, ∀ e ∈ cs.getI k, e < 2 ^ b)
include hcs

/-- **One block.** -/
theorem wp_block (a : AT) {k : ℕ} (hk : k < 2 ^ b) {Ψ : Set Cfg} {s : St} (hov : s.ov = false)
    (hs : s.ctr = k.testBit) :
    s.cfg ∈ wpP (inss (block b cs a)) Ψ ↔
      if k = s.chkV b then
        ∃ v, a.rho cs (s.chkV b) (s.reg a.reg) = some v ∧ (nxt b k true (s.setReg a.reg v)).cfg ∈ Ψ
      else (nxt b k false s).cfg ∈ Ψ := by
  simp only [block, cmps, inss_append, inss_cons, inss_nil, wpP_append, wpP_cons, wpP_nil]
  rw [wp_setEQ, and_iff_right hov, wp_cmps_list]
  have h2 : ({ { s with eq := true } with eq := true && decide (∀ r ∈ List.range b,
      ({ s with eq := true } : St).ctr r = ({ s with eq := true } : St).chk r) } : St) =
      { s with eq := decide (k = s.chkV b) } := by
    simp only [Bool.true_and, hs, decide_cmps hk]; rfl
  rw [h2, wp_act hcs]
  have hr : ∀ (e : Bool) (rg : Bool), ({ s with eq := e } : St).reg rg = s.reg rg := fun _ rg => by
    cases rg <;> rfl
  have hc : ∀ (e : Bool), ({ s with eq := e } : St).chkV b = s.chkV b := fun _ => rfl
  by_cases hkc : k = s.chkV b
  · have hd : decide (k = s.chkV b) = true := decide_eq_true hkc
    simp only [hd, if_true, hr, hc, if_pos hkc]
    refine exists_congr fun v => and_congr Iff.rfl ?_
    rw [wp_incCtr hk (by cases a.reg <;> simp [St.setReg, hs])]
    unfold nxt
    split_ifs <;> cases a.reg <;> simp [St.setReg]
  · have hd : decide (k = s.chkV b) = false := decide_eq_false hkc
    simp only [hd, if_false, Bool.false_eq_true, if_neg hkc]
    rw [wp_incCtr hk (by simp [hs])]
    unfold nxt
    split_ifs <;> rfl

/-- A chain after the overflow. -/
theorem wp_blocks_ov (as : List AT) {Ψ : Set Cfg} {s : St} (hov : s.ov = true) :
    s.cfg ∈ wpP (inss (blocks b cs as ++ [finI])) Ψ ↔
      as = [] ∧ { s with ov := false, eq := false }.cfg ∈ Ψ := by
  rcases as with _ | ⟨a, as⟩
  · simp only [blocks_nil, List.nil_append, inss_cons, inss_nil, wpP_cons, wpP_nil, wp_fin, hov]
    try simp
  · simp only [blocks_cons, block, inss_append, inss_cons, wpP_append, wpP_cons, List.append_assoc,
      List.cons_append, wp_setEQ, hov]
    try simp

theorem wp_chain_aux (as : List AT) : ∀ {k : ℕ} {Ψ : Set Cfg} {s : St}, k < 2 ^ b → s.ov = false →
    s.ctr = k.testBit →
    (s.cfg ∈ wpP (inss (blocks b cs as ++ [finI])) Ψ ↔ k + as.length = 2 ^ b ∧
      if k ≤ s.chkV b then
        ∃ v, (as.getD (s.chkV b - k) .id).rho cs (s.chkV b) (s.reg (as.getD (s.chkV b - k) .id).reg)
          = some v ∧ (fn (s.setReg (as.getD (s.chkV b - k) .id).reg v)).cfg ∈ Ψ
      else (fn s).cfg ∈ Ψ) := by
  have hcB : ∀ s : St, s.chkV b < 2 ^ b := fun s => ofB_lt _ _
  induction as with
  | nil =>
    intro k Ψ s hk hov hs
    simp only [blocks_nil, List.nil_append, inss_cons, inss_nil, wpP_cons, wpP_nil, wp_fin, hov]
    simp; omega
  | cons a as ih =>
    intro k Ψ s hk hov hs
    rw [blocks_cons, List.append_assoc, inss_append, wpP_append, wp_block hcs a hk hov hs]
    have hlen : k + (a :: as).length = 2 ^ b ↔ (k + 1) + as.length = 2 ^ b := by simp; omega
    rw [hlen]
    by_cases hkc : k = s.chkV b
    · rw [if_pos hkc, if_pos (le_of_eq hkc)]
      simp only [← hkc, Nat.sub_self, List.getD_cons_zero]
      by_cases hk1 : k + 1 < 2 ^ b
      · have e1 : ∀ v, nxt b k true (s.setReg a.reg v) =
            { s.setReg a.reg v with ctr := (k + 1).testBit, eq := true } := fun v => by
          simp [nxt, hk1]
        simp only [e1]
        constructor
        · rintro ⟨v, hv, h⟩
          rw [ih hk1 (by cases a.reg <;> exact hov) rfl] at h
          obtain ⟨h1, h2⟩ := h
          have hc' : ({ s.setReg a.reg v with ctr := (k + 1).testBit, eq := true } : St).chkV b = k := by
            rw [hkc]; cases a.reg <;> rfl
          rw [hc', if_neg (by omega)] at h2
          exact ⟨h1, v, hv, by convert h2 using 2 <;> cases a.reg <;> rfl⟩
        · rintro ⟨h1, v, hv, h⟩
          refine ⟨v, hv, ?_⟩
          rw [ih hk1 (by cases a.reg <;> exact hov) rfl]
          have hc' : ({ s.setReg a.reg v with ctr := (k + 1).testBit, eq := true } : St).chkV b = k := by
            rw [hkc]; cases a.reg <;> rfl
          rw [hc', if_neg (by omega)]
          exact ⟨h1, by convert h using 2 <;> cases a.reg <;> rfl⟩
      · have e1 : ∀ v, nxt b k true (s.setReg a.reg v) =
            { s.setReg a.reg v with ctr := fun _ => false, ov := true, eq := true } := fun v => by
          simp [nxt, hk1]
        simp only [e1]
        constructor
        · rintro ⟨v, hv, h⟩
          rw [wp_blocks_ov hcs as rfl] at h
          obtain ⟨rfl, h2⟩ := h
          exact ⟨by simp; omega, v, hv, by convert h2 using 2 <;> cases a.reg <;> rfl⟩
        · rintro ⟨h1, v, hv, h⟩
          refine ⟨v, hv, ?_⟩
          rw [wp_blocks_ov hcs as rfl]
          have : as = [] := List.eq_nil_of_length_eq_zero (by omega)
          exact ⟨this, by convert h using 2 <;> cases a.reg <;> rfl⟩
    · rw [if_neg hkc]
      have hle : k ≤ s.chkV b ↔ k + 1 ≤ s.chkV b := by omega
      by_cases hk1 : k + 1 < 2 ^ b
      · have e1 : nxt b k false s = { s with ctr := (k + 1).testBit, eq := false } := by
          simp [nxt, hk1]
        rw [e1, ih (s := { s with ctr := (k + 1).testBit, eq := false }) hk1 hov rfl]
        have hc' : ({ s with ctr := (k + 1).testBit, eq := false } : St).chkV b = s.chkV b := rfl
        rw [hc']
        refine and_congr_right fun _ => ?_
        by_cases hkc' : k + 1 ≤ s.chkV b
        · rw [if_pos hkc', if_pos (by omega)]
          have hidx : (a :: as).getD (s.chkV b - k) .id = as.getD (s.chkV b - (k + 1)) .id := by
            rw [show s.chkV b - k = (s.chkV b - (k + 1)) + 1 by omega]; rfl
          rw [hidx]
          refine exists_congr fun v => and_congr ?_ ?_
          · cases (as.getD (s.chkV b - (k + 1)) .id).reg <;> rfl
          · cases (as.getD (s.chkV b - (k + 1)) .id).reg <;> rfl
        · rw [if_neg hkc', if_neg (by omega)]
          rfl
      · have e1 : nxt b k false s = { s with ctr := fun _ => false, ov := true, eq := false } := by
          simp [nxt, hk1]
        rw [e1, wp_blocks_ov hcs as rfl, if_neg (by have := hcB s; omega)]
        constructor
        · rintro ⟨rfl, h⟩; exact ⟨by simp; omega, h⟩
        · rintro ⟨h1, h⟩; exact ⟨List.eq_nil_of_length_eq_zero (by omega), h⟩

/-- **The chain lemma.** -/
theorem wp_chain (as : List AT) {Ψ : Set Cfg} {s : St} (hov : s.ov = false)
    (hs : s.ctr = fun _ => false) :
    s.cfg ∈ wpP (inss (chain b cs as)) Ψ ↔ as.length = 2 ^ b ∧
      ∃ v, (as.getD (s.chkV b) .id).rho cs (s.chkV b) (s.reg (as.getD (s.chkV b) .id).reg) = some v ∧
        (fn (s.setReg (as.getD (s.chkV b) .id).reg v)).cfg ∈ Ψ := by
  rw [chain, wp_chain_aux hcs as (Nat.two_pow_pos b) hov (by rw [hs]; funext r; simp)]
  simp

end Blocks

end TOHard2

end FOND
