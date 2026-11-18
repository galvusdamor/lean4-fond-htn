import FondHtn.HardTR.Tab
import FondHtn.HardMP.Encoding
import FondHtn.TOHard2.Chain
/-!
# CB22 Thm 5, P2: the states and actions of the tableau transducer as FOND facts and actions

The states `TL.Rec (TT.Ctl S)` of the transducer machine `X.mach` are encoded as configurations
`HardMP.Cfg` (Boolean fields, `FOND.HardTR.TE.toCfg`):

* the phase one-hot (`fPh`), the round counter bitwise (`fC j`), the Boolean fields `par`, `sym`,
  `boot`, `bo`, `cy`, `dec`, `zi` (`fB 0 … fB 6`);
* the claim `σ` one-hot by a code `cS` (`fSg`), the guess `gs` one-hot (`fGs`), the comparators
  `cl`, `ch` one-hot (`fCl`, `fCh`) and the schedule counter one-hot (`fSc`).

Every action of the machine is an action specification `FOND.HardTR.TE.aspec` (conjunctions of
field literals, effects setting fields).  On *good* states (counter `< 2 ^ m`, phases, guess and
schedule in range) applicability and outcomes agree: `FOND.HardTR.TE.app_iff`,
`FOND.HardTR.TE.out_eq`.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TE

open TL TT HardMP

/-! ## Codes of the fields -/

def codePh : Ph → ℕ
  | .wb k => Nat.pair 0 k
  | .rv => Nat.pair 1 0
  | .rb k => Nat.pair 2 k
  | .op => Nat.pair 3 0
  | .inc => Nat.pair 4 0
  | .fin => Nat.pair 5 0
  | .drain => Nat.pair 6 0

theorem codePh_inj : Function.Injective codePh := by
  intro a b h
  cases a <;> cases b <;> simp only [codePh, Nat.pair_eq_pair] at h <;> (try omega) <;> simp_all

def codeGs : Option ℕ → ℕ
  | none => 0
  | some ℓ => ℓ + 1

theorem codeGs_inj : Function.Injective codeGs := by
  intro a b h
  cases a <;> cases b <;> simp_all [codeGs]

def codeOrd : Ordering → ℕ
  | .lt => 0
  | .eq => 1
  | .gt => 2

theorem codeOrd_inj : Function.Injective codeOrd := by
  intro a b h
  cases a <;> cases b <;> simp_all [codeOrd]

def fPh (x : Ph) : ℕ := Nat.pair 0 (codePh x)
def fC (j : ℕ) : ℕ := Nat.pair 1 j
/-- Boolean fields: `0` par, `1` sym, `2` boot, `3` bo, `4` cy, `5` dec, `6` zi. -/
def fB (i : ℕ) : ℕ := Nat.pair 2 i
def fSg (x : ℕ) : ℕ := Nat.pair 3 x
def fGs (o : Option ℕ) : ℕ := Nat.pair 4 (codeGs o)
def fCl (o : Ordering) : ℕ := Nat.pair 5 (codeOrd o)
def fCh (o : Ordering) : ℕ := Nat.pair 6 (codeOrd o)
def fSc (n : ℕ) : ℕ := Nat.pair 7 n
/-- A field that is never set. -/
def fNo : ℕ := Nat.pair 8 0

/-! ## The encoding of states -/

variable {S : Type} (cS : S → ℕ)

def bvalT (par sym : Bool) (g : Ctl S) : ℕ → Bool
  | 0 => par
  | 1 => sym
  | 2 => g.boot
  | 3 => g.bo
  | 4 => g.cy
  | 5 => g.dec
  | 6 => g.zi
  | _ => false

def bval (r : Rec (Ctl S)) (x : ℕ) : Bool := bvalT r.par r.sym r.g x

/-- The value of a field. -/
def fv (r : Rec (Ctl S)) (t x : ℕ) : Bool :=
  match t with
  | 0 => decide (codePh r.ph = x)
  | 1 => r.c.testBit x
  | 2 => bval r x
  | 3 => decide (cS r.g.σ = x)
  | 4 => decide (codeGs r.g.gs = x)
  | 5 => decide (codeOrd r.g.cl = x)
  | 6 => decide (codeOrd r.g.ch = x)
  | 7 => decide (r.g.s = x)
  | _ => false

/-- **The encoded configuration** of a state. -/
def toCfg (r : Rec (Ctl S)) : HardMP.Cfg := ⟨fun f => fv cS r (Nat.unpair f).1 (Nat.unpair f).2, none⟩

variable {cS}

theorem val_pair (r : Rec (Ctl S)) (t x : ℕ) : (toCfg cS r).val (Nat.pair t x) = fv cS r t x := by
  simp [toCfg, Nat.unpair_pair]

@[simp] theorem val_fPh (r : Rec (Ctl S)) (x : Ph) : (toCfg cS r).val (fPh x) = decide (r.ph = x) := by
  rw [fPh, val_pair]; simp [fv, codePh_inj.eq_iff]

@[simp] theorem val_fC (r : Rec (Ctl S)) (j : ℕ) : (toCfg cS r).val (fC j) = r.c.testBit j := by
  rw [fC, val_pair]; rfl

@[simp] theorem val_fB (r : Rec (Ctl S)) (i : ℕ) : (toCfg cS r).val (fB i) = bval r i := by
  rw [fB, val_pair]; rfl

@[simp] theorem val_fSg (r : Rec (Ctl S)) (x : ℕ) : (toCfg cS r).val (fSg x) = decide (cS r.g.σ = x) := by
  rw [fSg, val_pair]; rfl

@[simp] theorem val_fGs (r : Rec (Ctl S)) (o : Option ℕ) : (toCfg cS r).val (fGs o) = decide (r.g.gs = o) := by
  rw [fGs, val_pair]; simp [fv, codeGs_inj.eq_iff]

@[simp] theorem val_fCl (r : Rec (Ctl S)) (o : Ordering) : (toCfg cS r).val (fCl o) = decide (r.g.cl = o) := by
  rw [fCl, val_pair]; simp [fv, codeOrd_inj.eq_iff]

@[simp] theorem val_fCh (r : Rec (Ctl S)) (o : Ordering) : (toCfg cS r).val (fCh o) = decide (r.g.ch = o) := by
  rw [fCh, val_pair]; simp [fv, codeOrd_inj.eq_iff]

@[simp] theorem val_fSc (r : Rec (Ctl S)) (n : ℕ) : (toCfg cS r).val (fSc n) = decide (r.g.s = n) := by
  rw [fSc, val_pair]; rfl

@[simp] theorem val_fNo (r : Rec (Ctl S)) : (toCfg cS r).val fNo = false := by
  rw [fNo, val_pair]; rfl

@[simp] theorem toCfg_cur (r : Rec (Ctl S)) : (toCfg cS r).cur = none := rfl

/-- Configurations are equal if they agree on all fields `pair t x`. -/
theorem cfg_ext {c d : HardMP.Cfg} (h : ∀ t x, c.val (Nat.pair t x) = d.val (Nat.pair t x)) (hc : c.cur = d.cur) :
    c = d := by
  obtain ⟨cv, cc⟩ := c
  obtain ⟨dv, dc⟩ := d
  simp only at hc h ⊢
  subst hc
  congr 1
  funext f
  have := h (Nat.unpair f).1 (Nat.unpair f).2
  rwa [Nat.pair_unpair] at this

/-! ## Literals -/

/-- The field `f` required true when `b`. -/
def pos (f : ℕ) (b : Bool) : List ℕ := if b then [f] else []

/-- The field `f` required false when `¬ b`. -/
def neg (f : ℕ) (b : Bool) : List ℕ := if b then [] else [f]

/-- A static condition (the never-set field `fNo` when it fails). -/
noncomputable def chk (c : Prop) : List ℕ := by classical exact if c then [] else [fNo]

theorem lit_iff {c : HardMP.Cfg} {f : ℕ} {b : Bool} :
    ((∀ x ∈ pos f b, c.val x = true) ∧ ∀ x ∈ neg f b, c.val x = false) ↔ c.val f = b := by
  cases b <;> simp [pos, neg]

theorem chk_iff (r : Rec (Ctl S)) (c : Prop) : (∀ x ∈ chk c, (toCfg cS r).val x = true) ↔ c := by
  classical
  unfold chk
  split_ifs with h <;> simp [h]

/-! ## The action specifications -/

variable (X : Spec S) (cS) (allS : List S)

def sgCodes : List ℕ := allS.map fun s => fSg (cS s)
def gsCodes : List ℕ := fGs none :: (List.range X.no).map fun ℓ => fGs (some ℓ)
def clCodes : List ℕ := [fCl .lt, fCl .eq, fCl .gt]
def chCodes : List ℕ := [fCh .lt, fCh .eq, fCh .gt]
def scCodes : List ℕ := (List.range (X.P.length + 1)).map fSc

/-- The number of address bits. -/
abbrev mm : ℕ := X.e + 2

/-- The address of a special position. -/
def spA (s : ℕ) : ℕ := 2 * X.P.getD s 0 + 1

/-- The literals and effects of an operation: (true fields, false fields, added, deleted). -/
noncomputable def opSpec : Op → List ℕ × List ℕ × List ℕ × List ℕ
  | .t gs b w =>
    (pos (fB 1) b ++ pos (fB 3) (xor b w) ++
        (match gs with | none => [] | some ℓ => fSg (cS (X.sg ℓ)) :: chk (ℓ < X.no)),
      [fB 2, fC 0] ++ neg (fB 1) b ++ neg (fB 3) (xor b w) ++
        (match gs with | none => [] | some _ => (List.range (mm X)).map fC),
      (match gs with | none => [] | some ℓ => [fGs (some ℓ)]),
      (if b then [fB 3] else []) ++ (match gs with | none => [] | some _ => gsCodes X))
  | .i dec b w sp =>
    (pos (fB 1) b ++ [fC 0] ++ pos (fB 4) (xor b w) ++ pos (fB 5) dec ++
        (match sp with
          | none => []
          | some (ℓ, s) => fGs (some ℓ) :: fSc s :: chk (s < X.P.length) ++
              ((List.range (mm X)).filter fun j => (spA X s).testBit j).map fC),
      [fB 2] ++ neg (fB 1) b ++ neg (fB 4) (xor b w) ++ neg (fB 5) dec ++
        (match sp with
          | none => []
          | some (_, s) => ((List.range (mm X)).filter fun j => !(spA X s).testBit j).map fC),
      (if w = X.kb X.lo sp then [] else [fCl (if w then .gt else .lt)]) ++
        (if w = X.kb X.hi sp then [] else [fCh (if w then .gt else .lt)]) ++
        (match sp with | none => [] | some (_, s) => [fSc (s + 1)]),
      (if (if dec then !b else b) then [] else [fB 4]) ++ (if w then [fB 6] else []) ++
        (if w = X.kb X.lo sp then [] else clCodes) ++ (if w = X.kb X.hi sp then [] else chCodes) ++
        (match sp with | none => [] | some (_, s) => [fSc s]))
  | .bt w => ([fB 2] ++ pos (fC (X.e + 1)) (!w), [fC 0] ++ neg (fC (X.e + 1)) (!w), [], [])
  | .bi w => ([fB 2, fC 0], if w then [fC (X.e + 1)] else [], [], [])

/-- The effect setting the control to `rst σ cy dec`. -/
def rstEff (σ : S) (cy dec : Bool) : List ℕ × List ℕ :=
  ([fSg (cS σ), fB 3, fB 6, fGs none, fCl .eq, fCh .eq, fSc 0] ++ pos (fB 4) cy ++ pos (fB 5) dec,
    [fB 2] ++ sgCodes cS allS ++ gsCodes X ++ clCodes ++ chCodes ++ scCodes X ++ neg (fB 4) cy ++
      neg (fB 5) dec)

/-- The literals and the outcomes `(σ, cy, dec)` of a round end. -/
noncomputable def endSpec : En S → List ℕ × List ℕ × List (S × Bool × Bool)
  | .boot σ => ([fB 2] ++ chk (σ ∈ X.acc), [], [(σ, false, false)])
  | .norm z l c r => (pos (fB 6) z ++ [fSg (cS (X.F (if z then none else some l) c r))],
      [fB 2, fB 3, fB 4] ++ neg (fB 6) z,
      [(c, false, false), (r, true, false)] ++ (if z then [] else [(l, true, true)]))

/-- **The action specification of an action of the machine.** -/
noncomputable def aspec : Act Op (En S) → ASpec
  | .wb p k b => ([fPh (.wb k)] ++ pos (fB 0) p ++ pos (fC k) b ++ chk (k < mm X),
      neg (fB 0) p ++ neg (fC k) b, [([fPh (X.mach.nextWb k)], [fPh (.wb k)])], [], [])
  | .rv p γ => ([fPh .rv] ++ pos (fB 0) (!p), neg (fB 0) (!p),
      [([fPh (.rb (mm X - 1))] ++ pos (fB 1) γ, [fPh .rv] ++ neg (fB 1) γ)], [], [])
  | .rb p k b => ([fPh (.rb k)] ++ pos (fB 0) (!p) ++ pos (fC k) b, neg (fB 0) (!p) ++ neg (fC k) b,
      [([fPh (Mach.nextRb k)], [fPh (.rb k)])], [], [])
  | .op p o => ([fPh .op] ++ pos (fB 0) p ++ (opSpec cS X o).1, neg (fB 0) p ++ (opSpec cS X o).2.1,
      [([fPh .inc] ++ (opSpec cS X o).2.2.1, [fPh .op] ++ (opSpec cS X o).2.2.2)], [], [])
  | .inc p k => ([fPh .inc] ++ pos (fB 0) p ++ (List.range k).map fC ++ chk (k < mm X),
      neg (fB 0) p ++ [fC k], [([fPh (.wb 0), fC k], [fPh .inc] ++ (List.range k).map fC)], [], [])
  | .wrap p => ([fPh .inc] ++ pos (fB 0) p ++ (List.range (mm X)).map fC, neg (fB 0) p,
      [([fPh .fin], [fPh .inc] ++ (List.range (mm X)).map fC)], [], [])
  | .rend p e => ([fPh .fin] ++ pos (fB 0) p ++ (endSpec cS X e).1, neg (fB 0) p ++ (endSpec cS X e).2.1,
      (endSpec cS X e).2.2.map fun q => ([fPh (.wb 0)] ++ pos (fB 0) (!p) ++ (rstEff cS X allS q.1 q.2.1 q.2.2).1,
        [fPh .fin] ++ neg (fB 0) (!p) ++ (rstEff cS X allS q.1 q.2.1 q.2.2).2), [], [])
  | .nrd p => ([fPh .rv] ++ pos (fB 0) p ++ [fB 2], neg (fB 0) p, [([fPh .op], [fPh .rv, fB 1])], [], [])
  | .dr _ => ([fPh .drain], [], [([], [])], [], [])
  | .fin => ([fPh .fin, fB 3, fSc X.P.length, fCh .lt], [fB 2, fB 4, fGs none, fCl .lt],
      [([fPh .drain], [fPh .fin])], [], [])

/-! ## Good states -/

/-- The states in range. -/
structure Good (r : Rec (Ctl S)) : Prop where
  c_lt : r.c < 2 ^ mm X
  wb_lt : ∀ k, r.ph = .wb k → k < mm X
  rb_lt : ∀ k, r.ph = .rb k → k < mm X
  gs_lt : ∀ ℓ, r.g.gs = some ℓ → ℓ < X.no
  s_le : r.g.s ≤ X.P.length

/-! ## Applicability -/

section App

variable {X cS allS} {r : Rec (Ctl S)}

theorem app_def (a : ASpec) (c : HardMP.Cfg) (h : a.cpre = []) :
    a.App c ↔ (∀ f ∈ a.pre, c.val f = true) ∧ ∀ f ∈ a.neg, c.val f = false := by
  simp [ASpec.App, h]

theorem bits_zero_iff (hc : r.c < 2 ^ mm X) :
    (∀ f ∈ (List.range (mm X)).map fC, (toCfg cS r).val f = false) ↔ r.c = 0 := by
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    val_fC]
  constructor
  · intro h
    exact Eq.symm (TL.Mach.eq_of_testBit_lt (Nat.two_pow_pos _) hc fun j hj => by simp [h j hj])
  · intro h j _; simp [h]

end App

section App2

variable {X cS allS} {r : Rec (Ctl S)}

theorem app_wb (hG : Good X r) (p : Bool) (k : ℕ) (b : Bool) :
    (aspec cS X allS (.wb p k b)).App (toCfg cS r) ↔ X.mach.app (.wb p k b) r := by
  rw [app_def _ _ rfl]
  have h := hG.wb_lt k
  simp only [aspec, ASpec.pre, ASpec.neg, List.forall_mem_append, chk_iff, Mach.app]
  cases p <;> cases b <;> simp [pos, neg, bval] <;> tauto

theorem app_rv (p γ : Bool) :
    (aspec cS X allS (.rv p γ)).App (toCfg cS r) ↔ X.mach.app (.rv p γ) r := by
  rw [app_def _ _ rfl]
  simp only [aspec, ASpec.pre, ASpec.neg, List.forall_mem_append, Mach.app]
  cases p <;> simp [pos, neg, bval] <;> tauto

theorem app_rb (hG : Good X r) (p : Bool) (k : ℕ) (b : Bool) :
    (aspec cS X allS (.rb p k b)).App (toCfg cS r) ↔ X.mach.app (.rb p k b) r := by
  rw [app_def _ _ rfl]
  simp only [aspec, ASpec.pre, ASpec.neg, List.forall_mem_append, Mach.app]
  cases p <;> cases b <;> simp [pos, neg, bval] <;> tauto

theorem app_nrd (p : Bool) :
    (aspec cS X allS (.nrd p)).App (toCfg cS r) ↔ X.mach.app (.nrd p) r := by
  rw [app_def _ _ rfl]
  simp only [aspec, ASpec.pre, ASpec.neg, List.forall_mem_append, Mach.app, Spec.mach]
  cases p <;> simp [pos, neg, bval] <;> tauto

theorem app_dr (p : Bool) :
    (aspec cS X allS (.dr p)).App (toCfg cS r) ↔ X.mach.app (.dr p) r := by
  rw [app_def _ _ rfl]
  simp [aspec, ASpec.pre, ASpec.neg, Mach.app]

theorem app_fin (hG : Good X r) :
    (aspec cS X allS .fin).App (toCfg cS r) ↔ X.mach.app .fin r := by
  rw [app_def _ _ rfl]
  simp only [aspec, ASpec.pre, ASpec.neg, Mach.app, Spec.mach, Spec.finOK]
  simp [bval, Option.isSome_iff_ne_none]
  tauto

theorem app_inc (p : Bool) (k : ℕ) :
    (aspec cS X allS (.inc p k)).App (toCfg cS r) ↔ X.mach.app (.inc p k) r := by
  rw [app_def _ _ rfl]
  simp only [aspec, ASpec.pre, ASpec.neg, List.forall_mem_append, chk_iff, Mach.app, Spec.mach]
  cases p <;> simp [pos, neg, bval] <;> tauto

theorem app_wrap (p : Bool) :
    (aspec cS X allS (.wrap p)).App (toCfg cS r) ↔ X.mach.app (.wrap p) r := by
  rw [app_def _ _ rfl]
  simp only [aspec, ASpec.pre, ASpec.neg, List.forall_mem_append, Mach.app, Spec.mach]
  cases p <;> simp [pos, neg, bval] <;> tauto

theorem bits_eq_iff {v : ℕ} (hc : r.c < 2 ^ mm X) (hv : v < 2 ^ mm X) :
    ((∀ f ∈ ((List.range (mm X)).filter fun j => v.testBit j).map fC, (toCfg cS r).val f = true) ∧
      ∀ f ∈ ((List.range (mm X)).filter fun j => !v.testBit j).map fC, (toCfg cS r).val f = false) ↔
      r.c = v := by
  constructor
  · rintro ⟨h1, h2⟩
    refine TL.Mach.eq_of_testBit_lt hc hv fun j hj => ?_
    cases hb : v.testBit j
    · have := h2 (fC j) (List.mem_map.2 ⟨j, List.mem_filter.2 ⟨List.mem_range.2 hj, by simp [hb]⟩, rfl⟩)
      simpa using this
    · have := h1 (fC j) (List.mem_map.2 ⟨j, List.mem_filter.2 ⟨List.mem_range.2 hj, by simp [hb]⟩, rfl⟩)
      simpa using this
  · rintro rfl
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
      simpa using (List.mem_filter.1 hj).2
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
      simpa using (List.mem_filter.1 hj).2

theorem spA_lt (hX : X.Valid) {s : ℕ} (hs : s < X.P.length) : spA X s < 2 ^ mm X := by
  have h := hX.P_lt (X.P.getD s 0) (by rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem hs)
  simp only [spA, mm, pow_add, Spec.B] at h ⊢
  omega

set_option maxHeartbeats 4000000 in
theorem app_op (hS : Function.Injective cS) (hX : X.Valid) (hG : Good X r) (p : Bool) (o : Op) :
    (aspec cS X allS (.op p o)).App (toCfg cS r) ↔ X.mach.app (.op p o) r := by
  rw [app_def _ _ rfl]
  simp only [aspec, ASpec.pre, ASpec.neg, List.forall_mem_append, Mach.app, Spec.mach]
  cases o with
  | t gs b w =>
    cases gs with
    | none =>
      simp only [opSpec, Spec.opOK, List.append_nil, List.forall_mem_append, reduceCtorEq,
        false_implies, implies_true, and_true]
      cases p <;> cases b <;> cases w <;> simp [pos, neg, bval] <;> tauto
    | some ℓ =>
      simp only [opSpec, Spec.opOK, List.forall_mem_append, List.forall_mem_cons, chk_iff,
        bits_zero_iff hG.c_lt, Option.some.injEq, forall_eq', val_fSg, decide_eq_true_eq,
        hS.eq_iff]
      cases p <;> cases b <;> cases w <;> simp [pos, neg, bval] <;> tauto
  | i dec b w sp =>
    cases sp with
    | none =>
      simp only [opSpec, Spec.opOK, List.append_nil, List.forall_mem_append, reduceCtorEq,
        false_implies, implies_true, and_true]
      cases p <;> cases b <;> cases w <;> cases dec <;> simp [pos, neg, bval] <;> tauto
    | some q =>
      obtain ⟨ℓ, s⟩ := q
      simp only [opSpec, Spec.opOK, List.forall_mem_append, List.forall_mem_cons, chk_iff,
        Option.some.injEq, Prod.mk.injEq, val_fGs, val_fSc, decide_eq_true_eq]
      by_cases hs : s < X.P.length
      · have hb := bits_eq_iff (cS := cS) (r := r) hG.c_lt (spA_lt hX hs)
        cases p <;> cases b <;> cases w <;> cases dec <;> simp [pos, neg, bval, hs, spA] at hb ⊢ <;> tauto
      · have hf : ¬ ∀ x ∈ chk (s < X.P.length), (toCfg cS r).val x = true := by rw [chk_iff]; exact hs
        constructor
        · intro h; exfalso; apply hf; tauto
        · intro h; exfalso
          exact hs (h.2.2.2.2.2.2.2 ℓ s ⟨rfl, rfl⟩).2.2.1
  | bt w =>
    simp only [opSpec, Spec.opOK, List.append_nil, List.forall_mem_append]
    cases p <;> cases w <;> simp [pos, neg, bval] <;> tauto
  | bi w =>
    simp only [opSpec, Spec.opOK]
    cases p <;> cases w <;> simp [pos, neg, bval] <;> tauto

theorem app_rend (hS : Function.Injective cS) (p : Bool) (e : En S) :
    (aspec cS X allS (.rend p e)).App (toCfg cS r) ↔ X.mach.app (.rend p e) r := by
  rw [app_def _ _ rfl]
  simp only [aspec, ASpec.pre, ASpec.neg, List.forall_mem_append, Mach.app, Spec.mach]
  cases e with
  | boot σ =>
    simp only [endSpec, Spec.endOK, List.forall_mem_append, chk_iff]
    cases p <;> simp [pos, neg, bval] <;> tauto
  | norm z l c r' =>
    simp only [endSpec, Spec.endOK, List.forall_mem_append, List.forall_mem_cons, val_fSg,
      decide_eq_true_eq, hS.eq_iff, @eq_comm _ (X.F _ _ _)]
    cases p <;> cases z <;> simp [pos, neg, bval] <;> tauto

/-- **Applicability agrees on good states.** -/
theorem app_iff (hS : Function.Injective cS) (hX : X.Valid) (hG : Good X r) (a : Act Op (En S)) :
    (aspec cS X allS a).App (toCfg cS r) ↔ X.mach.app a r := by
  cases a with
  | wb p k b => exact app_wb hG p k b
  | rv p γ => exact app_rv p γ
  | rb p k b => exact app_rb hG p k b
  | op p o => exact app_op hS hX hG p o
  | inc p k => exact app_inc p k
  | wrap p => exact app_wrap p
  | rend p e => exact app_rend hS p e
  | nrd p => exact app_nrd p
  | dr p => exact app_dr p
  | fin => exact app_fin hG

end App2

end TE

end HardTR

end FOND
