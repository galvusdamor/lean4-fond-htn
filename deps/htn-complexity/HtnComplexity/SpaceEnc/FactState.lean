import HtnComplexity.SpaceEnc.Defs
import ComplexityTheory.SpaceEnc.Bits
/-!
# The fact states of the encoding

Every state reached by an execution of the encoding (before `fin`) is described by a record
`HTN.SpaceEnc.FS`: the program counter, the counter and the head as numbers, the machine state,
the parity, the round-0 flag, the input index, the last read symbol, the pending head move and
the "counter equals head" flag.  `HTN.SpaceEnc.enc` turns a record into a set of facts (together
with the input facts of the word), and this file computes, for every action, when it is
applicable to such a state and which record describes the result.
-/

namespace HTN

namespace SpaceEnc

open TM

/-- The record of a fact state. -/
structure FS (Q Γ : Type) where
  /-- The program counter. -/
  pc : ℕ
  /-- The position counter. -/
  cnt : ℕ
  /-- The head position. -/
  hd : ℕ
  /-- The machine state. -/
  st : Q
  /-- The parity of the writing loop. -/
  par : Bool
  /-- Round 0? -/
  first : Bool
  /-- The input index. -/
  u : ℕ
  /-- The last symbol read. -/
  sym : Option Γ
  /-- The pending head move. -/
  mv : Option Move
  /-- Does the counter agree with the head on the bits checked so far? -/
  eqv : Bool

variable {Q Γ : Type} [Fintype Γ]

/-- Which facts hold in the state described by a record, for the input word `w`. -/
def Holds (m : ℕ) (w : List Bool) (fs : FS Q Γ) : Fct Q Γ → Prop
  | .boot0 => False
  | .inp i b => i < w.length ∧ b = w.getD i false
  | .pc s => s = fs.pc
  | .cb k x => k < m ∧ x = fs.cnt.testBit k
  | .hb k x => k < m ∧ x = fs.hd.testBit k
  | .st q => q = fs.st
  | .sym g => fs.sym = some g
  | .mv μ => fs.mv = some μ
  | .par p => p = fs.par
  | .first => fs.first = true
  | .u j => j = fs.u
  | .eqf => fs.eqv = true
  | .neqf => fs.eqv = false
  | .drain => False

/-- **The set of facts of a record.** -/
def enc (m : ℕ) (w : List Bool) (fs : FS Q Γ) : Set (Fct Q Γ) := {f | Holds m w fs f}

omit [Fintype Γ] in
@[simp] theorem mem_enc {m : ℕ} {w : List Bool} {fs : FS Q Γ} {f : Fct Q Γ} :
    f ∈ enc m w fs ↔ Holds m w fs f := Iff.rfl

@[simp] theorem mem_symFacts {f : Fct Q Γ} : f ∈ (symFacts : List (Fct Q Γ)) ↔ ∃ g, f = .sym g := by
  simp [symFacts, eq_comm]

variable {m n' : ℕ} {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool} {fs : FS Q Γ}

theorem applicable_iff {a : Act Q Γ} {s : Set (Fct Q Γ)} :
    (am m n' ι N).Applicable a s ↔ ∀ f ∈ precL m n' a, f ∈ s := by
  simp [ActionModel.Applicable, am, Set.subset_def]

theorem mem_transition {a : Act Q Γ} {s : Set (Fct Q Γ)} {f : Fct Q Γ} :
    f ∈ (am m n' ι N).transition a s ↔ (f ∈ s ∧ f ∉ delL m a) ∨ f ∈ addL m ι N a := by
  simp [ActionModel.transition, am]

/-! ### Applicability -/

section App

variable (m n' ι N w fs)

theorem app_boot : ¬ (am m n' ι N).Applicable .boot (enc m w fs) := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact id

theorem app_drn : ¬ (am m n' ι N).Applicable .drn (enc m w fs) := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact fun h => h.2

theorem app_ws {p : Bool} : (am m n' ι N).Applicable (.ws p) (enc m w fs) ↔
    fs.pc = 0 ∧ fs.par = p := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩

theorem app_wb {p : Bool} {k : ℕ} {x e : Bool} : (am m n' ι N).Applicable (.wb p k x e) (enc m w fs) ↔
    fs.pc = k + 1 ∧ k < m ∧ x = fs.cnt.testBit k ∧ (if e then x else !x) = fs.hd.testBit k ∧
      fs.par = p := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, ⟨-, h4⟩, h5⟩
    exact ⟨h1.symm, h2, h3, h4, h5.symm⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1.symm, ⟨h2, h3⟩, ⟨h2, h4⟩, h5.symm⟩

theorem app_rb {p : Bool} {k : ℕ} {x : Bool} : (am m n' ι N).Applicable (.rb p k x) (enc m w fs) ↔
    fs.pc = 2 * m + 1 - k ∧ k < m ∧ x = fs.cnt.testBit k := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2, h3⟩⟩

theorem app_rv {p : Bool} {g : Γ} : (am m n' ι N).Applicable (.rv p g) (enc m w fs) ↔
    fs.pc = m + 1 ∧ fs.par = !p := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩

theorem app_ri {i : ℕ} {b : Bool} : (am m n' ι N).Applicable (.ri i b) (enc m w fs) ↔
    fs.pc = m + 1 ∧ fs.first = true ∧ fs.u = i ∧ i < w.length ∧ b = w.getD i false := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1.symm, h2, h3.symm, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1.symm, h2, h3.symm, h4, h5⟩

theorem app_rblank : (am m n' ι N).Applicable .rblank (enc m w fs) ↔
    fs.pc = m + 1 ∧ fs.first = true ∧ fs.u = n' := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2, h3.symm⟩, fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2, h3.symm⟩⟩

theorem app_cp {p : Bool} {g : Γ} : (am m n' ι N).Applicable (.cp p g) (enc m w fs) ↔
    fs.pc = 2 * m + 2 ∧ fs.eqv = false ∧ fs.sym = some g ∧ fs.par = p := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h2, h3, h4.symm⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h2, h3, h4.symm⟩⟩

theorem app_tr {p : Bool} {q0 q1 : Q} {g0 g1 : Γ} {μ : Move} :
    (am m n' ι N).Applicable (.tr p q0 g0 q1 g1 μ) (enc m w fs) ↔
    fs.pc = 2 * m + 2 ∧ fs.eqv = true ∧ fs.sym = some g0 ∧ fs.st = q0 ∧ fs.par = p := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1.symm, h2, h3, h4.symm, h5.symm⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1.symm, h2, h3, h4.symm, h5.symm⟩⟩

theorem app_inc {p : Bool} {k : ℕ} : (am m n' ι N).Applicable (.inc p k) (enc m w fs) ↔
    fs.pc = 2 * m + 3 ∧ fs.par = p ∧ k < m ∧ fs.cnt.testBit k = false ∧
      ∀ j < k, fs.cnt.testBit j = true := by
  simp only [applicable_iff, precL, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_map, List.mem_range, forall_eq_or_imp, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_enc, Holds]
  constructor
  · rintro ⟨h1, h2, ⟨h3, h4⟩, h5⟩
    exact ⟨h1.symm, h2.symm, h3, h4.symm, fun j hj => (h5 j hj).2.symm⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1.symm, h2.symm, ⟨h3, h4.symm⟩, fun j hj => ⟨by omega, (h5 j hj).symm⟩⟩

theorem app_wrap {p : Bool} : (am m n' ι N).Applicable (.wrap p) (enc m w fs) ↔
    fs.pc = 2 * m + 3 ∧ fs.par = p ∧ ∀ j < m, fs.cnt.testBit j = true := by
  simp only [applicable_iff, precL, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_map, List.mem_range, forall_eq_or_imp, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_enc, Holds]
  constructor
  · rintro ⟨h1, h2, h5⟩
    exact ⟨h1.symm, h2.symm, fun j hj => (h5 j hj).2.symm⟩
  · rintro ⟨h1, h2, h5⟩
    exact ⟨h1.symm, h2.symm, fun j hj => ⟨hj, (h5 j hj).symm⟩⟩

theorem app_hinc {p : Bool} {k : ℕ} : (am m n' ι N).Applicable (.hinc p k) (enc m w fs) ↔
    fs.pc = 2 * m + 4 ∧ fs.par = p ∧ fs.mv = some .right ∧ k < m ∧ fs.hd.testBit k = false ∧
      ∀ j < k, fs.hd.testBit j = true := by
  simp only [applicable_iff, precL, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_map, List.mem_range, forall_eq_or_imp, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_enc, Holds]
  constructor
  · rintro ⟨h1, h2, h0, ⟨h3, h4⟩, h5⟩
    exact ⟨h1.symm, h2.symm, h0, h3, h4.symm, fun j hj => (h5 j hj).2.symm⟩
  · rintro ⟨h1, h2, h0, h3, h4, h5⟩
    exact ⟨h1.symm, h2.symm, h0, ⟨h3, h4.symm⟩, fun j hj => ⟨by omega, (h5 j hj).symm⟩⟩

theorem app_hdec {p : Bool} {k : ℕ} : (am m n' ι N).Applicable (.hdec p k) (enc m w fs) ↔
    fs.pc = 2 * m + 4 ∧ fs.par = p ∧ fs.mv = some .left ∧ k < m ∧ fs.hd.testBit k = true ∧
      ∀ j < k, fs.hd.testBit j = false := by
  simp only [applicable_iff, precL, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_map, List.mem_range, forall_eq_or_imp, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_enc, Holds]
  constructor
  · rintro ⟨h1, h2, h0, ⟨h3, h4⟩, h5⟩
    exact ⟨h1.symm, h2.symm, h0, h3, h4.symm, fun j hj => (h5 j hj).2.symm⟩
  · rintro ⟨h1, h2, h0, h3, h4, h5⟩
    exact ⟨h1.symm, h2.symm, h0, ⟨h3, h4.symm⟩, fun j hj => ⟨by omega, (h5 j hj).symm⟩⟩

theorem app_hdec0 {p : Bool} : (am m n' ι N).Applicable (.hdec0 p) (enc m w fs) ↔
    fs.pc = 2 * m + 4 ∧ fs.par = p ∧ fs.mv = some .left ∧ ∀ j < m, fs.hd.testBit j = false := by
  simp only [applicable_iff, precL, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_map, List.mem_range, forall_eq_or_imp, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_enc, Holds]
  constructor
  · rintro ⟨h1, h2, h0, h5⟩
    exact ⟨h1.symm, h2.symm, h0, fun j hj => (h5 j hj).2.symm⟩
  · rintro ⟨h1, h2, h0, h5⟩
    exact ⟨h1.symm, h2.symm, h0, fun j hj => ⟨hj, (h5 j hj).symm⟩⟩

theorem app_hstay {p : Bool} : (am m n' ι N).Applicable (.hstay p) (enc m w fs) ↔
    fs.pc = 2 * m + 4 ∧ fs.par = p ∧ fs.mv = some .stay := by
  simp only [applicable_iff, precL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_enc, Holds]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, h3⟩⟩

theorem app_fin {q : Q} : (am m n' ι N).Applicable (.fin q) (enc m w fs) ↔
    fs.pc = 0 ∧ fs.st = q ∧ ∀ j < m, fs.cnt.testBit j = false := by
  simp only [applicable_iff, precL, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_map, List.mem_range, forall_eq_or_imp, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_enc, Holds]
  exact ⟨fun ⟨h1, h2, h5⟩ => ⟨h1.symm, h2.symm, fun j hj => (h5 j hj).2.symm⟩,
    fun ⟨h1, h2, h5⟩ => ⟨h1.symm, h2.symm, fun j hj => ⟨hj, (h5 j hj).symm⟩⟩⟩

end App

/-! ### Transitions -/

section Trans

variable (m n' ι N w fs)

theorem trans_ws (p : Bool) (h : fs.pc = 0) :
    (am m n' ι N).transition (.ws p) (enc m w fs) = enc m w { fs with pc := 1 } := by
  ext f
  rw [mem_transition]
  cases f <;> simp [delL, addL, Holds, h]

theorem trans_wb (p : Bool) (k : ℕ) (x e : Bool) (h : fs.pc = k + 1) :
    (am m n' ι N).transition (.wb p k x e) (enc m w fs) =
      enc m w { fs with pc := k + 2, eqv := fs.eqv && e } := by
  ext f
  rw [mem_transition]
  cases f <;> cases e <;> simp [delL, addL, Holds, h] <;> omega

theorem trans_rb (p : Bool) (k : ℕ) (x : Bool) (h : fs.pc = 2 * m + 1 - k) (hk : k < m) :
    (am m n' ι N).transition (.rb p k x) (enc m w fs) =
      enc m w { fs with pc := 2 * m + 2 - k } := by
  ext f
  rw [mem_transition]
  cases f <;> simp [delL, addL, Holds, h] <;> omega

theorem trans_rv (p : Bool) (g : Γ) (h : fs.pc = m + 1) :
    (am m n' ι N).transition (.rv p g) (enc m w fs) =
      enc m w { fs with pc := m + 2, sym := some g } := by
  ext f
  rw [mem_transition]
  cases f <;> simp [delL, addL, Holds, h] <;> first | omega | exact eq_comm

theorem trans_ri (i : ℕ) (b : Bool) (h : fs.pc = m + 1) (hu : fs.u = i) :
    (am m n' ι N).transition (.ri i b) (enc m w fs) =
      enc m w { fs with pc := 2 * m + 2, u := i + 1, sym := some (ι b) } := by
  ext f
  rw [mem_transition]
  cases f <;> simp [delL, addL, Holds, h, hu] <;> first | omega | exact eq_comm

theorem trans_rblank (h : fs.pc = m + 1) :
    (am m n' ι N).transition .rblank (enc m w fs) =
      enc m w { fs with pc := 2 * m + 2, sym := some N.blank } := by
  ext f
  rw [mem_transition]
  cases f <;> simp [delL, addL, Holds, h] <;> first | omega | exact eq_comm

theorem trans_cp (p : Bool) (g : Γ) (h : fs.pc = 2 * m + 2) :
    (am m n' ι N).transition (.cp p g) (enc m w fs) = enc m w { fs with pc := 2 * m + 3 } := by
  ext f
  rw [mem_transition]
  cases f <;> simp [delL, addL, Holds, h] <;> omega

theorem trans_tr (p : Bool) (q0 : Q) (g0 : Γ) (q1 : Q) (g1 : Γ) (μ : Move) (h : fs.pc = 2 * m + 2)
    (hq : fs.st = q0) (hmv : fs.mv = none) :
    (am m n' ι N).transition (.tr p q0 g0 q1 g1 μ) (enc m w fs) =
      enc m w { fs with pc := 2 * m + 3, st := q1, mv := some μ } := by
  ext f
  rw [mem_transition]
  cases f <;> simp [delL, addL, Holds, h, hq, hmv] <;> first | omega | tauto

theorem trans_inc (p : Bool) (k : ℕ) (h : fs.pc = 2 * m + 3) (hk : k < m)
    (hb : fs.cnt.testBit k = false) (hlow : ∀ j < k, fs.cnt.testBit j = true) :
    (am m n' ι N).transition (.inc p k) (enc m w fs) =
      enc m w { fs with pc := 0, cnt := fs.cnt + 1, eqv := true } := by
  ext f
  rw [mem_transition]
  cases f with
  | cb j x =>
    simp only [delL, addL, Holds, List.cons_append, List.mem_cons, List.mem_map, List.mem_range,
      mem_enc, testBit_succ_of hb hlow j]
    rcases lt_trichotomy j k with h1 | rfl | h1
    · have := hlow j h1
      cases x <;> simp [h1, this] <;> omega
    · cases x <;> simp [hb, hk]
    · have h2 : ¬ j < k := by omega
      have h3 : j ≠ k := by omega
      cases x <;> simp [h2, h3] <;> tauto
  | _ => simp [delL, addL, Holds, h] <;> omega

theorem trans_wrap (p : Bool) (h : fs.pc = 2 * m + 3) (hall : ∀ j < m, fs.cnt.testBit j = true) :
    (am m n' ι N).transition (.wrap p) (enc m w fs) =
      enc m w { fs with pc := 2 * m + 4, cnt := 0, eqv := true } := by
  ext f
  rw [mem_transition]
  cases f with
  | cb j x =>
    simp only [delL, addL, Holds, List.cons_append, List.mem_cons, List.mem_map, List.mem_range,
      mem_enc, Nat.zero_testBit]
    by_cases h1 : j < m
    · have := hall j h1
      cases x <;> simp [h1, this]
    · simp [h1]
  | _ => simp [delL, addL, Holds, h] <;> omega

theorem trans_hinc (p : Bool) (k : ℕ) (h : fs.pc = 2 * m + 4) (hp : fs.par = p)
    (hmv : fs.mv = some .right) (hk : k < m)
    (hb : fs.hd.testBit k = false) (hlow : ∀ j < k, fs.hd.testBit j = true) :
    (am m n' ι N).transition (.hinc p k) (enc m w fs) =
      enc m w { fs with pc := 0, par := !p, mv := none, first := false, hd := fs.hd + 1 } := by
  ext f
  rw [mem_transition]
  cases f with
  | hb j x =>
    simp only [delL, addL, Holds, List.cons_append, List.mem_cons, List.mem_map, List.mem_range,
      mem_enc, testBit_succ_of hb hlow j]
    rcases lt_trichotomy j k with h1 | rfl | h1
    · have := hlow j h1
      cases x <;> simp [h1, this] <;> omega
    · cases x <;> simp [hb, hk]
    · have h2 : ¬ j < k := by omega
      have h3 : j ≠ k := by omega
      cases x <;> simp [h2, h3] <;> tauto
  | par b => cases b <;> cases p <;> simp [delL, addL, Holds, hp]
  | mv μ => cases μ <;> simp [delL, addL, Holds, hmv]
  | _ => simp [delL, addL, Holds, h] <;> omega

theorem trans_hdec (p : Bool) (k : ℕ) (h : fs.pc = 2 * m + 4) (hp : fs.par = p)
    (hmv : fs.mv = some .left) (hk : k < m)
    (hb : fs.hd.testBit k = true) (hlow : ∀ j < k, fs.hd.testBit j = false) :
    (am m n' ι N).transition (.hdec p k) (enc m w fs) =
      enc m w { fs with pc := 0, par := !p, mv := none, first := false, hd := fs.hd - 1 } := by
  ext f
  rw [mem_transition]
  cases f with
  | hb j x =>
    simp only [delL, addL, Holds, List.cons_append, List.mem_cons, List.mem_map, List.mem_range,
      mem_enc, testBit_pred_of hb hlow j]
    rcases lt_trichotomy j k with h1 | rfl | h1
    · have := hlow j h1
      cases x <;> simp [h1, this] <;> omega
    · cases x <;> simp [hb, hk]
    · have h2 : ¬ j < k := by omega
      have h3 : j ≠ k := by omega
      cases x <;> simp [h2, h3] <;> tauto
  | par b => cases b <;> cases p <;> simp [delL, addL, Holds, hp]
  | mv μ => cases μ <;> simp [delL, addL, Holds, hmv]
  | _ => simp [delL, addL, Holds, h] <;> omega

theorem trans_hdec0 (p : Bool) (h : fs.pc = 2 * m + 4) (hp : fs.par = p)
    (hmv : fs.mv = some .left) :
    (am m n' ι N).transition (.hdec0 p) (enc m w fs) =
      enc m w { fs with pc := 0, par := !p, mv := none, first := false } := by
  ext f
  rw [mem_transition]
  cases f with
  | par b => cases b <;> cases p <;> simp [delL, addL, Holds, hp]
  | mv μ => cases μ <;> simp [delL, addL, Holds, hmv]
  | _ => simp [delL, addL, Holds, h] <;> omega

theorem trans_hstay (p : Bool) (h : fs.pc = 2 * m + 4) (hp : fs.par = p)
    (hmv : fs.mv = some .stay) :
    (am m n' ι N).transition (.hstay p) (enc m w fs) =
      enc m w { fs with pc := 0, par := !p, mv := none, first := false } := by
  ext f
  rw [mem_transition]
  cases f with
  | par b => cases b <;> cases p <;> simp [delL, addL, Holds, hp]
  | mv μ => cases μ <;> simp [delL, addL, Holds, hmv]
  | _ => simp [delL, addL, Holds, h] <;> omega

end Trans

end SpaceEnc

end HTN
