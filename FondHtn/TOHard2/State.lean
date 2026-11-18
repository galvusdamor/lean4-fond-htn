import FondHtn.TOHard2.Game
import FondHtn.TOHard2.Bits
/-!
# States and instructions of the 2-EXPTIME construction

The configurations visited by the construction are encodings `FOND.TOHard2.St.cfg` of records
`FOND.TOHard2.St`:

| field | number | meaning |
| --- | --- | --- |
| `ov` | 0 | the digit counter overflowed (the chain has visited `2 ^ b` digits) |
| `eq` | 1 | the current digit is the challenged one (`ctr = chk`) |
| `tb`, `ib` | 2, 3 | the challenged digit of the time `t` and of the cell `i` of the claim |
| `ml`, `mc`, `mr` | 4, 5, 6 | the challenge of nature (left / centre / right predecessor) |
| `chk r` | `2 r + 8` | bit `r` of the challenged digit index (set by nature) |
| `ctr r` | `2 r + 9` | bit `r` of the digit counter |

The instructions (lists of alternatives, `FOND.HardMP.ASpec`) and their weakest preconditions on
encoded states are computed here (`wp_*` lemmas).
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace FOND

namespace TOHard2

open HardMP

/-! ## States -/

/-- The record of a configuration. -/
structure St where
  chk : ℕ → Bool
  ctr : ℕ → Bool
  ov : Bool
  eq : Bool
  tb : Bool
  ib : Bool
  ml : Bool
  mc : Bool
  mr : Bool

/-- The field of bit `r` of the challenged digit index. -/
def fChk (r : ℕ) : ℕ := 2 * r + 8
/-- The field of bit `r` of the counter. -/
def fCtr (r : ℕ) : ℕ := 2 * r + 9

/-- The field of a register: `true` = time digit, `false` = cell digit. -/
def fReg (rg : Bool) : ℕ := if rg then 2 else 3

namespace St

/-- The value of field `f`. -/
def val (s : St) (f : ℕ) : Bool :=
  if f = 0 then s.ov else if f = 1 then s.eq else if f = 2 then s.tb else if f = 3 then s.ib
  else if f = 4 then s.ml else if f = 5 then s.mc else if f = 6 then s.mr else if f = 7 then false
  else if f % 2 = 0 then s.chk ((f - 8) / 2) else s.ctr ((f - 9) / 2)

/-- **The encoding of a state.** -/
def cfg (s : St) : Cfg := ⟨s.val, none⟩

@[simp] theorem val_0 (s : St) : s.val 0 = s.ov := rfl
@[simp] theorem val_1 (s : St) : s.val 1 = s.eq := rfl
@[simp] theorem val_2 (s : St) : s.val 2 = s.tb := rfl
@[simp] theorem val_3 (s : St) : s.val 3 = s.ib := rfl
@[simp] theorem val_4 (s : St) : s.val 4 = s.ml := rfl
@[simp] theorem val_5 (s : St) : s.val 5 = s.mc := rfl
@[simp] theorem val_6 (s : St) : s.val 6 = s.mr := rfl
@[simp] theorem val_7 (s : St) : s.val 7 = false := rfl
@[simp] theorem val_chk (s : St) (r : ℕ) : s.val (fChk r) = s.chk r := by
  unfold val fChk
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega
@[simp] theorem val_ctr (s : St) (r : ℕ) : s.val (fCtr r) = s.ctr r := by
  unfold val fCtr
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1; omega

@[simp] theorem cfg_val (s : St) : s.cfg.val = s.val := rfl
@[simp] theorem cfg_cur (s : St) : s.cfg.cur = none := rfl

/-- The register `rg`. -/
def reg (s : St) (rg : Bool) : Bool := if rg then s.tb else s.ib

/-- Set the register `rg`. -/
def setReg (s : St) (rg : Bool) (v : Bool) : St :=
  if rg then { s with tb := v } else { s with ib := v }

@[simp] theorem val_reg (s : St) (rg : Bool) : s.val (fReg rg) = s.reg rg := by
  cases rg <;> rfl

theorem cfg_injective : Function.Injective cfg := by
  intro s s' h
  have hv : s.val = s'.val := congrArg Cfg.val h
  have h0 := congrFun hv 0; have h1 := congrFun hv 1; have h2 := congrFun hv 2
  have h3 := congrFun hv 3; have h4 := congrFun hv 4; have h5 := congrFun hv 5
  have h6 := congrFun hv 6
  have hc : s.chk = s'.chk := funext fun r => by
    have := congrFun hv (fChk r); simpa using this
  have hd : s.ctr = s'.ctr := funext fun r => by
    have := congrFun hv (fCtr r); simpa using this
  cases s; cases s'; simp_all

end St

theorem field_cases (f : ℕ) : f < 8 ∨ (∃ r, f = fChk r) ∨ ∃ r, f = fCtr r := by
  rcases Nat.lt_or_ge f 8 with h | h
  · exact Or.inl h
  · rcases Nat.even_or_odd f with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inr (Or.inl ⟨k - 4, by unfold fChk; omega⟩)
    · exact Or.inr (Or.inr ⟨k - 4, by unfold fCtr; omega⟩)

/-- **Equality with an encoding**, field by field. -/
theorem cfg_eq {g : ℕ → Bool} {s : St} (h0 : g 0 = s.ov) (h1 : g 1 = s.eq) (h2 : g 2 = s.tb)
    (h3 : g 3 = s.ib) (h4 : g 4 = s.ml) (h5 : g 5 = s.mc) (h6 : g 6 = s.mr) (h7 : g 7 = false)
    (hc : ∀ r, g (fChk r) = s.chk r) (hd : ∀ r, g (fCtr r) = s.ctr r) :
    (⟨g, none⟩ : Cfg) = s.cfg := by
  show (⟨g, none⟩ : Cfg) = ⟨s.val, none⟩
  congr 1
  funext f
  rcases field_cases f with h | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · interval_cases f <;> simp [*]
  · simp [hc]
  · simp [hd]

/-- The effect of an alternative without change of the current task. -/
theorem eff_cfg (pre neg : List ℕ) (effs : List (List ℕ × List ℕ))
    (cpre : List (Option (Bool × ℕ))) (e : List ℕ × List ℕ) (s : St) :
    ASpec.eff (pre, neg, effs, cpre, []) e s.cfg =
      ⟨fun f => (s.val f && !decide (f ∈ e.2)) || decide (f ∈ e.1), none⟩ := rfl

theorem fChk_ne_small (r : ℕ) {f : ℕ} (h : f < 8) : fChk r ≠ f := by unfold fChk; omega
theorem fCtr_ne_small (r : ℕ) {f : ℕ} (h : f < 8) : fCtr r ≠ f := by unfold fCtr; omega
@[simp] theorem fChk_inj {r r' : ℕ} : fChk r = fChk r' ↔ r = r' := by unfold fChk; omega
@[simp] theorem fCtr_inj {r r' : ℕ} : fCtr r = fCtr r' ↔ r = r' := by unfold fCtr; omega
@[simp] theorem fChk_ne_fCtr (r r' : ℕ) : fChk r ≠ fCtr r' := by unfold fChk fCtr; omega
@[simp] theorem fCtr_ne_fChk (r r' : ℕ) : fCtr r ≠ fChk r' := by unfold fChk fCtr; omega
@[simp] theorem fChk_ne_0 (r : ℕ) : fChk r ≠ 0 := fChk_ne_small r (by norm_num)
@[simp] theorem fChk_ne_1 (r : ℕ) : fChk r ≠ 1 := fChk_ne_small r (by norm_num)
@[simp] theorem fChk_ne_2 (r : ℕ) : fChk r ≠ 2 := fChk_ne_small r (by norm_num)
@[simp] theorem fChk_ne_3 (r : ℕ) : fChk r ≠ 3 := fChk_ne_small r (by norm_num)
@[simp] theorem fChk_ne_4 (r : ℕ) : fChk r ≠ 4 := fChk_ne_small r (by norm_num)
@[simp] theorem fChk_ne_5 (r : ℕ) : fChk r ≠ 5 := fChk_ne_small r (by norm_num)
@[simp] theorem fChk_ne_6 (r : ℕ) : fChk r ≠ 6 := fChk_ne_small r (by norm_num)
@[simp] theorem fCtr_ne_0 (r : ℕ) : fCtr r ≠ 0 := fCtr_ne_small r (by norm_num)
@[simp] theorem fCtr_ne_1 (r : ℕ) : fCtr r ≠ 1 := fCtr_ne_small r (by norm_num)
@[simp] theorem fCtr_ne_2 (r : ℕ) : fCtr r ≠ 2 := fCtr_ne_small r (by norm_num)
@[simp] theorem fCtr_ne_3 (r : ℕ) : fCtr r ≠ 3 := fCtr_ne_small r (by norm_num)
@[simp] theorem fCtr_ne_4 (r : ℕ) : fCtr r ≠ 4 := fCtr_ne_small r (by norm_num)
@[simp] theorem fCtr_ne_5 (r : ℕ) : fCtr r ≠ 5 := fCtr_ne_small r (by norm_num)
@[simp] theorem fCtr_ne_6 (r : ℕ) : fCtr r ≠ 6 := fCtr_ne_small r (by norm_num)
@[simp] theorem fCtr_ne_7 (r : ℕ) : fCtr r ≠ 7 := fCtr_ne_small r (by norm_num)
@[simp] theorem fChk_ne_7 (r : ℕ) : fChk r ≠ 7 := fChk_ne_small r (by norm_num)
@[simp] theorem small_ne_fChk_0 (r : ℕ) : ¬ (0 = fChk r) := fun h => fChk_ne_small r (by norm_num : 0 < 8) h.symm
@[simp] theorem small_ne_fCtr_0 (r : ℕ) : ¬ (0 = fCtr r) := fun h => fCtr_ne_small r (by norm_num : 0 < 8) h.symm
@[simp] theorem small_ne_fChk_1 (r : ℕ) : ¬ (1 = fChk r) := fun h => fChk_ne_small r (by norm_num : 1 < 8) h.symm
@[simp] theorem small_ne_fCtr_1 (r : ℕ) : ¬ (1 = fCtr r) := fun h => fCtr_ne_small r (by norm_num : 1 < 8) h.symm
@[simp] theorem small_ne_fChk_2 (r : ℕ) : ¬ (2 = fChk r) := fun h => fChk_ne_small r (by norm_num : 2 < 8) h.symm
@[simp] theorem small_ne_fCtr_2 (r : ℕ) : ¬ (2 = fCtr r) := fun h => fCtr_ne_small r (by norm_num : 2 < 8) h.symm
@[simp] theorem small_ne_fChk_3 (r : ℕ) : ¬ (3 = fChk r) := fun h => fChk_ne_small r (by norm_num : 3 < 8) h.symm
@[simp] theorem small_ne_fCtr_3 (r : ℕ) : ¬ (3 = fCtr r) := fun h => fCtr_ne_small r (by norm_num : 3 < 8) h.symm
@[simp] theorem small_ne_fChk_4 (r : ℕ) : ¬ (4 = fChk r) := fun h => fChk_ne_small r (by norm_num : 4 < 8) h.symm
@[simp] theorem small_ne_fCtr_4 (r : ℕ) : ¬ (4 = fCtr r) := fun h => fCtr_ne_small r (by norm_num : 4 < 8) h.symm
@[simp] theorem small_ne_fChk_5 (r : ℕ) : ¬ (5 = fChk r) := fun h => fChk_ne_small r (by norm_num : 5 < 8) h.symm
@[simp] theorem small_ne_fCtr_5 (r : ℕ) : ¬ (5 = fCtr r) := fun h => fCtr_ne_small r (by norm_num : 5 < 8) h.symm
@[simp] theorem small_ne_fChk_6 (r : ℕ) : ¬ (6 = fChk r) := fun h => fChk_ne_small r (by norm_num : 6 < 8) h.symm
@[simp] theorem small_ne_fCtr_6 (r : ℕ) : ¬ (6 = fCtr r) := fun h => fCtr_ne_small r (by norm_num : 6 < 8) h.symm
@[simp] theorem small_ne_fChk_7 (r : ℕ) : ¬ (7 = fChk r) := fun h => fChk_ne_small r (by norm_num : 7 < 8) h.symm
@[simp] theorem small_ne_fCtr_7 (r : ℕ) : ¬ (7 = fCtr r) := fun h => fCtr_ne_small r (by norm_num : 7 < 8) h.symm

/-- Effects on a single small field. -/
theorem eff_small {pre neg : List ℕ} {effs : List (List ℕ × List ℕ)}
    {cpre : List (Option (Bool × ℕ))} {e : List ℕ × List ℕ} {s s' : St}
    (hsmall : ∀ f ∈ e.1 ++ e.2, f < 8)
    (h : ∀ f < 8, ((s.val f && !decide (f ∈ e.2)) || decide (f ∈ e.1)) = s'.val f)
    (hc : s'.chk = s.chk) (hd : s'.ctr = s.ctr) :
    ASpec.eff (pre, neg, effs, cpre, []) e s.cfg = s'.cfg := by
  rw [eff_cfg]
  have hnc : ∀ r, fChk r ∉ e.1 ∧ fChk r ∉ e.2 := fun r =>
    ⟨fun hm => fChk_ne_small r (hsmall _ (List.mem_append_left _ hm)) rfl,
     fun hm => fChk_ne_small r (hsmall _ (List.mem_append_right _ hm)) rfl⟩
  have hnd : ∀ r, fCtr r ∉ e.1 ∧ fCtr r ∉ e.2 := fun r =>
    ⟨fun hm => fCtr_ne_small r (hsmall _ (List.mem_append_left _ hm)) rfl,
     fun hm => fCtr_ne_small r (hsmall _ (List.mem_append_right _ hm)) rfl⟩
  refine cfg_eq (h 0 (by norm_num)) (h 1 (by norm_num)) (h 2 (by norm_num)) (h 3 (by norm_num))
    (h 4 (by norm_num)) (h 5 (by norm_num)) (h 6 (by norm_num)) ?_ (fun r => ?_) (fun r => ?_)
  · have := h 7 (by norm_num); rwa [St.val_7] at this
  · simp [(hnc r).1, (hnc r).2, hc]
  · simp [(hnd r).1, (hnd r).2, hd]

/-! ## Instructions -/

/-- Instruction names. -/
def iN (t p : ℕ) : ℕ := Nat.pair t p

/-- A test: alternatives of literals, without effect. -/
def tst (alts : List (List ℕ × List ℕ)) : List ASpec := alts.map fun pn => (pn.1, pn.2, noeff, [], [])

/-- The literals hold. -/
def Lits (s : St) (pn : List ℕ × List ℕ) : Prop :=
  (∀ f ∈ pn.1, s.val f = true) ∧ ∀ f ∈ pn.2, s.val f = false

theorem wp_tst {alts : List (List ℕ × List ℕ)} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (tst alts) Ψ ↔ (∃ pn ∈ alts, Lits s pn) ∧ s.cfg ∈ Ψ := by
  rw [mem_wpI_iff]
  constructor
  · rintro ⟨a, ha, happ, hall⟩
    obtain ⟨pn, hpn, rfl⟩ := List.mem_map.1 ha
    refine ⟨⟨pn, hpn, happ.1, happ.2.1⟩, ?_⟩
    have := hall ([], []) (by simp [ASpec.effs, noeff])
    rwa [eff_nil'] at this
  · rintro ⟨⟨pn, hpn, h1, h2⟩, h⟩
    refine ⟨_, List.mem_map.2 ⟨pn, hpn, rfl⟩, ⟨h1, h2, by simp [ASpec.cpre]⟩, fun e he => ?_⟩
    simp only [ASpec.effs, noeff, List.mem_singleton] at he
    subst he; rwa [eff_nil']

/-- Literals "the challenged index is `e`". -/
def eqLits (b e : ℕ) : List ℕ × List ℕ :=
  (((List.range b).filter fun r => e.testBit r).map fChk,
    ((List.range b).filter fun r => !e.testBit r).map fChk)

/-- Alternatives "the challenged index differs from `e`". -/
def neLits (b e : ℕ) : List (List ℕ × List ℕ) :=
  (List.range b).map fun r => if e.testBit r then ([], [fChk r]) else ([fChk r], [])

/-- The challenged index. -/
def St.chkV (s : St) (b : ℕ) : ℕ := ofB s.chk b

theorem lits_eqLits {s : St} {b e : ℕ} :
    Lits s (eqLits b e) ↔ ∀ r < b, s.chk r = e.testBit r := by
  simp only [Lits, eqLits, List.mem_map, List.mem_filter, List.mem_range, forall_exists_index,
    and_imp]
  constructor
  · rintro ⟨h1, h2⟩ r hr
    cases he : e.testBit r
    · exact by simpa using h2 _ r hr (by simp [he]) rfl
    · exact by simpa using h1 _ r hr he rfl
  · intro h
    refine ⟨fun f r hr he hf => ?_, fun f r hr he hf => ?_⟩
    · subst hf; simp [h r hr, he]
    · subst hf; simp only [Bool.not_eq_true'] at he; simp [h r hr, he]

theorem lits_eqLits_iff {s : St} {b e : ℕ} (he : e < 2 ^ b) :
    Lits s (eqLits b e) ↔ s.chkV b = e := by
  rw [lits_eqLits, St.chkV, ofB_eq_iff he]

theorem exists_neLits_iff {s : St} {b e : ℕ} (he : e < 2 ^ b) :
    (∃ pn ∈ neLits b e, Lits s pn) ↔ s.chkV b ≠ e := by
  rw [St.chkV, Ne, ofB_eq_iff he, not_forall]
  constructor
  · rintro ⟨pn, hpn, h⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hpn
    refine ⟨r, fun h' => ?_⟩
    have := h' (List.mem_range.1 hr)
    cases he' : e.testBit r <;> simp_all [Lits]
  · rintro ⟨r, hr⟩
    have hrb : r < b := by by_contra h; exact hr fun h' => absurd h' h
    have hne : s.chk r ≠ e.testBit r := fun h => hr fun _ => h
    refine ⟨_, List.mem_map.2 ⟨r, List.mem_range.2 hrb, rfl⟩, ?_⟩
    cases he' : e.testBit r <;> cases hs : s.chk r <;> simp_all [Lits]

/-- A single alternative with a single effect. -/
theorem wp_single {pre neg : List ℕ} {e : List ℕ × List ℕ} {Ψ : Set Cfg} {s s' : St}
    (heff : ASpec.eff (pre, neg, [e], [], []) e s.cfg = s'.cfg) :
    s.cfg ∈ wpI [(pre, neg, [e], [], [])] Ψ ↔ Lits s (pre, neg) ∧ s'.cfg ∈ Ψ := by
  rw [mem_wpI_iff]
  constructor
  · rintro ⟨a, ha, happ, hall⟩
    rw [List.mem_singleton] at ha; subst ha
    exact ⟨⟨happ.1, happ.2.1⟩, heff ▸ hall e (by simp [ASpec.effs])⟩
  · rintro ⟨⟨h1, h2⟩, h⟩
    refine ⟨_, List.mem_singleton_self _, ⟨h1, h2, by simp [ASpec.cpre]⟩, fun e' he' => ?_⟩
    simp only [ASpec.effs, List.mem_singleton] at he'
    subst he'; rwa [heff]

/-! ### The counter instructions -/

/-- Start a digit: no overflow yet; assume the digit is the challenged one. -/
def setEQ : ℕ × List ASpec := (iN 0 0, [([], [0], [([1], [])], [], [])])

theorem wp_setEQ {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI setEQ.2 Ψ ↔ s.ov = false ∧ { s with eq := true }.cfg ∈ Ψ := by
  dsimp only [setEQ]
  rw [wp_single (s := s) (s' := { s with eq := true }) (eff_small (by simp) (by
    intro f hf; interval_cases f <;> simp) rfl rfl)]
  simp [Lits]

/-- Compare bit `r` of the counter with bit `r` of the challenged index. -/
def cmpI (r : ℕ) : ℕ × List ASpec :=
  (iN 1 r, [([fCtr r, fChk r], [], noeff, [], []), ([], [fCtr r, fChk r], noeff, [], []),
    ([fCtr r], [fChk r], [([], [1])], [], []), ([fChk r], [fCtr r], [([], [1])], [], [])])

theorem wp_cmp {r : ℕ} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (cmpI r).2 Ψ ↔
      if s.ctr r = s.chk r then s.cfg ∈ Ψ else { s with eq := false }.cfg ∈ Ψ := by
  rw [mem_wpI_iff]
  have hd : ∀ (pre neg : List ℕ), ASpec.eff (pre, neg, [([], [1])], [], []) ([], [1]) s.cfg =
      { s with eq := false }.cfg := fun _ _ =>
    eff_small (by simp) (by intro f hf; interval_cases f <;> simp) rfl rfl
  simp only [cmpI, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    app_iff, ASpec.effs, noeff, List.mem_singleton, forall_eq, eff_nil', hd, St.cfg_val,
    St.val_chk, St.val_ctr, forall_eq_or_imp, IsEmpty.forall_iff, implies_true, and_true,
    List.not_mem_nil]
  cases s.ctr r <;> cases s.chk r <;> simp

/-- Clear the counter bits below `j`, set bit `j`. -/
def incF (g : ℕ → Bool) (j : ℕ) : ℕ → Bool := fun r => if r < j then false else if r = j then true else g r

/-- Increment the counter (alternative `j < b`: carry into bit `j`; `j = b`: overflow). -/
def incI (b : ℕ) : ℕ × List ASpec :=
  (iN 2 0, (List.range b).map (fun j => ((List.range j).map fCtr, [fCtr j],
      [([fCtr j], (List.range j).map fCtr)], [], [])) ++
    [((List.range b).map fCtr, [], [([0], (List.range b).map fCtr)], [], [])])

/-- Clear the counter bits below `b`. -/
def clrF (g : ℕ → Bool) (b : ℕ) : ℕ → Bool := fun r => if r < b then false else g r

theorem eff_inc (pre neg : List ℕ) (effs : List (List ℕ × List ℕ)) (s : St) (j : ℕ) :
    ASpec.eff (pre, neg, effs, [], []) ([fCtr j], (List.range j).map fCtr) s.cfg =
      { s with ctr := incF s.ctr j }.cfg := by
  rw [eff_cfg]
  refine cfg_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun r => ?_) (fun r => ?_)
  all_goals simp only [List.mem_map, List.mem_range, List.mem_singleton]
  all_goals try simp
  simp only [incF]
  by_cases h1 : r < j
  · simp [h1, show r ≠ j by omega]
  · by_cases h2 : r = j
    · subst h2; simp
    · simp [h1, h2]

theorem eff_ovf (pre neg : List ℕ) (effs : List (List ℕ × List ℕ)) (s : St) (b : ℕ) :
    ASpec.eff (pre, neg, effs, [], []) ([0], (List.range b).map fCtr) s.cfg =
      { s with ctr := clrF s.ctr b, ov := true }.cfg := by
  rw [eff_cfg]
  refine cfg_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun r => ?_) (fun r => ?_)
  all_goals simp only [List.mem_map, List.mem_range, List.mem_singleton]
  all_goals try simp
  simp only [clrF]
  by_cases h1 : r < b <;> simp [h1]

theorem wp_inc {b : ℕ} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (incI b).2 Ψ ↔
      (∃ j < b, (∀ r < j, s.ctr r = true) ∧ s.ctr j = false ∧ { s with ctr := incF s.ctr j }.cfg ∈ Ψ) ∨
      ((∀ r < b, s.ctr r = true) ∧ { s with ctr := clrF s.ctr b, ov := true }.cfg ∈ Ψ) := by
  rw [mem_wpI_iff]
  simp only [incI, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  constructor
  · rintro ⟨a, (⟨j, hj, rfl⟩ | rfl), happ, hall⟩
    · have h3 := hall _ (List.mem_singleton_self _)
      rw [eff_inc] at h3
      refine Or.inl ⟨j, hj, fun r hr => ?_, ?_, h3⟩
      · have := happ.1 (fCtr r) (List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩); simpa using this
      · have := happ.2.1 (fCtr j) (List.mem_singleton_self _); simpa using this
    · have h3 := hall _ (List.mem_singleton_self _)
      rw [eff_ovf] at h3
      refine Or.inr ⟨fun r hr => ?_, h3⟩
      have := happ.1 (fCtr r) (List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩); simpa using this
  · rintro (⟨j, hj, h1, h2, h3⟩ | ⟨h1, h3⟩)
    · refine ⟨_, Or.inl ⟨j, hj, rfl⟩, ⟨fun f hf => ?_, fun f hf => ?_, by simp [ASpec.cpre]⟩,
        fun e he => ?_⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf; simpa using h1 r (List.mem_range.1 hr)
      · simp only [ASpec.neg, List.mem_singleton] at hf; subst hf; simpa using h2
      · simp only [ASpec.effs, List.mem_singleton] at he; subst he; rwa [eff_inc]
    · refine ⟨_, Or.inr rfl, ⟨fun f hf => ?_, fun f hf => ?_, by simp [ASpec.cpre]⟩,
        fun e he => ?_⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf; simpa using h1 r (List.mem_range.1 hr)
      · simp [ASpec.neg] at hf
      · simp only [ASpec.effs, List.mem_singleton] at he; subst he; rwa [eff_ovf]

/-- End of a chain: the counter overflowed exactly once. -/
def finI : ℕ × List ASpec := (iN 3 0, [([0], [], [([], [0, 1])], [], [])])

theorem wp_fin {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI finI.2 Ψ ↔ s.ov = true ∧ { s with ov := false, eq := false }.cfg ∈ Ψ := by
  dsimp only [finI]
  rw [wp_single (s := s) (s' := { s with ov := false, eq := false }) (eff_small (by simp) (by
    intro f hf; interval_cases f <;> simp) rfl rfl)]
  simp [Lits]

/-! ### Acting on the challenged digit -/

/-- If the digit is the challenged one, the register must be `0` and becomes `1`. -/
def f01I (rg : Bool) : ℕ × List ASpec :=
  (iN 4 rg.toNat, [([], [1], noeff, [], []), ([1], [fReg rg], [([fReg rg], [])], [], [])])

/-- If the digit is the challenged one, the register must be `1` and becomes `0`. -/
def f10I (rg : Bool) : ℕ × List ASpec :=
  (iN 5 rg.toNat, [([], [1], noeff, [], []), ([1, fReg rg], [], [([], [fReg rg])], [], [])])

theorem fReg_lt (rg : Bool) : fReg rg < 8 := by cases rg <;> simp [fReg]

theorem wp_f01 {rg : Bool} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (f01I rg).2 Ψ ↔
      if s.eq then s.reg rg = false ∧ (s.setReg rg true).cfg ∈ Ψ else s.cfg ∈ Ψ := by
  rw [mem_wpI_iff]
  have he : ASpec.eff ([1], [fReg rg], [([fReg rg], [])], [], []) ([fReg rg], []) s.cfg =
      (s.setReg rg true).cfg := by
    refine eff_small (by simp [fReg_lt]) ?_ (by cases rg <;> rfl) (by cases rg <;> rfl)
    intro f hf; cases rg <;> interval_cases f <;> simp [fReg, St.setReg]
  simp only [f01I, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    app_iff, ASpec.effs, noeff, List.mem_singleton, forall_eq, eff_nil', he, St.cfg_val,
    St.val_1, St.val_reg, IsEmpty.forall_iff, implies_true, and_true, List.not_mem_nil]
  cases s.eq <;> simp

theorem wp_f10 {rg : Bool} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (f10I rg).2 Ψ ↔
      if s.eq then s.reg rg = true ∧ (s.setReg rg false).cfg ∈ Ψ else s.cfg ∈ Ψ := by
  rw [mem_wpI_iff]
  have he : ASpec.eff ([1, fReg rg], [], [([], [fReg rg])], [], []) ([], [fReg rg]) s.cfg =
      (s.setReg rg false).cfg := by
    refine eff_small (by simp [fReg_lt]) ?_ (by cases rg <;> rfl) (by cases rg <;> rfl)
    intro f hf; cases rg <;> interval_cases f <;> simp [fReg, St.setReg]
  simp only [f10I, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    app_iff, ASpec.effs, noeff, List.mem_singleton, forall_eq, eff_nil', he, St.cfg_val,
    St.val_1, St.val_reg, IsEmpty.forall_iff, implies_true, and_true, List.not_mem_nil,
    forall_eq_or_imp]
  cases s.eq <;> cases s.reg rg <;> simp

/-- If the digit is the challenged one, the cell digit must be `β`. -/
def bitI (β : Bool) : ℕ × List ASpec :=
  (iN 6 β.toNat, tst [([], [1]), if β then ([1, 3], []) else ([1], [3])])

theorem wp_bit {β : Bool} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (bitI β).2 Ψ ↔ (s.eq = true → s.ib = β) ∧ s.cfg ∈ Ψ := by
  rw [bitI, wp_tst]
  cases β <;> simp [Lits] <;> cases s.eq <;> cases s.ib <;> simp

/-! ### Comparisons with constants given by their set digits -/

/-- Equality with the constant, part one: `IB → chk ∈ ks`. -/
def ceAI (b k : ℕ) (ks : List ℕ) : ℕ × List ASpec :=
  (iN 7 k, tst ([([], [1]), ([], [3])] ++ ks.map fun e => (1 :: 3 :: (eqLits b e).1, (eqLits b e).2)))

/-- Equality with the constant, part two (for the `j`-th set digit `e`): `¬IB → chk ≠ e`. -/
def ceBI (b k j e : ℕ) : ℕ × List ASpec :=
  (iN 8 (Nat.pair k j), tst ([([], [1]), ([3], [])] ++ neLits b e))

/-- `IB` holds (part one of "greater"). -/
def cwAI : ℕ × List ASpec := (iN 9 0, tst [([], [1]), ([3], [])])

/-- The `j`-th set digit `e` differs from the challenged index (part two of "greater"). -/
def cwBI (b k j e : ℕ) : ℕ × List ASpec := (iN 10 (Nat.pair k j), tst (([], [1]) :: neLits b e))

/-- `¬IB` and the challenged index is a set digit ("smaller"). -/
def cvI (b k : ℕ) (ks : List ℕ) : ℕ × List ASpec :=
  (iN 11 k, tst (([], [1]) :: ks.map fun e => (1 :: (eqLits b e).1, 3 :: (eqLits b e).2)))

theorem lits_cons_true {s : St} {f : ℕ} {pn : List ℕ × List ℕ} :
    Lits s (f :: pn.1, pn.2) ↔ s.val f = true ∧ Lits s pn := by
  simp [Lits, and_assoc]

theorem lits_cons_false {s : St} {f : ℕ} {pn : List ℕ × List ℕ} :
    Lits s (pn.1, f :: pn.2) ↔ s.val f = false ∧ Lits s pn := by
  simp only [Lits, List.mem_cons, forall_eq_or_imp]; tauto

section Const

variable {b : ℕ} {ks : List ℕ} (hks : ∀ e ∈ ks, e < 2 ^ b)
include hks

theorem wp_ceA {k : ℕ} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (ceAI b k ks).2 Ψ ↔
      (s.eq = true → s.ib = true → s.chkV b ∈ ks) ∧ s.cfg ∈ Ψ := by
  rw [ceAI, wp_tst]
  refine and_congr_left fun _ => ?_
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨pn, (rfl | rfl) | ⟨e, he, rfl⟩, h⟩ heq hib
    · simp [Lits, heq] at h
    · simp [Lits, hib] at h
    · have h' := (lits_cons_true.1 (lits_cons_true.1 h).2).2
      rw [lits_eqLits_iff (hks e he)] at h'
      rw [h']; exact he
  · intro h
    cases heq : s.eq
    · exact ⟨_, Or.inl (Or.inl rfl), by simp [Lits, heq]⟩
    cases hib : s.ib
    · exact ⟨_, Or.inl (Or.inr rfl), by simp [Lits, hib]⟩
    · have hm := h heq hib
      refine ⟨_, Or.inr ⟨_, hm, rfl⟩, ?_⟩
      refine lits_cons_true.2 ⟨by simp [heq], lits_cons_true.2 ⟨by simp [hib], ?_⟩⟩
      exact (lits_eqLits_iff (hks _ hm)).2 rfl

omit hks in
theorem wp_ceB {k j e : ℕ} (he : e < 2 ^ b) {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (ceBI b k j e).2 Ψ ↔
      (s.eq = true → s.ib = false → s.chkV b ≠ e) ∧ s.cfg ∈ Ψ := by
  rw [ceBI, wp_tst]
  refine and_congr_left fun _ => ?_
  rw [← exists_neLits_iff he]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨pn, (rfl | rfl) | hn, h⟩ heq hib
    · simp [Lits, heq] at h
    · simp [Lits, hib] at h
    · exact ⟨pn, hn, h⟩
  · intro h
    cases heq : s.eq
    · exact ⟨_, Or.inl (Or.inl rfl), by simp [Lits, heq]⟩
    cases hib : s.ib
    · obtain ⟨pn, hn, h⟩ := h heq hib; exact ⟨pn, Or.inr hn, h⟩
    · exact ⟨_, Or.inl (Or.inr rfl), by simp [Lits, hib]⟩

omit hks in
theorem wp_cwA {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI cwAI.2 Ψ ↔ (s.eq = true → s.ib = true) ∧ s.cfg ∈ Ψ := by
  rw [cwAI, wp_tst]
  simp [Lits] <;> cases s.eq <;> cases s.ib <;> simp

omit hks in
theorem wp_cwB {k j e : ℕ} (he : e < 2 ^ b) {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (cwBI b k j e).2 Ψ ↔ (s.eq = true → s.chkV b ≠ e) ∧ s.cfg ∈ Ψ := by
  rw [cwBI, wp_tst]
  refine and_congr_left fun _ => ?_
  rw [← exists_neLits_iff he]
  simp only [List.mem_cons]
  constructor
  · rintro ⟨pn, rfl | hn, h⟩ heq
    · simp [Lits, heq] at h
    · exact ⟨pn, hn, h⟩
  · intro h
    cases heq : s.eq
    · exact ⟨_, Or.inl rfl, by simp [Lits, heq]⟩
    · obtain ⟨pn, hn, h⟩ := h heq; exact ⟨pn, Or.inr hn, h⟩

theorem wp_cv {k : ℕ} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (cvI b k ks).2 Ψ ↔
      (s.eq = true → s.ib = false ∧ s.chkV b ∈ ks) ∧ s.cfg ∈ Ψ := by
  rw [cvI, wp_tst]
  refine and_congr_left fun _ => ?_
  simp only [List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨pn, rfl | ⟨e, he, rfl⟩, h⟩ heq
    · simp [Lits, heq] at h
    · obtain ⟨h1, h2⟩ := h
      simp only [List.mem_cons, forall_eq_or_imp] at h1 h2
      have h3 : Lits s (eqLits b e) := ⟨h1.2, h2.2⟩
      rw [lits_eqLits_iff (hks e he)] at h3
      refine ⟨by simpa using h2.1, ?_⟩
      rw [h3]; exact he
  · intro h
    cases heq : s.eq
    · exact ⟨_, Or.inl rfl, by simp [Lits, heq]⟩
    · obtain ⟨hib, hm⟩ := h heq
      have h3 := (lits_eqLits_iff (s := s) (hks _ hm)).2 rfl
      refine ⟨_, Or.inr ⟨_, hm, rfl⟩, ?_, ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by simp [heq], h3.1⟩
      · simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨by simp [hib], h3.2⟩

end Const

/-! ### The other instructions -/

/-- Nature sets bit `r` of the challenged index. -/
def pickChkI (r : ℕ) : ℕ × List ASpec := (iN 12 r, [([], [], [([fChk r], []), ([], [fChk r])], [], [])])

theorem wp_pickChk {r : ℕ} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (pickChkI r).2 Ψ ↔ ∀ v, { s with chk := Function.update s.chk r v }.cfg ∈ Ψ := by
  rw [mem_wpI_iff]
  have h : ∀ v, ASpec.eff ([], [], [([fChk r], []), ([], [fChk r])], [], [])
      (bif v then ([fChk r], []) else ([], [fChk r])) s.cfg =
      { s with chk := Function.update s.chk r v }.cfg := by
    intro v
    rw [eff_cfg]
    refine cfg_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun r' => ?_) (fun r' => ?_) <;> cases v <;>
      simp [Function.update_apply]
    · by_cases h : r' = r <;> simp [h]
    · by_cases h : r' = r <;> simp [h]
  simp only [pickChkI, List.mem_singleton, exists_eq_left, app_iff, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_self, true_and, ASpec.effs, List.mem_cons, or_false,
    forall_eq_or_imp, forall_eq]
  have h1 := h true; have h2 := h false
  simp only [cond_true, cond_false] at h1 h2
  rw [h1, h2]
  constructor
  · rintro ⟨ht, hf⟩ v; cases v <;> assumption
  · intro hv; exact ⟨hv true, hv false⟩

/-- Clear the time digit (the first row is time `0`). -/
def clrTBI : ℕ × List ASpec := (iN 13 0, [([], [], [([], [2])], [], [])])

theorem wp_clrTB {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI clrTBI.2 Ψ ↔ { s with tb := false }.cfg ∈ Ψ := by
  dsimp only [clrTBI]
  rw [wp_single (s := s) (s' := { s with tb := false }) (eff_small (by simp) (by
    intro f hf; interval_cases f <;> simp) rfl rfl)]
  simp [Lits]

/-- The policy guesses the cell digit. -/
def guessIBI : ℕ × List ASpec := (iN 14 0, guessI 3)

theorem wp_guessIB {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI guessIBI.2 Ψ ↔ ∃ v, { s with ib := v }.cfg ∈ Ψ := by
  rw [guessIBI, mem_wpI_guess]
  refine exists_congr fun v => ?_
  have : s.cfg.set 3 v = { s with ib := v }.cfg := by
    show (⟨Function.update s.val 3 v, none⟩ : Cfg) = _
    refine cfg_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun r => ?_) (fun r => ?_) <;>
      simp [Function.update_apply]
  rw [this]

/-- The three challenges (one-hot). -/
def modeSt (s : St) (l c r : Bool) : St := { s with ml := l, mc := c, mr := r }

/-- Nature picks a challenge among `k` consecutive mode fields starting at `f₀`. -/
def pickMI (t f₀ k : ℕ) : ℕ × List ASpec := (iN t 0, pickI (fun i => f₀ + i) k)

/-- Pick `L`, `C` or `R`. -/
def pick3I : ℕ × List ASpec := pickMI 15 4 3
/-- Pick `L` or `C`. -/
def pickLCI : ℕ × List ASpec := pickMI 16 4 2
/-- Pick `C` or `R`. -/
def pickCRI : ℕ × List ASpec := pickMI 17 5 2

theorem pick_cfg (s : St) {f₀ k i : ℕ} (hf : 4 ≤ f₀) (hk : f₀ + k ≤ 7) (hi : i < k) :
    s.cfg.pick (fun i => f₀ + i) k i =
      (modeSt s (if f₀ ≤ 4 ∧ 4 < f₀ + k then decide (4 = f₀ + i) else s.ml)
        (if f₀ ≤ 5 ∧ 5 < f₀ + k then decide (5 = f₀ + i) else s.mc)
        (if f₀ ≤ 6 ∧ 6 < f₀ + k then decide (6 = f₀ + i) else s.mr)).cfg := by
  show (⟨_, none⟩ : Cfg) = _
  have hm : ∀ f, f ∈ (List.range k).map (fun i => f₀ + i) ↔ f₀ ≤ f ∧ f < f₀ + k := by
    intro f; simp only [List.mem_map, List.mem_range]
    exact ⟨fun ⟨a, ha, h⟩ => by omega, fun h => ⟨f - f₀, by omega, by omega⟩⟩
  have hout : ∀ f, (f < f₀ ∨ f₀ + k ≤ f) →
      ((s.val f && !decide (f₀ ≤ f ∧ f < f₀ + k)) || decide (f = f₀ + i)) = s.val f := by
    intro f hf
    rw [decide_eq_false (show ¬ (f₀ ≤ f ∧ f < f₀ + k) by omega),
      decide_eq_false (show f ≠ f₀ + i by omega)]
    simp
  have hin : ∀ f, f₀ ≤ f → f < f₀ + k →
      ((s.val f && !decide (f₀ ≤ f ∧ f < f₀ + k)) || decide (f = f₀ + i)) = decide (f = f₀ + i) := by
    intro f h1 h2
    rw [decide_eq_true (show f₀ ≤ f ∧ f < f₀ + k from ⟨h1, h2⟩)]
    simp
  refine cfg_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun r => ?_) (fun r => ?_)
  all_goals simp only [hm, List.mem_singleton, St.cfg_val]
  · exact hout 0 (by omega)
  · exact hout 1 (by omega)
  · exact hout 2 (by omega)
  · exact hout 3 (by omega)
  · by_cases h1 : f₀ ≤ 4 ∧ 4 < f₀ + k
    · rw [hin 4 h1.1 h1.2, if_pos h1]; simp [modeSt, eq_comm]
    · rw [hout 4 (by omega), if_neg h1]; rfl
  · by_cases h1 : f₀ ≤ 5 ∧ 5 < f₀ + k
    · rw [hin 5 h1.1 h1.2, if_pos h1]; simp [modeSt, eq_comm]
    · rw [hout 5 (by omega), if_neg h1]; rfl
  · by_cases h1 : f₀ ≤ 6 ∧ 6 < f₀ + k
    · rw [hin 6 h1.1 h1.2, if_pos h1]; simp [modeSt, eq_comm]
    · rw [hout 6 (by omega), if_neg h1]; rfl
  · exact hout 7 (by omega)
  · rw [hout _ (by unfold fChk; omega)]; simp [modeSt]
  · rw [hout _ (by unfold fCtr; omega)]; simp [modeSt]

theorem wp_pick3 {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI pick3I.2 Ψ ↔ (modeSt s true false false).cfg ∈ Ψ ∧
      (modeSt s false true false).cfg ∈ Ψ ∧ (modeSt s false false true).cfg ∈ Ψ := by
  rw [pick3I, pickMI, mem_wpI_pick]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h 0 (by norm_num); rw [pick_cfg s (by norm_num) (by norm_num) (by norm_num)] at this
      simpa using this
    · have := h 1 (by norm_num); rw [pick_cfg s (by norm_num) (by norm_num) (by norm_num)] at this
      simpa using this
    · have := h 2 (by norm_num); rw [pick_cfg s (by norm_num) (by norm_num) (by norm_num)] at this
      simpa using this
  · rintro ⟨h0, h1, h2⟩ i hi
    rw [pick_cfg s (by norm_num) (by norm_num) hi]
    interval_cases i <;> simpa

theorem wp_pickLC {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI pickLCI.2 Ψ ↔ (modeSt s true false s.mr).cfg ∈ Ψ ∧
      (modeSt s false true s.mr).cfg ∈ Ψ := by
  rw [pickLCI, pickMI, mem_wpI_pick]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 (by norm_num); rw [pick_cfg s (by norm_num) (by norm_num) (by norm_num)] at this
      simpa using this
    · have := h 1 (by norm_num); rw [pick_cfg s (by norm_num) (by norm_num) (by norm_num)] at this
      simpa using this
  · rintro ⟨h0, h1⟩ i hi
    rw [pick_cfg s (by norm_num) (by norm_num) hi]
    interval_cases i <;> simpa

theorem wp_pickCR {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI pickCRI.2 Ψ ↔ (modeSt s s.ml true false).cfg ∈ Ψ ∧
      (modeSt s s.ml false true).cfg ∈ Ψ := by
  rw [pickCRI, pickMI, mem_wpI_pick]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 (by norm_num); rw [pick_cfg s (by norm_num) (by norm_num) (by norm_num)] at this
      simpa using this
    · have := h 1 (by norm_num); rw [pick_cfg s (by norm_num) (by norm_num) (by norm_num)] at this
      simpa using this
  · rintro ⟨h0, h1⟩ i hi
    rw [pick_cfg s (by norm_num) (by norm_num) hi]
    interval_cases i <;> simpa

/-- Assert a field (a mode, `m = 0, 1, 2` for `L, C, R`). -/
def assertMI (m : ℕ) : ℕ × List ASpec := (iN 18 m, tst [([4 + m], [])])

theorem wp_assertM {m : ℕ} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (assertMI m).2 Ψ ↔ s.val (4 + m) = true ∧ s.cfg ∈ Ψ := by
  rw [assertMI, wp_tst]; simp [Lits]

/-- Assert the cell digit. -/
def assertIBI (β : Bool) : ℕ × List ASpec := (iN 19 β.toNat, tst [if β then ([3], []) else ([], [3])])

theorem wp_assertIB {β : Bool} {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI (assertIBI β).2 Ψ ↔ s.ib = β ∧ s.cfg ∈ Ψ := by
  rw [assertIBI, wp_tst]; cases β <;> simp [Lits] <;> cases s.ib <;> simp

/-- Assert the time digit (the root: time `2 ^ D - 1`). -/
def assertTBI : ℕ × List ASpec := (iN 20 0, tst [([2], [])])

theorem wp_assertTB {Ψ : Set Cfg} {s : St} :
    s.cfg ∈ wpI assertTBI.2 Ψ ↔ s.tb = true ∧ s.cfg ∈ Ψ := by
  rw [assertTBI, wp_tst]; simp [Lits]

end TOHard2

end FOND
