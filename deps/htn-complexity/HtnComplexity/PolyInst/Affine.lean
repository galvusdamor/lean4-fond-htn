import HtnComplexity.PolyInst.Kit
/-!
# Affine maps on serialised numerals, as finite-state transducers

Most compilations rename the facts of the source instance by an affine map `v ↦ c * v + d`
(`2 v`, `4 v`, `6 v`, `6 (v + 2) + 1`, …).  On the serialisation, where a numeral is written
least significant bit first, such a map is computed by a **finite-state transducer** that keeps
the carry: reading the bit `b` with carry `k` it writes the bit `(c b + k) mod 2` and moves to
the carry `(c b + k) / 2`, and at the end of the numeral it writes the remaining carry.  The carry
never exceeds `c + d`, so the machine has finitely many states.

* `HTN.Syn.PolyInst.affM c d e` — the machine.  Started at the beginning of a serialised list of
  numerals it rewrites every entry and writes `e` in place of the terminator of the list
  (`[false]` to keep the list closed, `[]` to leave it open for more entries); after the list it
  writes nothing;
* `HTN.Syn.PolyInst.affNum_serNat` and `HTN.Syn.PolyInst.affList_blist` — what it computes, for
  `c ≥ 1`;
* `HTN.Syn.PolyInst.cobham_affNum`, `HTN.Syn.PolyInst.cobham_affList` — it is a function of
  Cobham's class (`HTN.PTime.Mealy.cobham_mealy`).
-/

namespace HTN

namespace Syn

namespace PolyInst

open PTime

/-- The states of the affine transducer: before an entry of the list, before a bit of a numeral
(with a carry), at a bit of a numeral (with a carry), and after the list. -/
inductive AffSt
  | top
  | mk (k : ℕ)
  | bit (k : ℕ)
  | done
  deriving DecidableEq

/-- The value of a bit. -/
def bv (b : Bool) : ℕ := if b then 1 else 0

/-- **The affine transducer** for `v ↦ c * v + d`, writing `e` at the end of the list. -/
def affM (c d : ℕ) (e : List Bool) : Mealy AffSt where
  step
    | .top, true => .mk d
    | .top, false => .done
    | .mk k, true => .bit k
    | .mk _, false => .top
    | .bit k, b => .mk ((c * bv b + k) / 2)
    | .done, _ => .done
  out
    | .top, true => [true]
    | .top, false => e
    | .mk _, true => []
    | .mk k, false => bstr (bitsOfNat k)
    | .bit k, b => [true, decide ((c * bv b + k) % 2 = 1)]
    | .done, _ => []

section
variable (c d : ℕ) (e : List Bool)
@[simp] theorem affM_step_top_true : (affM c d e).step .top true = .mk d := rfl
@[simp] theorem affM_step_top_false : (affM c d e).step .top false = .done := rfl
@[simp] theorem affM_step_mk_true (k : ℕ) : (affM c d e).step (.mk k) true = .bit k := rfl
@[simp] theorem affM_step_mk_false (k : ℕ) : (affM c d e).step (.mk k) false = .top := rfl
@[simp] theorem affM_step_bit (k : ℕ) (b : Bool) :
    (affM c d e).step (.bit k) b = .mk ((c * bv b + k) / 2) := rfl
@[simp] theorem affM_out_top_true : (affM c d e).out .top true = [true] := rfl
@[simp] theorem affM_out_top_false : (affM c d e).out .top false = e := rfl
@[simp] theorem affM_out_mk_true (k : ℕ) : (affM c d e).out (.mk k) true = [] := rfl
@[simp] theorem affM_out_mk_false (k : ℕ) :
    (affM c d e).out (.mk k) false = bstr (bitsOfNat k) := rfl
@[simp] theorem affM_out_bit (k : ℕ) (b : Bool) :
    (affM c d e).out (.bit k) b = [true, decide ((c * bv b + k) % 2 = 1)] := rfl
end

/-- The states the transducer can reach. -/
def affStates (c d : ℕ) : List AffSt :=
  .top :: .done :: ((List.range (c + d + 1)).map .mk ++ (List.range (c + d + 1)).map .bit)

theorem affStates_closed (c d : ℕ) (e : List Bool) :
    ∀ s b, s ∈ affStates c d → (affM c d e).step s b ∈ affStates c d := by
  intro s b hs
  simp only [affStates, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hs
  rcases hs with rfl | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · cases b <;> simp [affM, affStates] <;> omega
  · cases b <;> simp [affM, affStates]
  · cases b <;> simp [affM, affStates] <;> omega
  · simp only [affM, affStates, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
    refine Or.inr (Or.inr (Or.inl ⟨_, ?_, rfl⟩))
    have : c * bv b ≤ c := by unfold bv; split <;> simp
    omega

theorem top_mem_affStates (c d : ℕ) : AffSt.top ∈ affStates c d := by simp [affStates]

theorem mk_mem_affStates (c d : ℕ) : AffSt.mk d ∈ affStates c d := by
  simp [affStates]

@[simp] theorem affM_outs_done (c d : ℕ) (e : List Bool) :
    ∀ z, (affM c d e).outs .done z = [] := by
  intro z
  induction z with
  | nil => rfl
  | cons b z ih => cases b <;> simpa [affM] using ih

theorem bitsOfNat_pos {m : ℕ} (hm : 0 < m) :
    bitsOfNat m = decide (m % 2 = 1) :: bitsOfNat (m / 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact bitsOfNat_succ n

/-- **The transducer rewrites a numeral**: from the state with carry `k`, it turns the
self-delimiting numeral of `a` into that of `c * a + k`, and returns to the state before an
entry. -/
theorem affM_num {c : ℕ} (hc : 1 ≤ c) (d : ℕ) (e : List Bool) :
    ∀ a k, (affM c d e).outs (.mk k) (bstr (bitsOfNat a)) = bstr (bitsOfNat (c * a + k)) ∧
      (affM c d e).st (.mk k) (bstr (bitsOfNat a)) = .top := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro k
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [affM]
    · have hlt : a / 2 < a := Nat.div_lt_self ha (by norm_num)
      have hbv : bv (decide (a % 2 = 1)) = a % 2 := by
        unfold bv; split <;> rename_i h <;> simp at h <;> omega
      obtain ⟨ih1, ih2⟩ := ih (a / 2) hlt ((c * (a % 2) + k) / 2)
      have hsplit : c * a + k = (c * (a % 2) + k) + 2 * (c * (a / 2)) := by
        have h := Nat.div_add_mod a 2
        calc c * a + k = c * (2 * (a / 2) + a % 2) + k := by rw [h]
          _ = (c * (a % 2) + k) + 2 * (c * (a / 2)) := by ring
      have hpos : 0 < c * a + k := by
        have : 1 ≤ c * a := Nat.one_le_iff_ne_zero.2 (by positivity)
        omega
      have hmod : (c * a + k) % 2 = (c * (a % 2) + k) % 2 := by
        rw [hsplit, Nat.add_mul_mod_self_left]
      have hdiv : (c * a + k) / 2 = c * (a / 2) + (c * (a % 2) + k) / 2 := by
        rw [hsplit, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]; ring
      rw [bitsOfNat_pos ha, bstr_cons]
      simp only [Mealy.outs_cons, Mealy.st_cons, affM_step_mk_true, affM_step_bit,
        affM_out_mk_true, affM_out_bit, hbv, List.nil_append, List.cons_append]
      refine ⟨?_, ih2⟩
      rw [ih1, bitsOfNat_pos hpos, bstr_cons, hmod, hdiv]

/-- **The transducer rewrites a serialised list of numerals**, writing `e` in place of the
terminator and nothing after the list. -/
theorem affM_list {c : ℕ} (hc : 1 ≤ c) (d : ℕ) (e : List Bool) (z : List Bool) :
    ∀ l : List ℕ, (affM c d e).outs .top (blist (l.map bitsOfNat) ++ z) =
      entriesEnc (l.map fun a => bitsOfNat (c * a + d)) ++ e := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, blist_cons, List.cons_append, Mealy.outs_cons, entriesEnc_cons,
      List.append_assoc, affM_step_top_true, affM_out_top_true]
    rw [Mealy.outs_append, (affM_num hc d e a d).2, (affM_num hc d e a d).1, ih]
    simp

/-! ### As functions of Cobham's class -/

/-- The affine rewriting of a serialised list of numerals (writing `e` at its end). -/
def affList (c d : ℕ) (e : List Bool) (y : List Bool) : List Bool := (affM c d e).outs .top y

/-- The affine rewriting of one self-delimiting numeral. -/
def affNum (c d : ℕ) (y : List Bool) : List Bool := (affM c 0 []).outs (.mk d) y

theorem affList_blist {c : ℕ} (hc : 1 ≤ c) (d : ℕ) (e : List Bool) (l : List ℕ)
    (z : List Bool) :
    affList c d e (blist (l.map bitsOfNat) ++ z) =
      entriesEnc (l.map fun a => bitsOfNat (c * a + d)) ++ e :=
  affM_list hc d e z l

theorem affList_serNatList {c : ℕ} (hc : 1 ≤ c) (d : ℕ) (l : List ℕ) (z : List Bool) :
    affList c d [false] (serNatList l ++ z) = serNatList (l.map fun a => c * a + d) := by
  rw [serNatList, affList_blist hc, serNatList, blist_eq_entriesEnc, List.map_map]
  rfl

theorem affNum_serNat {c : ℕ} (hc : 1 ≤ c) (d a : ℕ) :
    affNum c d (serNat a) = serNat (c * a + d) :=
  (affM_num hc 0 [] a d).1

theorem cobham_affList (c d : ℕ) (e : List Bool) {a : Fn} (ha : Cobham a) :
    Cobham fun args => affList c d e (a args) :=
  ((affM c d e).cobham_mealy (affStates c d) .top (fun _ => []) (top_mem_affStates c d)
    (affStates_closed c d e) ha).of_eq' fun args => by simp [affList]

theorem cobham_affNum (c d : ℕ) {a : Fn} (ha : Cobham a) :
    Cobham fun args => affNum c d (a args) := by
  have hmem : AffSt.mk d ∈ affStates c d := by simp [affStates]
  have hcl : ∀ s b, s ∈ affStates c d → (affM c 0 []).step s b ∈ affStates c d := by
    intro s b hs
    simp only [affStates, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hs
    rcases hs with rfl | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · cases b <;> simp [affM, affStates]
    · cases b <;> simp [affM, affStates]
    · cases b <;> simp [affM, affStates] <;> omega
    · simp only [affM, affStates, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
      refine Or.inr (Or.inr (Or.inl ⟨_, ?_, rfl⟩))
      have : c * bv b ≤ c := by unfold bv; split <;> simp
      omega
  exact ((affM c 0 []).cobham_mealy (affStates c d) (.mk d) (fun _ => []) hmem hcl ha).of_eq'
    fun args => by simp [affNum]

end PolyInst

end Syn

end HTN
