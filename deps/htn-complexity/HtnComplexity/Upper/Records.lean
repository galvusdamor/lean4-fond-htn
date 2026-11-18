import HtnPlanning.Basic
/-!
# Descriptions as finite sets of records, and a bit code that is trivial to read

`HTN.Table.PairUpper` asks for one *total computable* procedure `g` on pairs of bit strings that
decides plan existence from separate codes of a domain and of an instance.  So `g` has to read
a description off an arbitrary bit string.  This file supplies a coding for which reading is a
short primitive recursive function.

* A **record** (`HTN.Upper.Rec`) is a quintuple of numbers `(kind, tag, x, y, z)`.  A description
  is written as a finite set of records (`HTN.Upper.toDom`, `HTN.Upper.toInst` read a domain and
  an instance description off a list of records):
  - domain: `(0, a, f, 0, 0)` — `f` is in the precondition of action `a` (kinds `1`, `2`: add and
    delete list); `(3, 0, a, 0, 0)` — action `a` is listed; `(4, 0, j, c, 0)` — method number `j`
    decomposes the compound name `c`;
  - instance: `(0, 0, f, 0, 0)` — `f` holds initially; `(1, 0, f, 0, 0)` — `f` is a goal fact;
  - task network number `j` (`j = 0` for the initial task network of an instance):
    `(5, j, i, 0, 0)` — identifier `i`; `(6, j, i, i', 0)` — `i` before `i'`;
    `(7, j, i, b, n)` — identifier `i` is labelled by the name `n`, compound iff `b = 1`.
* A finite set of numbers is coded by its **characteristic bit string** (`HTN.Upper.maskOf`),
  and read back by `HTN.Upper.unmask`; a finite set of records by the set of their Gödel
  numbers (`HTN.Upper.recCode`, read back by `HTN.Upper.recsOf`).  The Gödel number of a record
  is polynomial in its entries (a record has fixed depth), so the code of a description is
  polynomial in the largest number it mentions (`HTN.Upper.length_recCode_le`).
* `HTN.Upper.primrec_toDom`, `HTN.Upper.primrec_toInst`, `HTN.Upper.primrec_recsOf` — reading is
  primitive recursive.
-/

namespace HTN

namespace Upper

open Syn

/-- A record: kind, tag and three entries. -/
abbrev Rec : Type := ℕ × ℕ × ℕ × ℕ × ℕ

/-! ### Reading descriptions off a list of records -/

/-- The records of a given kind and tag. -/
def sel (L : List Rec) (k j : ℕ) : List Rec := L.filter fun r => r.1 = k ∧ r.2.1 = j

/-- The first entries of the records of a given kind and tag. -/
def xs (L : List Rec) (k j : ℕ) : List ℕ := (sel L k j).map fun r => r.2.2.1

/-- The task network number `j`. -/
def body (L : List Rec) (j : ℕ) : TnDesc :=
  (xs L 5 j, (sel L 6 j).map (fun r => (r.2.2.1, r.2.2.2.1)),
    (sel L 7 j).map (fun r => (r.2.2.1, decide (r.2.2.2.1 = 1), r.2.2.2.2)))

/-- **The domain description written by a list of records.** -/
def toDom (L : List Rec) : DomDesc :=
  ((xs L 3 0).map (fun a => (a, xs L 0 a, xs L 1 a, xs L 2 a)),
    (sel L 4 0).map (fun r => (r.2.2.2.1, body L r.2.2.1)))

/-- **The instance description written by a list of records.** -/
def toInst (L : List Rec) : InstDesc := (xs L 0 0, xs L 1 0, body L 0)

theorem mem_sel {L : List Rec} {k j : ℕ} {r : Rec} :
    r ∈ sel L k j ↔ r ∈ L ∧ r.1 = k ∧ r.2.1 = j := by
  simp [sel]

theorem mem_xs {L : List Rec} {k j x : ℕ} :
    x ∈ xs L k j ↔ ∃ r ∈ L, r.1 = k ∧ r.2.1 = j ∧ r.2.2.1 = x := by
  simp only [xs, List.mem_map, mem_sel]
  constructor
  · rintro ⟨r, ⟨hr, hk, hj⟩, rfl⟩
    exact ⟨r, hr, hk, hj, rfl⟩
  · rintro ⟨r, hr, hk, hj, rfl⟩
    exact ⟨r, ⟨hr, hk, hj⟩, rfl⟩

/-! ### The characteristic bit string of a finite set of numbers -/

/-- The characteristic bit string of a finite set of numbers: bit `k` says whether `k ∈ S`. -/
noncomputable def maskOf (S : Finset ℕ) : List Bool :=
  (List.range (S.sup id + 1)).map fun k => decide (k ∈ S)

/-- The set coded by a bit string: the positions of its `true` bits, in increasing order. -/
def unmask (x : List Bool) : List ℕ := (List.range x.length).filter fun k => x.getD k false

theorem length_maskOf (S : Finset ℕ) : (maskOf S).length = S.sup id + 1 := by
  simp [maskOf]

theorem mem_unmask_maskOf {S : Finset ℕ} {k : ℕ} : k ∈ unmask (maskOf S) ↔ k ∈ S := by
  simp only [unmask, List.mem_filter, List.mem_range, length_maskOf]
  constructor
  · rintro ⟨hk, h⟩
    rw [List.getD_eq_getElem _ _ (by rw [length_maskOf]; exact hk)] at h
    simpa [maskOf] using h
  · intro h
    have hk : k < S.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) h)
    refine ⟨hk, ?_⟩
    rw [List.getD_eq_getElem _ _ (by rw [length_maskOf]; exact hk)]
    simpa [maskOf] using h

/-! ### Coding a finite set of records -/

/-- The bit code of a finite set of records: the characteristic string of their Gödel numbers. -/
noncomputable def recCode (R : Finset Rec) : List Bool := maskOf (R.image Encodable.encode)

/-- The records coded by a bit string. -/
def recsOf (x : List Bool) : List Rec := (unmask x).filterMap fun n => Encodable.decode n

theorem mem_recsOf_recCode {R : Finset Rec} {r : Rec} : r ∈ recsOf (recCode R) ↔ r ∈ R := by
  simp only [recsOf, recCode, List.mem_filterMap, mem_unmask_maskOf, Finset.mem_image]
  constructor
  · rintro ⟨n, ⟨r', hr', rfl⟩, h⟩
    rw [Encodable.encodek] at h
    cases h
    exact hr'
  · intro h
    exact ⟨Encodable.encode r, ⟨r, h, rfl⟩, Encodable.encodek r⟩

/-! ### The length of a code -/

/-- One level of pairing. -/
theorem pair_le_pow {a b M u k : ℕ} (hu : 2 ≤ u) (ha : a ≤ M) (hM : M + 1 ≤ u ^ k)
    (hb : b ≤ u ^ k) : Nat.pair a b ≤ u ^ (2 * k + 2) := by
  have h1 := Nat.pair_lt_max_add_one_sq a b
  have hmax : max a b ≤ u ^ k := max_le (by omega) hb
  have h2 : (max a b + 1) ^ 2 ≤ (2 * u ^ k) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h3 : (2 * u ^ k) ^ 2 ≤ u ^ (2 * k + 2) := by
    have h4 : (2 * u ^ k) ^ 2 = 4 * (u ^ k) ^ 2 := by ring
    have h5 : u ^ (2 * k + 2) = u ^ 2 * (u ^ k) ^ 2 := by ring
    have h6 : 4 ≤ u ^ 2 := by nlinarith
    rw [h4, h5]
    exact Nat.mul_le_mul_right _ h6
  omega

/-- A record whose entries are at most `M` has a Gödel number at most `(M + 2) ^ 46`. -/
theorem encode_rec_le {r : Rec} {M : ℕ} (h1 : r.1 ≤ M) (h2 : r.2.1 ≤ M) (h3 : r.2.2.1 ≤ M)
    (h4 : r.2.2.2.1 ≤ M) (h5 : r.2.2.2.2 ≤ M) : Encodable.encode r ≤ (M + 2) ^ 46 := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := r
  simp only at h1 h2 h3 h4 h5
  simp only [Encodable.encode_prod_val, Encodable.encode_nat]
  have hu : 2 ≤ M + 2 := by omega
  have hp : ∀ k, k ≠ 0 → M + 1 ≤ (M + 2) ^ k := fun k hk =>
    le_trans (by omega) (Nat.le_self_pow hk (M + 2))
  have l1 : Nat.pair x4 x5 ≤ (M + 2) ^ 4 :=
    pair_le_pow (k := 1) hu h4 (by simp) (by simp; omega)
  have l2 : Nat.pair x3 (Nat.pair x4 x5) ≤ (M + 2) ^ 10 :=
    pair_le_pow (k := 4) hu h3 (hp 4 (by norm_num)) l1
  have l3 : Nat.pair x2 (Nat.pair x3 (Nat.pair x4 x5)) ≤ (M + 2) ^ 22 :=
    pair_le_pow (k := 10) hu h2 (hp 10 (by norm_num)) l2
  exact pair_le_pow (k := 22) hu h1 (hp 22 (by norm_num)) l3

/-- **The length of the code of a set of records** is polynomial in the largest entry. -/
theorem length_recCode_le {R : Finset Rec} {M : ℕ}
    (h : ∀ r ∈ R, r.1 ≤ M ∧ r.2.1 ≤ M ∧ r.2.2.1 ≤ M ∧ r.2.2.2.1 ≤ M ∧ r.2.2.2.2 ≤ M) :
    (recCode R).length ≤ (M + 2) ^ 46 + 1 := by
  rw [recCode, length_maskOf]
  refine Nat.add_le_add_right (Finset.sup_le fun n hn => ?_) 1
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := h r hr
  exact encode_rec_le h1 h2 h3 h4 h5

/-! ### Reading is primitive recursive -/

theorem primrec_filter_bool {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun x => (f x).filter (p x) := by
  have h : Primrec₂ fun (x : α) (b : β) => if p x b = true then some b else none := by
    refine Primrec₂.mk (Primrec.ite ?_ (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none))
    exact PrimrecRel.comp Primrec.eq (hp.comp Primrec.fst Primrec.snd) (Primrec.const true)
  refine (Primrec.listFilterMap hf h).of_eq fun x => ?_
  induction f x with
  | nil => rfl
  | cons b l ih =>
    by_cases hb : p x b = true
    · simp [hb, ih]
    · simp [hb, ih]

theorem primrec_sel : Primrec fun w : List Rec × ℕ × ℕ => sel w.1 w.2.1 w.2.2 := by
  have h : Primrec₂ fun (w : List Rec × ℕ × ℕ) (r : Rec) =>
      decide (r.1 = w.2.1 ∧ r.2.1 = w.2.2) := by
    refine Primrec₂.mk ?_
    have h1 : PrimrecPred fun u : (List Rec × ℕ × ℕ) × Rec => u.2.1 = u.1.2.1 :=
      PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have h2 : PrimrecPred fun u : (List Rec × ℕ × ℕ) × Rec => u.2.2.1 = u.1.2.2 :=
      PrimrecRel.comp Primrec.eq (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact (h1.and h2).decide
  exact (primrec_filter_bool Primrec.fst h).of_eq fun w => by simp [sel]

theorem primrec_xs : Primrec fun w : List Rec × ℕ × ℕ => xs w.1 w.2.1 w.2.2 :=
  Primrec.list_map primrec_sel (Primrec₂.mk (Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd.comp Primrec.snd))))

theorem primrec_body : Primrec fun w : List Rec × ℕ => body w.1 w.2 := by
  have hs : ∀ k, Primrec fun w : List Rec × ℕ => sel w.1 k w.2 := fun k =>
    primrec_sel.comp (Primrec.pair Primrec.fst (Primrec.pair (Primrec.const k) Primrec.snd))
  have hx : Primrec fun w : List Rec × ℕ => xs w.1 5 w.2 :=
    primrec_xs.comp (Primrec.pair Primrec.fst (Primrec.pair (Primrec.const 5) Primrec.snd))
  have h3 : Primrec fun r : Rec => r.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h4 : Primrec fun r : Rec => r.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h5 : Primrec fun r : Rec => r.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ho : Primrec fun w : List Rec × ℕ =>
      (sel w.1 6 w.2).map (fun r => (r.2.2.1, r.2.2.2.1)) :=
    Primrec.list_map (hs 6) (Primrec₂.mk ((Primrec.pair h3 h4).comp Primrec.snd))
  have hb : Primrec fun r : Rec => decide (r.2.2.2.1 = 1) :=
    (PrimrecRel.comp Primrec.eq h4 (Primrec.const 1)).decide
  have hl : Primrec fun w : List Rec × ℕ =>
      (sel w.1 7 w.2).map (fun r => (r.2.2.1, decide (r.2.2.2.1 = 1), r.2.2.2.2)) :=
    Primrec.list_map (hs 7)
      (Primrec₂.mk ((Primrec.pair h3 (Primrec.pair hb h5)).comp Primrec.snd))
  exact Primrec.pair hx (Primrec.pair ho hl)

theorem primrec_toDom : Primrec toDom := by
  have hx : ∀ k, Primrec₂ fun (L : List Rec) (j : ℕ) => xs L k j := fun k =>
    Primrec₂.mk (primrec_xs.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.const k) Primrec.snd)))
  have hacts : Primrec fun L : List Rec =>
      (xs L 3 0).map (fun a => (a, xs L 0 a, xs L 1 a, xs L 2 a)) :=
    Primrec.list_map ((hx 3).comp Primrec.id (Primrec.const 0))
      (Primrec₂.mk (Primrec.pair Primrec.snd (Primrec.pair ((hx 0).comp Primrec.fst Primrec.snd)
        (Primrec.pair ((hx 1).comp Primrec.fst Primrec.snd)
          ((hx 2).comp Primrec.fst Primrec.snd)))))
  have hsel : Primrec fun L : List Rec => sel L 4 0 :=
    primrec_sel.comp (Primrec.pair Primrec.id (Primrec.const (4, 0)))
  have hmeth : Primrec fun L : List Rec =>
      (sel L 4 0).map (fun r => (r.2.2.2.1, body L r.2.2.1)) :=
    Primrec.list_map hsel (Primrec₂.mk (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (primrec_body.comp (Primrec.pair Primrec.fst
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))
  exact Primrec.pair hacts hmeth

theorem primrec_toInst : Primrec toInst := by
  have hx : ∀ k, Primrec fun L : List Rec => xs L k 0 := fun k =>
    primrec_xs.comp (Primrec.pair Primrec.id (Primrec.const (k, 0)))
  exact Primrec.pair (hx 0) (Primrec.pair (hx 1)
    (primrec_body.comp (Primrec.pair Primrec.id (Primrec.const 0))))

theorem primrec_unmask : Primrec unmask := by
  have h : Primrec₂ fun (x : List Bool) (k : ℕ) => x.getD k false :=
    Primrec.list_getD false
  exact primrec_filter_bool (Primrec.list_range.comp Primrec.list_length) h

theorem primrec_recsOf : Primrec recsOf :=
  Primrec.listFilterMap primrec_unmask
    (Primrec₂.mk (Primrec.decode.comp Primrec.snd))

end Upper

end HTN
