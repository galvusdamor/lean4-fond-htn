import HtnComplexity.PT.Arith
/-!
# Decoding in polynomial time

The typed calculus of `HtnComplexity/PT/Core.lean` computes on the codes `enc a`.  To decide a
*language* of codes one also has to recognise codes.  This file supplies **polynomial-time
decoders**:

* `HTN.Syn.PolyDom.BDec α` — a decoder `decR : List Bool → α × List Bool` reading one encoded
  value off the front of a bit list (`decR (enc a ++ r) = (a, r)`), a polynomial-time function of
  the calculus, together with the polynomial-time re-encoding `encL : α → List Bool`;
* instances for `Bool`, `ℕ`, products and lists — hence for every type built from these, in
  particular the descriptions of planning problems;
* `HTN.Syn.PolyDom.isCode` — the recogniser `x ↦ (enc (decR x).1 = x)`, which is exact:
  `isCode x = true ↔ ∃ a, enc a = x` (`HTN.Syn.PolyDom.isCode_iff`), and polynomial-time.

Here a bit list is itself a value of the calculus (of type `List Bool`), so all these are
statements about typed functions; `HtnComplexity/PT/Lang.lean` passes to raw bit strings.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

/-! ### Sizes -/

variable {α β σ : Type} [BEnc α] [BEnc β] [BEnc σ]

theorem sz_bool (b : Bool) : sz b = 1 := rfl

theorem sz_nat_le_two {n : ℕ} (h : n ≤ 2) : sz n ≤ 5 := by
  interval_cases n <;> simp [sz_nat, bitsOfNat_succ] <;> decide

/-! ### Self-delimiting strings, read by a fold -/

/-- The state of the reader: the mode (`0` expecting a marker, `1` expecting a data bit, `2`
finished), the bits read so far and the bits after the string. -/
abbrev BState : Type := ℕ × List Bool × List Bool

/-- One step of the reader. -/
def bstrStep (s : BState) (b : Bool) : BState :=
  bif s.1 == 0 then (bif b then (1, s.2) else (2, s.2))
  else bif s.1 == 1 then (0, s.2.1 ++ [b], s.2.2)
  else (2, s.2.1, s.2.2 ++ [b])

/-- **Reading a self-delimiting string**: its content and the rest. -/
def bstrParse (x : List Bool) : List Bool × List Bool :=
  ((x.foldl bstrStep (0, [], [])).2.1, (x.foldl bstrStep (0, [], [])).2.2)

theorem foldl_bstrStep_done (c r t : List Bool) :
    t.foldl bstrStep (2, c, r) = (2, c, r ++ t) := by
  induction t generalizing r with
  | nil => simp
  | cons b t ih => simp [bstrStep, ih]

theorem foldl_bstrStep_bstr (w c : List Bool) :
    (bstr w).foldl bstrStep (0, c, []) = (2, c ++ w, []) := by
  induction w generalizing c with
  | nil => simp [bstr, bstrStep]
  | cons b w ih =>
    simp only [bstr, List.foldr_cons, List.foldl_cons]
    have : bstrStep (bstrStep (0, c, []) true) b = (0, c ++ [b], []) := by simp [bstrStep]
    rw [this]
    have := ih (c ++ [b])
    simp only [bstr] at this
    rw [this, List.append_assoc]; rfl

theorem bstrParse_bstr (w r : List Bool) : bstrParse (bstr w ++ r) = (w, r) := by
  simp [bstrParse, List.foldl_append, foldl_bstrStep_bstr, foldl_bstrStep_done]

theorem sz_bstrStep (s : BState) (b : Bool) : sz (bstrStep s b) ≤ sz s + 9 := by
  obtain ⟨m, c, r⟩ := s
  have hm : sz m ≥ 1 := by rw [sz_nat]; omega
  have h0 := sz_nat_le_two (n := 0) (by omega)
  have h1 := sz_nat_le_two (n := 1) (by omega)
  have h2 := sz_nat_le_two (n := 2) (by omega)
  simp only [bstrStep]
  cases m == 0 <;> cases b <;> cases m == 1 <;>
    simp only [cond_true, cond_false, sz_prod, sz_append_single, sz_bool] <;> omega

theorem pt_bstrStep : PT fun q : List Bool × BState × Bool => bstrStep q.2.1 q.2.2 := by
  unfold bstrStep
  have hm : PT fun q : List Bool × BState × Bool => q.2.1.1 := PT.fst.comp (PT.fst.comp PT.snd)
  have hc : PT fun q : List Bool × BState × Bool => q.2.1.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.fst.comp PT.snd))
  have hr : PT fun q : List Bool × BState × Bool => q.2.1.2.2 :=
    PT.snd.comp (PT.snd.comp (PT.fst.comp PT.snd))
  have hb : PT fun q : List Bool × BState × Bool => q.2.2 := PT.snd.comp PT.snd
  have hs : PT fun q : List Bool × BState × Bool => q.2.1.2 := PT.snd.comp (PT.fst.comp PT.snd)
  refine PT.cond (PT.beq hm (PT.const (0 : ℕ))) ?_ (PT.cond (PT.beq hm (PT.const (1 : ℕ))) ?_ ?_)
  · exact PT.cond hb (PT.pair (PT.const (1 : ℕ)) hs) (PT.pair (PT.const (2 : ℕ)) hs)
  · exact PT.pair (PT.const (0 : ℕ)) (PT.pair (PT.append hc (PT.single hb)) hr)
  · exact PT.pair (PT.const (2 : ℕ)) (PT.pair hc (PT.append hr (PT.single hb)))

theorem pt_bstrParse : PT bstrParse := by
  have h : PT fun x : List Bool => x.foldl bstrStep (0, [], []) :=
    PT.foldl (α := List Bool) (β := Bool) (σ := BState) (g := fun _ s b => bstrStep s b) PT.id
      (PT.const _) pt_bstrStep (c := 0) (d := 9)
      fun _ s _ _ => by simpa using sz_bstrStep s _
  exact PT.pair (PT.fst.comp (PT.snd.comp h)) (PT.snd.comp (PT.snd.comp h))

theorem length_bstrParse_fst_le (x : List Bool) : (bstrParse x).1.length ≤ x.length := by
  have key : ∀ (t : List Bool) (s : BState), s.2.1.length + t.length ≥
      (t.foldl bstrStep s).2.1.length := by
    intro t
    induction t with
    | nil => intro s; simp
    | cons b t ih =>
      intro s
      simp only [List.foldl_cons, List.length_cons]
      have := ih (bstrStep s b)
      have h2 : (bstrStep s b).2.1.length ≤ s.2.1.length + 1 := by
        unfold bstrStep; cases s.1 == 0 <;> cases b <;> cases s.1 == 1 <;> simp
      omega
  simpa [bstrParse] using key x (0, [], [])

theorem length_bstrParse_snd_le (x : List Bool) : (bstrParse x).2.length ≤ x.length := by
  have key : ∀ (t : List Bool) (s : BState),
      (t.foldl bstrStep s).2.2.length ≤ s.2.2.length + t.length := by
    intro t
    induction t with
    | nil => intro s; simp
    | cons b t ih =>
      intro s
      simp only [List.foldl_cons, List.length_cons]
      have := ih (bstrStep s b)
      have h2 : (bstrStep s b).2.2.length ≤ s.2.2.length + 1 := by
        unfold bstrStep; cases s.1 == 0 <;> cases b <;> cases s.1 == 1 <;> simp
      omega
  simpa [bstrParse] using key x (0, [], [])

/-! ### Decoders -/

/-- **A polynomial-time decoder** for an encoded type. -/
class BDec (α : Type) [BEnc α] where
  /-- Read one encoded value off the front of a bit list. -/
  decR : List Bool → α × List Bool
  decR_enc : ∀ (a : α) (r : List Bool), decR (enc a ++ r) = (a, r)
  pt_decR : PT decR
  /-- The rest is never longer than the input. -/
  decR_length : ∀ x, (decR x).2.length ≤ x.length
  /-- The encoding, as a function of the calculus. -/
  pt_encL : PT fun a : α => (enc a : List Bool)

export BDec (decR)

instance : BDec Bool where
  decR x := (x.headI, x.tail)
  decR_enc a r := rfl
  pt_decR := PT.pair (PT.headI PT.id) (PT.tail PT.id)
  decR_length x := by simp
  pt_encL := PT.single PT.id

/-- The decoder of numbers. -/
def decNat (x : List Bool) : ℕ × List Bool := (natOfBits (bstrParse x).1, (bstrParse x).2)

theorem bstr_eq_flatMap (w : List Bool) : bstr w = w.flatMap (fun b => [true, b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [bstr] at ih ⊢; exact ih

instance : BDec ℕ where
  decR := decNat
  decR_enc n r := by
    simp [decNat, enc_nat, serNat, bstrParse_bstr, natOfBits_bitsOfNat]
  pt_decR := PT.pair (PT.ofBits (PT.fst.comp pt_bstrParse)) (PT.snd.comp pt_bstrParse)
  decR_length x := length_bstrParse_snd_le x
  pt_encL := by
    refine (PT.append (PT.flatMap (g := fun _ b => [true, b]) PT.bits
      (PT.cons (PT.const true) (PT.single PT.snd)))
      (PT.const [false])).of_eq fun n => ?_
    simp [enc_nat, serNat, bstr_eq_flatMap]

/-- The decoder of pairs. -/
def decProd [BDec α] [BDec β] (x : List Bool) : (α × β) × List Bool :=
  (((decR x : α × List Bool).1, (decR (decR x : α × List Bool).2 : β × List Bool).1),
    (decR (decR x : α × List Bool).2 : β × List Bool).2)

theorem decProd_enc [BDec α] [BDec β] (p : α × β) (r : List Bool) :
    decProd (enc p ++ r) = (p, r) := by
  rw [show enc p = enc p.1 ++ enc p.2 from rfl, List.append_assoc]
  simp [decProd, BDec.decR_enc]

instance [BDec α] [BDec β] : BDec (α × β) where
  decR := decProd
  decR_enc := decProd_enc
  pt_decR := by
    have h1 : PT fun x : List Bool => (decR x : α × List Bool) := BDec.pt_decR
    have h2 : PT fun x : List Bool => (decR (decR x : α × List Bool).2 : β × List Bool) :=
      BDec.pt_decR.comp (PT.snd.comp h1)
    exact PT.pair (PT.pair (PT.fst.comp h1) (PT.fst.comp h2)) (PT.snd.comp h2)
  decR_length x := (BDec.decR_length (α := β) _).trans (BDec.decR_length (α := α) x)
  pt_encL := PT.append (BDec.pt_encL.comp PT.fst) (BDec.pt_encL.comp PT.snd)

/-! ### Lists -/

theorem sz_listBool (l : List Bool) : sz l = 4 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [sz_cons, ih, sz_bool, List.length_cons]; ring

theorem sz_le_of_length_le {l l' : List Bool} (h : l.length ≤ l'.length) : sz l ≤ sz l' := by
  rw [sz_listBool, sz_listBool]; omega

section List

variable [BDec α]

/-- The state of the list reader: the values read, the rest, and whether the list is finished. -/
abbrev LState (α : Type) : Type := List α × List Bool × Bool

/-- One step of the list reader. -/
def lstep (s : LState α) : LState α :=
  bif s.2.2 then s
  else bif s.2.1.isEmpty then (s.1, [], true)
  else bif s.2.1.headI then
    (s.1 ++ [(decR (bstrParse s.2.1.tail).1 : α × List Bool).1], (bstrParse s.2.1.tail).2, false)
  else (s.1, s.2.1.tail, true)

/-- **The list decoder**: `sz x + 1` steps of the reader. -/
def decList (x : List Bool) : List α × List Bool :=
  ((lstep (α := α))^[sz x + 1] ([], x, false)).1 |> fun l =>
    (l, ((lstep (α := α))^[sz x + 1] ([], x, false)).2.1)

theorem lstep_done (acc : List α) (r : List Bool) : lstep (acc, r, true) = (acc, r, true) := rfl

theorem iterate_lstep_done (acc : List α) (r : List Bool) (k : ℕ) :
    (lstep (α := α))^[k] (acc, r, true) = (acc, r, true) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, lstep_done, ih]

theorem iterate_lstep_enc (l : List α) (acc : List α) (r : List Bool) :
    (lstep (α := α))^[l.length + 1] (acc, enc l ++ r, false) = (acc ++ l, r, true) := by
  induction l generalizing acc with
  | nil => simp [enc_nil, lstep]
  | cons a l ih =>
    rw [Function.iterate_succ_apply, enc_cons]
    have : lstep (acc, true :: (bstr (enc a) ++ enc l) ++ r, false) =
        (acc ++ [a], enc l ++ r, false) := by
      simp only [lstep, List.cons_append, List.isEmpty_cons, List.headI_cons, List.tail_cons,
        cond_false, cond_true, List.append_assoc, bstrParse_bstr]
      rw [show enc a = enc a ++ [] by simp, BDec.decR_enc]
    rw [this, show (a :: l).length = l.length + 1 from rfl, ih]
    simp

theorem decList_enc (l : List α) (r : List Bool) : decList (enc l ++ r) = (l, r) := by
  have hlen : l.length + 1 ≤ sz (enc l ++ r) + 1 := by
    have h1 : l.length ≤ (enc l).length := by
      have := length_le_sz l; rw [sz] at this; exact this
    have h2 : (enc l ++ r).length ≤ sz (enc l ++ r) := length_le_sz _
    simp only [List.length_append] at h2
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hlen
  have hk' : sz (enc l ++ r) + 1 = k + (l.length + 1) := by omega
  show (((lstep (α := α))^[sz (enc l ++ r) + 1] ([], enc l ++ r, false)).1,
    ((lstep (α := α))^[sz (enc l ++ r) + 1] ([], enc l ++ r, false)).2.1) = (l, r)
  rw [hk', Function.iterate_add_apply, iterate_lstep_enc, iterate_lstep_done]
  simp

theorem length_rest_lstep (s : LState α) : (lstep s).2.1.length ≤ s.2.1.length := by
  unfold lstep
  cases s.2.2 <;> simp only [cond_true, cond_false, le_refl]
  cases h : s.2.1 with
  | nil => simp
  | cons b t =>
    have := length_bstrParse_snd_le t
    cases b <;> simp [List.isEmpty_cons] <;> omega

theorem length_rest_iterate (x : List Bool) (k : ℕ) :
    ((lstep (α := α))^[k] ([], x, false)).2.1.length ≤ x.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact (length_rest_lstep _).trans ih

theorem pt_lstep : PT₂ fun (_ : List Bool) (s : LState α) => lstep s := by
  unfold PT₂ lstep
  have hs : PT fun q : List Bool × LState α => q.2 := PT.snd
  have hacc : PT fun q : List Bool × LState α => q.2.1 := PT.fst.comp hs
  have hr : PT fun q : List Bool × LState α => q.2.2.1 := PT.fst.comp (PT.snd.comp hs)
  have hd : PT fun q : List Bool × LState α => q.2.2.2 := PT.snd.comp (PT.snd.comp hs)
  have hp : PT fun q : List Bool × LState α => bstrParse q.2.2.1.tail := pt_bstrParse.comp (PT.tail hr)
  refine PT.cond hd hs (PT.cond (PT.isEmpty hr) (PT.pair hacc (PT.pair PT.nil (PT.const true)))
    (PT.cond (PT.headI hr) ?_ (PT.pair hacc (PT.pair (PT.tail hr) (PT.const true)))))
  exact PT.pair (PT.append hacc (PT.single (PT.fst.comp (BDec.pt_decR.comp (PT.fst.comp hp)))))
    (PT.pair (PT.snd.comp hp) (PT.const false))

/-- The size of the reader's state stays polynomial. -/
theorem sz_iterate_lstep (cα dα : ℕ) (hα : ∀ x, sz (decR x : α × List Bool) ≤ dα * (sz x + 1) ^ cα)
    (x : List Bool) (k : ℕ) :
    sz ((lstep (α := α))^[k] ([], x, false)).1 ≤ 1 +
      (x.length - ((lstep (α := α))^[k] ([], x, false)).2.1.length) *
        (2 * (dα * (sz x + 1) ^ cα) + 2) := by
  induction k with
  | zero => simp [sz_nil]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set st := (lstep (α := α))^[k] ([], x, false) with hst
    have hrx : st.2.1.length ≤ x.length := length_rest_iterate x k
    obtain ⟨acc, r, d⟩ := st
    simp only at ih hrx
    unfold lstep
    cases d
    · simp only [cond_false]
      cases r with
      | nil => simpa using ih
      | cons b t =>
        cases b
        · simp only [List.isEmpty_cons, List.headI_cons, cond_false, List.tail_cons,
            List.length_cons] at ih ⊢
          calc sz acc ≤ 1 + (x.length - (t.length + 1)) * (2 * (dα * (sz x + 1) ^ cα) + 2) := ih
            _ ≤ 1 + (x.length - t.length) * (2 * (dα * (sz x + 1) ^ cα) + 2) :=
              Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
        · simp only [List.isEmpty_cons, List.headI_cons, cond_false, cond_true, List.tail_cons,
            List.length_cons] at ih hrx ⊢
          set e := (bstrParse t).1
          have hlt : (bstrParse t).2.length ≤ t.length := length_bstrParse_snd_le t
          have hel : e.length ≤ x.length := (length_bstrParse_fst_le t).trans (by omega)
          have hsa : sz (decR e : α × List Bool).1 ≤ dα * (sz x + 1) ^ cα := by
            have h1 := hα e
            rw [sz_prod] at h1
            have h2 : sz e ≤ sz x := sz_le_of_length_le hel
            have h3 : (sz e + 1) ^ cα ≤ (sz x + 1) ^ cα := Nat.pow_le_pow_left (by omega) _
            calc sz (decR e : α × List Bool).1 ≤ dα * (sz e + 1) ^ cα := by omega
              _ ≤ dα * (sz x + 1) ^ cα := Nat.mul_le_mul_left _ h3
          rw [sz_append_single]
          have hk : x.length - (bstrParse t).2.length ≥ (x.length - (t.length + 1)) + 1 := by omega
          calc sz acc + 2 * sz (decR e : α × List Bool).1 + 2
              ≤ 1 + (x.length - (t.length + 1)) * (2 * (dα * (sz x + 1) ^ cα) + 2) +
                  (2 * (dα * (sz x + 1) ^ cα) + 2) := by omega
            _ = 1 + ((x.length - (t.length + 1)) + 1) * (2 * (dα * (sz x + 1) ^ cα) + 2) := by ring
            _ ≤ 1 + (x.length - (bstrParse t).2.length) * (2 * (dα * (sz x + 1) ^ cα) + 2) :=
              Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _
    · simpa using ih

theorem pt_decList : PT (decList (α := α)) := by
  obtain ⟨cα, dα, hα⟩ := (BDec.pt_decR (α := α)).pb
  have hb : ∀ (x : List Bool) k, sz ((lstep (α := α))^[k] ([], x, false)) ≤
      (6 + 2 * dα) * (sz x + 1) ^ (cα + 2) := by
    intro x k
    have h1 := sz_iterate_lstep cα dα hα x k
    have h2 : sz ((lstep (α := α))^[k] ([], x, false)).2.1 ≤ sz x :=
      sz_le_of_length_le (length_rest_iterate x k)
    have h3 : sz ((lstep (α := α))^[k] ([], x, false)).2.2 ≤ 1 := by
      cases ((lstep (α := α))^[k] ([], x, false)).2.2 <;> rfl
    have hxl : x.length ≤ sz x + 1 := by rw [sz_listBool]; omega
    generalize (lstep (α := α))^[k] ([], x, false) = st at h1 h2 h3 ⊢
    obtain ⟨acc, r, d⟩ := st
    simp only [sz_prod] at h1 h2 h3 ⊢
    set P := (sz x + 1) ^ cα with hP
    set R := (sz x + 1) ^ (cα + 2) with hR
    have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
    have hPR : (sz x + 1) * ((sz x + 1) * P) = R := by rw [hP, hR]; ring
    have hR1 : sz x + 1 ≤ R := by
      calc sz x + 1 = (sz x + 1) * 1 * 1 := by ring
        _ ≤ (sz x + 1) * (sz x + 1) * P := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hP1
        _ = R := by rw [← hPR]; ring
    have e1 : (x.length - r.length) * (2 * (dα * P) + 2) ≤ (sz x + 1) * ((2 * dα + 2) * P) :=
      Nat.mul_le_mul (by omega) (by nlinarith)
    have e2 : (sz x + 1) * ((2 * dα + 2) * P) ≤ (2 * dα + 2) * R := by
      calc (sz x + 1) * ((2 * dα + 2) * P) = (2 * dα + 2) * ((sz x + 1) * P) := by ring
        _ ≤ (2 * dα + 2) * ((sz x + 1) * ((sz x + 1) * P)) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
        _ = (2 * dα + 2) * R := by rw [hPR]
    have : (6 + 2 * dα) * R = (2 * dα + 2) * R + 4 * R := by ring
    omega
  have hit := PT.iterate (init := fun x : List Bool => (([] : List α), x, false))
    (step := fun _ s => lstep s) (PT.pair PT.nil (PT.pair PT.id (PT.const false))) pt_lstep hb 1 1
  refine (PT.pair (PT.fst.comp hit) (PT.fst.comp (PT.snd.comp hit))).of_eq fun x => ?_
  simp [decList]

theorem decList_length (x : List Bool) : (decList (α := α) x).2.length ≤ x.length :=
  length_rest_iterate x _

theorem pt_encL_list : PT fun l : List α => (enc l : List Bool) := by
  refine (PT.append (PT.flatMap (g := fun _ a => true :: bstr (enc a)) PT.id ?_)
    (PT.const [false])).of_eq fun l => ?_
  · refine PT.cons (PT.const true) ?_
    have h : PT fun q : List α × α => (enc q.2 : List Bool) := BDec.pt_encL.comp PT.snd
    refine (PT.append (PT.flatMap (g := fun _ b => [true, b]) h
      (PT.cons (PT.const true) (PT.single PT.snd))) (PT.const [false])).of_eq fun q => ?_
    rw [bstr_eq_flatMap]
  · induction l with
    | nil => rfl
    | cons a l ih =>
      rw [enc_cons, List.flatMap_cons, List.append_assoc, ih]
      rfl

instance : BDec (List α) where
  decR := decList
  decR_enc := decList_enc
  pt_decR := pt_decList
  decR_length := decList_length
  pt_encL := pt_encL_list

end List

/-! ### The recogniser -/

/-- **Is this bit list the code of a value of `α`?** -/
def isCode (α : Type) [BEnc α] [BDec α] (x : List Bool) : Bool :=
  decide ((enc (decR x : α × List Bool).1 : List Bool) = x)

theorem isCode_iff {α : Type} [BEnc α] [BDec α] (x : List Bool) :
    isCode α x = true ↔ ∃ a : α, enc a = x := by
  unfold isCode
  constructor
  · intro h; exact ⟨_, of_decide_eq_true h⟩
  · rintro ⟨a, rfl⟩
    rw [show enc a = enc a ++ [] by simp, BDec.decR_enc]
    simp

theorem pt_isCode (α : Type) [BEnc α] [BDec α] : PT (isCode α) := by
  unfold isCode
  exact PT.eq (BDec.pt_encL.comp (PT.fst.comp BDec.pt_decR)) PT.id

end PolyDom

end Syn

end HTN
