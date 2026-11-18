import HtnComplexity.Logspace.Located
/-!
# Parsing codes by positions

The codes of descriptions are built from numbers, bits, pairs and lists
(`HTN.Syn.PolyDom.BEnc`).  `HTN.Logspace.Fmt` names such a format and `HTN.Logspace.Fmt.enc` its
code.  `HTN.Logspace.prs F w s` parses a code of `F` in `w` from position `s` by positions only:
it returns the position after the code, or `|w| + 1` if there is none.  It reads the string
only through single bits, the content of a nested string at its odd positions
(`HTN.Logspace.cstr`), and it is written so that a term of the fold language computes it
(`HtnComplexity/Logspace/ParseT.lean`).

* **`HTN.Logspace.prs_enc`** — on a code the parse returns its end;
* **`HTN.Logspace.exists_of_prs_le`** — if the parse succeeds, a code is there.
-/

namespace HTN

namespace Logspace

open Syn PTime

/-! ### Formats -/

/-- **Formats of codes.** -/
inductive Fmt where
  | nat
  | bool
  | pair (F G : Fmt)
  | list (F : Fmt)

/-- The values of a format. -/
@[reducible] def Fmt.ty : Fmt → Type
  | .nat => ℕ
  | .bool => Bool
  | .pair F G => F.ty × G.ty
  | .list F => List F.ty

/-- **The code of a value of a format.** -/
def Fmt.enc : (F : Fmt) → F.ty → List Bool
  | .nat, n => serNat n
  | .bool, b => [b]
  | .pair F G, a => F.enc a.1 ++ G.enc a.2
  | .list F, l => blist (List.map F.enc l)

theorem Fmt.enc_list (F : Fmt) (l : List F.ty) : (Fmt.list F).enc l = blist (l.map F.enc) := rfl

theorem Fmt.enc_pair (F G : Fmt) (a : F.ty) (b : G.ty) : (Fmt.pair F G).enc (a, b) = F.enc a ++ G.enc b :=
  rfl

theorem blist_ne_nil (l : List (List Bool)) : blist l ≠ [] := by
  cases l <;> simp [blist]

theorem Fmt.enc_ne_nil : ∀ (F : Fmt) (a : F.ty), F.enc a ≠ []
  | .nat, n => by simp [Fmt.enc, serNat, bstr]; cases bitsOfNat n <;> simp
  | .bool, b => by simp [Fmt.enc]
  | .pair F _, a => by simp [Fmt.enc, Fmt.enc_ne_nil F a.1]
  | .list _, l => blist_ne_nil _

/-! ### Canonical numerals -/

/-- A canonical numeral: empty or ending in `true`. -/
def Canon (c : List Bool) : Prop := c.length = 0 ∨ c.getD (c.length - 1) false = true

theorem canon_bitsOfNat (n : ℕ) : Canon (bitsOfNat n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => left; simp
    | m + 1 =>
      right
      rw [bitsOfNat_succ]
      have hlt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by norm_num)
      rcases ih _ hlt with h | h
      · have h0 : (m + 1) / 2 = 0 := by
          by_contra hne
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
          rw [hk, bitsOfNat_succ] at h; simp at h
        have : (m + 1) % 2 = 1 := by omega
        rw [List.length_eq_zero_iff.1 h]; simp [this]
      · have hne : (bitsOfNat ((m + 1) / 2)).length ≠ 0 := by
          intro h0; rw [List.length_eq_zero_iff.1 h0] at h; simp at h
        simp only [List.length_cons, Nat.add_sub_cancel]
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
        rw [hk, List.getD_cons_succ]; rw [hk] at h; simpa using h

theorem bitsOfNat_natOfBits_of_canon : ∀ c : List Bool, Canon c → bitsOfNat (natOfBits c) = c
  | [], _ => by simp
  | b :: c, h => by
    rcases h with h | h
    · simp at h
    · rcases c with _ | ⟨b', c'⟩
      · simp at h; subst h; simp [natOfBits]
      · have hc : Canon (b' :: c') := by
          right; simpa using h
        have ih := bitsOfNat_natOfBits_of_canon (b' :: c') hc
        have hpos : natOfBits (b' :: c') ≠ 0 := by
          intro h0; rw [h0] at ih; simp at ih
        rw [natOfBits_cons]
        obtain ⟨k, hk⟩ : ∃ k, (if b then 1 else 0) + 2 * natOfBits (b' :: c') = k + 1 :=
          ⟨(if b then 1 else 0) + 2 * natOfBits (b' :: c') - 1, by omega⟩
        rw [hk, bitsOfNat_succ, ← hk]
        have h1 : ((if b then 1 else 0) + 2 * natOfBits (b' :: c')) / 2 = natOfBits (b' :: c') := by
          cases b <;> simp <;> omega
        rw [h1, ih]
        cases b <;> simp <;> omega

/-! ### First indices -/

/-- The least `j < N` with `f j`, or `N`. -/
def firstIdx (f : ℕ → Bool) (N : ℕ) : ℕ := ((List.range N).find? f).getD N

theorem firstIdx_succ (f : ℕ → Bool) (N : ℕ) :
    firstIdx f (N + 1) = if firstIdx f N < N then firstIdx f N else if f N then N else N + 1 := by
  unfold firstIdx
  rw [List.range_succ, List.find?_append]
  rcases h : (List.range N).find? f with _ | j
  · simp only [Option.none_or, Option.getD_none, lt_irrefl, if_false]
    by_cases hf : f N <;> simp [List.find?, hf]
  · have hj : j < N := List.mem_range.1 (List.mem_of_find?_eq_some h)
    simp [hj]

theorem firstIdx_le (f : ℕ → Bool) : ∀ N, firstIdx f N ≤ N := by
  intro N
  induction N with
  | zero => simp [firstIdx]
  | succ N ih => rw [firstIdx_succ]; split_ifs <;> omega

theorem firstIdx_spec (f : ℕ → Bool) : ∀ N, (∀ j < firstIdx f N, f j = false) ∧
    (firstIdx f N < N → f (firstIdx f N) = true) := by
  intro N
  induction N with
  | zero => simp [firstIdx]
  | succ N ih =>
    rw [firstIdx_succ]
    have hle := firstIdx_le f N
    by_cases h : firstIdx f N < N
    · simp only [h, if_true]; exact ⟨ih.1, fun _ => ih.2 h⟩
    · have he : firstIdx f N = N := by omega
      simp only [h, if_false]
      by_cases hf : f N
      · simp only [hf, if_true]; exact ⟨fun j hj => ih.1 j (by omega), fun _ => by simp [hf]⟩
      · have hf' : f N = false := by simpa using hf
        simp only [hf', Bool.false_eq_true, if_false]
        refine ⟨fun j hj => ?_, fun h' => by omega⟩
        rcases Nat.lt_or_ge j N with hj' | hj'
        · exact ih.1 j (by omega)
        · rw [show j = N by omega]; simpa using hf

theorem firstIdx_eq {f : ℕ → Bool} {N j : ℕ} (hj : j < N) (hf : f j = true) (hb : ∀ i < j, f i = false) :
    firstIdx f N = j := by
  obtain ⟨h1, h2⟩ := firstIdx_spec f N
  rcases lt_trichotomy (firstIdx f N) j with h | h | h
  · have := h2 (by omega); rw [hb _ h] at this; simp at this
  · exact h
  · rw [h1 j h] at hf; simp at hf

/-! ### Self-delimiting strings by positions -/

theorem bt_drop (w : List Bool) (s i : ℕ) : bt (w.drop s) i = bt w (s + i) := by
  simp only [bt, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The length of the content of the self-delimiting string at `s`. -/
def layLen (w : List Bool) (s : ℕ) : ℕ := firstIdx (fun j => !bt w (s + 2 * j)) w.length

/-- The content (`j` bits) of the self-delimiting string at `s`. -/
def cstr (w : List Bool) (s j : ℕ) : List Bool := (List.range j).map fun k => bt w (s + 2 * k + 1)

theorem cstr_succ (w : List Bool) (s j : ℕ) : cstr w s (j + 1) = bt w (s + 1) :: cstr w (s + 2) j := by
  simp only [cstr, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply]; congr 1; omega

theorem length_cstr (w : List Bool) (s j : ℕ) : (cstr w s j).length = j := by simp [cstr]

/-- A self-delimiting string at `s`, by positions. -/
theorem bstr_at {w : List Bool} {s : ℕ} {c r : List Bool} (h : w.drop s = bstr c ++ r) :
    (∀ j < c.length, bt w (s + 2 * j) = true) ∧ bt w (s + 2 * c.length) = false ∧
      s + 2 * c.length < w.length ∧ layLen w s = c.length ∧ cstr w s c.length = c := by
  have hb : ∀ i, bt w (s + i) = bt (bstr c ++ r) i := fun i => by rw [← bt_drop, h]
  have hl := length_bstr c
  have he : ∀ j ≤ c.length, bt w (s + 2 * j) = decide (j < c.length) := by
    intro j hj
    rw [hb, bt, List.getD_append _ _ _ _ (by omega), bstr_getD_even c j hj]
  have hlen : s + 2 * c.length < w.length := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_append] at this
    omega
  refine ⟨fun j hj => by rw [he j hj.le]; simpa using hj, by rw [he _ le_rfl]; simp, hlen, ?_, ?_⟩
  · unfold layLen
    exact firstIdx_eq (by omega) (by rw [he _ le_rfl]; simp)
      (fun i hi => by rw [he i hi.le]; simpa using hi)
  · apply List.ext_getElem (by simp [length_cstr])
    intro k hk _
    simp only [cstr, List.getElem_map, List.getElem_range]
    rw [show s + 2 * k + 1 = s + (2 * k + 1) by ring, hb, bt,
      List.getD_append _ _ _ _ (by rw [length_cstr] at hk; omega),
      bstr_getD_odd c k (by rw [length_cstr] at hk; exact hk), List.getD_eq_getElem]

/-- The converse: a string of escaped bits with its terminator is a self-delimiting string. -/
theorem drop_eq_bstr {w : List Bool} : ∀ {s j : ℕ}, (∀ i < j, bt w (s + 2 * i) = true) →
    s + 2 * j < w.length → bt w (s + 2 * j) = false →
    w.drop s = bstr (cstr w s j) ++ w.drop (s + 2 * j + 1) := by
  intro s j
  induction j generalizing s with
  | zero =>
    intro _ hs hb
    simp only [mul_zero, add_zero] at hs hb ⊢
    simp only [cstr, List.range_zero, List.map_nil, bstr, List.foldr_nil]
    rw [List.drop_eq_getElem_cons hs]
    simp only [bt, List.getD_eq_getElem _ _ hs] at hb
    simp [hb]
  | succ j ih =>
    intro hesc hs hb
    have h0 := hesc 0 (by omega)
    rw [cstr_succ]
    have hs1 : s + 1 < w.length := by omega
    have hrest := ih (s := s + 2)
      (fun i hi => by rw [show s + 2 + 2 * i = s + 2 * (i + 1) by ring]; exact hesc _ (by omega)) (by omega) (by rw [show s + 2 + 2 * j = s + 2 * (j + 1) by ring]; exact hb)
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons hs1, hrest]
    simp only [mul_zero, add_zero, bt, List.getD_eq_getElem _ _ (show s < w.length by omega),
      List.getD_eq_getElem _ _ hs1] at h0 ⊢
    simp only [bstr, List.foldr_cons, h0, List.cons_append]
    rw [show s + 2 + 2 * j + 1 = s + 2 * (j + 1) + 1 by ring]

/-! ### The parser -/

/-- One step through a list: at an entry (a leading `true`), check the entry with `q` and move
behind it; at the end (a leading `false`) stay. -/
def lstep (q : List Bool → ℕ → ℕ) (w : List Bool) (acc : ℕ) : ℕ :=
  if bt w acc = true then
    if acc + 1 + 2 * layLen w (acc + 1) < w.length ∧ bt w (acc + 1 + 2 * layLen w (acc + 1)) = false then
      if q (cstr w (acc + 1) (layLen w (acc + 1))) 0 = layLen w (acc + 1) then
        acc + 2 + 2 * layLen w (acc + 1)
      else w.length + 1
    else w.length + 1
  else acc

/-- **The parser**: the position after the code of `F` at `s`, or `|w| + 1`. -/
def prs : Fmt → List Bool → ℕ → ℕ
  | .nat, w, s =>
    if s + 2 * layLen w s < w.length ∧ bt w (s + 2 * layLen w s) = false ∧
        (layLen w s = 0 ∨ bt w (s + 2 * layLen w s - 1) = true) then s + 2 * layLen w s + 1
    else w.length + 1
  | .bool, w, s => if s < w.length then s + 1 else w.length + 1
  | .pair F G, w, s => if prs F w s ≤ w.length then prs G w (prs F w s) else w.length + 1
  | .list F, w, s =>
    if bt w ((List.range (w.length + 1)).foldl (fun acc _ => lstep (prs F) w acc) s) = false ∧
        (List.range (w.length + 1)).foldl (fun acc _ => lstep (prs F) w acc) s < w.length then
      (List.range (w.length + 1)).foldl (fun acc _ => lstep (prs F) w acc) s + 1
    else w.length + 1

theorem foldl_range_iter (f : ℕ → ℕ) : ∀ (N a : ℕ), (List.range N).foldl (fun acc _ => f acc) a = f^[N] a := by
  intro N
  induction N with
  | zero => intro a; rfl
  | succ N ih => intro a; rw [List.range_succ, List.foldl_append, ih]; simp [Function.iterate_succ_apply']

theorem canon_cstr_iff {w : List Bool} {s j : ℕ} (hj : s + 2 * j < w.length) :
    Canon (cstr w s j) ↔ (j = 0 ∨ bt w (s + 2 * j - 1) = true) := by
  unfold Canon
  rw [length_cstr]
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; simp
  · simp only [show j ≠ 0 by omega, false_or]
    rw [List.getD_eq_getElem _ _ (by rw [length_cstr]; omega)]
    simp only [cstr, List.getElem_map, List.getElem_range]
    rw [show s + 2 * (j - 1) + 1 = s + 2 * j - 1 by omega]

theorem len_drop_ge {w r e : List Bool} {s : ℕ} (h : w.drop s = e ++ r) (he : e ≠ []) :
    s + e.length ≤ w.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  have : e.length ≠ 0 := by simpa using he
  omega

theorem blist_cons (x : List Bool) (l : List (List Bool)) : blist (x :: l) = true :: (bstr x ++ blist l) :=
  rfl

theorem blist_nil : blist [] = [false] := rfl

theorem length_blist_cons (x : List Bool) (l : List (List Bool)) :
    (blist (x :: l)).length = (bstr x).length + (blist l).length + 1 := by
  rw [blist_cons]; simp only [List.length_cons, List.length_append]

theorem length_le_blist (l : List (List Bool)) : l.length + 1 ≤ (blist l).length := by
  induction l with
  | nil => simp [blist_nil]
  | cons x l ih => rw [length_blist_cons]; simp; omega

theorem bt_of_drop {w r : List Bool} {s : ℕ} {b : Bool} (h : w.drop s = b :: r) : bt w s = b := by
  have := congrArg (fun z => bt z 0) h
  simpa [bt_drop] using this

theorem drop_blist_cons {w r x : List Bool} {l : List (List Bool)} {s : ℕ}
    (h : w.drop s = blist (x :: l) ++ r) :
    bt w s = true ∧ w.drop (s + 1) = bstr x ++ (blist l ++ r) ∧
      w.drop (s + 1 + (bstr x).length) = blist l ++ r := by
  rw [blist_cons, List.cons_append] at h
  refine ⟨bt_of_drop h, ?_, ?_⟩
  · rw [← List.drop_drop, h]; simp
  · rw [← List.drop_drop, ← List.drop_drop, h]; simp

theorem drop_blist_end {w r : List Bool} : ∀ {l : List (List Bool)} {s : ℕ},
    w.drop s = blist l ++ r → w.drop (s + (blist l).length - 1) = false :: r := by
  intro l
  induction l with
  | nil => intro s h; simpa [blist_nil] using h
  | cons x l ih =>
    intro s h
    have := ih (drop_blist_cons h).2.2
    rw [length_blist_cons]
    have hp := length_le_blist l
    rw [show s + ((bstr x).length + (blist l).length + 1) - 1 = s + 1 + (bstr x).length + (blist l).length - 1
      by omega]
    exact this

/-- **On a code the parser returns its end.** -/
theorem prs_enc : ∀ (F : Fmt) (w : List Bool) (s : ℕ) (a : F.ty) (r : List Bool),
    w.drop s = F.enc a ++ r → prs F w s = s + (F.enc a).length
  | .nat, w, s, n, r, h => by
    obtain ⟨-, hb, hlt, hlay, hc⟩ := bstr_at (c := bitsOfNat n) (r := r) h
    simp only [prs, hlay]
    have hcan : (bitsOfNat n).length = 0 ∨ bt w (s + 2 * (bitsOfNat n).length - 1) = true := by
      rw [← canon_cstr_iff hlt, hc]; exact canon_bitsOfNat n
    rw [if_pos ⟨hlt, hb, hcan⟩]
    simp only [Fmt.enc, serNat, length_bstr]; omega
  | .bool, w, s, b, r, h => by
    have := len_drop_ge h (Fmt.enc_ne_nil .bool b)
    simp only [prs, Fmt.enc, List.length_singleton] at this ⊢
    rw [if_pos (by omega)]
  | .pair F G, w, s, a, r, h => by
    have h1 : w.drop s = F.enc a.1 ++ (G.enc a.2 ++ r) := by rw [h]; simp [Fmt.enc]
    have e1 := prs_enc F w s a.1 _ h1
    have hle := len_drop_ge h1 (Fmt.enc_ne_nil F a.1)
    have h2 : w.drop (s + (F.enc a.1).length) = G.enc a.2 ++ r := by
      rw [← List.drop_drop, h1, List.drop_left]
    simp only [prs, e1, if_pos hle, prs_enc G w _ a.2 r h2, Fmt.enc, List.length_append]
    ring
  | .list F, w, s, l, r, h => by
    rw [Fmt.enc_list] at h ⊢
    have key : ∀ (l : List F.ty) (s : ℕ) (r : List Bool), w.drop s = blist (l.map F.enc) ++ r →
        ∀ N, l.length ≤ N → (lstep (prs F) w)^[N] s = s + (blist (l.map F.enc)).length - 1 := by
      intro l
      induction l with
      | nil =>
        intro s r h N _
        have hb : bt w s = false := bt_of_drop (by simpa [blist_nil] using h)
        have hfix : lstep (prs F) w s = s := by simp [lstep, hb]
        rw [Function.iterate_fixed hfix]
        simp [blist_nil]
      | cons a l ih =>
        intro s r h N hN
        obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
        rw [List.map_cons] at h
        obtain ⟨hb, h', hrest⟩ := drop_blist_cons h
        obtain ⟨-, hesc, hlt, hlay, hc⟩ := bstr_at h'
        have hin := prs_enc F (F.enc a) 0 a [] (by simp)
        have hstep : lstep (prs F) w s = s + 2 + 2 * (F.enc a).length := by
          simp only [lstep, hb, if_true, hlay, hc, hin]
          rw [if_pos ⟨hlt, hesc⟩]; simp
        rw [length_bstr, show s + 1 + (2 * (F.enc a).length + 1) = s + 2 + 2 * (F.enc a).length by ring]
          at hrest
        rw [Function.iterate_succ_apply, hstep, ih _ _ hrest N (by simp at hN; omega), List.map_cons,
          length_blist_cons, length_bstr]
        have := length_le_blist (l.map F.enc)
        omega
    have hle := len_drop_ge h (blist_ne_nil _)
    have hlen : l.length ≤ w.length + 1 := by
      have := length_le_blist (l.map F.enc)
      simp at this; omega
    have hk := key l s r h (w.length + 1) hlen
    have hpos : 1 ≤ (blist (l.map F.enc)).length := List.length_pos_iff.2 (blist_ne_nil _)
    have hend : bt w (s + (blist (l.map F.enc)).length - 1) = false := bt_of_drop (drop_blist_end h)
    simp only [prs, foldl_range_iter, hk]
    rw [if_pos ⟨hend, by omega⟩]
    omega

/-- **If the parser succeeds, a code is there.** -/
theorem exists_of_prs_le : ∀ (F : Fmt) (w : List Bool) (s : ℕ), prs F w s ≤ w.length →
    ∃ (a : F.ty) (r : List Bool), w.drop s = F.enc a ++ r
  | .nat, w, s, h => by
    simp only [prs] at h
    split_ifs at h with hc
    · obtain ⟨hlt, hb, hcan⟩ := hc
      obtain ⟨hesc, -⟩ := firstIdx_spec (fun j => !bt w (s + 2 * j)) w.length
      have hd := drop_eq_bstr (w := w) (s := s) (j := layLen w s)
        (fun i hi => by simpa using hesc i hi) hlt hb
      refine ⟨natOfBits (cstr w s (layLen w s)), w.drop (s + 2 * layLen w s + 1), ?_⟩
      rw [hd]
      simp only [Fmt.enc, serNat]
      rw [bitsOfNat_natOfBits_of_canon _ ((canon_cstr_iff hlt).2 hcan)]
    · omega
  | .bool, w, s, h => by
    simp only [prs] at h
    split_ifs at h with hs
    · exact ⟨w[s], w.drop (s + 1), by rw [List.drop_eq_getElem_cons hs]; rfl⟩
    · omega
  | .pair F G, w, s, h => by
    simp only [prs] at h
    split_ifs at h with h1
    · obtain ⟨a, r, ha⟩ := exists_of_prs_le F w s h1
      have e1 := prs_enc F w s a r ha
      rw [e1] at h
      obtain ⟨b, r', hb⟩ := exists_of_prs_le G w _ h
      refine ⟨(a, b), r', ?_⟩
      have : r = G.enc b ++ r' := by
        rw [← List.drop_drop, ha, List.drop_left] at hb; exact hb
      rw [ha, this]; simp [Fmt.enc]
    · omega
  | .list F, w, s, h => by
    simp only [prs, foldl_range_iter] at h
    split_ifs at h with hc
    · obtain ⟨hb, hlt⟩ := hc
      generalize he : (lstep (prs F) w)^[w.length + 1] s = e at hb hlt h
      have key : ∀ N acc, (lstep (prs F) w)^[N] acc = e →
          ∃ (l : List F.ty) (r : List Bool), w.drop acc = blist (l.map F.enc) ++ r := by
        intro N
        induction N with
        | zero =>
          intro acc hacc
          simp only [Function.iterate_zero, id] at hacc
          subst hacc
          refine ⟨[], w.drop (acc + 1), ?_⟩
          rw [List.drop_eq_getElem_cons hlt]
          simp only [bt, List.getD_eq_getElem _ _ hlt] at hb
          simp [blist_nil, hb]
        | succ N ih =>
          intro acc hacc
          rw [Function.iterate_succ_apply] at hacc
          by_cases hba : bt w acc = true
          · by_cases hc : acc + 1 + 2 * layLen w (acc + 1) < w.length ∧
                bt w (acc + 1 + 2 * layLen w (acc + 1)) = false
            · by_cases hq : prs F (cstr w (acc + 1) (layLen w (acc + 1))) 0 = layLen w (acc + 1)
              · have hst : lstep (prs F) w acc = acc + 2 + 2 * layLen w (acc + 1) := by
                  simp [lstep, hba, hc, hq]
                rw [hst] at hacc
                obtain ⟨l, r, hl⟩ := ih _ hacc
                obtain ⟨a, r', ha⟩ := exists_of_prs_le F _ 0
                  (by rw [hq, length_cstr])
                have hlen := prs_enc F _ 0 a r' ha
                rw [hq] at hlen
                have hr' : r' = [] := by
                  have := congrArg List.length ha
                  simp only [List.drop_zero, length_cstr, List.length_append] at this
                  rw [hlen] at this
                  exact List.length_eq_zero_iff.1 (by omega)
                subst hr'
                simp only [List.drop_zero, List.append_nil] at ha
                obtain ⟨hesc, -⟩ := firstIdx_spec (fun j => !bt w (acc + 1 + 2 * j)) w.length
                have hd := drop_eq_bstr (w := w) (s := acc + 1) (j := layLen w (acc + 1))
                  (fun i hi => by simpa using hesc i hi) hc.1 hc.2
                refine ⟨a :: l, r, ?_⟩
                have hacc_lt : acc < w.length := by omega
                rw [List.drop_eq_getElem_cons hacc_lt, hd, ha,
                  show acc + 1 + 2 * layLen w (acc + 1) + 1 = acc + 2 + 2 * layLen w (acc + 1) by ring, hl]
                simp only [bt, List.getD_eq_getElem _ _ hacc_lt] at hba
                rw [List.map_cons, blist_cons, hba]; simp
              · have hst : lstep (prs F) w acc = w.length + 1 := by simp [lstep, hba, hc, hq]
                rw [hst] at hacc
                have hfix : lstep (prs F) w (w.length + 1) = w.length + 1 := by
                  simp [lstep, bt, List.getD_eq_default _ _ (show w.length ≤ w.length + 1 by omega)]
                rw [Function.iterate_fixed hfix] at hacc
                omega
            · have hst : lstep (prs F) w acc = w.length + 1 := by
                simp only [lstep, hba, if_true]; rw [if_neg hc]
              rw [hst] at hacc
              have hfix : lstep (prs F) w (w.length + 1) = w.length + 1 := by
                simp [lstep, bt, List.getD_eq_default _ _ (show w.length ≤ w.length + 1 by omega)]
              rw [Function.iterate_fixed hfix] at hacc
              omega
          · have hst : lstep (prs F) w acc = acc := by simp [lstep, hba]
            rw [hst] at hacc
            exact ih acc hacc
      obtain ⟨l, r, hl⟩ := key _ s he
      exact ⟨l, r, by rw [Fmt.enc_list]; exact hl⟩
    · omega

end Logspace

end HTN
