import ComplexityTheory.TM.Theory.Machine
/-!
# Guessing an exponentially long witness is free at the exponential level

The source side of the three open cells of Table 3 needs, besides a hardness construction, the
statement

> `Σ₁` of the exponential scale is contained in `NEXPTIME`

(`HTN.Space.SigmaOneNExp`).  Unwound, `Σ₁` of the exponential scale is

> there is an exponential-time machine `M` and an exponentially long string `y` such that `M`
> accepts `x` together with `y`,

and the containment is the standard *guess the witness, then verify it* simulation: a
nondeterministic machine writes the witness on the tape itself.  Over the one-way infinite tape of
`ComplexityTheory/TM/Theory/Machine.lean` the witness does not even have to be written in a separate phase —
the machine can guess each witness cell at the moment it first reads it, because the part of the
tape beyond the input is blank and a blank cell is read at most once (the machines considered never
write a blank, so the first read of a cell is also the moment it stops being blank).

That is what this file formalises.

## Main definitions

* `TM.NTM.BlankAvoiding` — the machine never writes the blank symbol;
* `TM.NTM.guess` — the *guessing variant* of a machine: reading a blank, it may act as if it had
  read any bit, so that the blank part of the tape behaves like a nondeterministically chosen
  string;
* `TM.Refines` — `d` refines `c` if the two configurations agree except that `d` may still have
  blanks where `c` already has bits.

## Main results

* `TM.NTM.reaches_congr` — **locality**: a run of `n` steps depends only on the tape cells
  `≤ head + n`, so two configurations that agree there have matching runs;
* `TM.NTM.guess_reaches_of_reaches` — the guessing machine can mirror any run of the original
  machine on a completed tape (it guesses the right bits);
* `TM.NTM.exists_completion_of_guess_reaches` — conversely, every run of the guessing machine can
  be *explained*: there is a blank-free completion of the tape on which the original machine makes
  the same run;
* `TM.NTM.acceptsWithin_guess_iff` — the two together:

  `(M.guess).AcceptsWithin (x.map some) K ↔ ∃ y, y.length = K + 1 ∧
      M.AcceptsWithin ((x ++ y).map some) K`,

  i.e. guessing a witness of length `K + 1` costs nothing.  With `K = 2 ^ p(|x|)` this is exactly
  the simulation `Σ₁ ⊆ NEXPTIME` at the exponential scale; it is applied in
  `HtnCompilability/Space/ExpScale.lean`.
-/

namespace TM

variable {Q : Type*}

/-! ### Locality of a run -/

namespace NTM

/-- **A run of `n` steps only depends on the first `head + n + 1` tape cells.**  If `e` agrees
with `c` on those cells, then every run of `n` steps from `c` is matched by a run from `e` ending
in the same state. -/
theorem reaches_congr {Γ : Type*} (N : NTM Q Γ) :
    ∀ {n : ℕ} {c c' e : Config Q Γ}, N.Reaches n c c' → e.state = c.state → e.head = c.head →
      (∀ i ≤ c.head + n, e.tape i = c.tape i) → ∃ e', N.Reaches n e e' ∧ e'.state = c'.state := by
  intro n
  induction n with
  | zero =>
      intro c c' e h hstate _ _
      exact ⟨e, rfl, by rw [hstate, show c = c' from h]⟩
  | succ n ih =>
      intro c c' e h hstate hhead hag
      obtain ⟨d, hstep, hd⟩ := h
      obtain ⟨q', γ', m, hmem, rfl⟩ := hstep
      have hread : e.tape e.head = c.tape c.head := by
        rw [hhead]; exact hag c.head (by omega)
      refine ?_
      set e₁ : Config Q Γ := ⟨q', m.apply e.head, Function.update e.tape e.head γ'⟩ with he₁
      have hstep' : N.Step e e₁ := ⟨q', γ', m, by rw [hstate, hread]; exact hmem, rfl⟩
      have hag' : ∀ i ≤ m.apply c.head + n, e₁.tape i = (Function.update c.tape c.head γ') i := by
        intro i hi
        have hle : i ≤ c.head + (n + 1) := by
          have := m.apply_le c.head; omega
        by_cases hic : i = c.head
        · subst hic
          simp [he₁, hhead]
        · simp only [he₁, hhead, Function.update_of_ne hic]
          exact hag i hle
      obtain ⟨e', hreach, hstate'⟩ := ih hd (by simp [he₁]) (by simp [he₁, hhead]) hag'
      exact ⟨e', ⟨e₁, hstep', hreach⟩, hstate'⟩

/-! ### The guessing variant of a machine -/

/-- **A machine never writes the blank symbol.**  Over the alphabet `Option Bool` this is a
normalisation: a cell, once written, carries a bit. -/
def BlankAvoiding (M : NTM Q (Option Bool)) : Prop :=
  ∀ q γ t, t ∈ M.step q γ → t.2.1 ≠ none

/-- **The guessing variant of `M`.**  On a bit the machine behaves exactly like `M`; on a blank it
may behave like `M` reading any bit — i.e. it *guesses* the content of the still blank cell.  Since
`M` never writes a blank, a cell is read blank at most once, so the guesses made along a run are
consistent with one completion of the tape. -/
def guess (M : NTM Q (Option Bool)) : NTM Q (Option Bool) where
  step q γ := match γ with
    | some b => M.step q (some b)
    | none => {t | ∃ b : Bool, t ∈ M.step q (some b)}
  init := M.init
  accept := M.accept
  blank := M.blank

@[simp] lemma guess_init (M : NTM Q (Option Bool)) : (guess M).init = M.init := rfl
@[simp] lemma guess_accept (M : NTM Q (Option Bool)) : (guess M).accept = M.accept := rfl
@[simp] lemma guess_blank (M : NTM Q (Option Bool)) : (guess M).blank = M.blank := rfl

@[simp] lemma guess_step_some (M : NTM Q (Option Bool)) (q : Q) (b : Bool) :
    (guess M).step q (some b) = M.step q (some b) := rfl

lemma guess_step_none (M : NTM Q (Option Bool)) (q : Q) :
    (guess M).step q none = {t | ∃ b : Bool, t ∈ M.step q (some b)} := rfl

/-- The guessing variant never writes a blank either. -/
lemma BlankAvoiding.guess {M : NTM Q (Option Bool)} (h : BlankAvoiding M) :
    BlankAvoiding (NTM.guess M) := by
  intro q γ t ht
  cases γ with
  | some b => exact h q (some b) t ht
  | none =>
      obtain ⟨b, hb⟩ := ht
      exact h q (some b) t hb

end NTM

/-! ### Refinement: a partially blank tape -/

/-- `Refines d c` says that the configuration `d` is the configuration `c` with some of its cells
still blank: same state, same head position, and every cell of `d` is either blank or carries the
symbol `c` has there. -/
structure Refines (d c : Config Q (Option Bool)) : Prop where
  /-- Same state. -/
  state : d.state = c.state
  /-- Same head position. -/
  head : d.head = c.head
  /-- Every cell of `d` is blank or agrees with `c`. -/
  tape : ∀ i, d.tape i = none ∨ d.tape i = c.tape i

namespace NTM

/-! ### The guessing machine can mirror a run on a completed tape -/

/-- **The guesses can be made right.**  If `M` runs for `n` steps from a configuration `c` whose
relevant cells all carry bits, then from any configuration `d` refining `c` the guessing machine
has a matching run: whenever it reads a blank it guesses the bit `c` has there. -/
theorem guess_reaches_of_reaches {M : NTM Q (Option Bool)} (hba : BlankAvoiding M) :
    ∀ {n : ℕ} {c c' d : Config Q (Option Bool)}, M.Reaches n c c' →
      (∀ i ≤ c.head + n, c.tape i ≠ none) → Refines d c →
      ∃ d', (guess M).Reaches n d d' ∧ Refines d' c' := by
  intro n
  induction n with
  | zero =>
      intro c c' d h _ href
      exact ⟨d, rfl, by rwa [show c = c' from h] at href⟩
  | succ n ih =>
      intro c c' d h hnb href
      obtain ⟨e, hstep, he⟩ := h
      obtain ⟨q', γ', m, hmem, rfl⟩ := hstep
      have hnbhead : c.tape c.head ≠ none := hnb c.head (by omega)
      obtain ⟨b, hb⟩ : ∃ b : Bool, c.tape c.head = some b := by
        cases hc : c.tape c.head with
        | none => exact absurd hc hnbhead
        | some b => exact ⟨b, rfl⟩
      -- the guessing machine can take the same transition
      have hmem' : (q', γ', m) ∈ (guess M).step d.state (d.tape d.head) := by
        rcases href.tape d.head with hd | hd
        · rw [href.state, hd, guess_step_none]
          exact ⟨b, by rw [← hb]; exact hmem⟩
        · rw [href.state, hd, href.head, hb]
          rw [hb] at hmem
          exact hmem
      set d₁ : Config Q (Option Bool) :=
        ⟨q', m.apply d.head, Function.update d.tape d.head γ'⟩ with hd₁
      have hstep' : (guess M).Step d d₁ := ⟨q', γ', m, hmem', rfl⟩
      have hγ' : γ' ≠ none := hba c.state (c.tape c.head) (q', γ', m) hmem
      have href' : Refines d₁ ⟨q', m.apply c.head, Function.update c.tape c.head γ'⟩ := by
        refine ⟨rfl, by simp [hd₁, href.head], ?_⟩
        intro i
        by_cases hic : i = c.head
        · subst hic
          right
          simp [hd₁, href.head]
        · have hid : i ≠ d.head := by rw [href.head]; exact hic
          simp only [hd₁, Function.update_of_ne hid, Function.update_of_ne hic]
          exact href.tape i
      have hnb' : ∀ i ≤ (Config.mk q' (m.apply c.head)
          (Function.update c.tape c.head γ') : Config Q (Option Bool)).head + n,
          (Function.update c.tape c.head γ') i ≠ none := by
        intro i hi
        by_cases hic : i = c.head
        · subst hic; simpa using hγ'
        · rw [Function.update_of_ne hic]
          refine hnb i ?_
          have := m.apply_le c.head
          simp only at hi
          omega
      obtain ⟨d', hreach, hfin⟩ := ih he hnb' href'
      exact ⟨d', ⟨d₁, hstep', hreach⟩, hfin⟩

/-! ### Every run of the guessing machine is explained by a completion -/

/-- **Extraction of the guessed witness.**  Every run of the guessing machine comes from a run of
`M` on a tape without blanks that refines the starting configuration: the cells guessed along the
run are filled in with the guessed bits, the never-read cells arbitrarily. -/
theorem exists_completion_of_guess_reaches {M : NTM Q (Option Bool)} (hba : BlankAvoiding M) :
    ∀ {n : ℕ} {d d' : Config Q (Option Bool)}, (guess M).Reaches n d d' →
      ∃ c c' : Config Q (Option Bool), Refines d c ∧ (∀ i, c.tape i ≠ none) ∧
        M.Reaches n c c' ∧ c'.state = d'.state := by
  intro n
  induction n with
  | zero =>
      intro d d' h
      subst h
      refine ⟨⟨d.state, d.head, fun i => some ((d.tape i).getD false)⟩,
        ⟨d.state, d.head, fun i => some ((d.tape i).getD false)⟩, ⟨rfl, rfl, ?_⟩,
        by intro i; simp, rfl, rfl⟩
      intro i
      cases hi : d.tape i with
      | none => exact Or.inl rfl
      | some b => exact Or.inr (by simp [hi])
  | succ n ih =>
      intro d d' h
      obtain ⟨e, hstep, he⟩ := h
      obtain ⟨q', γ', m, hmem, rfl⟩ := hstep
      -- the symbol the guessing machine acted on, always a bit
      obtain ⟨β, hβnone, hβmem, hβref⟩ :
          ∃ β : Option Bool, β ≠ none ∧ (q', γ', m) ∈ M.step d.state β ∧
            (d.tape d.head = none ∨ d.tape d.head = β) := by
        cases hd : d.tape d.head with
        | some b =>
            refine ⟨some b, by simp, ?_, Or.inr rfl⟩
            rw [hd] at hmem
            exact hmem
        | none =>
            rw [hd, guess_step_none] at hmem
            obtain ⟨b, hb⟩ := hmem
            exact ⟨some b, by simp, hb, Or.inl rfl⟩
      have hγ' : γ' ≠ none := hba.guess d.state (d.tape d.head) (q', γ', m) hmem
      obtain ⟨ce, c', hrefe, hnbe, hreach, hstate⟩ := ih he
      -- `ce` already carries `γ'` at the written cell
      have hce : ce.tape d.head = γ' := by
        rcases hrefe.tape d.head with hd | hd
        · simp at hd; exact absurd hd hγ'
        · simpa using hd.symm
      refine ⟨⟨d.state, d.head, Function.update ce.tape d.head β⟩, c', ⟨rfl, rfl, ?_⟩, ?_, ?_,
        hstate⟩
      · intro i
        by_cases hid : i = d.head
        · subst hid; exact hβref.imp id (by simp)
        · simp only [Function.update_of_ne hid]
          have := hrefe.tape i
          simpa [Function.update_of_ne hid] using this
      · intro i
        by_cases hid : i = d.head
        · subst hid; simpa using hβnone
        · simpa [Function.update_of_ne hid] using hnbe i
      · refine ⟨ce, ⟨q', γ', m, by simpa using hβmem, ?_⟩, hreach⟩
        have hstate' : ce.state = q' := hrefe.state.symm
        have hhead' : ce.head = m.apply d.head := hrefe.head.symm
        have htape : Function.update (Function.update ce.tape d.head β) d.head γ' = ce.tape := by
          funext i
          by_cases hid : i = d.head
          · subst hid; simp [hce]
          · simp [Function.update_of_ne hid]
        cases ce with
        | mk st hd tp =>
            simp only at hstate' hhead' htape
            subst hstate'
            subst hhead'
            simp [htape]

/-! ### The simulation -/

lemma getD_map_some {l : List Bool} {i : ℕ} (hi : i < l.length) :
    (l.map some).getD i none = some l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

lemma getD_map_some_of_le {l : List Bool} {i : ℕ} (hi : l.length ≤ i) :
    (l.map some).getD i none = none := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_none (by simpa using hi)]
  rfl

/-- **Guessing an extra `K + 1` cells of input is free.**  A machine that never writes a blank
accepts `x` extended by some string `y` of length `K + 1` within `K` steps if and only if its
guessing variant accepts `x` alone within `K` steps.

With `K = 2 ^ p(|x|)` the left-hand side is the `Σ₁`-condition of the exponential scale — an
exponentially long witness verified in exponential time — and the right-hand side is membership of
`NEXPTIME`; this is the content of `HTN.Space.SigmaOneNExp`. -/
theorem acceptsWithin_guess_iff {M : NTM Q (Option Bool)} (hba : BlankAvoiding M)
    (hblank : M.blank = none) (x : List Bool) (K : ℕ) :
    (guess M).AcceptsWithin (x.map some) K ↔
      ∃ y : List Bool, y.length = K + 1 ∧ M.AcceptsWithin ((x ++ y).map some) K := by
  constructor
  · rintro ⟨n, hn, d', hreach, hacc⟩
    obtain ⟨c, c', href, hnb, hrun, hstate⟩ := exists_completion_of_guess_reaches hba hreach
    refine ⟨(List.range (K + 1)).map (fun j => (c.tape (x.length + j)).getD false), by simp, ?_⟩
    set y := (List.range (K + 1)).map (fun j => (c.tape (x.length + j)).getD false) with hy
    have hylen : y.length = K + 1 := by simp [hy]
    have hyget : ∀ j (hj : j < K + 1), y[j]'(by omega) = (c.tape (x.length + j)).getD false := by
      intro j hj
      simp [hy]
    -- the initial configuration on the completed input agrees with `c` where it matters
    have hc0head : c.head = 0 := by
      have := href.head
      simp [initConfig] at this
      omega
    have hag : ∀ i ≤ c.head + n, (M.initConfig ((x ++ y).map some)).tape i = c.tape i := by
      intro i hi
      have hiK : i ≤ K := by omega
      have hilt : i < (x ++ y).length := by simp [hylen]; omega
      have h1 : (M.initConfig ((x ++ y).map some)).tape i = some ((x ++ y)[i]'hilt) := by
        simp only [initConfig, hblank]
        exact getD_map_some hilt
      rw [h1]
      by_cases hix : i < x.length
      · have h2 : (x ++ y)[i]'hilt = x[i]'hix := List.getElem_append_left hix
        rw [h2]
        have h3 : ((guess M).initConfig (x.map some)).tape i = some (x[i]'hix) := by
          simp only [initConfig, guess_blank, hblank]
          exact getD_map_some hix
        rcases href.tape i with h | h
        · rw [h3] at h; exact absurd h (by simp)
        · rw [h3] at h; exact h
      · push_neg at hix
        have h2 : (x ++ y)[i]'hilt = y[i - x.length]'(by simp [hylen]; omega) :=
          List.getElem_append_right hix
        rw [h2, hyget (i - x.length) (by simp [hylen] at hilt ⊢; omega)]
        have hxi : x.length + (i - x.length) = i := by omega
        rw [hxi]
        cases hci : c.tape i with
        | none => exact absurd hci (hnb i)
        | some b => simp
    obtain ⟨e', hreach', hstate'⟩ :=
      reaches_congr M hrun (by simpa [initConfig] using href.state)
        (by simp [initConfig, hc0head]) hag
    exact ⟨n, hn, e', hreach', by rw [hstate', hstate]; exact hacc⟩
  · rintro ⟨y, hylen, n, hn, c', hrun, hacc⟩
    set c₀ := M.initConfig ((x ++ y).map some) with hc₀
    have hc₀tape : ∀ i, c₀.tape i = ((x ++ y).map some).getD i none := by
      intro i; simp [hc₀, initConfig, hblank]
    have hnb : ∀ i ≤ c₀.head + n, c₀.tape i ≠ none := by
      intro i hi
      have hi' : i < (x ++ y).length := by
        simp only [hc₀, initConfig] at hi
        simp [hylen]
        omega
      rw [hc₀tape, getD_map_some hi']
      simp
    have href : Refines ((guess M).initConfig (x.map some)) c₀ := by
      refine ⟨by simp [initConfig, hc₀], by simp [initConfig, hc₀], ?_⟩
      intro i
      by_cases hix : i < x.length
      · right
        have h1 : ((guess M).initConfig (x.map some)).tape i = some (x[i]'hix) := by
          simp only [initConfig, guess_blank, hblank]
          exact getD_map_some hix
        have hilt : i < (x ++ y).length := by simp; omega
        have h2 : c₀.tape i = some ((x ++ y)[i]'hilt) := by
          rw [hc₀tape]; exact getD_map_some hilt
        rw [h1, h2, List.getElem_append_left hix]
      · left
        push_neg at hix
        simp only [initConfig, guess_blank, hblank]
        exact getD_map_some_of_le hix
    obtain ⟨d', hreach, hfin⟩ := guess_reaches_of_reaches hba hrun hnb href
    exact ⟨n, hn, d', hreach, by rw [guess_accept, hfin.state]; exact hacc⟩

/-- **Acceptance within `K` steps only depends on the first `K + 1` input symbols.**  This is
locality, read on the input word. -/
theorem acceptsWithin_congr_input {Γ : Type*} (N : NTM Q Γ) {u v : List Γ} {K : ℕ}
    (h : ∀ i ≤ K, u.getD i N.blank = v.getD i N.blank) (hu : N.AcceptsWithin u K) :
    N.AcceptsWithin v K := by
  obtain ⟨n, hn, c, hreach, hacc⟩ := hu
  obtain ⟨e', hreach', hstate'⟩ :=
    reaches_congr N (e := N.initConfig v) hreach rfl rfl (fun i hi => (h i (by
      simp only [initConfig] at hi; omega)).symm)
  exact ⟨n, hn, e', hreach', by rw [hstate']; exact hacc⟩

/-- **Trailing symbols of the guessed part are irrelevant.**  A run of `K` steps on `x ++ u`
reads at most `K + 1` cells, so only the first `K + 1` symbols of `u` matter. -/
theorem acceptsWithin_append_take {M : NTM Q (Option Bool)} (hblank : M.blank = none)
    (x u : List Bool) {K : ℕ} (hu : K + 1 ≤ u.length) :
    M.AcceptsWithin ((x ++ u).map some) K ↔
      M.AcceptsWithin ((x ++ u.take (K + 1)).map some) K := by
  have key : ∀ i ≤ K, ((x ++ u).map some).getD i M.blank =
      ((x ++ u.take (K + 1)).map some).getD i M.blank := by
    intro i hi
    have h1 : i < (x ++ u).length := by simp; omega
    have h2 : i < (x ++ u.take (K + 1)).length := by
      simp only [List.length_append, List.length_take]
      omega
    rw [hblank, getD_map_some h1, getD_map_some h2]
    by_cases hix : i < x.length
    · rw [List.getElem_append_left hix, List.getElem_append_left hix]
    · push_neg at hix
      rw [List.getElem_append_right hix, List.getElem_append_right hix]
      simp
  exact ⟨acceptsWithin_congr_input M key, acceptsWithin_congr_input M fun i hi => (key i hi).symm⟩

end NTM

end TM
