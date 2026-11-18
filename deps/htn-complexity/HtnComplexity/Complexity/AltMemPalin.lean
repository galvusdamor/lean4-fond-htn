import HtnComplexity.Complexity.AltMemUniform
/-!
# A uniform family that decides the palindromes

`HtnComplexity/Complexity/AltMemUniform.lean` turns a *uniform family* of alternating
machines with a memory — one machine per input length, with a memory and a transition list that
may grow with the length, run on the padded input — into a polynomial-time hardness family.
This file exhibits such a family, for the language of **palindromes**, which is not regular:
it therefore shows that uniform families reach strictly beyond `HTN.Syn.amFamily`, whose fixed
machine has a constant memory, reads its input once, and thus accepts a regular language.

The machine for the inputs of length `n` has `n + 1` memory bits and runs for `2 * n + 1` steps,
which is exactly the length of the input padded with one bit per input bit:

* steps `0, …, n - 1` (the input word) — in the state `p` it reads the bit `b` and writes it
  into the memory bit `p`, so after the word has been read the memory holds the word;
* step `n` (the marker of the padding) — a step with no effect, into the state `n + 1`;
* steps `n + 1, …, 2 * n` (the zeros of the padding) — in the state `n + 1 + j` it checks that
  the memory bits `j` and `n - 1 - j` agree, which is the palindrome condition for the position
  `j`; the memory bit `n` is a scratch bit, always `false`, which the no-op writes of these
  steps overwrite with itself (a write has to name the value it overwrites);
* the state `2 * n + 1` is accepting.

The results are

* `HTN.Syn.palinMach_accepts_iff` — the machine for the length of `w` accepts the padded `w`
  exactly when `w` is a palindrome;
* `HTN.Syn.palinFamily` — the uniform family, and
  `HTN.Syn.nonempty_hardFamilyPT_palindrome_TO_HTN`, `…_HTN_TR`, `…_HTN_AC` — the resulting
  polynomial-time hardness families for the palindromes in the three source classes of the eight
  open cells of the compilability table.
-/

namespace HTN

namespace Syn

/-! ### The machine -/

/-- The transitions copying the input into the memory: in the state `p` the bit `b` is written
into the memory bit `p`, which is still `false`. -/
def palinCopy (n : ℕ) : List AmExTr :=
  (List.range n).flatMap fun p =>
    [((p : ℕ), false, ([] : List MemLit), ((p, false, false) : MemWrite), p + 1),
      ((p : ℕ), true, ([] : List MemLit), ((p, false, true) : MemWrite), p + 1)]

/-- The transition reading the marker of the padding: it writes the scratch bit `n` with its own
value, i.e. it has no effect. -/
def palinMark (n : ℕ) : List AmExTr :=
  [((n : ℕ), true, ([] : List MemLit), ((n, false, false) : MemWrite), n + 1)]

/-- The transitions comparing the memory bits `j` and `n - 1 - j`, one per zero of the
padding. -/
def palinCmp (n : ℕ) : List AmExTr :=
  (List.range n).flatMap fun j =>
    [((n + 1 + j : ℕ), false, ([(j, false), (n - 1 - j, false)] : List MemLit),
        ((n, false, false) : MemWrite), n + 2 + j),
      ((n + 1 + j : ℕ), false, ([(j, true), (n - 1 - j, true)] : List MemLit),
        ((n, false, false) : MemWrite), n + 2 + j)]

/-- **The machine of the family for the inputs of length `n`.**  It has no universal
transitions: what the family demonstrates is the memory and the padding, while alternation is
demonstrated by `HTN.Syn.twoCheck`. -/
def palinMach (n : ℕ) : BitAltMem where
  mem := n + 1
  start := 0
  acc := [(2 * n + 1, [])]
  ex := palinCopy n ++ palinMark n ++ palinCmp n
  un := []

@[simp] theorem palinMach_mem (n : ℕ) : (palinMach n).mem = n + 1 := rfl

@[simp] theorem palinMach_un (n : ℕ) : (palinMach n).un = [] := rfl

@[simp] theorem palinMach_start (n : ℕ) : (palinMach n).start = 0 := rfl

@[simp] theorem palinMach_acc (n : ℕ) : (palinMach n).acc = [(2 * n + 1, [])] := rfl

theorem mem_palinCopy {n : ℕ} {t : AmExTr} (h : t ∈ palinCopy n) :
    ∃ p < n, t = ((p : ℕ), false, ([] : List MemLit), ((p, false, false) : MemWrite), p + 1) ∨
      t = ((p : ℕ), true, ([] : List MemLit), ((p, false, true) : MemWrite), p + 1) := by
  simp only [palinCopy, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at h
  obtain ⟨p, hp, h⟩ := h
  exact ⟨p, hp, h⟩

theorem mem_palinCmp {n : ℕ} {t : AmExTr} (h : t ∈ palinCmp n) :
    ∃ j < n, ∃ b : Bool, t = ((n + 1 + j : ℕ), false,
      ([(j, b), (n - 1 - j, b)] : List MemLit), ((n, false, false) : MemWrite), n + 2 + j) := by
  simp only [palinCmp, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at h
  obtain ⟨j, hj, h | h⟩ := h
  · exact ⟨j, hj, false, h⟩
  · exact ⟨j, hj, true, h⟩

theorem copy_mem_palinEx {n p : ℕ} (hp : p < n) (b : Bool) :
    ((p : ℕ), b, ([] : List MemLit), ((p, false, b) : MemWrite), p + 1) ∈ (palinMach n).ex := by
  have h : ((p : ℕ), b, ([] : List MemLit), ((p, false, b) : MemWrite), p + 1) ∈ palinCopy n := by
    simp only [palinCopy, List.mem_flatMap, List.mem_range]
    exact ⟨p, hp, by cases b <;> simp⟩
  simp only [palinMach, List.mem_append]
  exact Or.inl (Or.inl h)

theorem mark_mem_palinEx (n : ℕ) :
    ((n : ℕ), true, ([] : List MemLit), ((n, false, false) : MemWrite), n + 1) ∈
      (palinMach n).ex := by
  simp [palinMach, palinMark]

theorem cmp_mem_palinEx {n j : ℕ} (hj : j < n) (b : Bool) :
    ((n + 1 + j : ℕ), false, ([(j, b), (n - 1 - j, b)] : List MemLit),
      ((n, false, false) : MemWrite), n + 2 + j) ∈ (palinMach n).ex := by
  have h : ((n + 1 + j : ℕ), false, ([(j, b), (n - 1 - j, b)] : List MemLit),
      ((n, false, false) : MemWrite), n + 2 + j) ∈ palinCmp n := by
    simp only [palinCmp, List.mem_flatMap, List.mem_range]
    exact ⟨j, hj, by cases b <;> simp⟩
  simp only [palinMach, List.mem_append]
  exact Or.inr h

/-- **The source state of a transition says which phase it belongs to.** -/
theorem mem_palinEx_cases {n : ℕ} {t : AmExTr} (h : t ∈ (palinMach n).ex) :
    (∃ p < n, ∃ b : Bool,
        t = ((p : ℕ), b, ([] : List MemLit), ((p, false, b) : MemWrite), p + 1)) ∨
      t = ((n : ℕ), true, ([] : List MemLit), ((n, false, false) : MemWrite), n + 1) ∨
      (∃ j < n, ∃ b : Bool, t = ((n + 1 + j : ℕ), false,
        ([(j, b), (n - 1 - j, b)] : List MemLit), ((n, false, false) : MemWrite), n + 2 + j)) := by
  simp only [palinMach, List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨p, hp, h | h⟩ := mem_palinCopy h
    · exact Or.inl ⟨p, hp, false, h⟩
    · exact Or.inl ⟨p, hp, true, h⟩
  · simp only [palinMark, List.mem_singleton] at h
    exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (mem_palinCmp h))

/-! ### The memory invariants -/

/-- The memory after `p` bits of `w` have been copied. -/
def PalinInv (w : List Bool) (p : ℕ) (μ : ℕ → Bool) : Prop :=
  (∀ i < p, μ i = w.getD i false) ∧ ∀ i, p ≤ i → μ i = false

theorem palinInv_zero (w : List Bool) : PalinInv w 0 (fun _ => false) :=
  ⟨fun i hi => absurd hi (by omega), fun _ _ => rfl⟩

/-! ### Soundness and completeness of the phases -/

section

variable {w : List Bool}

/-- **The copying phase, from a palindrome to a run.** -/
theorem palin_copy_forward (hcont : ∀ ν : ℕ → Bool, PalinInv w w.length ν →
      (palinMach w.length).AccFrom w.length
        (true :: List.replicate w.length false) ν) :
    ∀ (rest : List Bool) (p : ℕ) (μ : ℕ → Bool), w.drop p = rest → p + rest.length = w.length →
      PalinInv w p μ →
      (palinMach w.length).AccFrom p (rest ++ true :: List.replicate w.length false) μ := by
  intro rest
  induction rest with
  | nil =>
    intro p μ _ hlen hinv
    have hp : p = w.length := by simpa using hlen
    subst hp
    simpa using hcont μ hinv
  | cons b rest ih =>
    intro p μ hdrop hlen hinv
    have hp : p < w.length := by simp at hlen; omega
    have hbit : w.getD p false = b := by
      have h0 : (w.drop p)[0]? = w[p]? := by simp
      rw [hdrop] at h0
      simp only [List.getElem?_cons_zero] at h0
      simp [List.getD, ← h0]
    refine BitAltMem.AccFrom.ex (t := ((p : ℕ), b, ([] : List MemLit),
      ((p, false, b) : MemWrite), p + 1)) (copy_mem_palinEx hp b) rfl rfl
      (by intro q hq; simp [AmExTr.guard] at hq) (by simp [AmExTr.wr, MemWrite.idx]; omega)
      (by simpa [AmExTr.wr, MemWrite.idx, MemWrite.old] using hinv.2 p (le_refl p)) ?_
    have hdrop' : w.drop (p + 1) = rest := by
      have h1 : List.drop 1 (List.drop p w) = List.drop (p + 1) w := List.drop_drop
      rw [hdrop] at h1
      simpa using h1.symm
    have hinv' : PalinInv w (p + 1) (memUpd μ p b) := by
      constructor
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
        · rw [memUpd_of_ne (by omega)]
          exact hinv.1 i hlt
        · rw [memUpd_self, hbit]
      · intro i hi
        rw [memUpd_of_ne (by omega)]
        exact hinv.2 i (by omega)
    have := ih (p + 1) (memUpd μ p b) hdrop' (by simp at hlen ⊢; omega) hinv'
    simpa [AmExTr.tgt, AmExTr.wr, MemWrite.idx, MemWrite.new] using this

end

/-! ### The palindrome condition, positionwise -/

/-- A word is a palindrome exactly when the bits at the positions `i` and `|w| - 1 - i`
agree. -/
theorem reverse_eq_self_iff (w : List Bool) :
    w.reverse = w ↔ ∀ i < w.length, w.getD i false = w.getD (w.length - 1 - i) false := by
  constructor
  · intro h i hi
    have h1 : w[i]? = w[w.length - 1 - i]? := by
      conv_lhs => rw [← h]
      rw [List.getElem?_reverse (by omega)]
    simp only [List.getD_eq_getElem?_getD, h1]
  · intro h
    refine List.ext_getElem (by simp) ?_
    intro i h1 h2
    have hi : i < w.length := by simpa using h2
    have hget := h i hi
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at hget
    rw [List.getElem_reverse]
    exact hget.symm

/-! ### The remaining phases -/

section

variable {w : List Bool}

/-- **The comparing phase, from a palindrome to a run.** -/
theorem palin_cmp_forward
    (hpal : ∀ i < w.length, w.getD i false = w.getD (w.length - 1 - i) false) :
    ∀ (m j : ℕ) (ν : ℕ → Bool), j + m = w.length →
      (∀ i < w.length, ν i = w.getD i false) → (∀ i, w.length ≤ i → ν i = false) →
      (palinMach w.length).AccFrom (w.length + 1 + j) (List.replicate m false) ν := by
  intro m
  induction m with
  | zero =>
    intro j ν hj _ _
    simp only [List.replicate_zero]
    refine BitAltMem.AccFrom.nil (c := (2 * w.length + 1, [])) (by simp)
      (by simp only [AmAcc.st]; omega) ?_
    intro q hq
    simp [AmAcc.guard] at hq
  | succ m ih =>
    intro j ν hj hmem hzero
    have hjn : j < w.length := by omega
    have hb : ν (w.length - 1 - j) = ν j := by
      rw [hmem j hjn, hmem (w.length - 1 - j) (by omega), hpal j hjn]
    rw [List.replicate_succ]
    refine BitAltMem.AccFrom.ex (t := ((w.length + 1 + j : ℕ), false,
      ([(j, ν j), (w.length - 1 - j, ν j)] : List MemLit),
      ((w.length, false, false) : MemWrite), w.length + 2 + j))
      (cmp_mem_palinEx hjn (ν j)) rfl rfl ?_ (by simp [AmExTr.wr, MemWrite.idx])
      (by simpa [AmExTr.wr, MemWrite.idx, MemWrite.old] using hzero w.length le_rfl) ?_
    · intro q hq
      simp only [AmExTr.guard, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨by simp; omega, rfl⟩
      · exact ⟨by simp; omega, hb⟩
    · have hkey := ih (j + 1) ν (by omega) hmem hzero
      have hmu : memUpd ν w.length false = ν := memUpd_eq_self (hzero w.length le_rfl)
      have hstate : w.length + 2 + j = w.length + 1 + (j + 1) := by omega
      simpa [AmExTr.tgt, AmExTr.wr, MemWrite.idx, MemWrite.new, hmu, hstate] using hkey

/-- **The marker step, from a palindrome to a run.** -/
theorem palin_mark_forward
    (hpal : ∀ i < w.length, w.getD i false = w.getD (w.length - 1 - i) false)
    (ν : ℕ → Bool) (hmem : ∀ i < w.length, ν i = w.getD i false)
    (hzero : ∀ i, w.length ≤ i → ν i = false) :
    (palinMach w.length).AccFrom w.length (true :: List.replicate w.length false) ν := by
  refine BitAltMem.AccFrom.ex (t := ((w.length : ℕ), true, ([] : List MemLit),
    ((w.length, false, false) : MemWrite), w.length + 1)) (mark_mem_palinEx _) rfl rfl
    (by intro q hq; simp [AmExTr.guard] at hq) (by simp [AmExTr.wr, MemWrite.idx])
    (by simpa [AmExTr.wr, MemWrite.idx, MemWrite.old] using hzero w.length le_rfl) ?_
  have hkey := palin_cmp_forward hpal w.length 0 ν (by omega) hmem hzero
  have hmu : memUpd ν w.length false = ν := memUpd_eq_self (hzero w.length le_rfl)
  simpa [AmExTr.tgt, AmExTr.wr, MemWrite.idx, MemWrite.new, hmu] using hkey

/-- **The comparing phase, from a run to the palindrome condition.** -/
theorem palin_cmp_backward :
    ∀ (m j : ℕ) (ν : ℕ → Bool), j + m = w.length →
      (palinMach w.length).AccFrom (w.length + 1 + j) (List.replicate m false) ν →
      ∀ i, j ≤ i → i < w.length → ν i = ν (w.length - 1 - i) := by
  intro m
  induction m with
  | zero =>
    intro j ν hj _ i hi hin
    omega
  | succ m ih =>
    intro j ν hj hacc i hi hin
    rw [List.replicate_succ] at hacc
    cases hacc with
    | un ht => simp [palinMach] at ht
    | ex ht hq hb hg hw hu h' =>
      rename_i t
      rcases mem_palinEx_cases ht with ⟨p, hp, b, rfl⟩ | rfl | ⟨j', hj', b, rfl⟩
      · exact absurd hq (by simp only [AmExTr.src]; omega)
      · exact absurd hq (by simp only [AmExTr.src]; omega)
      · have hjj : j' = j := by
          have := hq
          simp only [AmExTr.src] at this
          omega
        subst hjj
        have h1 := hg (j', b) (by simp [AmExTr.guard])
        have h2 := hg (w.length - 1 - j', b) (by simp [AmExTr.guard])
        have hjb : ν j' = ν (w.length - 1 - j') := by rw [h1.2, h2.2]
        have hmu : memUpd ν w.length false = ν :=
          memUpd_eq_self (by simpa [AmExTr.wr, MemWrite.idx, MemWrite.old] using hu)
        have hstate : w.length + 2 + j' = w.length + 1 + (j' + 1) := by omega
        have h'' : (palinMach w.length).AccFrom (w.length + 1 + (j' + 1))
            (List.replicate m false) ν := by
          simpa [AmExTr.tgt, AmExTr.wr, MemWrite.idx, MemWrite.new, hmu, hstate] using h'
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · exact hjb
        · exact ih (j' + 1) ν (by omega) h'' i (by omega) hin

/-- **The marker step, from a run to the comparing phase.** -/
theorem palin_mark_backward (ν : ℕ → Bool)
    (hacc : (palinMach w.length).AccFrom w.length
      (true :: List.replicate w.length false) ν) :
    (palinMach w.length).AccFrom (w.length + 1) (List.replicate w.length false) ν := by
  cases hacc with
  | un ht => simp [palinMach] at ht
  | ex ht hq hb hg hw hu h' =>
    rename_i t
    rcases mem_palinEx_cases ht with ⟨p, hp, b, rfl⟩ | rfl | ⟨j', hj', b, rfl⟩
    · exact absurd hq (by simp only [AmExTr.src]; omega)
    · have hmu : memUpd ν w.length false = ν :=
        memUpd_eq_self (by simpa [AmExTr.wr, MemWrite.idx, MemWrite.old] using hu)
      simpa [AmExTr.tgt, AmExTr.wr, MemWrite.idx, MemWrite.new, hmu] using h'
    · exact absurd hq (by simp only [AmExTr.src]; omega)

/-- **The copying phase, from a run to the memory holding the word.** -/
theorem palin_copy_backward :
    ∀ (rest : List Bool) (p : ℕ) (μ : ℕ → Bool), w.drop p = rest → p + rest.length = w.length →
      PalinInv w p μ →
      (palinMach w.length).AccFrom p (rest ++ true :: List.replicate w.length false) μ →
      ∃ ν, PalinInv w w.length ν ∧
        (palinMach w.length).AccFrom w.length (true :: List.replicate w.length false) ν := by
  intro rest
  induction rest with
  | nil =>
    intro p μ _ hlen hinv hacc
    have hp : p = w.length := by simpa using hlen
    subst hp
    exact ⟨μ, hinv, by simpa using hacc⟩
  | cons b rest ih =>
    intro p μ hdrop hlen hinv hacc
    have hp : p < w.length := by simp at hlen; omega
    have hbit : w.getD p false = b := by
      have h0 : (w.drop p)[0]? = w[p]? := by simp
      rw [hdrop] at h0
      simp only [List.getElem?_cons_zero] at h0
      simp [List.getD, ← h0]
    have hdrop' : w.drop (p + 1) = rest := by
      have h1 : List.drop 1 (List.drop p w) = List.drop (p + 1) w := List.drop_drop
      rw [hdrop] at h1
      simpa using h1.symm
    rw [List.cons_append] at hacc
    cases hacc with
    | un ht => simp [palinMach] at ht
    | ex ht hq hb' hg hw hu h' =>
      rename_i t
      rcases mem_palinEx_cases ht with ⟨p', hp', b', rfl⟩ | rfl | ⟨j', hj', b', rfl⟩
      · have hpp : p' = p := by simpa [AmExTr.src] using hq
        subst hpp
        have hbb : b' = b := by simpa [AmExTr.bit] using hb'
        subst hbb
        have hinv' : PalinInv w (p' + 1) (memUpd μ p' b') := by
          constructor
          · intro i hi
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
            · rw [memUpd_of_ne (by omega)]
              exact hinv.1 i hlt
            · rw [memUpd_self, hbit]
          · intro i hi
            rw [memUpd_of_ne (by omega)]
            exact hinv.2 i (by omega)
        refine ih (p' + 1) (memUpd μ p' b') hdrop' (by simp at hlen ⊢; omega) hinv' ?_
        simpa [AmExTr.tgt, AmExTr.wr, MemWrite.idx, MemWrite.new] using h'
      · exact absurd hq (by simp only [AmExTr.src]; omega)
      · exact absurd hq (by simp only [AmExTr.src]; omega)

end

/-! ### The characterisation -/

/-- **The machine for the length of `w` accepts the padded `w` exactly when `w` is a
palindrome.** -/
theorem palinMach_accepts_iff (w : List Bool) :
    (palinMach w.length).Accepts (padWord 1 w) ↔ w.reverse = w := by
  have hword : padWord 1 w = w ++ true :: List.replicate w.length false := by
    simp [padWord, padGen]
  rw [reverse_eq_self_iff, BitAltMem.Accepts, hword]
  constructor
  · intro hacc
    have hacc0 : (palinMach w.length).AccFrom 0
        (w ++ true :: List.replicate w.length false) (fun _ => false) := by
      simpa using hacc
    obtain ⟨ν, hinv, hν⟩ :=
      palin_copy_backward w 0 (fun _ => false) (by simp) (by simp) (palinInv_zero w) hacc0
    have h2 := palin_mark_backward ν hν
    have h3 := palin_cmp_backward (w := w) w.length 0 ν (by omega) (by simpa using h2)
    intro i hi
    have hi' := h3 i (by omega) hi
    rw [hinv.1 i hi, hinv.1 (w.length - 1 - i) (by omega)] at hi'
    exact hi'
  · intro hpal
    have hcont : ∀ ν : ℕ → Bool, PalinInv w w.length ν →
        (palinMach w.length).AccFrom w.length (true :: List.replicate w.length false) ν :=
      fun ν hinv => palin_mark_forward hpal ν hinv.1 hinv.2
    have hkey := palin_copy_forward hcont w 0 (fun _ => false) (by simp) (by simp)
      (palinInv_zero w)
    simpa using hkey

/-! ### Replacing the language of a hardness family -/

namespace Coded

/-- A hardness family for a language is one for every language with the same words. -/
def HardFamilyPT.congrLang {𝒟 : Table.Family} {S : SynClass 𝒟} {c : BitCoding InstDesc}
    {L L' : List Bool → Prop} (F : HardFamilyPT c S L) (h : ∀ w, L w ↔ L' w) :
    HardFamilyPT c S L' where
  dom := F.dom
  inst := F.inst
  bound := F.bound
  dom_size := F.dom_size
  inst_size := F.inst_size
  dom_ok := F.dom_ok
  inst_ok := F.inst_ok
  inst_injective := F.inst_injective
  correct := fun w => (F.correct w).trans (h w)
  dom_computable := F.dom_computable
  inst_polyTime := F.inst_polyTime

end Coded

/-! ### The size of the machine -/

theorem length_flatMap_pair {α : Type*} (g h : ℕ → α) (n : ℕ) :
    ((List.range n).flatMap fun j => [g j, h j]).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp
    omega

theorem sum_guard_flatMap_pair (t₁ t₂ : ℕ → AmExTr) (c n : ℕ)
    (hc : ∀ j, (t₁ j).guard.length + (t₂ j).guard.length = c) :
    (((List.range n).flatMap fun j => [t₁ j, t₂ j]).map fun t => t.guard.length).sum = c * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih]
    have := hc n
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [Nat.mul_succ]
    omega

theorem length_palinEx (n : ℕ) : (palinMach n).ex.length = 4 * n + 1 := by
  have h1 : (palinCopy n).length = 2 * n := length_flatMap_pair _ _ n
  have h2 : (palinCmp n).length = 2 * n := length_flatMap_pair _ _ n
  simp only [palinMach, List.length_append, h1, h2, palinMark, List.length_singleton]
  omega

theorem sum_guard_palinEx (n : ℕ) :
    (((palinMach n).ex).map fun t => t.guard.length).sum = 4 * n := by
  have h1 : ((palinCopy n).map fun t => t.guard.length).sum = 0 * n :=
    sum_guard_flatMap_pair _ _ 0 n fun _ => rfl
  have h2 : ((palinCmp n).map fun t => t.guard.length).sum = 4 * n :=
    sum_guard_flatMap_pair _ _ 4 n fun _ => rfl
  simp only [palinMach, List.map_append, List.sum_append, h1, h2, palinMark, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  simp [AmExTr.guard]

theorem budget_palinMach (n : ℕ) : amBudget (palinMach n) = 5 * n + 6 := by
  simp only [amBudget, palinMach_mem, sum_guard_palinEx, palinMach_un, palinMach_acc,
    List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, AmAcc.guard, List.length_nil]
  omega

theorem coef_palinMach (n : ℕ) : amCoef (palinMach n) = 80 * n ^ 2 + 164 * n + 36 := by
  simp only [amCoef, budget_palinMach, length_palinEx, palinMach_un, List.length_nil, add_zero]
  ring

theorem const_palinMach (n : ℕ) : amConst (palinMach n) = 80 * n ^ 2 + 156 * n + 84 := by
  simp only [amConst, budget_palinMach, length_palinEx, palinMach_acc, List.length_singleton]
  ring

/-! ### The machine family is primitive recursive -/

theorem primrec_palinCopy : Primrec palinCopy := by
  have key : Primrec fun n : ℕ => (List.range n).flatMap fun p =>
      [((p : ℕ), false, ([] : List MemLit), ((p, false, false) : MemWrite), p + 1),
        ((p : ℕ), true, ([] : List MemLit), ((p, false, true) : MemWrite), p + 1)] := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    have pp : Primrec fun x : ℕ × ℕ => x.2 := Primrec.snd
    have psucc : Primrec fun x : ℕ × ℕ => x.2 + 1 :=
      Primrec.nat_add.comp pp (Primrec.const 1)
    have e₁ := Primrec.pair pp (Primrec.pair (Primrec.const false)
      (Primrec.pair (Primrec.const ([] : List MemLit))
        (Primrec.pair (Primrec.pair pp (Primrec.pair (Primrec.const false)
          (Primrec.const false))) psucc)))
    have e₂ := Primrec.pair pp (Primrec.pair (Primrec.const true)
      (Primrec.pair (Primrec.const ([] : List MemLit))
        (Primrec.pair (Primrec.pair pp (Primrec.pair (Primrec.const false)
          (Primrec.const true))) psucc)))
    exact Primrec.list_cons.comp e₁ (Primrec.list_cons.comp e₂ (Primrec.const []))
  exact key.of_eq fun n => rfl

theorem primrec_palinMark : Primrec palinMark := by
  have key : Primrec fun n : ℕ =>
      [((n : ℕ), true, ([] : List MemLit), ((n, false, false) : MemWrite), n + 1)] := by
    have nn : Primrec fun n : ℕ => n := Primrec.id
    have nsucc : Primrec fun n : ℕ => n + 1 := Primrec.nat_add.comp nn (Primrec.const 1)
    have e := Primrec.pair nn (Primrec.pair (Primrec.const true)
      (Primrec.pair (Primrec.const ([] : List MemLit))
        (Primrec.pair (Primrec.pair nn (Primrec.pair (Primrec.const false)
          (Primrec.const false))) nsucc)))
    exact Primrec.list_cons.comp e (Primrec.const [])
  exact key.of_eq fun n => rfl

theorem primrec_palinCmp : Primrec palinCmp := by
  have key : Primrec fun n : ℕ => (List.range n).flatMap fun j =>
      [((n + 1 + j : ℕ), false, ([(j, false), (n - 1 - j, false)] : List MemLit),
          ((n, false, false) : MemWrite), n + 2 + j),
        ((n + 1 + j : ℕ), false, ([(j, true), (n - 1 - j, true)] : List MemLit),
          ((n, false, false) : MemWrite), n + 2 + j)] := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    have nn : Primrec fun x : ℕ × ℕ => x.1 := Primrec.fst
    have jj : Primrec fun x : ℕ × ℕ => x.2 := Primrec.snd
    have hsrc : Primrec fun x : ℕ × ℕ => x.1 + 1 + x.2 :=
      Primrec.nat_add.comp (Primrec.nat_add.comp nn (Primrec.const 1)) jj
    have htgt : Primrec fun x : ℕ × ℕ => x.1 + 2 + x.2 :=
      Primrec.nat_add.comp (Primrec.nat_add.comp nn (Primrec.const 2)) jj
    have hmir : Primrec fun x : ℕ × ℕ => x.1 - 1 - x.2 :=
      Primrec.nat_sub.comp (Primrec.nat_sub.comp nn (Primrec.const 1)) jj
    have hwr := Primrec.pair nn (Primrec.pair (Primrec.const false) (Primrec.const false))
    have hg₁ := Primrec.list_cons.comp (Primrec.pair jj (Primrec.const false))
      (Primrec.list_cons.comp (Primrec.pair hmir (Primrec.const false)) (Primrec.const []))
    have hg₂ := Primrec.list_cons.comp (Primrec.pair jj (Primrec.const true))
      (Primrec.list_cons.comp (Primrec.pair hmir (Primrec.const true)) (Primrec.const []))
    have e₁ := Primrec.pair hsrc (Primrec.pair (Primrec.const false)
      (Primrec.pair hg₁ (Primrec.pair hwr htgt)))
    have e₂ := Primrec.pair hsrc (Primrec.pair (Primrec.const false)
      (Primrec.pair hg₂ (Primrec.pair hwr htgt)))
    exact Primrec.list_cons.comp e₁ (Primrec.list_cons.comp e₂ (Primrec.const []))
  exact key.of_eq fun n => rfl

theorem machFamPrimrec_palinMach : MachFamPrimrec palinMach where
  mem := Primrec.nat_add.comp Primrec.id (Primrec.const 1)
  start := Primrec.const 0
  acc := by
    have key : Primrec fun n : ℕ => [((2 * n + 1 : ℕ), ([] : List MemLit))] := by
      have hst : Primrec fun n : ℕ => 2 * n + 1 :=
        Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
          (Primrec.const 1)
      exact Primrec.list_cons.comp (Primrec.pair hst (Primrec.const [])) (Primrec.const [])
    exact key.of_eq fun n => rfl
  ex := by
    have key : Primrec fun n : ℕ => palinCopy n ++ palinMark n ++ palinCmp n :=
      Primrec.list_append.comp (Primrec.list_append.comp primrec_palinCopy primrec_palinMark)
        primrec_palinCmp
    exact key.of_eq fun n => rfl
  un := Primrec.const []

/-! ### The family -/

/-- **The uniform family of alternating machines with a memory deciding the palindromes.** -/
noncomputable def palinFamily : UniAltMem where
  mach := palinMach
  padding := padLinear 1
  bound := Polynomial.C 160 * Polynomial.X ^ 3 + Polynomial.C 488 * Polynomial.X ^ 2
    + Polynomial.C 392 * Polynomial.X + Polynomial.C 120
  mach_primrec := machFamPrimrec_palinMach
  dom_size := fun n => by
    simp only [coef_palinMach, const_palinMach, padLinear_len, padLen, padLenOf,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    ring_nf
    omega

@[simp] theorem palinFamily_mach : palinFamily.mach = palinMach := rfl

@[simp] theorem palinFamily_padding : palinFamily.padding = padLinear 1 := rfl

/-- **The language of the family is the palindromes.** -/
theorem palinFamily_L_iff (w : List Bool) : palinFamily.L w ↔ w.reverse = w :=
  palinMach_accepts_iff w

/-- **A polynomial-time hardness family for the palindromes, in `TO-HTN`.** -/
theorem nonempty_hardFamilyPT_palindrome_TO_HTN :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN_root fun w : List Bool =>
      w.reverse = w) :=
  ⟨(Classical.choice palinFamily.nonempty_hardFamilyPT_TO_HTN).congrLang palinFamily_L_iff⟩

/-- … in `HTN-TR`. -/
theorem nonempty_hardFamilyPT_palindrome_HTN_TR :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_TR_root fun w : List Bool =>
      w.reverse = w) :=
  ⟨(Classical.choice palinFamily.nonempty_hardFamilyPT_HTN_TR).congrLang palinFamily_L_iff⟩

/-- … in `HTN-AC`. -/
theorem nonempty_hardFamilyPT_palindrome_HTN_AC :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_AC_root fun w : List Bool =>
      w.reverse = w) :=
  ⟨(Classical.choice palinFamily.nonempty_hardFamilyPT_HTN_AC).congrLang palinFamily_L_iff⟩

end Syn

end HTN
