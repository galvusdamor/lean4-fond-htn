import ComplexityTheory.CFG.TSMRun
/-!
# The grammar of one stack of a two-stack machine

For a two-stack machine `M`, a stack `b` and an initial content `s` of that stack, the grammar
`HTN.CFG.gram M b s` generates exactly the words of transitions that

* run the stack `b` down from `s` (`HTN.CFG.RunDown`), and
* chain the control states from the initial to the accepting state (`HTN.CFG.SRun`),

transitions on the other stack being allowed anywhere (`HTN.CFG.lang_gram_iff`).  It is the
classical triple construction of a pushdown automaton: the nonterminal `N p X q` derives the
words that, started in the state `p`, pop the stack symbol `X` and end in `q`.  Every right-hand
side has at most two symbols (`HTN.CFG.isBinary_gram`).

Nonterminals (`Nat.pair` of a tag and the data):

| nonterminal | derives |
| --- | --- |
| `ntS` | the start symbol |
| `ntE p q` | words of transitions on the other stack from `p` to `q` |
| `ntN p X q` | words that pop `X`, from `p` to `q`, ending with the popping run |
| `ntP n q` | the transition `n` followed by the run-down of its pushed word |
| `ntK p n i q` | the run-down of the pushed word of `n` from its `i`-th symbol |
| `ntI p i q` | the run-down of `s` from its `i`-th symbol, then other transitions |
-/

namespace HTN

namespace CFG

open Undec

variable (M : TSM)

/-- The control states that matter: the initial, the accepting and those of the transitions. -/
def states : List ℕ := M.start :: M.acc :: M.trans.flatMap fun t => [t.src, t.tgt]

/-- The start symbol. -/
def ntS : ℕ := Nat.pair 0 0
/-- Words of transitions on the other stack, from `p` to `q`. -/
def ntE (p q : ℕ) : ℕ := Nat.pair 1 (Nat.pair p q)
/-- Words popping `X`, from `p` to `q`. -/
def ntN (p X q : ℕ) : ℕ := Nat.pair 2 (Nat.pair p (Nat.pair X q))
/-- The transition `n`, then the run-down of its pushed word, to `q`. -/
def ntP (n q : ℕ) : ℕ := Nat.pair 3 (Nat.pair n q)
/-- The run-down of the pushed word of `n` from its `i`-th symbol, from `p` to `q`. -/
def ntK (p n i q : ℕ) : ℕ := Nat.pair 4 (Nat.pair p (Nat.pair n (Nat.pair i q)))
/-- The run-down of the initial stack from its `i`-th symbol, from `p` to `q`. -/
def ntI (p i q : ℕ) : ℕ := Nat.pair 5 (Nat.pair p (Nat.pair i q))

variable (b : Bool) (s : List ℕ)

/-- The positions of the transitions on the stack `b`. -/
def idxOn : List ℕ := (List.range M.trans.length).filter fun n => (trn M n).stk == b

/-- The positions of the transitions on the other stack. -/
def idxOff : List ℕ := (List.range M.trans.length).filter fun n => !((trn M n).stk == b)

/-- The rules of `ntE`. -/
def rulesE : List Rule :=
  (states M).map (fun p => (ntE p p, [])) ++
    (idxOff M b).flatMap fun n => (states M).map fun q =>
      (ntE (trn M n).src q, [Sum.inl n, Sum.inr (ntE (trn M n).tgt q)])

/-- The rules of `ntN`. -/
def rulesN : List Rule :=
  (idxOn M b).flatMap fun n => (states M).flatMap fun p => (states M).map fun q =>
    (ntN p (trn M n).pop q, [Sum.inr (ntE p (trn M n).src), Sum.inr (ntP n q)])

/-- The rules of `ntP`. -/
def rulesP : List Rule :=
  (idxOn M b).flatMap fun n => (states M).map fun q =>
    (ntP n q, [Sum.inl n, Sum.inr (ntK (trn M n).tgt n 0 q)])

/-- The rules of `ntK`. -/
def rulesK : List Rule :=
  (idxOn M b).flatMap fun n =>
    ((List.range (trn M n).push.length).flatMap fun i => (states M).flatMap fun p =>
      (states M).flatMap fun q => (states M).map fun r =>
        (ntK p n i q, [Sum.inr (ntN p ((trn M n).push.getD i 0) r), Sum.inr (ntK r n (i + 1) q)])) ++
    (states M).map fun p => (ntK p n (trn M n).push.length p, [])

/-- The rules of `ntI`. -/
def rulesI : List Rule :=
  ((List.range s.length).flatMap fun i => (states M).flatMap fun p =>
      (states M).flatMap fun q => (states M).map fun r =>
        (ntI p i q, [Sum.inr (ntN p (s.getD i 0) r), Sum.inr (ntI r (i + 1) q)])) ++
    (states M).flatMap fun p => (states M).map fun q => (ntI p s.length q, [Sum.inr (ntE p q)])

/-- The rules that do not depend on the initial stack. -/
def rulesFix : List Rule :=
  (ntS, [Sum.inr (ntI M.start 0 M.acc)]) :: (rulesE M b ++ rulesN M b ++ rulesP M b ++ rulesK M b)

/-- **The grammar of the stack `b`, started with `s`.** -/
def gram : Grammar := (ntS, rulesFix M b ++ rulesI M s)

variable {M b s}

/-! ### Elementary facts -/

theorem src_mem_states {n : ℕ} (hn : n < M.trans.length) : (trn M n).src ∈ states M := by
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, trn_mem hn, ?_⟩))
  simp

theorem tgt_mem_states {n : ℕ} (hn : n < M.trans.length) : (trn M n).tgt ∈ states M := by
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, trn_mem hn, ?_⟩))
  simp

theorem SRun.mem_states {p q : ℕ} {w : List ℕ} (h : SRun M p w q) (hp : p ∈ states M) :
    q ∈ states M := by
  induction h with
  | nil => exact hp
  | cons hn _ _ ih => exact ih (tgt_mem_states hn)

theorem mem_idxOn {n : ℕ} : n ∈ idxOn M b ↔ n < M.trans.length ∧ (trn M n).stk = b := by
  simp [idxOn]

theorem mem_idxOff {n : ℕ} : n ∈ idxOff M b ↔ n < M.trans.length ∧ (trn M n).stk ≠ b := by
  simp [idxOff]

theorem isBinary_gram : (gram M b s).IsBinary := by
  intro r hr
  simp only [gram, Grammar.rules, rulesFix, rulesE, rulesN, rulesP, rulesK, rulesI,
    List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map] at hr
  rcases hr with (rfl | (((⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) | ⟨_, _, _, _, _, _, rfl⟩) |
    ⟨_, _, _, _, rfl⟩) | ⟨_, _, ⟨_, _, _, _, _, _, _, _, rfl⟩ | ⟨_, _, rfl⟩⟩) |
    ⟨_, _, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> simp

/-! ### Lists of transitions -/

/-- The last transition of a word, if any, is on the stack `b`. -/
def EndOK (M : TSM) (b : Bool) (w : List ℕ) : Prop := ∀ n ∈ w.getLast?, (trn M n).stk = b

theorem endOK_nil : EndOK M b [] := by simp [EndOK]

theorem EndOK.append {u v : List ℕ} (hu : EndOK M b u) (hv : EndOK M b v) :
    EndOK M b (u ++ v) := by
  intro n hn
  rw [List.getLast?_append] at hn
  cases hv' : v.getLast? with
  | none => rw [hv'] at hn; exact hu n (by simpa using hn)
  | some m => rw [hv'] at hn; exact hv n (by simpa [hv'] using hn)

theorem EndOK.append_right {u v : List ℕ} (hv : EndOK M b v) (hne : v ≠ []) :
    EndOK M b (u ++ v) := by
  intro n hn
  rw [List.getLast?_append] at hn
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hne)
  rw [hm] at hn
  exact hv n (by rw [hm]; simpa using hn)

theorem endOK_cons {n : ℕ} {v : List ℕ} (hn : (trn M n).stk = b) (hv : EndOK M b v) :
    EndOK M b (n :: v) := by
  by_cases hne : v = []
  · subst hne; intro m hm; simp at hm; subst hm; exact hn
  · exact EndOK.append_right (u := [n]) hv hne

theorem EndOK.of_append {u v : List ℕ} (h : EndOK M b (u ++ v)) (hv : v ≠ []) :
    EndOK M b v := by
  intro n hn
  apply h n
  rw [List.getLast?_append]
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hv)
  rw [hm] at hn ⊢
  simpa using hn

theorem onStk_eq_nil_iff {u : List ℕ} : onStk M b u = [] ↔ ∀ m ∈ u, (trn M m).stk ≠ b := by
  simp [onStk, List.filter_eq_nil_iff]

theorem EndOK.eq_nil {v : List ℕ} (h : EndOK M b v) (h' : onStk M b v = []) : v = [] := by
  by_contra hv
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hv)
  exact onStk_eq_nil_iff.1 h' m (List.mem_of_getLast? hm) (h m (by simp [hm]))

/-- The first transition on the stack `b`. -/
theorem exists_first {v y : List ℕ} {n : ℕ} (h : onStk M b v = n :: y) :
    ∃ u v', v = u ++ n :: v' ∧ onStk M b u = [] ∧ onStk M b v' = y ∧ (trn M n).stk = b := by
  induction v with
  | nil => simp at h
  | cons m v ih =>
    rw [onStk_cons] at h
    by_cases hm : (trn M m).stk = b
    · rw [if_pos hm] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨[], v, rfl, rfl, rfl, hm⟩
    · rw [if_neg hm] at h
      obtain ⟨u, v', rfl, hu, hv', hn⟩ := ih h
      refine ⟨m :: u, v', rfl, ?_, hv', hn⟩
      rw [onStk_cons, if_neg hm, hu]

/-- **Splitting a word after the last transition of a non-empty part of its `b`-transitions.** -/
theorem exists_split {v y₁ y₂ : List ℕ} (h : onStk M b v = y₁ ++ y₂) (hy : y₁ ≠ []) :
    ∃ v₁ v₂, v = v₁ ++ v₂ ∧ onStk M b v₁ = y₁ ∧ onStk M b v₂ = y₂ ∧ v₁ ≠ [] ∧
      EndOK M b v₁ := by
  induction v generalizing y₁ with
  | nil => simp at h; exact absurd h.1 hy
  | cons m v ih =>
    rw [onStk_cons] at h
    by_cases hm : (trn M m).stk = b
    · rw [if_pos hm] at h
      cases y₁ with
      | nil => exact absurd rfl hy
      | cons x y₁ =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨hx, h⟩ := h
        subst hx
        by_cases hy₁ : y₁ = []
        · subst hy₁
          refine ⟨[m], v, rfl, ?_, by simpa using h, by simp, ?_⟩
          · rw [onStk_cons, if_pos hm]; rfl
          · intro n hn; simp at hn; subst hn; exact hm
        · obtain ⟨v₁, v₂, rfl, h₁, h₂, hne, hend⟩ := ih h hy₁
          refine ⟨m :: v₁, v₂, rfl, ?_, h₂, by simp, ?_⟩
          · rw [onStk_cons, if_pos hm, h₁]
          · intro n hn
            apply hend n
            rw [List.getLast?_cons] at hn
            obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hne)
            rw [hk] at hn ⊢
            simp only [Option.getD_some] at hn
            simpa using hn
    · rw [if_neg hm] at h
      obtain ⟨v₁, v₂, rfl, h₁, h₂, hne, hend⟩ := ih h hy
      refine ⟨m :: v₁, v₂, rfl, ?_, h₂, by simp, ?_⟩
      · rw [onStk_cons, if_neg hm, h₁]
      · intro n hn
        apply hend n
        rw [List.getLast?_cons] at hn
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hne)
        rw [hk] at hn ⊢
        simp only [Option.getD_some] at hn
        simpa using hn

/-! ### What the nonterminals derive -/

variable (M b s)

/-- Words of other transitions from `p` to `q`. -/
def SemE (p q : ℕ) (w : List ℕ) : Prop := (∀ n ∈ w, (trn M n).stk ≠ b) ∧ SRun M p w q

/-- Words popping `X`, from `p` to `q`. -/
def SemN (p X q : ℕ) (w : List ℕ) : Prop :=
  RunDown M b [X] (onStk M b w) ∧ SRun M p w q ∧ w ≠ [] ∧ EndOK M b w

/-- The transition `n` and the run-down of its pushed word. -/
def SemP (n q : ℕ) (w : List ℕ) : Prop :=
  ∃ v, w = n :: v ∧ n < M.trans.length ∧ (trn M n).stk = b ∧
    RunDown M b (trn M n).push (onStk M b v) ∧ SRun M (trn M n).tgt v q ∧ EndOK M b v

/-- The run-down of the pushed word of `n` from its `i`-th symbol. -/
def SemK (p n i q : ℕ) (w : List ℕ) : Prop :=
  RunDown M b ((trn M n).push.drop i) (onStk M b w) ∧ SRun M p w q ∧ EndOK M b w

/-- The run-down of the initial stack from its `i`-th symbol. -/
def SemI (p i q : ℕ) (w : List ℕ) : Prop :=
  RunDown M b (s.drop i) (onStk M b w) ∧ SRun M p w q

/-- The words of the start symbol. -/
def SemS (w : List ℕ) : Prop := RunDown M b s (onStk M b w) ∧ SRun M M.start w M.acc

/-- What a nonterminal derives. -/
def SemNT (Z : ℕ) (w : List ℕ) : Prop :=
  (Z = ntS ∧ SemS M b s w) ∨ (∃ p q, Z = ntE p q ∧ SemE M b p q w) ∨
    (∃ p X q, Z = ntN p X q ∧ SemN M b p X q w) ∨ (∃ n q, Z = ntP n q ∧ SemP M b n q w) ∨
    (∃ p n i q, Z = ntK p n i q ∧ SemK M b p n i q w) ∨ (∃ p i q, Z = ntI p i q ∧ SemI M b s p i q w)

/-- What a sentential form derives. -/
def SemForm : List Sym → List ℕ → Prop
  | [], w => w = []
  | Sum.inl a :: α, w => ∃ v, w = a :: v ∧ SemForm α v
  | Sum.inr Z :: α, w => ∃ u v, w = u ++ v ∧ SemNT M b s Z u ∧ SemForm α v

variable {M b s}

theorem semForm_append {α β : List Sym} {w : List ℕ} (h : SemForm M b s (α ++ β) w) :
    ∃ u v, w = u ++ v ∧ SemForm M b s α u ∧ SemForm M b s β v := by
  induction α generalizing w with
  | nil => exact ⟨[], w, rfl, rfl, h⟩
  | cons x α ih =>
    rcases x with a | Z
    · obtain ⟨v, rfl, hv⟩ := h
      obtain ⟨u, v', rfl, hu, hv'⟩ := ih hv
      exact ⟨a :: u, v', rfl, ⟨u, rfl, hu⟩, hv'⟩
    · obtain ⟨u, v, rfl, hZ, hv⟩ := h
      obtain ⟨u', v', rfl, hu', hv'⟩ := ih hv
      exact ⟨u ++ u', v', by simp, ⟨u, u', rfl, hZ, hu'⟩, hv'⟩

/-! Reading off the tag of a nonterminal. -/

theorem semNT_E {p q : ℕ} {w : List ℕ} (h : SemNT M b s (ntE p q) w) : SemE M b p q w := by
  rcases h with ⟨h, -⟩ | ⟨p', q', h, h'⟩ | ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, _, h, -⟩ |
    ⟨_, _, _, h, -⟩ <;>
    simp only [ntS, ntE, ntN, ntP, ntK, ntI, Nat.pair_eq_pair] at h <;> try omega
  obtain ⟨-, rfl, rfl⟩ := h; exact h'

theorem semNT_N {p X q : ℕ} {w : List ℕ} (h : SemNT M b s (ntN p X q) w) : SemN M b p X q w := by
  rcases h with ⟨h, -⟩ | ⟨_, _, h, -⟩ | ⟨p', X', q', h, h'⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, _, h, -⟩ |
    ⟨_, _, _, h, -⟩ <;>
    simp only [ntS, ntE, ntN, ntP, ntK, ntI, Nat.pair_eq_pair] at h <;> try omega
  obtain ⟨-, rfl, rfl, rfl⟩ := h; exact h'

theorem semNT_P {n q : ℕ} {w : List ℕ} (h : SemNT M b s (ntP n q) w) : SemP M b n q w := by
  rcases h with ⟨h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h, -⟩ | ⟨n', q', h, h'⟩ | ⟨_, _, _, _, h, -⟩ |
    ⟨_, _, _, h, -⟩ <;>
    simp only [ntS, ntE, ntN, ntP, ntK, ntI, Nat.pair_eq_pair] at h <;> try omega
  obtain ⟨-, rfl, rfl⟩ := h; exact h'

theorem semNT_K {p n i q : ℕ} {w : List ℕ} (h : SemNT M b s (ntK p n i q) w) :
    SemK M b p n i q w := by
  rcases h with ⟨h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨p', n', i', q', h, h'⟩ |
    ⟨_, _, _, h, -⟩ <;>
    simp only [ntS, ntE, ntN, ntP, ntK, ntI, Nat.pair_eq_pair] at h <;> try omega
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h; exact h'

theorem semNT_I {p i q : ℕ} {w : List ℕ} (h : SemNT M b s (ntI p i q) w) : SemI M b s p i q w := by
  rcases h with ⟨h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, _, h, -⟩ |
    ⟨p', i', q', h, h'⟩ <;>
    simp only [ntS, ntE, ntN, ntP, ntK, ntI, Nat.pair_eq_pair] at h <;> try omega
  obtain ⟨-, rfl, rfl, rfl⟩ := h; exact h'

theorem semNT_S {w : List ℕ} (h : SemNT M b s ntS w) : SemS M b s w := by
  rcases h with ⟨-, h'⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h, -⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, _, h, -⟩ |
    ⟨_, _, _, h, -⟩
  · exact h'
  all_goals simp only [ntS, ntE, ntN, ntP, ntK, ntI, Nat.pair_eq_pair] at h; omega

/-! ### Soundness -/

theorem drop_eq_cons {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    l.drop i = l.getD i 0 :: l.drop (i + 1) := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.drop_eq_getElem_cons hi

/-- **Every rule is sound.** -/
theorem rule_sound {Z : ℕ} {β : List Sym} (hr : (Z, β) ∈ (gram M b s).rules) {u : List ℕ}
    (hu : SemForm M b s β u) : SemNT M b s Z u := by
  simp only [gram, Grammar.rules, rulesFix, rulesE, rulesN, rulesP, rulesK, rulesI,
    List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hr
  rcases hr with (⟨rfl, rfl⟩ | (((⟨p, hp, rfl, rfl⟩ | ⟨n, hn, q, hq, rfl, rfl⟩) |
    ⟨n, hn, p, hp, q, hq, rfl, rfl⟩) | ⟨n, hn, q, hq, rfl, rfl⟩) |
    ⟨n, hn, ⟨i, hi, p, hp, q, hq, r, hr, rfl, rfl⟩ | ⟨p, hp, rfl, rfl⟩⟩) |
    ⟨i, hi, p, hp, q, hq, r, hr, rfl, rfl⟩ | ⟨p, hp, q, hq, rfl, rfl⟩
  · -- the start rule
    obtain ⟨u₁, v, rfl, h₁, rfl⟩ := hu
    obtain ⟨h₁, h₂⟩ := semNT_I h₁
    exact Or.inl ⟨rfl, by simpa using h₁, by simpa using h₂⟩
  · -- `E p p → ε`
    rw [show u = [] from hu]
    exact Or.inr (Or.inl ⟨p, p, rfl, by simp, SRun.nil p⟩)
  · -- `E (src n) q → n · E (tgt n) q`
    obtain ⟨v, rfl, u₁, v', rfl, h₁, rfl⟩ := hu
    obtain ⟨hn₁, hn₂⟩ := mem_idxOff.1 hn
    obtain ⟨h₁, h₂⟩ := semNT_E h₁
    refine Or.inr (Or.inl ⟨_, q, rfl, ?_, SRun.cons hn₁ rfl (by simpa using h₂)⟩)
    intro m hm
    simp only [List.append_nil, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact hn₂
    · exact h₁ m hm
  · -- `N p (pop n) q → E p (src n) · P n q`
    obtain ⟨u₁, v, rfl, h₁, u₂, v', rfl, h₂, rfl⟩ := hu
    obtain ⟨he, hr₁⟩ := semNT_E h₁
    obtain ⟨v, rfl, hn₁, hn₂, hrd, hr₂, hend⟩ := semNT_P h₂
    refine Or.inr (Or.inr (Or.inl ⟨p, _, q, rfl, ?_, ?_, by simp, ?_⟩))
    · rw [List.append_nil, onStk_append, onStk_eq_nil_iff.2 he, List.nil_append, onStk_cons,
        if_pos hn₂]
      exact RunDown.step hn₁ hn₂ (by simpa using hrd)
    · simp only [List.append_nil]
      exact hr₁.append (SRun.cons hn₁ rfl hr₂)
    · simp only [List.append_nil]
      exact EndOK.append_right (endOK_cons hn₂ hend) (by simp)
  · -- `P n q → n · K (tgt n) n 0 q`
    obtain ⟨v, rfl, u₂, v', rfl, h₂, rfl⟩ := hu
    obtain ⟨hn₁, hn₂⟩ := mem_idxOn.1 hn
    obtain ⟨h₁, h₂, h₃⟩ := semNT_K h₂
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, q, rfl, u₂, by simp, hn₁, hn₂, by simpa using h₁,
      h₂, h₃⟩)))
  · -- `K p n i q → N p (push[i]) r · K r n (i+1) q`
    obtain ⟨u₁, v, rfl, h₁, u₂, v', rfl, h₂, rfl⟩ := hu
    obtain ⟨h₁, h₁', hne, hend₁⟩ := semNT_N h₁
    obtain ⟨h₂, h₂', hend₂⟩ := semNT_K h₂
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, n, i, q, rfl, ?_, ?_, ?_⟩))))
    · rw [List.append_nil, onStk_append, drop_eq_cons (List.mem_range.1 hi)]
      exact RunDown.append (s := [_]) h₁ h₂
    · rw [List.append_nil]; exact h₁'.append h₂'
    · rw [List.append_nil]
      by_cases hu₂ : u₂ = []
      · subst hu₂; simpa using hend₁
      · exact EndOK.append_right hend₂ hu₂
  · -- `K p n |push| p → ε`
    rw [show u = [] from hu]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, n, _, p, rfl, ?_, SRun.nil p, endOK_nil⟩))))
    rw [List.drop_length]; exact RunDown.nil
  · -- `I p i q → N p (s[i]) r · I r (i+1) q`
    obtain ⟨u₁, v, rfl, h₁, u₂, v', rfl, h₂, rfl⟩ := hu
    obtain ⟨h₁, h₁', -, -⟩ := semNT_N h₁
    obtain ⟨h₂, h₂'⟩ := semNT_I h₂
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, i, q, rfl, ?_, ?_⟩))))
    · rw [List.append_nil, onStk_append, drop_eq_cons (List.mem_range.1 hi)]
      exact RunDown.append (s := [_]) h₁ h₂
    · rw [List.append_nil]; exact h₁'.append h₂'
  · -- `I p |s| q → E p q`
    obtain ⟨u₁, v, rfl, h₁, rfl⟩ := hu
    obtain ⟨h₁, h₁'⟩ := semNT_E h₁
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, _, q, rfl, ?_, by simpa using h₁'⟩))))
    rw [List.append_nil, onStk_eq_nil_iff.2 h₁, List.drop_length]
    exact RunDown.nil

/-- **Soundness**: what a sentential form derives is what its symbols mean. -/
theorem semForm_of_gen {α : List Sym} {w : List ℕ} (h : Gen (gram M b s) α w) :
    SemForm M b s α w := by
  induction h with
  | nil => rfl
  | term _ ih => exact ⟨_, rfl, ih⟩
  | nonterm hr _ ih =>
    obtain ⟨u, v, rfl, hu, hv⟩ := semForm_append ih
    exact ⟨u, v, rfl, rule_sound hr hu, hv⟩

theorem semS_of_lang {w : List ℕ} (h : (gram M b s).Lang w) : SemS M b s w := by
  obtain ⟨u, v, rfl, hu, rfl⟩ := semForm_of_gen h
  simpa using semNT_S hu

/-! ### Completeness -/

theorem mem_rules_E {r : Rule} (h : r ∈ rulesE M b) : r ∈ (gram M b s).rules := by
  simp [gram, Grammar.rules, rulesFix, h]

theorem mem_rules_N {r : Rule} (h : r ∈ rulesN M b) : r ∈ (gram M b s).rules := by
  simp [gram, Grammar.rules, rulesFix, h]

theorem mem_rules_P {r : Rule} (h : r ∈ rulesP M b) : r ∈ (gram M b s).rules := by
  simp [gram, Grammar.rules, rulesFix, h]

theorem mem_rules_K {r : Rule} (h : r ∈ rulesK M b) : r ∈ (gram M b s).rules := by
  simp [gram, Grammar.rules, rulesFix, h]

theorem mem_rules_I {r : Rule} (h : r ∈ rulesI M s) : r ∈ (gram M b s).rules := by
  simp [gram, Grammar.rules, h]

theorem gen_rule {Z : ℕ} {β : List Sym} {w : List ℕ} (hr : (Z, β) ∈ (gram M b s).rules)
    (h : Gen (gram M b s) β w) : Gen (gram M b s) [Sum.inr Z] w :=
  gen_nonterm_iff.2 ⟨β, hr, h⟩

theorem gen_two {Y Z : ℕ} {u v : List ℕ} (hu : Gen (gram M b s) [Sum.inr Y] u)
    (hv : Gen (gram M b s) [Sum.inr Z] v) : Gen (gram M b s) [Sum.inr Y, Sum.inr Z] (u ++ v) :=
  gen_append (α := [Sum.inr Y]) (β := [Sum.inr Z]) hu hv

theorem gen_E {p q : ℕ} {w : List ℕ} (hp : p ∈ states M) (h : SemE M b p q w) :
    Gen (gram M b s) [Sum.inr (ntE p q)] w := by
  induction w generalizing p with
  | nil =>
    obtain rfl := h.2.nil_inv
    exact gen_rule (mem_rules_E (List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩))) Gen.nil
  | cons n w ih =>
    obtain ⟨hn, rfl, hr⟩ := h.2.cons_inv
    have hq : q ∈ states M := h.2.mem_states hp
    have hoff : n ∈ idxOff M b := mem_idxOff.2 ⟨hn, h.1 n List.mem_cons_self⟩
    refine gen_rule (mem_rules_E (List.mem_append_right _
      (List.mem_flatMap.2 ⟨n, hoff, List.mem_map.2 ⟨q, hq, rfl⟩⟩))) (Gen.term ?_)
    exact ih (tgt_mem_states hn) ⟨fun m hm => h.1 m (List.mem_cons_of_mem _ hm), hr⟩

theorem endOK_tail {u v : List ℕ} (h : EndOK M b (u ++ v)) : EndOK M b v := by
  by_cases hv : v = []
  · subst hv; exact endOK_nil
  · exact h.of_append hv

theorem gen_NK (m : ℕ) :
    (∀ v : List ℕ, v.length = m → ∀ p X q, p ∈ states M → SemN M b p X q v →
      Gen (gram M b s) [Sum.inr (ntN p X q)] v) ∧
    (∀ v : List ℕ, v.length = m → ∀ p n i q, p ∈ states M → n ∈ idxOn M b →
      i ≤ (trn M n).push.length → SemK M b p n i q v → Gen (gram M b s) [Sum.inr (ntK p n i q)] v) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hA : ∀ v : List ℕ, v.length = m → ∀ p X q, p ∈ states M → SemN M b p X q v →
      Gen (gram M b s) [Sum.inr (ntN p X q)] v := by
    intro v hv p X q hp ⟨hrd, hsr, hne, hend⟩
    obtain ⟨n, y, hy⟩ : ∃ n y, onStk M b v = n :: y := by
      cases h : onStk M b v with
      | nil => rw [h] at hrd; exact absurd rfl hrd.ne_nil
      | cons n y => exact ⟨n, y, rfl⟩
    rw [hy] at hrd
    obtain ⟨rest, hX, hn, hb, hrd'⟩ := hrd.cons_inv
    obtain ⟨rfl, rfl⟩ := List.cons.inj hX
    obtain ⟨u, v', rfl, hu, hv', -⟩ := exists_first hy
    obtain ⟨r, h₁, h₂⟩ := hsr.split
    obtain ⟨-, rfl, h₂'⟩ := h₂.cons_inv
    have hq : q ∈ states M := hsr.mem_states hp
    have hon : n ∈ idxOn M b := mem_idxOn.2 ⟨hn, hb⟩
    have hend' : EndOK M b v' := endOK_tail (u := u ++ [n]) (by simpa using hend)
    refine gen_rule (mem_rules_N (List.mem_flatMap.2 ⟨n, hon, List.mem_flatMap.2
      ⟨p, hp, List.mem_map.2 ⟨q, hq, rfl⟩⟩⟩)) (gen_two (gen_E hp ⟨onStk_eq_nil_iff.1 hu, h₁⟩) ?_)
    refine gen_rule (mem_rules_P (List.mem_flatMap.2 ⟨n, hon, List.mem_map.2 ⟨q, hq, rfl⟩⟩))
      (Gen.term ?_)
    have hlt : v'.length < m := by rw [← hv]; simp; omega
    exact (ih _ hlt).2 v' rfl _ n 0 q (tgt_mem_states hn) hon (Nat.zero_le _)
      ⟨by simpa [hv'] using hrd', h₂', hend'⟩
  refine ⟨hA, ?_⟩
  intro v hv p n i q hp hon hi ⟨hrd, hsr, hend⟩
  rcases Nat.lt_or_ge i (trn M n).push.length with hi' | hi'
  · rw [drop_eq_cons hi'] at hrd
    obtain ⟨y₁, y₂, hy, h₁, h₂⟩ := (RunDown.append_iff (s := [_])).1 hrd
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂, hne₁, hend₁⟩ := exists_split hy h₁.ne_nil
    obtain ⟨r, hs₁, hs₂⟩ := hsr.split
    have hr : r ∈ states M := hs₁.mem_states hp
    have hq : q ∈ states M := hs₂.mem_states hr
    have hgen₁ : Gen (gram M b s) [Sum.inr (ntN p ((trn M n).push.getD i 0) r)] v₁ := by
      have hle : v₁.length ≤ m := by rw [← hv]; simp
      rcases Nat.lt_or_ge v₁.length m with hlt | hge
      · exact (ih _ hlt).1 v₁ rfl p _ r hp ⟨by rw [hv₁]; exact h₁, hs₁, hne₁, hend₁⟩
      · exact hA v₁ (le_antisymm hle hge) p _ r hp ⟨by rw [hv₁]; exact h₁, hs₁, hne₁, hend₁⟩
    have hlt : v₂.length < m := by
      rw [← hv, List.length_append]
      have := List.length_pos_of_ne_nil hne₁
      omega
    have hgen₂ := (ih _ hlt).2 v₂ rfl r n (i + 1) q hr hon hi' ⟨by rw [hv₂]; exact h₂, hs₂,
      endOK_tail hend⟩
    exact gen_rule (mem_rules_K (List.mem_flatMap.2 ⟨n, hon, List.mem_append_left _
      (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi', List.mem_flatMap.2 ⟨p, hp,
        List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨r, hr, rfl⟩⟩⟩⟩)⟩)) (gen_two hgen₁ hgen₂)
  · obtain rfl : i = (trn M n).push.length := le_antisymm hi hi'
    rw [List.drop_length] at hrd
    obtain rfl := hend.eq_nil hrd.nil_inv
    obtain rfl := hsr.nil_inv
    exact gen_rule (mem_rules_K (List.mem_flatMap.2 ⟨n, hon, List.mem_append_right _
      (List.mem_map.2 ⟨p, hp, rfl⟩)⟩)) Gen.nil

theorem gen_N {v : List ℕ} {p X q : ℕ} (hp : p ∈ states M) (h : SemN M b p X q v) :
    Gen (gram M b s) [Sum.inr (ntN p X q)] v :=
  (gen_NK v.length).1 v rfl p X q hp h

theorem gen_I (m : ℕ) : ∀ v : List ℕ, v.length = m → ∀ p i q, p ∈ states M → i ≤ s.length →
    SemI M b s p i q v → Gen (gram M b s) [Sum.inr (ntI p i q)] v := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hv p i q hp hi ⟨hrd, hsr⟩
  rcases Nat.lt_or_ge i s.length with hi' | hi'
  · rw [drop_eq_cons hi'] at hrd
    obtain ⟨y₁, y₂, hy, h₁, h₂⟩ := (RunDown.append_iff (s := [_])).1 hrd
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂, hne₁, hend₁⟩ := exists_split hy h₁.ne_nil
    obtain ⟨r, hs₁, hs₂⟩ := hsr.split
    have hr : r ∈ states M := hs₁.mem_states hp
    have hq : q ∈ states M := hs₂.mem_states hr
    have hlt : v₂.length < m := by
      rw [← hv, List.length_append]
      have := List.length_pos_of_ne_nil hne₁
      omega
    exact gen_rule (mem_rules_I (List.mem_append_left _ (List.mem_flatMap.2 ⟨i,
      List.mem_range.2 hi', List.mem_flatMap.2 ⟨p, hp, List.mem_flatMap.2 ⟨q, hq,
        List.mem_map.2 ⟨r, hr, rfl⟩⟩⟩⟩)))
      (gen_two (gen_N hp ⟨by rw [hv₁]; exact h₁, hs₁, hne₁, hend₁⟩)
        (ih _ hlt v₂ rfl r (i + 1) q hr hi' ⟨by rw [hv₂]; exact h₂, hs₂⟩))
  · obtain rfl : i = s.length := le_antisymm hi hi'
    rw [List.drop_length] at hrd
    have hq : q ∈ states M := hsr.mem_states hp
    exact gen_rule (mem_rules_I (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp,
      List.mem_map.2 ⟨q, hq, rfl⟩⟩)))
      (gen_append (α := [Sum.inr (ntE p q)]) (β := []) (v := [])
        (gen_E hp ⟨onStk_eq_nil_iff.1 hrd.nil_inv, hsr⟩) Gen.nil |> fun h => by simpa using h)

/-- **The language of the grammar of the stack `b`**: the words of transitions that run the stack
`b` down from `s` along a chain of control states from the initial to the accepting state. -/
theorem lang_gram_iff {w : List ℕ} :
    (gram M b s).Lang w ↔ RunDown M b s (onStk M b w) ∧ SRun M M.start w M.acc := by
  constructor
  · exact semS_of_lang
  · intro h
    refine gen_rule (Z := ntS) (β := [Sum.inr (ntI M.start 0 M.acc)])
      (by simp [gram, Grammar.rules, rulesFix]) ?_
    simpa using gen_I w.length w rfl M.start 0 M.acc List.mem_cons_self (Nat.zero_le _)
      ⟨by simpa using h.1, h.2⟩

/-- **A two-stack machine halts iff the grammars of its two stacks have a common word.** -/
theorem halts_iff_inter {s₁ s₂ : List ℕ} :
    M.Halts s₁ s₂ ↔ Inter (gram M false s₁) (gram M true s₂) := by
  rw [halts_iff]
  constructor
  · rintro ⟨w, h₁, h₂, h₃⟩
    exact ⟨w, lang_gram_iff.2 ⟨h₁, h₃⟩, lang_gram_iff.2 ⟨h₂, h₃⟩⟩
  · rintro ⟨w, h₁, h₂⟩
    obtain ⟨h₁, h₃⟩ := lang_gram_iff.1 h₁
    exact ⟨w, h₁, (lang_gram_iff.1 h₂).1, h₃⟩

end CFG

end HTN
