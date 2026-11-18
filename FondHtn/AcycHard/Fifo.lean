import FondHtn.AcycHard.ChainGame
/-!
# The FIFO queue of counter cells

The memory of the EXPSPACE lower bound for acyclic partially ordered problems
(`doc/notes_acyc_expspace.md`, the "counters" construction of the ideas file): a queue of `S`
symbols is held by `S` pool chains, the **cells**.  A cell for the symbol `τ` is the chain

    init τ · (tick · res)^S · fin τ

The control runs, for every *step*, `S` windows `T`, `S` windows `R`, then one window each of
`F` (a cell finishes and reports its symbol `rd τ`), `I` (the player starts a new cell of a
symbol `τ` of her choice, reported as `wr τ`) and `U` (the player executes one *option*, an
arbitrary data action gated by `U` — this is how the data state is updated).  Since a cell that
has ticked must resume before it can tick again, the `S` windows `T` tick *every* live cell
exactly once; the cell that has ticked `S` times is the unique one that can finish.  So the
cells implement a queue of length `S` (a delay line): the symbol read at a step is the one
written `S` steps earlier.

At the start, the pool holds `S` blank cells without `init`; a *pre-warm* phase of
`tri S = S (S - 1) / 2` pairs of windows `T`, `R` lets the player advance single cells.  Unless
she staggers them perfectly, she is stuck within `S` steps (`not_wwin_bad`).

* `FOND.AcycHard.FSpec.QWin` — **the queue game**: a program of steps and plain data actions;
  a step reads the head of the queue, lets the player append a symbol `τ` and execute an option;
* **`FOND.AcycHard.FSpec.wwin_fifo_iff`** — the window game with pre-warm phase and cells is
  the queue game started from the queue `b^S` (`S ≥ 1`, at least `S` steps);
* **`FOND.AcycHard.FSpec.cwin_fifo_iff`** — the same for the chain game with the token
  encoding (`FOND.AcycHard.WSys.cwin_iff_wwin`).
-/

namespace FOND

namespace AcycHard

set_option linter.unusedSectionVars false

/-- The gates of the cell construction. -/
inductive Gate
  | T
  | R
  | F
  | I
  | U
  deriving DecidableEq

/-- Pool actions: cell actions and options. -/
inductive PA (Sym O : Type)
  | init (τ : Sym)
  | tick
  | res
  | fin (τ : Sym)
  | opt (o : O)
  deriving DecidableEq

/-- A cell/queue specification: the cell length `S`, the data facts reporting reads and writes,
the options and the plain control actions. -/
structure FSpec (Sym O D P : Type) where
  /-- Length of the queue (= number of `tick · res` units of a cell). -/
  S : ℕ
  /-- The fact "symbol `τ` read". -/
  rd : Sym → D
  /-- The fact "symbol `τ` written". -/
  wr : Sym → D
  /-- Data precondition of an option. -/
  opre : O → Set D
  /-- Add list of an option. -/
  oadd : O → Set D
  /-- Delete list of an option. -/
  odel : O → Set D
  /-- Precondition of a plain action. -/
  ppre : P → Set D
  /-- Effects of a plain action. -/
  peffs : P → Set (Set D × Set D)

namespace FSpec

variable {Sym O D P : Type} [DecidableEq Sym] [DecidableEq O] (X : FSpec Sym O D P)

/-- The window system of a specification. -/
def sys : WSys Gate D (PA Sym O) P where
  gate
    | .init _ => .I
    | .tick => .T
    | .res => .R
    | .fin _ => .F
    | .opt _ => .U
  pre
    | .opt o => X.opre o
    | _ => ∅
  add
    | .init τ => {X.wr τ}
    | .fin τ => {X.rd τ}
    | .opt o => X.oadd o
    | _ => ∅
  del
    | .opt o => X.odel o
    | _ => ∅
  ppre := X.ppre
  peffs := X.peffs

/-! ## Cells -/

/-- A resumed cell of symbol `τ` with `k` units `tick · res` left. -/
def cellR (τ : Sym) : ℕ → List (PA Sym O)
  | 0 => [.fin τ]
  | k + 1 => .tick :: .res :: cellR τ k

/-- A fresh cell. -/
def newCell (τ : Sym) : List (PA Sym O) := .init τ :: cellR τ X.S

/-- The resumed cells `(τ, k)` of a multiset. -/
def liveR (L : Multiset (Sym × ℕ)) : Multiset (List (PA Sym O)) :=
  L.map fun x => cellR x.1 x.2

/-- The paused cells: they have ticked and wait for `res`; `(τ, k)` has `k` units left after
resuming. -/
def liveP (L : Multiset (Sym × ℕ)) : Multiset (List (PA Sym O)) :=
  L.map fun x => .res :: cellR x.1 x.2

/-- The rest of the pool: finished chains, fresh cells and options. -/
def UOk (U : Multiset (List (PA Sym O))) : Prop :=
  ∀ c ∈ U, c = [] ∨ (∃ τ, c = X.newCell τ) ∨ ∃ o, c = [.opt o]

lemma cellR_ne_nil (τ : Sym) (k : ℕ) : cellR (O := O) τ k ≠ [] := by
  cases k <;> simp [cellR]

lemma cellR_length (τ : Sym) (k : ℕ) : (cellR (O := O) τ k).length = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [cellR, ih]; ring

lemma cellR_getLast? (τ : Sym) : ∀ k, (cellR (O := O) τ k).getLast? = some (.fin τ)
  | 0 => rfl
  | k + 1 => by
    have h := cellR_getLast? τ k
    cases k with
    | zero => rfl
    | succ k => simpa [cellR, List.getLast?_cons_cons] using h

lemma cellR_inj : Function.Injective fun x : Sym × ℕ => cellR (O := O) x.1 x.2 := by
  rintro ⟨τ, k⟩ ⟨τ', k'⟩ h
  simp only at h
  have hk : k = k' := by
    have := congrArg List.length h
    rw [cellR_length, cellR_length] at this
    omega
  subst hk
  have := congrArg List.getLast? h
  rw [cellR_getLast?, cellR_getLast?] at this
  cases this
  rfl

lemma cellP_inj : Function.Injective fun x : Sym × ℕ => (.res :: cellR (O := O) x.1 x.2) := by
  intro x y h
  exact cellR_inj (List.cons.inj h).2

lemma cellR_eq_cons {τ : Sym} {k : ℕ} {a : PA Sym O} {c : List (PA Sym O)}
    (h : cellR τ k = a :: c) :
    (k = 0 ∧ a = .fin τ ∧ c = []) ∨ ∃ k', k = k' + 1 ∧ a = .tick ∧ c = .res :: cellR τ k' := by
  cases k with
  | zero =>
    simp only [cellR, List.cons.injEq] at h
    exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
  | succ k =>
    simp only [cellR, List.cons.injEq] at h
    exact Or.inr ⟨k, rfl, h.1.symm, h.2.symm⟩

lemma mem_pool {L₁ L₂ : Multiset (Sym × ℕ)} {U : Multiset (List (PA Sym O))} (hU : X.UOk U)
    {a : PA Sym O} {c : List (PA Sym O)} (h : a :: c ∈ liveR L₁ + liveP L₂ + U) :
    (∃ τ, (τ, 0) ∈ L₁ ∧ a = .fin τ ∧ c = []) ∨
    (∃ τ k, (τ, k + 1) ∈ L₁ ∧ a = .tick ∧ c = .res :: cellR τ k) ∨
    (∃ x ∈ L₂, a = .res ∧ c = cellR x.1 x.2) ∨
    (∃ τ, X.newCell τ ∈ U ∧ a = .init τ ∧ c = cellR τ X.S) ∨
    (∃ o, [.opt o] ∈ U ∧ a = .opt o ∧ c = []) := by
  rcases Multiset.mem_add.1 h with h | h
  · rcases Multiset.mem_add.1 h with h | h
    · obtain ⟨⟨τ, k⟩, hx, hxe⟩ := Multiset.mem_map.1 h
      rcases cellR_eq_cons hxe with ⟨rfl, rfl, rfl⟩ | ⟨k', rfl, rfl, rfl⟩
      · exact Or.inl ⟨τ, hx, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨τ, k', hx, rfl, rfl⟩)
    · obtain ⟨x, hx, hxe⟩ := Multiset.mem_map.1 h
      simp only [List.cons.injEq] at hxe
      exact Or.inr (Or.inr (Or.inl ⟨x, hx, hxe.1.symm, hxe.2.symm⟩))
  · rcases hU _ h with h' | ⟨τ, h'⟩ | ⟨o, h'⟩
    · cases h'
    · simp only [newCell, List.cons.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨τ, ?_, rfl, rfl⟩)))
      simpa [newCell] using h
    · simp only [List.cons.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨o, h, rfl, rfl⟩)))

/-! ### Rewriting the pool -/

lemma erase_R {L₁ L₂ : Multiset (Sym × ℕ)} {U : Multiset (List (PA Sym O))} {x : Sym × ℕ}
    (hx : x ∈ L₁) :
    (liveR L₁ + liveP L₂ + U).erase (cellR x.1 x.2) = liveR (L₁.erase x) + liveP L₂ + U := by
  have hm : cellR (O := O) x.1 x.2 ∈ liveR L₁ := Multiset.mem_map_of_mem _ hx
  rw [Multiset.erase_add_left_pos _ (Multiset.mem_add.2 (Or.inl hm)),
    Multiset.erase_add_left_pos _ hm, liveR, liveR,
    Multiset.map_erase _ cellR_inj]

lemma erase_P {L₁ L₂ : Multiset (Sym × ℕ)} {U : Multiset (List (PA Sym O))} {x : Sym × ℕ}
    (hx : x ∈ L₂) :
    (liveR L₁ + liveP L₂ + U).erase (.res :: cellR x.1 x.2) = liveR L₁ + liveP (L₂.erase x) + U := by
  have hm : (.res :: cellR (O := O) x.1 x.2) ∈ liveP L₂ := Multiset.mem_map_of_mem _ hx
  rw [Multiset.erase_add_left_pos _ (Multiset.mem_add.2 (Or.inr hm)),
    Multiset.erase_add_right_pos _ hm, liveP, liveP,
    Multiset.map_erase _ cellP_inj]

lemma erase_U {L₁ L₂ : Multiset (Sym × ℕ)} {U : Multiset (List (PA Sym O))} {c : List (PA Sym O)}
    (hc : c ∈ U) :
    (liveR L₁ + liveP L₂ + U).erase c = liveR L₁ + liveP L₂ + U.erase c :=
  Multiset.erase_add_right_pos _ hc

lemma cons_R (L₁ L₂ : Multiset (Sym × ℕ)) (U : Multiset (List (PA Sym O))) (x : Sym × ℕ) :
    cellR x.1 x.2 ::ₘ (liveR L₁ + liveP L₂ + U) = liveR (x ::ₘ L₁) + liveP L₂ + U := by
  simp [liveR, Multiset.cons_add]

lemma cons_P (L₁ L₂ : Multiset (Sym × ℕ)) (U : Multiset (List (PA Sym O))) (x : Sym × ℕ) :
    (.res :: cellR x.1 x.2) ::ₘ (liveR L₁ + liveP L₂ + U) = liveR L₁ + liveP (x ::ₘ L₂) + U := by
  simp [liveP, Multiset.cons_add, Multiset.add_cons]

lemma cons_U (L₁ L₂ : Multiset (Sym × ℕ)) (U : Multiset (List (PA Sym O))) (c : List (PA Sym O)) :
    c ::ₘ (liveR L₁ + liveP L₂ + U) = liveR L₁ + liveP L₂ + (c ::ₘ U) := by
  simp [Multiset.add_cons]

lemma UOk.cons_nil {U : Multiset (List (PA Sym O))} (hU : X.UOk U) : X.UOk ([] ::ₘ U) := by
  intro c hc
  rcases Multiset.mem_cons.1 hc with rfl | hc
  · exact Or.inl rfl
  · exact hU c hc

lemma UOk.erase {U : Multiset (List (PA Sym O))} (hU : X.UOk U) (c : List (PA Sym O)) :
    X.UOk (U.erase c) := fun c' hc' => hU c' (Multiset.mem_of_mem_erase hc')

/-! ## The windows -/

open WSys

lemma upd_empty (d : Set D) : WSys.upd d ∅ ∅ = d := by simp [WSys.upd]

lemma upd_single (d : Set D) (x : D) : WSys.upd d {x} ∅ = insert x d := by
  simp [WSys.upd, Set.union_singleton]

/-- A window `T`: some resumed cell with a unit left ticks and pauses. -/
lemma wwin_T {ws : List (WI Gate P)} {L₁ L₂ : Multiset (Sym × ℕ)}
    {U : Multiset (List (PA Sym O))} (hU : X.UOk U) {d : Set D} :
    X.sys.WWin (.win .T :: ws) (liveR L₁ + liveP L₂ + U) d ↔
      ∃ τ k, (τ, k + 1) ∈ L₁ ∧ X.sys.WWin ws (liveR (L₁.erase (τ, k + 1)) + liveP ((τ, k) ::ₘ L₂) + U) d := by
  simp only [WWin]
  constructor
  · rintro ⟨a, c, hc, hg, -, hw⟩
    rcases X.mem_pool hU hc with ⟨τ, -, rfl, rfl⟩ | ⟨τ, k, hx, rfl, rfl⟩ | ⟨x, -, rfl, rfl⟩ |
      ⟨τ, -, rfl, rfl⟩ | ⟨o, -, rfl, rfl⟩
    · cases hg
    · refine ⟨τ, k, hx, ?_⟩
      have h1 := erase_R (L₂ := L₂) (U := U) hx
      simp only [cellR] at h1
      rw [h1, cons_P _ _ _ (τ, k)] at hw
      simpa [sys, upd_empty] using hw
    · cases hg
    · cases hg
    · cases hg
  · rintro ⟨τ, k, hx, hw⟩
    refine ⟨.tick, .res :: cellR τ k, ?_, rfl, by simp [sys], ?_⟩
    · exact Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl
        (Multiset.mem_map.2 ⟨(τ, k + 1), hx, rfl⟩))))
    · have h1 := erase_R (L₂ := L₂) (U := U) hx
      simp only [cellR] at h1
      rw [h1, cons_P _ _ _ (τ, k)]
      simpa [sys, upd_empty] using hw

/-- A window `R`: some paused cell resumes. -/
lemma wwin_R {ws : List (WI Gate P)} {L₁ L₂ : Multiset (Sym × ℕ)}
    {U : Multiset (List (PA Sym O))} (hU : X.UOk U) {d : Set D} :
    X.sys.WWin (.win .R :: ws) (liveR L₁ + liveP L₂ + U) d ↔
      ∃ x ∈ L₂, X.sys.WWin ws (liveR (x ::ₘ L₁) + liveP (L₂.erase x) + U) d := by
  simp only [WWin]
  constructor
  · rintro ⟨a, c, hc, hg, -, hw⟩
    rcases X.mem_pool hU hc with ⟨τ, -, rfl, rfl⟩ | ⟨τ, k, -, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩ |
      ⟨τ, -, rfl, rfl⟩ | ⟨o, -, rfl, rfl⟩
    · cases hg
    · cases hg
    · refine ⟨x, hx, ?_⟩
      rw [erase_P hx, cons_R] at hw
      simpa [sys, upd_empty] using hw
    · cases hg
    · cases hg
  · rintro ⟨x, hx, hw⟩
    refine ⟨.res, cellR x.1 x.2, ?_, rfl, by simp [sys], ?_⟩
    · exact Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inr
        (Multiset.mem_map.2 ⟨x, hx, rfl⟩))))
    · rw [erase_P hx, cons_R]
      simpa [sys, upd_empty] using hw

/-- A window `F`: a resumed cell without units left finishes and reports its symbol. -/
lemma wwin_F {ws : List (WI Gate P)} {L₁ L₂ : Multiset (Sym × ℕ)}
    {U : Multiset (List (PA Sym O))} (hU : X.UOk U) {d : Set D} :
    X.sys.WWin (.win .F :: ws) (liveR L₁ + liveP L₂ + U) d ↔
      ∃ τ, (τ, 0) ∈ L₁ ∧
        X.sys.WWin ws (liveR (L₁.erase (τ, 0)) + liveP L₂ + ([] ::ₘ U)) (insert (X.rd τ) d) := by
  simp only [WWin]
  constructor
  · rintro ⟨a, c, hc, hg, -, hw⟩
    rcases X.mem_pool hU hc with ⟨τ, hx, rfl, rfl⟩ | ⟨τ, k, -, rfl, rfl⟩ | ⟨x, -, rfl, rfl⟩ |
      ⟨τ, -, rfl, rfl⟩ | ⟨o, -, rfl, rfl⟩
    · refine ⟨τ, hx, ?_⟩
      have h1 := erase_R (L₂ := L₂) (U := U) hx
      simp only [cellR] at h1
      rw [h1, cons_U] at hw
      simpa [sys, upd_single] using hw
    · cases hg
    · cases hg
    · cases hg
    · cases hg
  · rintro ⟨τ, hx, hw⟩
    refine ⟨.fin τ, [], ?_, rfl, by simp [sys], ?_⟩
    · exact Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl
        (Multiset.mem_map.2 ⟨(τ, 0), hx, rfl⟩))))
    · have h1 := erase_R (L₂ := L₂) (U := U) hx
      simp only [cellR] at h1
      rw [h1, cons_U]
      simpa [sys, upd_single] using hw

/-- A window `I`: the player starts a fresh cell of a symbol of her choice. -/
lemma wwin_I {ws : List (WI Gate P)} {L₁ L₂ : Multiset (Sym × ℕ)}
    {U : Multiset (List (PA Sym O))} (hU : X.UOk U) {d : Set D} :
    X.sys.WWin (.win .I :: ws) (liveR L₁ + liveP L₂ + U) d ↔
      ∃ τ, X.newCell τ ∈ U ∧
        X.sys.WWin ws (liveR ((τ, X.S) ::ₘ L₁) + liveP L₂ + U.erase (X.newCell τ))
          (insert (X.wr τ) d) := by
  simp only [WWin]
  constructor
  · rintro ⟨a, c, hc, hg, -, hw⟩
    rcases X.mem_pool hU hc with ⟨τ, -, rfl, rfl⟩ | ⟨τ, k, -, rfl, rfl⟩ | ⟨x, -, rfl, rfl⟩ |
      ⟨τ, hx, rfl, rfl⟩ | ⟨o, -, rfl, rfl⟩
    · cases hg
    · cases hg
    · cases hg
    · refine ⟨τ, hx, ?_⟩
      have h1 := erase_U (L₁ := L₁) (L₂ := L₂) hx
      simp only [newCell] at h1
      rw [h1, show cellR τ X.S = cellR ((τ, X.S) : Sym × ℕ).1 (τ, X.S).2 from rfl, cons_R] at hw
      simpa [sys, upd_single, newCell] using hw
    · cases hg
  · rintro ⟨τ, hx, hw⟩
    refine ⟨.init τ, cellR τ X.S, ?_, rfl, by simp [sys], ?_⟩
    · exact Multiset.mem_add.2 (Or.inr hx)
    · have h1 := erase_U (L₁ := L₁) (L₂ := L₂) hx
      simp only [newCell] at h1
      rw [h1, show cellR τ X.S = cellR ((τ, X.S) : Sym × ℕ).1 (τ, X.S).2 from rfl, cons_R]
      simpa [sys, upd_single, newCell] using hw

/-- A window `U`: the player executes an option whose precondition holds. -/
lemma wwin_U {ws : List (WI Gate P)} {L₁ L₂ : Multiset (Sym × ℕ)}
    {U : Multiset (List (PA Sym O))} (hU : X.UOk U) {d : Set D} :
    X.sys.WWin (.win .U :: ws) (liveR L₁ + liveP L₂ + U) d ↔
      ∃ o, [.opt o] ∈ U ∧ X.opre o ⊆ d ∧
        X.sys.WWin ws (liveR L₁ + liveP L₂ + ([] ::ₘ U.erase [.opt o]))
          (WSys.upd d (X.oadd o) (X.odel o)) := by
  simp only [WWin]
  constructor
  · rintro ⟨a, c, hc, hg, hpre, hw⟩
    rcases X.mem_pool hU hc with ⟨τ, -, rfl, rfl⟩ | ⟨τ, k, -, rfl, rfl⟩ | ⟨x, -, rfl, rfl⟩ |
      ⟨τ, -, rfl, rfl⟩ | ⟨o, ho, rfl, rfl⟩
    · cases hg
    · cases hg
    · cases hg
    · cases hg
    · refine ⟨o, ho, hpre, ?_⟩
      rw [erase_U ho, cons_U] at hw
      simpa [sys] using hw
  · rintro ⟨o, ho, hpre, hw⟩
    refine ⟨.opt o, [], Multiset.mem_add.2 (Or.inr ho), rfl, hpre, ?_⟩
    rw [erase_U ho, cons_U]
    simpa [sys] using hw

/-! ## Phases and steps -/

/-- One unit less. -/
def dec (x : Sym × ℕ) : Sym × ℕ := (x.1, x.2 - 1)

lemma map_dec_erase {L₁ L₂ : Multiset (Sym × ℕ)} {τ : Sym} {k : ℕ} (hx : (τ, k + 1) ∈ L₁) :
    (L₁.erase (τ, k + 1)).map dec + (τ, k) ::ₘ L₂ = L₁.map dec + L₂ := by
  conv_rhs => rw [← Multiset.cons_erase hx]
  simp [dec, Multiset.add_cons, Multiset.cons_add]

/-- **The tick phase**: `n` windows `T` with `n` resumed cells tick every cell once. -/
lemma wwin_Tphase {U : Multiset (List (PA Sym O))} (hU : X.UOk U) :
    ∀ (n : ℕ) (L₁ L₂ : Multiset (Sym × ℕ)) (ws : List (WI Gate P)) (d : Set D),
    Multiset.card L₁ = n →
    (X.sys.WWin (List.replicate n (.win .T) ++ ws) (liveR L₁ + liveP L₂ + U) d ↔
      (∀ x ∈ L₁, 1 ≤ x.2) ∧ X.sys.WWin ws (liveR 0 + liveP (L₁.map dec + L₂) + U) d) := by
  intro n
  induction n with
  | zero =>
    intro L₁ L₂ ws d h
    rw [Multiset.card_eq_zero.1 h]
    simp
  | succ n ih =>
    intro L₁ L₂ ws d h
    rw [List.replicate_succ, List.cons_append, X.wwin_T hU]
    constructor
    · rintro ⟨τ, k, hx, hw⟩
      have hc : Multiset.card (L₁.erase (τ, k + 1)) = n := by
        rw [Multiset.card_erase_of_mem hx, h]; rfl
      obtain ⟨hall, hw⟩ := (ih _ _ ws d hc).1 hw
      refine ⟨fun x hx' => ?_, by rwa [map_dec_erase hx] at hw⟩
      rw [← Multiset.cons_erase hx] at hx'
      rcases Multiset.mem_cons.1 hx' with rfl | hx'
      · simp
      · exact hall x hx'
    · rintro ⟨hall, hw⟩
      obtain ⟨⟨τ, k'⟩, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card L₁)
      obtain ⟨k, rfl⟩ : ∃ k, k' = k + 1 := ⟨k' - 1, by have := hall _ hx; simp at this; omega⟩
      have hc : Multiset.card (L₁.erase (τ, k + 1)) = n := by
        rw [Multiset.card_erase_of_mem hx, h]; rfl
      refine ⟨τ, k, hx, (ih _ _ ws d hc).2 ⟨fun x hx' => hall x (Multiset.mem_of_mem_erase hx'), ?_⟩⟩
      rwa [map_dec_erase hx]

/-- **The resume phase**: `n` windows `R` with `n` paused cells resume every cell. -/
lemma wwin_Rphase {U : Multiset (List (PA Sym O))} (hU : X.UOk U) :
    ∀ (n : ℕ) (L₁ L₂ : Multiset (Sym × ℕ)) (ws : List (WI Gate P)) (d : Set D),
    Multiset.card L₂ = n →
    (X.sys.WWin (List.replicate n (.win .R) ++ ws) (liveR L₁ + liveP L₂ + U) d ↔
      X.sys.WWin ws (liveR (L₂ + L₁) + liveP 0 + U) d) := by
  intro n
  induction n with
  | zero =>
    intro L₁ L₂ ws d h
    rw [Multiset.card_eq_zero.1 h]
    simp
  | succ n ih =>
    intro L₁ L₂ ws d h
    rw [List.replicate_succ, List.cons_append, X.wwin_R hU]
    have key : ∀ x ∈ L₂, L₂.erase x + x ::ₘ L₁ = L₂ + L₁ := by
      intro x hx
      conv_rhs => rw [← Multiset.cons_erase hx]
      simp [Multiset.add_cons, Multiset.cons_add]
    have hc : ∀ x ∈ L₂, Multiset.card (L₂.erase x) = n := by
      intro x hx; rw [Multiset.card_erase_of_mem hx, h]; rfl
    constructor
    · rintro ⟨x, hx, hw⟩
      rwa [ih _ _ ws d (hc x hx), key x hx] at hw
    · intro hw
      obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card L₂)
      exact ⟨x, hx, by rwa [ih _ _ ws d (hc x hx), key x hx]⟩

/-- The windows of one step with `n` live cells. -/
def stepW (n : ℕ) : List (WI Gate P) :=
  List.replicate n (.win .T) ++ (List.replicate n (.win .R) ++ [.win .F, .win .I, .win .U])

/-- **One step** on `n` resumed cells `L`: every cell must have a unit left; a cell with one unit
left finishes and reports `σ`; the player starts a cell `τ` and executes an option `o`. -/
lemma wwin_step {U : Multiset (List (PA Sym O))} (hU : X.UOk U) {n : ℕ}
    {L : Multiset (Sym × ℕ)} (hn : Multiset.card L = n) (ws : List (WI Gate P)) (d : Set D) :
    X.sys.WWin (stepW n ++ ws) (liveR L + liveP 0 + U) d ↔
      (∀ x ∈ L, 1 ≤ x.2) ∧ ∃ σ, (σ, 0) ∈ L.map dec ∧ ∃ τ, X.newCell τ ∈ [] ::ₘ U ∧
        ∃ o, [.opt o] ∈ ([] ::ₘ U).erase (X.newCell τ) ∧
          X.opre o ⊆ insert (X.wr τ) (insert (X.rd σ) d) ∧
          X.sys.WWin ws (liveR ((τ, X.S) ::ₘ (L.map dec).erase (σ, 0)) + liveP 0 +
              ([] ::ₘ (([] ::ₘ U).erase (X.newCell τ)).erase [.opt o]))
            (WSys.upd (insert (X.wr τ) (insert (X.rd σ) d)) (X.oadd o) (X.odel o)) := by
  simp only [stepW, List.append_assoc, List.cons_append, List.nil_append]
  rw [X.wwin_Tphase hU n L 0 _ d hn]
  apply and_congr_right
  intro _
  rw [X.wwin_Rphase hU n 0 _ _ d (by simp [hn])]
  simp only [add_zero]
  rw [X.wwin_F hU]
  apply exists_congr
  intro σ
  apply and_congr_right
  intro hσ
  rw [X.wwin_I (hU.cons_nil)]
  apply exists_congr
  intro τ
  apply and_congr_right
  intro _
  rw [X.wwin_U (UOk.erase X (UOk.cons_nil X hU) (X.newCell τ))]

/-! ## Queues -/

/-- The cells of a queue `q` whose head has `i + 1` units left: the `j`-th symbol has
`i + j + 1` units left. -/
def enc : List Sym → ℕ → Multiset (Sym × ℕ)
  | [], _ => 0
  | σ :: q, i => (σ, i + 1) ::ₘ enc q (i + 1)

lemma mem_enc : ∀ {q : List Sym} {i : ℕ} {x : Sym × ℕ}, x ∈ enc q i →
    i + 1 ≤ x.2 ∧ x.2 ≤ i + q.length ∧ x.1 ∈ q
  | [], _, _, h => by simp [enc] at h
  | σ :: q, i, x, h => by
    rcases Multiset.mem_cons.1 h with rfl | h
    · simp
    · obtain ⟨h1, h2, h3⟩ := mem_enc h
      simp only [List.length_cons, List.mem_cons]
      exact ⟨by omega, by omega, Or.inr h3⟩

lemma card_enc : ∀ (q : List Sym) (i : ℕ), Multiset.card (enc q i) = q.length
  | [], _ => rfl
  | σ :: q, i => by simp [enc, card_enc q (i + 1)]

lemma map_dec_enc : ∀ (q : List Sym) (i : ℕ), (enc q (i + 1)).map dec = enc q i
  | [], _ => rfl
  | σ :: q, i => by
    simp only [enc, Multiset.map_cons, map_dec_enc q (i + 1)]
    rfl

lemma enc_append (τ : Sym) : ∀ (q : List Sym) (i : ℕ),
    enc (q ++ [τ]) i = (τ, i + q.length + 1) ::ₘ enc q i
  | [], i => by simp [enc]
  | σ :: q, i => by
    simp only [List.cons_append, enc, enc_append τ q (i + 1), List.length_cons,
      Multiset.cons_swap (σ, i + 1)]
    congr 2
    omega

lemma nodup_enc : ∀ (q : List Sym) (i : ℕ), (enc q i).Nodup
  | [], _ => Multiset.nodup_zero
  | σ :: q, i => by
    refine Multiset.nodup_cons.2 ⟨fun h => ?_, nodup_enc q (i + 1)⟩
    have := (mem_enc h).1
    simp at this

/-- Steps of a queue program (`none`). -/
def steps : List (Option P) → ℕ
  | [] => 0
  | none :: r => steps r + 1
  | some _ :: r => steps r

/-- The window program of a queue program. -/
def expandQ : List (Option P) → List (WI Gate P)
  | [] => []
  | none :: r => stepW X.S ++ expandQ r
  | some p :: r => .plain p :: expandQ r

/-- **The queue game.**  A step on the queue `σ :: q`: the player appends a symbol `τ` (a fresh
cell of the pool `U`) and executes an option `o` whose precondition holds after `rd σ` and
`wr τ` have been added.  A plain action: precondition, and every outcome. -/
def QWin : List (Option P) → List Sym → Multiset (List (PA Sym O)) → Set D → Prop
  | [], _, _, _ => True
  | some p :: r, q, U, d => X.ppre p ⊆ d ∧ ∀ e ∈ X.peffs p, QWin r q U (WSys.upd d e.1 e.2)
  | none :: _, [], _, _ => False
  | none :: r, σ :: q, U, d => ∃ τ, X.newCell τ ∈ [] ::ₘ U ∧
      ∃ o, [.opt o] ∈ ([] ::ₘ U).erase (X.newCell τ) ∧
        X.opre o ⊆ insert (X.wr τ) (insert (X.rd σ) d) ∧
        QWin r (q ++ [τ]) ([] ::ₘ (([] ::ₘ U).erase (X.newCell τ)).erase [.opt o])
          (WSys.upd (insert (X.wr τ) (insert (X.rd σ) d)) (X.oadd o) (X.odel o))

lemma UOk.step {U : Multiset (List (PA Sym O))} (hU : X.UOk U) (τ : Sym) (o : O) :
    X.UOk ([] ::ₘ (([] ::ₘ U).erase (X.newCell τ)).erase [.opt o]) :=
  UOk.cons_nil X (UOk.erase X (UOk.erase X (UOk.cons_nil X hU) _) _)

/-- **Good queues**: on the cells of a queue of length `S`, the window game is the queue
game. -/
theorem wwin_good_iff : ∀ (prog : List (Option P)) (q : List Sym)
    (U : Multiset (List (PA Sym O))) (d : Set D), q.length = X.S → X.UOk U →
    (X.sys.WWin (X.expandQ prog) (liveR (enc q 0) + liveP 0 + U) d ↔ X.QWin prog q U d) := by
  intro prog
  induction prog with
  | nil => intro q U d _ _; simp [expandQ, WSys.WWin, QWin]
  | cons i r ih =>
    intro q U d hq hU
    cases i with
    | some p =>
      simp only [expandQ, WSys.WWin, QWin]
      apply and_congr_right
      intro _
      exact forall₂_congr fun e _ => ih q U _ hq hU
    | none =>
      simp only [expandQ]
      rw [X.wwin_step hU (by rw [card_enc, hq]) _ d]
      cases q with
      | nil =>
        simp only [QWin, iff_false, not_and, not_exists]
        intro _ σ h
        simp [enc] at h
      | cons σ q =>
        have hL : (enc (σ :: q) 0).map dec = (σ, 0) ::ₘ enc q 0 := by
          simp only [enc, Multiset.map_cons, map_dec_enc q 0]
          rfl
        simp only [QWin]
        constructor
        · rintro ⟨-, σ', hσ', τ, hτ, o, ho, hpre, hw⟩
          rw [hL] at hσ' hw
          have hσσ : σ' = σ := by
            rcases Multiset.mem_cons.1 hσ' with h | h
            · exact (Prod.mk.inj h).1
            · exact absurd (mem_enc h).1 (by simp)
          subst hσσ
          refine ⟨τ, hτ, o, ho, hpre, ?_⟩
          rw [Multiset.erase_cons_head] at hw
          have he : (τ, X.S) ::ₘ enc q 0 = enc (q ++ [τ]) 0 := by
            rw [enc_append]; simp at hq; congr 2; omega
          rw [he] at hw
          exact (ih _ _ _ (by simp at hq ⊢; omega) (UOk.step X hU τ o)).1 hw
        · rintro ⟨τ, hτ, o, ho, hpre, hw⟩
          refine ⟨fun x hx => ?_, σ, by rw [hL]; exact Multiset.mem_cons_self _ _, τ, hτ, o, ho,
            hpre, ?_⟩
          · simp only [enc] at hx
            rcases Multiset.mem_cons.1 hx with rfl | hx
            · simp
            · have := (mem_enc hx).1; omega
          · rw [hL, Multiset.erase_cons_head]
            have he : (τ, X.S) ::ₘ enc q 0 = enc (q ++ [τ]) 0 := by
              rw [enc_append]; simp at hq; congr 2; omega
            rw [he]
            exact (ih _ _ _ (by simp at hq ⊢; omega) (UOk.step X hU τ o)).2 hw

/-- **Bad staggering loses**: if some number of units `v ∈ [1, S]` is missing among `S` live
cells, the player is stuck within `v` steps. -/
theorem not_wwin_bad (hne : ∀ p, (X.peffs p).Nonempty) : ∀ (prog : List (Option P))
    (L : Multiset (Sym × ℕ)) (U : Multiset (List (PA Sym O))) (d : Set D) (v : ℕ),
    X.UOk U → Multiset.card L = X.S → 1 ≤ v → v ≤ X.S → v ∉ L.map Prod.snd → v ≤ steps prog →
    ¬ X.sys.WWin (X.expandQ prog) (liveR L + liveP 0 + U) d := by
  intro prog
  induction prog with
  | nil => intro L U d v _ _ h1 _ _ hs; simp [steps] at hs; omega
  | cons i r ih =>
    intro L U d v hU hL h1 hvS hv hs hw
    cases i with
    | some p =>
      simp only [expandQ, WSys.WWin] at hw
      obtain ⟨e, he⟩ := hne p
      exact ih L U _ v hU hL h1 hvS hv (by simpa [steps] using hs) (hw.2 e he)
    | none =>
      simp only [expandQ] at hw
      rw [X.wwin_step hU hL] at hw
      obtain ⟨hall, σ, hσ, τ, -, o, -, -, hw⟩ := hw
      obtain ⟨⟨σ', k⟩, hx, hxe⟩ := Multiset.mem_map.1 hσ
      simp only [dec, Prod.mk.injEq] at hxe
      have hk1 := hall _ hx
      simp only at hk1
      by_cases hv1 : v = 1
      · subst hv1
        exact hv (Multiset.mem_map.2 ⟨_, hx, by simp; omega⟩)
      · refine ih _ _ _ (v - 1) (UOk.step X hU τ o) ?_ (by omega) (by omega) ?_ (by simp [steps] at hs; omega) hw
        · rw [Multiset.card_cons, Multiset.card_erase_of_mem hσ, Multiset.card_map, hL,
            Nat.pred_eq_sub_one]
          omega
        · intro hm
          rw [Multiset.map_cons, Multiset.mem_cons] at hm
          rcases hm with hm | hm
          · simp at hm; omega
          · have hm' := Multiset.map_le_map (f := Prod.snd) (Multiset.erase_le (σ, 0) (L.map dec))
            obtain ⟨y, hy, hye⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hm' hm)
            obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
            have := hall z hz
            simp only [dec] at hye
            exact hv (Multiset.mem_map.2 ⟨z, hz, by omega⟩)

/-! ## The pre-warm phase -/

/-- `m` pairs of windows `T`, `R`. -/
def preW : ℕ → List (WI Gate P)
  | 0 => []
  | m + 1 => .win .T :: .win .R :: preW m

/-- `m` single-unit advances of cells. -/
def PreReach : ℕ → Multiset (Sym × ℕ) → Multiset (Sym × ℕ) → Prop
  | 0, L, L' => L' = L
  | m + 1, L, L' => ∃ τ k, (τ, k + 1) ∈ L ∧ PreReach m ((τ, k) ::ₘ L.erase (τ, k + 1)) L'

lemma wwin_pair {U : Multiset (List (PA Sym O))} (hU : X.UOk U) (L : Multiset (Sym × ℕ))
    (ws : List (WI Gate P)) (d : Set D) :
    X.sys.WWin (.win .T :: .win .R :: ws) (liveR L + liveP 0 + U) d ↔
      ∃ τ k, (τ, k + 1) ∈ L ∧
        X.sys.WWin ws (liveR ((τ, k) ::ₘ L.erase (τ, k + 1)) + liveP 0 + U) d := by
  rw [X.wwin_T hU]
  apply exists_congr; intro τ; apply exists_congr; intro k; apply and_congr_right; intro _
  rw [X.wwin_R hU]
  simp

lemma wwin_preW {U : Multiset (List (PA Sym O))} (hU : X.UOk U) :
    ∀ (m : ℕ) (L : Multiset (Sym × ℕ)) (ws : List (WI Gate P)) (d : Set D),
    X.sys.WWin (preW m ++ ws) (liveR L + liveP 0 + U) d ↔
      ∃ L', PreReach m L L' ∧ X.sys.WWin ws (liveR L' + liveP 0 + U) d := by
  intro m
  induction m with
  | zero => intro L ws d; simp [preW, PreReach]
  | succ m ih =>
    intro L ws d
    simp only [preW, List.cons_append, PreReach]
    rw [X.wwin_pair hU]
    constructor
    · rintro ⟨τ, k, hx, hw⟩
      obtain ⟨L', h1, h2⟩ := (ih _ ws d).1 hw
      exact ⟨L', ⟨τ, k, hx, h1⟩, h2⟩
    · rintro ⟨L', ⟨τ, k, hx, h1⟩, h2⟩
      exact ⟨τ, k, hx, (ih _ ws d).2 ⟨L', h1, h2⟩⟩

lemma PreReach.card : ∀ {m : ℕ} {L L' : Multiset (Sym × ℕ)}, PreReach m L L' →
    Multiset.card L' = Multiset.card L
  | 0, _, _, h => by rw [h]
  | m + 1, L, L', ⟨τ, k, hx, h⟩ => by
    rw [PreReach.card h, Multiset.card_cons, Multiset.card_erase_of_mem hx, Nat.pred_eq_sub_one]
    have : 0 < Multiset.card L := Multiset.card_pos_iff_exists_mem.2 ⟨_, hx⟩
    omega

lemma PreReach.fst {b : Sym} : ∀ {m : ℕ} {L L' : Multiset (Sym × ℕ)}, PreReach m L L' →
    (∀ x ∈ L, x.1 = b) → ∀ x ∈ L', x.1 = b
  | 0, _, _, h, hL => by rw [h]; exact hL
  | m + 1, L, L', ⟨τ, k, hx, h⟩, hL => by
    refine PreReach.fst h fun x hx' => ?_
    rcases Multiset.mem_cons.1 hx' with rfl | hx'
    · exact hL (τ, k + 1) hx
    · exact hL x (Multiset.mem_of_mem_erase hx')

lemma PreReach.frame (y : Sym × ℕ) : ∀ {m : ℕ} {L L' : Multiset (Sym × ℕ)}, PreReach m L L' →
    PreReach m (y ::ₘ L) (y ::ₘ L')
  | 0, _, _, h => by rw [h]; rfl
  | m + 1, L, L', ⟨τ, k, hx, h⟩ => by
    refine ⟨τ, k, Multiset.mem_cons_of_mem hx, ?_⟩
    rw [Multiset.erase_cons_tail_of_mem hx, Multiset.cons_swap]
    exact PreReach.frame y h

lemma PreReach.trans : ∀ {m₁ m₂ : ℕ} {L L' L'' : Multiset (Sym × ℕ)}, PreReach m₁ L L' →
    PreReach m₂ L' L'' → PreReach (m₁ + m₂) L L''
  | 0, m₂, L, L', L'', h1, h2 => by rw [h1] at h2; simpa using h2
  | m₁ + 1, m₂, L, L', L'', ⟨τ, k, hx, h⟩, h2 => by
    rw [show m₁ + 1 + m₂ = (m₁ + m₂) + 1 by ring]
    exact ⟨τ, k, hx, PreReach.trans h h2⟩

lemma PreReach.move (τ : Sym) (L : Multiset (Sym × ℕ)) : ∀ (j K : ℕ), j ≤ K →
    PreReach j ((τ, K) ::ₘ L) ((τ, K - j) ::ₘ L)
  | 0, K, _ => by simp [PreReach]
  | j + 1, K, h => by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    refine ⟨τ, K', Multiset.mem_cons_self _ _, ?_⟩
    rw [Multiset.erase_cons_head]
    have := PreReach.move τ L j K' (by omega)
    rwa [show K' + 1 - (j + 1) = K' - j by omega]

/-- `tri n = n (n - 1) / 2`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + n

/-- **Perfect staggering** of `n` cells with `K` units: `tri n` advances. -/
lemma PreReach.stagger (τ : Sym) : ∀ (n K : ℕ), n ≤ K →
    PreReach (tri n) (Multiset.replicate n (τ, K)) (enc (List.replicate n τ) (K - n))
  | 0, K, _ => by simp [tri, PreReach, enc]
  | n + 1, K, h => by
    rw [Multiset.replicate_succ, tri]
    have h1 := (PreReach.stagger τ n K (by omega)).frame (τ, K)
    have h2 := PreReach.move τ (enc (List.replicate n τ) (K - n)) n K (by omega)
    have h3 := h1.trans h2
    rw [List.replicate_succ, enc, show K - (n + 1) + 1 = K - n by omega]
    exact h3

lemma eq_enc_of {b : Sym} {L : Multiset (Sym × ℕ)} (hb : ∀ x ∈ L, x.1 = b)
    (hc : Multiset.card L = X.S) (hall : ∀ v, 1 ≤ v → v ≤ X.S → v ∈ L.map Prod.snd) :
    L = enc (List.replicate X.S b) 0 := by
  symm
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (nodup_enc _ _)).2 ?_) ?_
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := mem_enc hx
    simp only [List.length_replicate, zero_add, List.mem_replicate] at h1 h2 h3
    obtain ⟨y, hy, hye⟩ := Multiset.mem_map.1 (hall x.2 h1 h2)
    have : y = x := Prod.ext ((hb y hy).trans h3.2.symm) hye
    exact this ▸ hy
  · rw [hc, card_enc, List.length_replicate]

/-! ## The main theorem -/

/-- **The FIFO theorem (window game).**  Starting from `S` blank cells `b` with all `S`
units, the pre-warm phase followed by a queue program with at least `S` steps is won iff the
queue game is won from the queue `b^S`. -/
theorem wwin_fifo_iff (hne : ∀ p, (X.peffs p).Nonempty)
    {U : Multiset (List (PA Sym O))} (hU : X.UOk U) (prog : List (Option P))
    (hst : X.S ≤ steps prog) (b : Sym) (d : Set D) :
    X.sys.WWin (preW (tri X.S) ++ X.expandQ prog) (liveR (Multiset.replicate X.S (b, X.S)) + U) d ↔
      X.QWin prog (List.replicate X.S b) U d := by
  have h0 : ∀ L : Multiset (Sym × ℕ), liveR (O := O) L + U = liveR L + liveP 0 + U := by
    intro L; simp [liveP]
  rw [h0, X.wwin_preW hU]
  constructor
  · rintro ⟨L', hr, hw⟩
    have hc : Multiset.card L' = X.S := by rw [hr.card]; simp
    have hb : ∀ x ∈ L', x.1 = b :=
      hr.fst fun x hx => (Multiset.eq_of_mem_replicate hx).symm ▸ rfl
    by_cases hall : ∀ v, 1 ≤ v → v ≤ X.S → v ∈ L'.map Prod.snd
    · rw [X.eq_enc_of hb hc hall] at hw
      exact (X.wwin_good_iff prog _ U d (by simp) hU).1 hw
    · push_neg at hall
      obtain ⟨v, h1, h2, hv⟩ := hall
      exact absurd hw (X.not_wwin_bad hne prog L' U d v hU hc h1 h2 hv (by omega))
  · intro hq
    refine ⟨_, PreReach.stagger b X.S X.S le_rfl, ?_⟩
    rw [Nat.sub_self]
    exact (X.wwin_good_iff prog _ U d (by simp) hU).2 hq

/-- **The FIFO theorem (chain game)**: the same for the chain game with the token encoding, the
control ending with at least as many refills as the pool has tasks. -/
theorem cwin_fifo_iff (hne : ∀ p, (X.peffs p).Nonempty)
    {U : Multiset (List (PA Sym O))} (hU : X.UOk U) (prog : List (Option P))
    (hst : X.S ≤ steps prog) (b : Sym) (d : Set D) (R : ℕ)
    (hR : WSys.size (liveR (Multiset.replicate X.S (b, X.S)) + U) ≤ R) :
    CWin X.sys.δC X.sys.δP (WSys.expand (preW (tri X.S) ++ X.expandQ prog) ++
        List.replicate R .refill) (liveR (Multiset.replicate X.S (b, X.S)) + U) (WSys.idle d) ↔
      X.QWin prog (List.replicate X.S b) U d := by
  rw [X.sys.cwin_iff_wwin R _ _ d hR]
  exact X.wwin_fifo_iff hne hU prog hst b d

end FSpec

end AcycHard

end FOND
