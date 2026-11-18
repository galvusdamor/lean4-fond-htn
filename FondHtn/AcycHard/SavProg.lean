import FondHtn.AcycHard.SavGame
import FondHtn.AcycHard.SavChk
/-!
# The queue program of the Savitch game

The automaton queue game (`FOND.AcycHard.autSpec`) that plays the Savitch game of a machine `N`
with `S` cells and `K` rounds (`doc/notes_acyc_expspace.md` §4):

* **input sweep** (`S` steps, states `inp i`): the player writes the triples `(c₀ᵢ, eᵢ, eᵢ)`,
  `c₀` the initial configuration, `e` the claimed accepting configuration;
* **`K` rounds** (`S` steps each, state `rd h`): reading the triples whose projection `h`
  (`FOND.AcycHard.Sav.proj`) is the current pair `(xᵢ, yᵢ)`, the player writes `(xᵢ, mᵢ, yᵢ)`,
  `m` the midpoint; nature then picks the next half `h` (`half`, or `halfChk` after the last
  round);
* **check sweep** (`S` steps, states `ck h c`): the check automaton `FOND.AcycHard.Sav.chk`
  reads the pairs of the chosen half; it guesses the last cell and moves to `ok`, which `acc`
  requires.

**`FOND.AcycHard.Sav.qi_prog_iff`**: the queue game is won iff some accepting configuration
wins the Savitch game against the initial one.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

namespace Sav

open HTN TM

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] [Inhabited Γ] [Inhabited Q]

/-- The queue symbols: triples of cells (or the blank). -/
abbrev Sym (Q Γ : Type) := Option (X Q Γ × X Q Γ × X Q Γ)

/-- The automaton states. -/
inductive AS (Q : Type)
  | inp (i : ℕ)
  | rd (h : Bool)
  | ck (h : Bool) (c : CS Q)
  | ok
  deriving DecidableEq

/-- The plain actions. -/
inductive Pl
  | toRd
  | half
  | halfChk
  | acc
  deriving DecidableEq

/-- The pair of a half: `false` the left half `(x, m)`, `true` the right half `(m, y)`. -/
def proj : Bool → X Q Γ × X Q Γ × X Q Γ → X Q Γ × X Q Γ
  | false, t => (t.1, t.2.1)
  | true, t => (t.2.1, t.2.2)

/-- A cell of an accepting configuration. -/
def AccOK (N : NTM Q Γ) (e : X Q Γ) : Prop := ∀ q, e.2 = some q → q ∈ N.accept

variable (N : NTM Q Γ) (c₀ : Config Q Γ) (L : ℕ)

/-- **The transitions.** -/
def Δ : Set (AS Q × Sym Q Γ × Sym Q Γ × AS Q) := {o |
  (∃ i, o.1 = .inp i ∧ i ≤ L + 1 ∧ o.2.2.2 = .inp (min (i + 1) (L + 1)) ∧
    ∃ e, AccOK N e ∧ o.2.2.1 = some (mk c₀ i, e, e)) ∨
  (∃ h, o.1 = .rd h ∧ o.2.2.2 = .rd h ∧ ∃ t t', o.2.1 = some t ∧ o.2.2.1 = some t' ∧
    t'.1 = (proj h t).1 ∧ t'.2.2 = (proj h t).2) ∨
  (∃ h c, o.1 = .ck h c ∧ ∃ t, o.2.1 = some t ∧ ∃ c', chk N c (proj h t) c' ∧
    (o.2.2.2 = .ck h c' ∨ (final c' ∧ o.2.2.2 = .ok)))}

/-- Preconditions of the plain actions. -/
def pp : Pl → Set (Fct (AS Q) (Sym Q Γ))
  | .acc => {Fct.st .ok}
  | _ => ∅

/-- Effects of the plain actions. -/
def pe : Pl → Set (Set (Fct (AS Q) (Sym Q Γ)) × Set (Fct (AS Q) (Sym Q Γ)))
  | .toRd => {({Fct.st (.rd false)}, {f | ∃ i ≤ L + 1, f = Fct.st (.inp i)})}
  | .half => {e | ∃ h, e = ({Fct.st (.rd h)}, {Fct.st (.rd false), Fct.st (.rd true)})}
  | .halfChk => {e | ∃ h, e = ({Fct.st (.ck h .start)}, {Fct.st (.rd false), Fct.st (.rd true)})}
  | .acc => {(∅, ∅)}

variable (S : ℕ)

/-- **The specification.** -/
abbrev spec : FSpec (Sym Q Γ) (AS Q × Sym Q Γ × Sym Q Γ × AS Q) (Fct (AS Q) (Sym Q Γ)) Pl :=
  autSpec S pp (pe L)

/-- A sweep. -/
def sweep : List (Option Pl) := List.replicate S none

/-- The rounds: `rnd k` has `k + 1` rounds and the check sweep. -/
def rnd : ℕ → List (Option Pl)
  | 0 => sweep S ++ [some .halfChk] ++ sweep S ++ [some .acc]
  | k + 1 => sweep S ++ [some .half] ++ rnd k

/-- **The program** with `K + 1` rounds. -/
def prog (K : ℕ) : List (Option Pl) := sweep S ++ [some .toRd] ++ rnd S K

/-- The game. -/
abbrev G (prog : List (Option Pl)) (q : List (Sym Q Γ)) (d : Set (Fct (AS Q) (Sym Q Γ))) : Prop :=
  (spec L S).QI (fun _ => True) (· ∈ Δ N c₀ L) prog q d

/-! ## The transitions by state -/

section Mem

variable {N c₀ L}

theorem mem_Δ_inp {i : ℕ} {σ τ : Sym Q Γ} {a' : AS Q} : (AS.inp i, σ, τ, a') ∈ Δ N c₀ L ↔
    i ≤ L + 1 ∧ a' = .inp (min (i + 1) (L + 1)) ∧ ∃ e, AccOK N e ∧ τ = some (mk c₀ i, e, e) := by
  simp [Δ]

theorem mem_Δ_rd {h : Bool} {σ τ : Sym Q Γ} {a' : AS Q} : (AS.rd h, σ, τ, a') ∈ Δ N c₀ L ↔
    a' = .rd h ∧ ∃ t t', σ = some t ∧ τ = some t' ∧ t'.1 = (proj h t).1 ∧ t'.2.2 = (proj h t).2 := by
  simp only [Δ, Set.mem_setOf_eq, reduceCtorEq, false_and, exists_false, false_or, or_false,
    AS.rd.injEq, exists_eq_left']

theorem mem_Δ_ck {h : Bool} {c : CS Q} {σ τ : Sym Q Γ} {a' : AS Q} : (AS.ck h c, σ, τ, a') ∈ Δ N c₀ L ↔
    ∃ t, σ = some t ∧ ∃ c', chk N c (proj h t) c' ∧ (a' = .ck h c' ∨ (final c' ∧ a' = .ok)) := by
  simp only [Δ, Set.mem_setOf_eq, reduceCtorEq, false_and, exists_false, false_or,
    AS.ck.injEq]
  constructor
  · rintro ⟨h', c', ⟨rfl, rfl⟩, h⟩; exact h
  · intro h'; exact ⟨h, c, ⟨rfl, rfl⟩, h'⟩

theorem not_mem_Δ_ok {σ τ : Sym Q Γ} {a' : AS Q} : (AS.ok, σ, τ, a') ∉ Δ N c₀ L := by
  simp [Δ]

end Mem

/-! ## The check sweep -/

theorem upd_same (d : Set (Fct (AS Q) (Sym Q Γ))) : WSys.upd d ∅ ∅ = d := by simp [WSys.upd]

theorem G_ok : ∀ (n : ℕ) (q : List (Sym Q Γ)), n ≤ q.length →
    (G N c₀ L S (List.replicate n none ++ [some .acc]) q {Fct.st .ok} ↔ n = 0) := by
  intro n q hq
  rcases n with _ | n
  · simp only [List.replicate_zero, List.nil_append, G, qi_plain, pp, pe, Set.mem_singleton_iff,
      forall_eq, upd_same, iff_true]
    exact ⟨subset_rfl, trivial⟩
  · obtain ⟨σ, q, rfl⟩ : ∃ σ q', q = σ :: q' := by
      cases q with
      | nil => simp at hq
      | cons σ q => exact ⟨σ, q, rfl⟩
    simp only [List.replicate_succ, List.cons_append, G, qi_step, true_and]
    simp [not_mem_Δ_ok]

theorem G_check (h : Bool) : ∀ (ts : List (X Q Γ × X Q Γ × X Q Γ)) (rest : List (Sym Q Γ)) (c : CS Q),
    G N c₀ L S (List.replicate ts.length none ++ [some .acc]) (ts.map some ++ rest) {Fct.st (.ck h c)} ↔
      Acc N c (ts.map (proj h)) ∧ ts ≠ [] := by
  intro ts
  induction ts with
  | nil =>
    intro rest c
    simp only [List.length_nil, List.replicate_zero, List.nil_append, List.map_nil, G, qi_plain, pp,
      Set.singleton_subset_iff, Set.mem_singleton_iff, Fct.st.injEq, reduceCtorEq, false_and,
      ne_eq, not_true_eq_false, and_false]
  | cons t ts ih =>
    intro rest c
    simp only [List.length_cons, List.replicate_succ, List.cons_append, List.map_cons, G, qi_step,
      true_and, mem_Δ_ck, Option.some.injEq]
    constructor
    · rintro ⟨τ, a', ⟨t', rfl, c', hc, ha | ⟨hf, rfl⟩⟩, h'⟩
      · subst ha
        have := (ih (rest ++ [τ]) c').1 (by simpa [List.append_assoc] using h')
        exact ⟨⟨c', hc, this.1⟩, by simp⟩
      · have hn := (G_ok N c₀ L S ts.length (ts.map some ++ (rest ++ [τ])) (by simp)).1 (by simpa [List.append_assoc] using h')
        rw [List.length_eq_zero_iff] at hn
        subst hn
        exact ⟨⟨c', hc, hf⟩, by simp⟩
    · rintro ⟨⟨c', hc, h'⟩, -⟩
      by_cases hts : ts = []
      · subst hts
        refine ⟨none, .ok, ⟨t, rfl, c', hc, Or.inr ⟨h', rfl⟩⟩, ?_⟩
        exact (G_ok N c₀ L S 0 _ (Nat.zero_le _)).2 rfl
      · refine ⟨none, .ck h c', ⟨t, rfl, c', hc, Or.inl rfl⟩, ?_⟩
        have := (ih (rest ++ [none]) c').2 ⟨h', hts⟩
        simpa [List.append_assoc] using this

/-! ## The rounds -/

/-- The writes of a round step in half `h`. -/
def WR (h : Bool) (_ : ℕ) (σ τ : Sym Q Γ) : Prop :=
  ∃ t t', σ = some t ∧ τ = some t' ∧ t'.1 = (proj h t).1 ∧ t'.2.2 = (proj h t).2

theorem hΔ_rd (h : Bool) : ∀ j (σ τ : Sym Q Γ) (a' : AS Q),
    True ∧ ((fun _ : ℕ => (AS.rd h : AS Q)) j, σ, τ, a') ∈ Δ N c₀ L ↔
      WR h j σ τ ∧ a' = (fun _ : ℕ => (AS.rd h : AS Q)) (j + 1) := by
  intro j σ τ a'
  simp only [true_and, mem_Δ_rd, WR]
  tauto

/-- The writes as triples. -/
theorem ws_iff (h : Bool) (ts : List (X Q Γ × X Q Γ × X Q Γ)) (P : List (Sym Q Γ) → Prop) :
    (∃ ws : List (Sym Q Γ), ws.length = (ts.map some).length ∧
      (∀ i (h1 : i < (ts.map some).length) (h2 : i < ws.length), WR h i (ts.map some)[i] ws[i]) ∧
        P ws) ↔
    ∃ ts' : List (X Q Γ × X Q Γ × X Q Γ), ts'.map Prod.fst = ts.map (fun t => (proj h t).1) ∧
      ts'.map (fun t => t.2.2) = ts.map (fun t => (proj h t).2) ∧ P (ts'.map some) := by
  constructor
  · rintro ⟨ws, hl, hW, hP⟩
    have hsome : ∀ i (hi : i < ws.length), ∃ t', ws[i] = some t' ∧
        t'.1 = (proj h (ts.getD i default)).1 ∧ t'.2.2 = (proj h (ts.getD i default)).2 := by
      intro i hi
      have hi' : i < ts.length := by simp at hl; omega
      obtain ⟨t, t', ht, ht', e1, e2⟩ := hW i (by simpa using hi') hi
      simp only [List.getElem_map, Option.some.injEq] at ht
      rw [List.getD_eq_getElem _ _ hi', ht]
      exact ⟨t', ht', e1, e2⟩
    refine ⟨ws.map fun σ => σ.getD default, ?_, ?_, ?_⟩
    · refine List.ext_getElem (by simp at hl ⊢; omega) fun i h1 h2 => ?_
      obtain ⟨t', e, e1, -⟩ := hsome i (by simpa using h1)
      have hi : i < ts.length := by simpa using h2
      simp [e, e1, List.getElem?_eq_getElem hi]
    · refine List.ext_getElem (by simp at hl ⊢; omega) fun i h1 h2 => ?_
      obtain ⟨t', e, -, e2⟩ := hsome i (by simpa using h1)
      have hi : i < ts.length := by simpa using h2
      simp [e, e2, List.getElem?_eq_getElem hi]
    · convert hP
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      obtain ⟨t', e, -, -⟩ := hsome i h2
      simp [e]
  · rintro ⟨ts', e1, e2, hP⟩
    have hl : ts'.length = ts.length := by simpa using congrArg List.length e1
    refine ⟨ts'.map some, by simp [hl], fun i h1 h2 => ?_, hP⟩
    simp only [List.length_map] at h1 h2
    refine ⟨ts[i], ts'[i], by simp, by simp, ?_, ?_⟩
    · have := congrArg (fun l => l[i]?) e1; simpa [h1, h2] using this
    · have := congrArg (fun l => l[i]?) e2; simpa [h1, h2] using this

/-- Choosing the triples is choosing the midpoint. -/
theorem mid_iff (x y : List (X Q Γ)) (hxy : x.length = y.length) (R : List (X Q Γ) → Prop) :
    (∃ ts' : List (X Q Γ × X Q Γ × X Q Γ), ts'.map Prod.fst = x ∧ ts'.map (fun t => t.2.2) = y ∧
      R (ts'.map fun t => t.2.1)) ↔ ∃ m : List (X Q Γ), m.length = x.length ∧ R m := by
  constructor
  · rintro ⟨ts', rfl, rfl, hR⟩
    exact ⟨_, by simp, hR⟩
  · rintro ⟨m, hm, hR⟩
    refine ⟨x.zip (m.zip y), ?_, ?_, ?_⟩
    · exact List.map_fst_zip (by simp; omega)
    · rw [show (fun t : X Q Γ × X Q Γ × X Q Γ => t.2.2) = Prod.snd ∘ Prod.snd from rfl,
        ← List.map_map, List.map_snd_zip (by simp; omega), List.map_snd_zip (by omega)]
    · rw [show (fun t : X Q Γ × X Q Γ × X Q Γ => t.2.1) = Prod.fst ∘ Prod.snd from rfl,
        ← List.map_map, List.map_snd_zip (by simp; omega), List.map_fst_zip (by omega)]
      exact hR

theorem upd_half (h h' : Bool) (a : AS Q) (ha : a = .rd false ∨ a = .rd true) :
    WSys.upd ({Fct.st (.rd h)} : Set (Fct (AS Q) (Sym Q Γ))) {Fct.st a}
      {Fct.st (.rd false), Fct.st (.rd true)} = {Fct.st a} := by
  ext f
  simp only [WSys.upd, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro (⟨rfl, h2⟩ | h1)
    · cases h <;> simp at h2
    · exact h1
  · intro h1; exact Or.inr h1

theorem upd_halfChk (h h' : Bool) :
    WSys.upd ({Fct.st (.rd h)} : Set (Fct (AS Q) (Sym Q Γ))) {Fct.st (.ck h' .start)}
      {Fct.st (.rd false), Fct.st (.rd true)} = {Fct.st (.ck h' .start)} := by
  ext f
  simp only [WSys.upd, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro (⟨rfl, h2⟩ | h1)
    · cases h <;> simp at h2
    · exact h1
  · intro h1; exact Or.inr h1

theorem G_halfChk (h : Bool) (ts' : List (X Q Γ × X Q Γ × X Q Γ)) (hl : ts'.length = S) (hS : 0 < S) :
    G N c₀ L S ([some .halfChk] ++ (List.replicate S none ++ [some .acc])) (ts'.map some)
      {Fct.st (.rd h)} ↔ ∀ h', Acc N .start (ts'.map (proj h')) := by
  rw [List.cons_append, List.nil_append, G, qi_plain]
  simp only [pp, Set.empty_subset, true_and, pe, Set.mem_setOf_eq, forall_exists_index]
  constructor
  · intro hall h'
    have := hall _ h' rfl
    rw [upd_halfChk, show (List.replicate S none : List (Option Pl)) = List.replicate ts'.length none
      by rw [hl], ← List.append_nil (ts'.map some)] at this
    exact ((G_check N c₀ L S h' ts' [] .start).1 this).1
  · rintro hall e h' rfl
    rw [upd_halfChk, show (List.replicate S none : List (Option Pl)) = List.replicate ts'.length none
      by rw [hl], ← List.append_nil (ts'.map some)]
    exact (G_check N c₀ L S h' ts' [] .start).2
      ⟨hall h', by intro hn; rw [hn] at hl; simp at hl; omega⟩

theorem G_half (h : Bool) (k : ℕ) (ts' : List (Sym Q Γ)) :
    G N c₀ L S ([some .half] ++ rnd S k) ts' {Fct.st (.rd h)} ↔
      ∀ h', G N c₀ L S (rnd S k) ts' {Fct.st (.rd h')} := by
  rw [List.cons_append, List.nil_append, G, qi_plain]
  simp only [pp, Set.empty_subset, true_and, pe, Set.mem_setOf_eq, forall_exists_index]
  constructor
  · intro hall h'
    have := hall _ h' rfl
    rwa [upd_half h h' _ (by cases h' <;> simp)] at this
  · rintro hall e h' rfl
    rw [upd_half h h' _ (by cases h' <;> simp)]
    exact hall h'

theorem proj_false_map (ts' : List (X Q Γ × X Q Γ × X Q Γ)) :
    ts'.map (proj false) = (ts'.map Prod.fst).zip (ts'.map fun t => t.2.1) := by
  rw [List.zip_map']; rfl

theorem proj_true_map (ts' : List (X Q Γ × X Q Γ × X Q Γ)) :
    ts'.map (proj true) = (ts'.map fun t => t.2.1).zip (ts'.map fun t => t.2.2) := by
  rw [List.zip_map']; rfl

/-- The triples of a midpoint. -/
def tri (x m y : List (X Q Γ)) : List (X Q Γ × X Q Γ × X Q Γ) := x.zip (m.zip y)

theorem tri_maps {x m y : List (X Q Γ)} (h1 : m.length = x.length) (h2 : y.length = x.length) :
    (tri x m y).map Prod.fst = x ∧ (tri x m y).map (fun t => t.2.1) = m ∧
      (tri x m y).map (fun t => t.2.2) = y ∧ (tri x m y).length = x.length := by
  refine ⟨List.map_fst_zip (by simp; omega), ?_, ?_, by simp [tri]; omega⟩
  · rw [show (fun t : X Q Γ × X Q Γ × X Q Γ => t.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← List.map_map, tri, List.map_snd_zip (by simp; omega), List.map_fst_zip (by omega)]
  · rw [show (fun t : X Q Γ × X Q Γ × X Q Γ => t.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← List.map_map, tri, List.map_snd_zip (by simp; omega), List.map_snd_zip (by omega)]

/-- **The rounds are the list game.** -/
theorem G_rnd (hS : 0 < S) : ∀ (k : ℕ) (h : Bool) (ts : List (X Q Γ × X Q Γ × X Q Γ)), ts.length = S →
    (G N c₀ L S (rnd S k) (ts.map some) {Fct.st (.rd h)} ↔
      LW N S (k + 1) (ts.map fun t => (proj h t).1) (ts.map fun t => (proj h t).2)) := by
  intro k
  induction k with
  | zero =>
    intro h ts hts
    have e : rnd S 0 = List.replicate (ts.map some).length none ++
        ([some .halfChk] ++ (List.replicate S none ++ [some .acc])) := by
      simp [rnd, sweep, hts, List.append_assoc]
    have hs := qi_sweep (S := S) (pp := pp) (pe := pe L) (fun _ => True) (Δ N c₀ L)
      (fun _ => (AS.rd h : AS Q)) (WR h) (hΔ_rd N c₀ L h)
      ([some .halfChk] ++ (List.replicate S none ++ [some .acc])) (ts.map some) [] 0
    simp only [List.append_nil, List.nil_append, Nat.zero_add] at hs
    rw [e]
    refine hs.trans ?_
    rw [ws_iff h ts]
    simp only [LW]
    constructor
    · rintro ⟨ts', e1, e2, hq⟩
      have hl : ts'.length = S := by simpa [hts] using congrArg List.length e1
      have hq' := (G_halfChk N c₀ L S h ts' hl hS).1 hq
      refine ⟨ts'.map fun t => t.2.1, by simp [hl], ?_, ?_⟩
      · rw [← e1, ← proj_false_map]; exact hq' false
      · rw [← e2, ← proj_true_map]; exact hq' true
    · rintro ⟨m, hm, hL, hR⟩
      obtain ⟨f1, f2, f3, f4⟩ := tri_maps (x := ts.map fun t => (proj h t).1) (m := m)
        (y := ts.map fun t => (proj h t).2) (by simp [hm, hts]) (by simp)
      refine ⟨_, f1, f3, (G_halfChk N c₀ L S h _ (by simp at f4; omega) hS).2 fun h' => ?_⟩
      cases h'
      · rw [proj_false_map, f1, f2]; exact hL
      · rw [proj_true_map, f2, f3]; exact hR
  | succ k ih =>
    intro h ts hts
    have e : rnd S (k + 1) = List.replicate (ts.map some).length none ++ ([some .half] ++ rnd S k) := by
      simp [rnd, sweep, hts]
    have hs := qi_sweep (S := S) (pp := pp) (pe := pe L) (fun _ => True) (Δ N c₀ L)
      (fun _ => (AS.rd h : AS Q)) (WR h) (hΔ_rd N c₀ L h)
      ([some .half] ++ rnd S k) (ts.map some) [] 0
    simp only [List.append_nil, List.nil_append, Nat.zero_add] at hs
    rw [e]
    refine hs.trans ?_
    rw [ws_iff h ts, LW]
    constructor
    · rintro ⟨ts', e1, e2, hq⟩
      have hl : ts'.length = S := by simpa [hts] using congrArg List.length e1
      have hq' := (G_half N c₀ L S h k _).1 hq
      refine ⟨ts'.map fun t => t.2.1, by simp [hl], ?_, ?_⟩
      · have := (ih false ts' hl).1 (hq' false); rw [← e1]; simpa [proj] using this
      · have := (ih true ts' hl).1 (hq' true); rw [← e2]; simpa [proj] using this
    · rintro ⟨m, hm, hL, hR⟩
      obtain ⟨f1, f2, f3, f4⟩ := tri_maps (x := ts.map fun t => (proj h t).1) (m := m)
        (y := ts.map fun t => (proj h t).2) (by simp [hm, hts]) (by simp)
      have hl : (tri (ts.map fun t => (proj h t).1) m (ts.map fun t => (proj h t).2)).length = S := by
        simp at f4; omega
      refine ⟨_, f1, f3, (G_half N c₀ L S h k _).2 fun h' => ?_⟩
      cases h'
      · refine (ih false _ hl).2 ?_
        have g1 : (tri (ts.map fun t => (proj h t).1) m (ts.map fun t => (proj h t).2)).map
            (fun t => (proj false t).1) = ts.map fun t => (proj h t).1 := f1
        have g2 : (tri (ts.map fun t => (proj h t).1) m (ts.map fun t => (proj h t).2)).map
            (fun t => (proj false t).2) = m := f2
        rw [g1, g2]; exact hL
      · refine (ih true _ hl).2 ?_
        have g1 : (tri (ts.map fun t => (proj h t).1) m (ts.map fun t => (proj h t).2)).map
            (fun t => (proj true t).1) = m := f2
        have g2 : (tri (ts.map fun t => (proj h t).1) m (ts.map fun t => (proj h t).2)).map
            (fun t => (proj true t).2) = ts.map fun t => (proj h t).2 := f3
        rw [g1, g2]; exact hR

/-! ## The input sweep and the program -/

/-- The writes of the input sweep. -/
def WI (j : ℕ) (_ τ : Sym Q Γ) : Prop := ∃ e, AccOK N e ∧ τ = some (mk c₀ j, e, e)

variable {N c₀ L} in
theorem hΔ_inp (hL : ∀ j, L + 1 ≤ j → mk c₀ j = mk c₀ (L + 1)) : ∀ j (σ τ : Sym Q Γ) (a' : AS Q),
    True ∧ ((fun j => (AS.inp (min j (L + 1)) : AS Q)) j, σ, τ, a') ∈ Δ N c₀ L ↔
      WI N c₀ j σ τ ∧ a' = (fun j => (AS.inp (min j (L + 1)) : AS Q)) (j + 1) := by
  intro j σ τ a'
  have hm : mk c₀ (min j (L + 1)) = mk c₀ j := by
    rcases le_total j (L + 1) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, hL j h]
  simp only [true_and, mem_Δ_inp, WI, hm, show min (min j (L + 1) + 1) (L + 1) = min (j + 1) (L + 1) by omega]
  constructor
  · rintro ⟨-, h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨by omega, h1, h2⟩

/-- The triples of the input sweep. -/
def inpT (es : List (X Q Γ)) : List (X Q Γ × X Q Γ × X Q Γ) :=
  ((List.range S).zip es).map fun p => (mk c₀ p.1, p.2, p.2)

theorem ws_inp_iff (P : List (Sym Q Γ) → Prop) :
    (∃ ws : List (Sym Q Γ), ws.length = (List.replicate S (none : Sym Q Γ)).length ∧
      (∀ i (h1 : i < (List.replicate S (none : Sym Q Γ)).length) (h2 : i < ws.length),
        WI N c₀ i (List.replicate S none)[i] ws[i]) ∧ P ws) ↔
    ∃ es : List (X Q Γ), es.length = S ∧ (∀ e ∈ es, AccOK N e) ∧ P ((inpT c₀ S es).map some) := by
  constructor
  · rintro ⟨ws, hl, hW, hP⟩
    simp only [List.length_replicate] at hl hW
    have hw : ∀ i (hi : i < ws.length), ∃ e, AccOK N e ∧ ws[i] = some (mk c₀ i, e, e) :=
      fun i hi => hW i (by omega) hi
    refine ⟨ws.map fun σ => (σ.getD default).2.1, by simp [hl], fun e he => ?_, ?_⟩
    · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hσ
      obtain ⟨e, he, h⟩ := hw i hi
      simpa [h] using he
    · convert hP
      refine List.ext_getElem (by simp [inpT, hl]) fun i h1 h2 => ?_
      obtain ⟨e, -, h⟩ := hw i h2
      simp [inpT, h]
  · rintro ⟨es, hl, hacc, hP⟩
    refine ⟨_, by simp [inpT, hl], fun i h1 h2 => ?_, hP⟩
    simp only [List.length_replicate] at h1
    refine ⟨es[i]'(by omega), hacc _ (List.getElem_mem _), ?_⟩
    simp [inpT]

theorem inpT_maps (es : List (X Q Γ)) (hl : es.length = S) :
    (inpT c₀ S es).map (fun t => (proj false t).1) = enc S c₀ ∧
      (inpT c₀ S es).map (fun t => (proj false t).2) = es ∧ (inpT c₀ S es).length = S := by
  refine ⟨?_, ?_, by simp [inpT, hl]⟩
  · refine List.ext_getElem (by simp [inpT, enc, hl]) fun i h1 h2 => ?_
    simp [inpT, enc, proj]
  · refine List.ext_getElem (by simp [inpT, hl]) fun i h1 h2 => ?_
    simp [inpT, proj]

theorem upd_toRd {i : ℕ} (hi : i ≤ L + 1) :
    WSys.upd ({Fct.st (.inp i)} : Set (Fct (AS Q) (Sym Q Γ))) {Fct.st (.rd false)}
      {f | ∃ i ≤ L + 1, f = Fct.st (.inp i)} = {Fct.st (.rd false)} := by
  ext f
  simp only [WSys.upd, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (⟨rfl, h2⟩ | h1)
    · exact absurd ⟨i, hi, rfl⟩ h2
    · exact h1
  · intro h1; exact Or.inr h1

theorem accOK_enc (c : Config Q Γ) (hc : c.head < S) : (∀ e ∈ enc S c, AccOK N e) ↔ c.state ∈ N.accept := by
  constructor
  · intro h
    exact h (mk c c.head) (List.mem_map.2 ⟨c.head, List.mem_range.2 hc, rfl⟩) c.state (by simp [mk])
  · intro h e he q hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    obtain ⟨-, rfl⟩ := mk_snd_some.1 hq
    exact h

/-- **The queue program plays the Savitch game.** -/
theorem qi_prog_iff (hS : 0 < S) (K : ℕ) (hc0 : c₀.head = 0)
    (hL : ∀ j, L + 1 ≤ j → mk c₀ j = mk c₀ (L + 1)) :
    G N c₀ L S (prog S K) (List.replicate S none) {Fct.st (.inp 0)} ↔
      ∃ c, c.state ∈ N.accept ∧ ATM.SavWin N S (K + 1) c₀ c := by
  have hs := qi_sweep (S := S) (pp := pp) (pe := pe L) (fun _ => True) (Δ N c₀ L)
    (fun j => (AS.inp (min j (L + 1)) : AS Q)) (WI N c₀) (hΔ_inp hL)
    ([some .toRd] ++ rnd S K) (List.replicate S none) [] 0
  simp only [List.append_nil, List.nil_append, Nat.zero_add, List.length_replicate] at hs
  have e : prog S K = List.replicate S none ++ ([some .toRd] ++ rnd S K) := by
    simp [prog, sweep]
  rw [e]
  refine (hs.trans ?_)
  have := ws_inp_iff N c₀ S (fun ws => (autSpec S pp (pe L)).QI (fun _ => True) (· ∈ Δ N c₀ L)
    ([some .toRd] ++ rnd S K) ws {Fct.st (.inp (min S (L + 1)))})
  simp only [List.length_replicate] at this
  rw [this]
  have hfit : Fits S c₀.tape c₀ := ⟨by omega, fun _ _ => rfl⟩
  constructor
  · rintro ⟨es, hl, hacc, hq⟩
    rw [List.cons_append, List.nil_append, qi_plain] at hq
    simp only [pp, Set.empty_subset, true_and, pe, Set.mem_singleton_iff, forall_eq] at hq
    rw [upd_toRd L (by omega)] at hq
    obtain ⟨f1, f2, f3⟩ := inpT_maps c₀ S es hl
    have := (G_rnd N c₀ L S hS K false _ f3).1 hq
    rw [f1, f2, lw_iff N S hS c₀.tape _ _ _ (enc_length S c₀) hl] at this
    obtain ⟨c, c', hc, hc', e1, rfl, hw⟩ := this
    obtain rfl := enc_inj S c₀ c hfit hc e1
    exact ⟨c', (accOK_enc N S c' hc'.1).1 hacc, hw⟩
  · rintro ⟨c, hc, hw⟩
    have hcf := savWin_fits N S hfit hw
    refine ⟨enc S c, enc_length S c, (accOK_enc N S c hcf.1).2 hc, ?_⟩
    rw [List.cons_append, List.nil_append, qi_plain]
    simp only [pp, Set.empty_subset, true_and, pe, Set.mem_singleton_iff, forall_eq]
    rw [upd_toRd L (by omega)]
    obtain ⟨f1, f2, f3⟩ := inpT_maps c₀ S (enc S c) (enc_length S c)
    refine (G_rnd N c₀ L S hS K false _ f3).2 ?_
    rw [f1, f2, lw_iff N S hS c₀.tape _ _ _ (enc_length S c₀) (enc_length S c)]
    exact ⟨c₀, c, hfit, hcf, rfl, rfl, hw⟩

end Sav

end AcycHard

end FOND
