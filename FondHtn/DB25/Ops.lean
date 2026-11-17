import FondHtn.DB25.Phase
import FondHtn.Lang.Desc
/-!
# Register operations as FOND gadgets

Boolean registers `v` are represented by two facts `lit v true`, `lit v false` (exactly one of
them holds), the machine state by a fact `qF q`.  A state encoding the assignment `ρ` of the
registers `V` and the state `q` is `FOND.DB.enc V ρ q`.

Each **operation** (`FOND.DB.Op`) is implemented by a list of phases of FOND actions
(`FOND.DB.opPhases`); phases are executed one after the other, the actions of a phase in an order
chosen by the policy.  The abstract meaning of an operation is `FOND.DB.opSem`:

* `choice r` — the policy chooses the value of `r` (two unordered tasks "set `r` to 0/1"; the one
  executed last wins);
* `nature r` — nature chooses the value of `r` (one task with two outcomes);
* `copy s d` — `d := s` (two tasks whose order is forced by the value of `s`; the last one writes
  `d`);
* `check Φ` — the CNF `Φ` must hold (per clause: copy the clause's registers into helper facts;
  check tasks `hlit ℓ → sat`, `sat → win`, and `win →` all helper facts; then reset);
* `upd q pre q' sets` — a deterministic update: requires state `q` and the literals `pre`, moves to
  `q'` and sets the literals `sets`.

`FOND.DB.phasesWin_opPhases` — executing the phases of `op` from `enc V ρ q` with terminal
condition `K` is `opSem op (K ∘ enc V)`.
-/

namespace FOND

namespace DB

open Problem

/-! ## Facts -/

/-- Register `v` has value `b`. -/
def lit (v : ℕ) (b : Bool) : ℕ := Nat.pair 0 (Nat.pair v b.toNat)
/-- Helper copy of register `v` has value `b`. -/
def hlit (v : ℕ) (b : Bool) : ℕ := Nat.pair 1 (Nat.pair v b.toNat)
/-- The current clause is satisfied. -/
def satF : ℕ := Nat.pair 2 0
/-- The current clause is checked. -/
def winF : ℕ := Nat.pair 3 0
/-- Machine state `q`. -/
def qF (q : ℕ) : ℕ := Nat.pair 4 q

theorem toNat_inj {b c : Bool} : b.toNat = c.toNat ↔ b = c := by cases b <;> cases c <;> simp

@[simp] theorem lit_inj {v w : ℕ} {b c : Bool} : lit v b = lit w c ↔ v = w ∧ b = c := by
  simp [lit, Nat.pair_eq_pair, toNat_inj]
@[simp] theorem hlit_inj {v w : ℕ} {b c : Bool} : hlit v b = hlit w c ↔ v = w ∧ b = c := by
  simp [hlit, Nat.pair_eq_pair, toNat_inj]
@[simp] theorem qF_inj {q q' : ℕ} : qF q = qF q' ↔ q = q' := by simp [qF, Nat.pair_eq_pair]
@[simp] theorem lit_ne_hlit (v w : ℕ) (b c : Bool) : lit v b ≠ hlit w c := by
  simp [lit, hlit, Nat.pair_eq_pair]
@[simp] theorem hlit_ne_lit (v w : ℕ) (b c : Bool) : hlit v b ≠ lit w c := fun h =>
  lit_ne_hlit w v c b h.symm
@[simp] theorem lit_ne_satF (v : ℕ) (b : Bool) : lit v b ≠ satF := by simp [lit, satF, Nat.pair_eq_pair]
@[simp] theorem lit_ne_winF (v : ℕ) (b : Bool) : lit v b ≠ winF := by simp [lit, winF, Nat.pair_eq_pair]
@[simp] theorem lit_ne_qF (v : ℕ) (b : Bool) (q : ℕ) : lit v b ≠ qF q := by
  simp [lit, qF, Nat.pair_eq_pair]
@[simp] theorem hlit_ne_satF (v : ℕ) (b : Bool) : hlit v b ≠ satF := by
  simp [hlit, satF, Nat.pair_eq_pair]
@[simp] theorem hlit_ne_winF (v : ℕ) (b : Bool) : hlit v b ≠ winF := by
  simp [hlit, winF, Nat.pair_eq_pair]
@[simp] theorem hlit_ne_qF (v : ℕ) (b : Bool) (q : ℕ) : hlit v b ≠ qF q := by
  simp [hlit, qF, Nat.pair_eq_pair]
@[simp] theorem satF_ne_winF : satF ≠ winF := by simp [satF, winF, Nat.pair_eq_pair]
@[simp] theorem qF_ne_satF (q : ℕ) : qF q ≠ satF := by simp [qF, satF, Nat.pair_eq_pair]
@[simp] theorem qF_ne_winF (q : ℕ) : qF q ≠ winF := by simp [qF, winF, Nat.pair_eq_pair]
@[simp] theorem winF_ne_satF : winF ≠ satF := fun h => satF_ne_winF h.symm
@[simp] theorem satF_ne_qF (q : ℕ) : satF ≠ qF q := fun h => qF_ne_satF q h.symm
@[simp] theorem winF_ne_qF (q : ℕ) : winF ≠ qF q := fun h => qF_ne_winF q h.symm
@[simp] theorem satF_ne_lit (v : ℕ) (b : Bool) : satF ≠ lit v b := fun h => lit_ne_satF v b h.symm
@[simp] theorem winF_ne_lit (v : ℕ) (b : Bool) : winF ≠ lit v b := fun h => lit_ne_winF v b h.symm
@[simp] theorem qF_ne_lit (v : ℕ) (b : Bool) (q : ℕ) : qF q ≠ lit v b := fun h =>
  lit_ne_qF v b q h.symm
@[simp] theorem satF_ne_hlit (v : ℕ) (b : Bool) : satF ≠ hlit v b := fun h =>
  hlit_ne_satF v b h.symm
@[simp] theorem winF_ne_hlit (v : ℕ) (b : Bool) : winF ≠ hlit v b := fun h =>
  hlit_ne_winF v b h.symm
@[simp] theorem qF_ne_hlit (v : ℕ) (b : Bool) (q : ℕ) : qF q ≠ hlit v b := fun h =>
  hlit_ne_qF v b q h.symm

/-! ## Encoded states -/

/-- The state encoding the registers `V` under `ρ` and the machine state `q`. -/
def enc (V : List ℕ) (ρ : ℕ → Bool) (q : ℕ) : Set ℕ :=
  {f | (∃ v ∈ V, f = lit v (ρ v)) ∨ f = qF q}

/-- With helper copies of the registers `W`. -/
def encH (V : List ℕ) (ρ : ℕ → Bool) (q : ℕ) (W : List ℕ) : Set ℕ :=
  enc V ρ q ∪ {f | ∃ v ∈ W, f = hlit v (ρ v)}

theorem lit_mem_enc {V : List ℕ} {ρ : ℕ → Bool} {q v : ℕ} (hv : v ∈ V) (b : Bool) :
    lit v b ∈ enc V ρ q ↔ ρ v = b := by
  simp only [enc, Set.mem_setOf_eq, lit_inj, lit_ne_qF, or_false]
  constructor
  · rintro ⟨w, -, rfl, h⟩; exact h.symm
  · rintro rfl; exact ⟨v, hv, rfl, rfl⟩

theorem qF_mem_enc {V : List ℕ} {ρ : ℕ → Bool} {q q' : ℕ} : qF q' ∈ enc V ρ q ↔ q' = q := by
  simp [enc]

/-! ## Actions -/

/-- The single effect of a deterministic action description. -/
theorem outcomes_single {a : FActDesc} {e : List ℕ × List ℕ} (h : a.2.2.2 = [e]) (s : Set ℕ) :
    a.toAction.outcomes s = {(s \ {f | f ∈ e.2}) ∪ {f | f ∈ e.1}} := by
  ext s'
  simp only [Action.outcomes, FActDesc.toAction, FActDesc.effs, h, List.mem_singleton,
    Set.mem_setOf_eq, exists_eq_left, Action.applyEff, Set.mem_singleton_iff]

theorem applicable_iff {a : FActDesc} (h : a.2.2.1 = []) (s : Set ℕ) :
    a.toAction.Applicable s ↔ ∀ f ∈ a.2.1, f ∈ s := by
  simp only [Action.Applicable, FActDesc.toAction, h, List.not_mem_nil, Set.setOf_false,
    Set.empty_disjoint, and_true]
  exact ⟨fun h f hf => h hf, fun h f hf => h f hf⟩

/-- Set register `r` to `b`. -/
def setA (r : ℕ) (b : Bool) : FActDesc := (0, [], [], [([lit r b], [lit r (!b)])])

/-- Nature sets register `r`. -/
def natA (r : ℕ) : FActDesc :=
  (0, [], [], [([lit r true], [lit r false]), ([lit r false], [lit r true])])

/-- Half of a copy gadget `s → dl`: requires `s = b`, flips `s` and writes `dl (!b)`. -/
def cpA (src : ℕ) (dl : Bool → ℕ) (b : Bool) : FActDesc :=
  (0, [lit src b], [], [([lit src (!b), dl (!b)], [lit src b, dl b])])

/-- Check of a literal of the current clause. -/
def chkA (l : ℕ × Bool) : FActDesc := (0, [hlit l.1 l.2], [], [([satF], [])])

/-- The clause is satisfied. -/
def finA : FActDesc := (0, [satF], [], [([winF], [])])

/-- Release of the remaining checks. -/
def clrA (W : List ℕ) : FActDesc :=
  (0, [winF], [], [(W.flatMap fun v => [hlit v true, hlit v false], [])])

/-- Reset of the clause gadget. -/
def rstA (W : List ℕ) : FActDesc :=
  (0, [], [], [([], [satF, winF] ++ W.flatMap fun v => [hlit v true, hlit v false])])

/-- A deterministic update. -/
def updA (q : ℕ) (pre : List (ℕ × Bool)) (q' : ℕ) (sets : List (ℕ × Bool)) : FActDesc :=
  (0, qF q :: pre.map (fun l => lit l.1 l.2), [],
    [(qF q' :: sets.map (fun l => lit l.1 l.2), qF q :: sets.map (fun l => lit l.1 (!l.2)))])

/-! ## Operations -/

/-- A clause: a list of literals `(v, b)` (`v = b`). -/
abbrev Clause : Type := List (ℕ × Bool)

/-- The registers of a clause. -/
def cvars (C : Clause) : List ℕ := (C.map Prod.fst).dedup

/-- `ρ` satisfies the clause. -/
def SatC (ρ : ℕ → Bool) (C : Clause) : Prop := ∃ l ∈ C, ρ l.1 = l.2

/-- Register operations. -/
inductive Op
  | choice (r : ℕ)
  | nature (r : ℕ)
  | copy (src dst : ℕ)
  | check (Φ : List Clause)
  | upd (q : ℕ) (pre : List (ℕ × Bool)) (q' : ℕ) (sets : List (ℕ × Bool))

/-- `ρ` with the literals `sets` made true. -/
def setAll (ρ : ℕ → Bool) (sets : List (ℕ × Bool)) : ℕ → Bool := fun v =>
  if (v, true) ∈ sets then true else if (v, false) ∈ sets then false else ρ v

/-- **The meaning of an operation.** -/
def opSem : Op → ((ℕ → Bool) → ℕ → Prop) → (ℕ → Bool) → ℕ → Prop
  | .choice r, K, ρ, q => ∃ b, K (Function.update ρ r b) q
  | .nature r, K, ρ, q => ∀ b, K (Function.update ρ r b) q
  | .copy s d, K, ρ, q => K (Function.update ρ d (ρ s)) q
  | .check Φ, K, ρ, q => (∀ C ∈ Φ, SatC ρ C) ∧ K ρ q
  | .upd q₀ pre q' sets, K, ρ, q => q = q₀ ∧ (∀ l ∈ pre, ρ l.1 = l.2) ∧ K (setAll ρ sets) q'

/-- The copy phase of register `v` into its helper. -/
def hcopy (v : ℕ) : List FActDesc := [cpA v (hlit v) true, cpA v (hlit v) false]

/-- The phases of a clause check. -/
def clausePhases (C : Clause) : List (List FActDesc) :=
  (cvars C).map hcopy ++ [C.map chkA ++ [finA, clrA (cvars C)], [rstA (cvars C)]]

/-- **The phases of an operation.** -/
def opPhases : Op → List (List FActDesc)
  | .choice r => [[setA r false, setA r true]]
  | .nature r => [[natA r]]
  | .copy s d => [[cpA s (lit d) true, cpA s (lit d) false]]
  | .check Φ => Φ.flatMap clausePhases
  | .upd q pre q' sets => [[updA q pre q' sets]]

/-- Executing phases one after the other. -/
def phasesWin (phs : List (List FActDesc)) (K : Set ℕ → Prop) : Set ℕ → Prop :=
  phs.foldr (fun ph K' => setWin K' (ph.map FActDesc.toAction)) K

theorem phasesWin_append (p q : List (List FActDesc)) (K : Set ℕ → Prop) :
    phasesWin (p ++ q) K = phasesWin p (phasesWin q K) := by
  simp [phasesWin, List.foldr_append]

theorem phasesWin_cons (ph : List FActDesc) (q : List (List FActDesc)) (K : Set ℕ → Prop) :
    phasesWin (ph :: q) K = setWin (phasesWin q K) (ph.map FActDesc.toAction) := rfl

theorem phasesWin_nil (K : Set ℕ → Prop) : phasesWin [] K = K := rfl

end DB

end FOND
