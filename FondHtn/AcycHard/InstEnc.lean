import FondHtn.AcycHard.SavProg
import FondHtn.AcycHard.Transfer
/-!
# The Savitch queue game as a FOND problem: codes and actions

Codes (natural numbers, `Nat.pair` with tags) of the facts `Tok Gate (Fct AS Sym)` and the names
of the control instructions and pool actions of the Savitch queue specification
`FOND.AcycHard.Sav.spec`; the described actions (`actC`, `actP`) are the images of the actions of
the window system (`toAction_actC`, `toAction_actP`).
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

namespace Sav

open HTN TM

variable {k : ℕ}

/-- The cells, states and symbols of the construction for `k` states and the tape symbols
`Option Bool`. -/
abbrev XK (k : ℕ) := X (Fin k) (Option Bool)
abbrev SymK (k : ℕ) := Sym (Fin k) (Option Bool)
abbrev ASK (k : ℕ) := AS (Fin k)
abbrev DK (k : ℕ) := Fct (ASK k) (SymK k)
abbrev OK (k : ℕ) := ASK k × SymK k × SymK k × ASK k

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
instance instDecSymK (k : ℕ) : DecidableEq (SymK k) := inferInstance

instance instDecOK (k : ℕ) : DecidableEq (OK k) := inferInstance

/-! ## Codes -/

def codeTS : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

def codeOQ : Option (Fin k) → ℕ
  | none => 0
  | some q => q.val + 1

def codeX (x : XK k) : ℕ := Nat.pair (codeTS x.1) (codeOQ x.2)

def codeSym : SymK k → ℕ
  | none => 0
  | some t => Nat.pair (codeX t.1) (Nat.pair (codeX t.2.1) (codeX t.2.2)) + 1

def codeCS : CS (Fin k) → ℕ
  | .start => 0
  | .eqp => 1
  | .eqd => 2
  | .pre => 3
  | .dn => 4
  | .pl q => 2 * q.val + 5
  | .pr q => 2 * q.val + 6

def codeAS : ASK k → ℕ
  | .inp i => Nat.pair 0 i
  | .rd h => Nat.pair 1 h.toNat
  | .ck h c => Nat.pair 2 (Nat.pair h.toNat (codeCS c))
  | .ok => Nat.pair 3 0

def codeFct : DK k → ℕ
  | .st a => Nat.pair 0 (codeAS a)
  | .rd σ => Nat.pair 1 (codeSym σ)
  | .wr σ => Nat.pair 2 (codeSym σ)

def codeGate : Gate → ℕ
  | .T => 0
  | .R => 1
  | .F => 2
  | .I => 3
  | .U => 4

def codeTok : Tok Gate (DK k) → ℕ
  | .op g => Nat.pair 0 (codeGate g)
  | .dn g => Nat.pair 1 (codeGate g)
  | .dat d => Nat.pair 2 (codeFct d)

theorem codeTS_inj : Function.Injective codeTS := by
  intro a b h; rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [codeTS]

theorem codeOQ_inj : Function.Injective (codeOQ (k := k)) := by
  intro a b h; rcases a with _ | a <;> rcases b with _ | b <;> simp_all [codeOQ]
  exact Fin.ext h

theorem codeX_inj : Function.Injective (codeX (k := k)) := by
  intro a b h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.1 h
  exact Prod.ext (codeTS_inj h1) (codeOQ_inj h2)

theorem codeSym_inj : Function.Injective (codeSym (k := k)) := by
  intro a b h
  rcases a with _ | ⟨a1, a2, a3⟩ <;> rcases b with _ | ⟨b1, b2, b3⟩ <;> simp only [codeSym] at h
  · rfl
  · omega
  · omega
  · have h' := Nat.pair_eq_pair.1 (Nat.succ_injective h)
    have h'' := Nat.pair_eq_pair.1 h'.2
    rw [codeX_inj h'.1, codeX_inj h''.1, codeX_inj h''.2]

theorem codeCS_inj : Function.Injective (codeCS (k := k)) := by
  intro a b h
  rcases a with _ | _ | _ | _ | a | a | _ <;> rcases b with _ | _ | _ | _ | b | b | _ <;>
    simp only [codeCS] at h <;> first | rfl | omega | (congr 1; exact Fin.ext (by omega))

theorem codeAS_inj : Function.Injective (codeAS (k := k)) := by
  intro a b h
  rcases a with i | h1 | ⟨h1, c1⟩ | _ <;> rcases b with j | h2 | ⟨h2, c2⟩ | _ <;>
    simp only [codeAS, Nat.pair_eq_pair] at h <;> (try omega)
  · rw [h.2]
  · have := h.2; cases h1 <;> cases h2 <;> simp_all
  · obtain ⟨-, h4, h5⟩ := h
    rw [codeCS_inj h5]
    cases h1 <;> cases h2 <;> simp_all
  · rfl

theorem codeFct_inj : Function.Injective (codeFct (k := k)) := by
  intro a b h
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    simp only [codeFct, Nat.pair_eq_pair] at h <;> (try omega)
  · rw [codeAS_inj h.2]
  · rw [codeSym_inj h.2]
  · rw [codeSym_inj h.2]

theorem codeGate_inj : Function.Injective codeGate := by
  intro a b h; cases a <;> cases b <;> simp_all [codeGate]

theorem codeTok_inj : Function.Injective (codeTok (k := k)) := by
  intro a b h
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    simp only [codeTok, Nat.pair_eq_pair] at h <;> (try omega)
  · rw [codeGate_inj h.2]
  · rw [codeGate_inj h.2]
  · rw [codeFct_inj h.2]

/-! ## Names of the actions -/

def codePl : Pl → ℕ
  | .toRd => 0
  | .half => 1
  | .halfChk => 2
  | .acc => 3

def codeO (o : OK k) : ℕ :=
  Nat.pair (codeAS o.1) (Nat.pair (codeSym o.2.1) (Nat.pair (codeSym o.2.2.1) (codeAS o.2.2.2)))

/-- Names of the control instructions. -/
def nC : CI Gate Pl → ℕ
  | .opn g => Nat.pair 0 (codeGate g)
  | .cls g => Nat.pair 1 (codeGate g)
  | .plain p => Nat.pair 2 (codePl p)
  | .refill => Nat.pair 3 0

/-- Names of the pool actions. -/
def nP : PA (SymK k) (OK k) → ℕ
  | .init τ => Nat.pair 4 (codeSym τ)
  | .tick => Nat.pair 5 0
  | .res => Nat.pair 6 0
  | .fin τ => Nat.pair 7 (codeSym τ)
  | .opt o => Nat.pair 8 (codeO o)

theorem codeO_inj : Function.Injective (codeO (k := k)) := by
  intro a b h
  obtain ⟨a1, a2, a3, a4⟩ := a
  obtain ⟨b1, b2, b3, b4⟩ := b
  simp only [codeO, Nat.pair_eq_pair] at h
  rw [codeAS_inj h.1, codeSym_inj h.2.1, codeSym_inj h.2.2.1, codeAS_inj h.2.2.2]

theorem nP_inj : Function.Injective (nP (k := k)) := by
  intro a b h
  rcases a with a | _ | _ | a | a <;> rcases b with b | _ | _ | b | b <;>
    simp only [nP, Nat.pair_eq_pair] at h <;> (try omega)
  · rw [codeSym_inj h.2]
  · rfl
  · rfl
  · rw [codeSym_inj h.2]
  · rw [codeO_inj h.2]

/-! ## The actions as lists of facts -/

/-- The data facts of a plain action's precondition. -/
def ppL : Pl → List (DK k)
  | .acc => [Fct.st .ok]
  | _ => []

/-- The effects of a plain action. -/
def peL (L : ℕ) : Pl → List (List (DK k) × List (DK k))
  | .toRd => [([Fct.st (.rd false)], (List.range (L + 2)).map fun i => Fct.st (.inp i))]
  | .half => [([Fct.st (.rd false)], [Fct.st (.rd false), Fct.st (.rd true)]),
      ([Fct.st (.rd true)], [Fct.st (.rd false), Fct.st (.rd true)])]
  | .halfChk => [([Fct.st (.ck false .start)], [Fct.st (.rd false), Fct.st (.rd true)]),
      ([Fct.st (.ck true .start)], [Fct.st (.rd false), Fct.st (.rd true)])]
  | .acc => [([], [])]

/-- A control instruction (other than `refill`) as lists of facts. -/
def ctlLists (L : ℕ) : CI Gate Pl → List (Tok Gate (DK k)) × List (List (Tok Gate (DK k)) × List (Tok Gate (DK k)))
  | .opn g => ([], [([.op g], [])])
  | .cls g => ([.dn g], [([], [.dn g])])
  | .plain p => ((ppL p).map Tok.dat, (peL L p).map fun e => (e.1.map Tok.dat, e.2.map Tok.dat))
  | .refill => ([], [])

/-- A pool action as lists of facts. -/
def poolLists : PA (SymK k) (OK k) → List (Tok Gate (DK k)) × List (List (Tok Gate (DK k)) × List (Tok Gate (DK k)))
  | .init τ => ([.op .I], [([.dn .I, .dat (.wr τ)], [.op .I])])
  | .tick => ([.op .T], [([.dn .T], [.op .T])])
  | .res => ([.op .R], [([.dn .R], [.op .R])])
  | .fin τ => ([.op .F], [([.dn .F, .dat (.rd τ)], [.op .F])])
  | .opt o => ([.op .U, .dat (.st o.1), .dat (.rd o.2.1), .dat (.wr o.2.2.1)],
      [([.dn .U, .dat (.st o.2.2.2)], [.op .U, .dat (.st o.1), .dat (.rd o.2.1), .dat (.wr o.2.2.1)])])

theorem image_list {α β : Type} (f : α → β) (l : List α) : f '' {x | x ∈ l} = {y | y ∈ l.map f} := by
  ext y; simp

theorem image_listEffs {α β : Type} (g : α → β) (L : List (List α × List α)) :
    (fun e : Set α × Set α => (g '' e.1, g '' e.2)) '' {e | ∃ x ∈ L, e = ({f | f ∈ x.1}, {f | f ∈ x.2})} =
      {e | ∃ x ∈ L.map (fun x => (x.1.map g, x.2.map g)), e = ({f | f ∈ x.1}, {f | f ∈ x.2})} := by
  ext e
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp only [image_list]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp only [image_list]⟩

theorem pp_eq (p : Pl) : pp (Q := Fin k) (Γ := Option Bool) p = {f | f ∈ ppL p} := by
  cases p <;> ext f <;> simp [pp, ppL]

theorem pe_eq (L : ℕ) (p : Pl) :
    pe (Q := Fin k) (Γ := Option Bool) L p = {e | ∃ x ∈ peL L p, e = ({f | f ∈ x.1}, {f | f ∈ x.2})} := by
  cases p
  · ext e
    simp only [pe, peL, Set.mem_singleton_iff, List.mem_singleton, Set.mem_setOf_eq, exists_eq_left]
    constructor
    · rintro rfl
      refine Prod.ext (by ext f; simp) (by ext f; simp; constructor <;> rintro ⟨i, hi, h⟩ <;>
        exact ⟨i, by omega, h.symm⟩)
    · rintro rfl
      refine Prod.ext (by ext f; simp) (by ext f; simp; constructor <;> rintro ⟨i, hi, h⟩ <;>
        exact ⟨i, by omega, h.symm⟩)
  · ext e
    simp only [pe, peL, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left]
    constructor
    · rintro ⟨h, rfl⟩; cases h
      · left; refine Prod.ext (by ext f; simp) (by ext f; simp)
      · right; refine Prod.ext (by ext f; simp) (by ext f; simp)
    · rintro (rfl | rfl)
      · exact ⟨false, Prod.ext (by ext f; simp) (by ext f; simp)⟩
      · exact ⟨true, Prod.ext (by ext f; simp) (by ext f; simp)⟩
  · ext e
    simp only [pe, peL, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left]
    constructor
    · rintro ⟨h, rfl⟩; cases h
      · left; refine Prod.ext (by ext f; simp) (by ext f; simp)
      · right; refine Prod.ext (by ext f; simp) (by ext f; simp)
    · rintro (rfl | rfl)
      · exact ⟨false, Prod.ext (by ext f; simp) (by ext f; simp)⟩
      · exact ⟨true, Prod.ext (by ext f; simp) (by ext f; simp)⟩
  · ext e
    simp only [pe, peL, Set.mem_singleton_iff, List.mem_singleton, Set.mem_setOf_eq, exists_eq_left]
    constructor
    · rintro rfl; exact Prod.ext (by ext f; simp) (by ext f; simp)
    · rintro rfl; exact Prod.ext (by ext f; simp) (by ext f; simp)

theorem ctlLists_eq (L S : ℕ) (x : CI Gate Pl) (hx : x ≠ .refill) :
    listAct (ctlLists (k := k) L x).1 [] (ctlLists L x).2 = (spec L S).sys.δC x := by
  cases x with
  | opn g =>
    refine Action.ext' ?_ ?_ ?_ <;> (try ext) <;> simp [listAct, ctlLists, WSys.δC, eq_comm]
  | cls g =>
    refine Action.ext' ?_ ?_ ?_ <;> (try ext) <;> simp [listAct, ctlLists, WSys.δC, eq_comm]
  | plain p =>
    refine Action.ext' ?_ ?_ ?_
    · simp only [listAct, ctlLists, WSys.δC, FSpec.sys, spec, autSpec, pp_eq, image_list]
    · simp [listAct, ctlLists, WSys.δC]
    · simp only [listAct, ctlLists, WSys.δC, FSpec.sys, spec, autSpec, pe_eq, image_listEffs]
  | refill => exact absurd rfl hx

theorem listAct_single {F : Type} (pre : List F) (e : List F × List F) :
    listAct pre [] [e] = ⟨{f | f ∈ pre}, ∅, {({f | f ∈ e.1}, {f | f ∈ e.2})}⟩ := by
  refine Action.ext' rfl (by ext; simp [listAct]) ?_
  ext x; simp [listAct]

theorem poolLists_eq (L S : ℕ) (a : PA (SymK k) (OK k)) :
    listAct (poolLists a).1 [] (poolLists a).2 = (spec L S).sys.δP a := by
  cases a with
  | init τ =>
    rw [poolLists, listAct_single]
    refine Action.ext' ?_ rfl ?_
    · ext f; simp [WSys.δP, FSpec.sys]
    · simp only [WSys.δP, FSpec.sys, Set.singleton_eq_singleton_iff, Prod.mk.injEq]
      refine ⟨?_, ?_⟩ <;> ext f <;> simp [spec, autSpec]
  | tick =>
    rw [poolLists, listAct_single]
    refine Action.ext' ?_ rfl ?_
    · ext f; simp [WSys.δP, FSpec.sys]
    · simp only [WSys.δP, FSpec.sys, Set.singleton_eq_singleton_iff, Prod.mk.injEq]
      refine ⟨?_, ?_⟩ <;> ext f <;> simp
  | res =>
    rw [poolLists, listAct_single]
    refine Action.ext' ?_ rfl ?_
    · ext f; simp [WSys.δP, FSpec.sys]
    · simp only [WSys.δP, FSpec.sys, Set.singleton_eq_singleton_iff, Prod.mk.injEq]
      refine ⟨?_, ?_⟩ <;> ext f <;> simp
  | fin τ =>
    rw [poolLists, listAct_single]
    refine Action.ext' ?_ rfl ?_
    · ext f; simp [WSys.δP, FSpec.sys]
    · simp only [WSys.δP, FSpec.sys, Set.singleton_eq_singleton_iff, Prod.mk.injEq]
      refine ⟨?_, ?_⟩ <;> ext f <;> simp [spec, autSpec]
  | opt o =>
    rw [poolLists, listAct_single]
    refine Action.ext' ?_ rfl ?_
    · ext f
      simp only [WSys.δP, FSpec.sys, spec, autSpec, Set.mem_setOf_eq, List.mem_cons,
        List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inl h
        · exact Or.inr ⟨_, Or.inl rfl, h.symm⟩
        · exact Or.inr ⟨_, Or.inr (Or.inl rfl), h.symm⟩
        · exact Or.inr ⟨_, Or.inr (Or.inr rfl), h.symm⟩
      · rintro (h | ⟨x, hx, rfl⟩)
        · exact Or.inl h
        · rcases hx with rfl | rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
    · simp only [WSys.δP, FSpec.sys, spec, autSpec, Set.singleton_eq_singleton_iff, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · ext f; simp [eq_comm]
      · ext f
        simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
          Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro (h | h | h | h)
          · exact Or.inl h
          · exact Or.inr ⟨_, Or.inl rfl, h.symm⟩
          · exact Or.inr ⟨_, Or.inr (Or.inl rfl), h.symm⟩
          · exact Or.inr ⟨_, Or.inr (Or.inr rfl), h.symm⟩
        · rintro (h | ⟨x, hx, rfl⟩)
          · exact Or.inl h
          · rcases hx with rfl | rfl | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr rfl))

end Sav

end AcycHard

end FOND
