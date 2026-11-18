import FondHtn.AcycHard.InstDesc
import FondHtn.ATM.Savitch
/-!
# The Savitch instance of a machine and an input

`FOND.AcycHard.Sav.instOf N P E₁ E₂ w`: the instance for the space bound `S = 2 ^ P`, the
supply `n = 2 ^ E₁`, the refills `R = 2 ^ E₂` and `E₂ + 1` bits; the symbols are all symbols,
the options are the input transitions of `w` (`optsI`) and the constant transitions (`optsC`).

**`FOND.AcycHard.Sav.instOf_iff`**: for large enough `E₁, E₂`, strong OD (and MP strong)
solvability of the description is the Savitch game of `N` on `w`.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

namespace Sav

open HTN TM

variable {k : ℕ}

/-! ## Enumerations -/

def allTS : List (Option Bool) := [none, some false, some true]

def allOQ (k : ℕ) : List (Option (Fin k)) := none :: (List.finRange k).map some

def allX (k : ℕ) : List (XK k) := allTS.flatMap fun a => (allOQ k).map fun b => (a, b)

/-- **All symbols.** -/
def allSyms (k : ℕ) : List (SymK k) :=
  none :: (allX k).flatMap fun x => (allX k).flatMap fun y => (allX k).map fun z => some (x, y, z)

theorem mem_allTS (a : Option Bool) : a ∈ allTS := by
  rcases a with _ | _ | _ <;> simp [allTS]

theorem mem_allOQ (b : Option (Fin k)) : b ∈ allOQ k := by
  rcases b with _ | q <;> simp [allOQ]

theorem mem_allX (x : XK k) : x ∈ allX k := by
  simp only [allX, List.mem_flatMap, List.mem_map]
  exact ⟨x.1, mem_allTS _, x.2, mem_allOQ _, rfl⟩

theorem mem_allSyms (τ : SymK k) : τ ∈ allSyms k := by
  rcases τ with _ | ⟨x, y, z⟩
  · simp [allSyms]
  · simp only [allSyms, List.mem_cons, reduceCtorEq, List.mem_flatMap, List.mem_map, false_or]
    exact ⟨x, mem_allX _, y, mem_allX _, z, mem_allX _, rfl⟩

def allCS (k : ℕ) : List (CS (Fin k)) :=
  [.start, .eqp, .eqd, .pre, .dn] ++ (List.finRange k).map .pl ++ (List.finRange k).map .pr

theorem mem_allCS (c : CS (Fin k)) : c ∈ allCS k := by
  cases c <;> simp [allCS]

/-- The automaton states of the read and check phases. -/
def rcStates (k : ℕ) : List (ASK k) :=
  [.rd false, .rd true, .ok] ++ [false, true].flatMap fun h => (allCS k).map (.ck h)

theorem rd_mem_rcStates (h : Bool) : (AS.rd h : ASK k) ∈ rcStates k := by
  cases h <;> simp [rcStates]

theorem ck_mem_rcStates (h : Bool) (c : CS (Fin k)) : (AS.ck h c : ASK k) ∈ rcStates k := by
  cases h <;> simp [rcStates, mem_allCS]

theorem ok_mem_rcStates : (AS.ok : ASK k) ∈ rcStates k := by simp [rcStates]

/-! ## The options -/

variable (N : NTM (Fin k) (Option Bool))

/-- The accepting cells of the input transitions. -/
noncomputable def accE : List (XK k) := by
  classical exact (allX k).filter fun e => decide (AccOK N e)

theorem mem_accE {e : XK k} : e ∈ accE N ↔ AccOK N e := by
  classical
  simp [accE, mem_allX]

/-- The read and check transitions. -/
def ΔRC : Set (OK k) := {o |
  (∃ h, o.1 = .rd h ∧ o.2.2.2 = .rd h ∧ ∃ t t', o.2.1 = some t ∧ o.2.2.1 = some t' ∧
    t'.1 = (proj h t).1 ∧ t'.2.2 = (proj h t).2) ∨
  (∃ h c, o.1 = .ck h c ∧ ∃ t, o.2.1 = some t ∧ ∃ c', chk N c (proj h t) c' ∧
    (o.2.2.2 = .ck h c' ∨ (final c' ∧ o.2.2.2 = .ok)))}

/-- **The constant options.** -/
noncomputable def optsC : List (OK k) := by
  classical exact ((rcStates k).flatMap fun a => (allSyms k).flatMap fun σ => (allSyms k).flatMap
    fun τ => (rcStates k).map fun a' => (a, σ, τ, a')).filter fun o => decide (o ∈ ΔRC N)

theorem mem_optsC {o : OK k} : o ∈ optsC N ↔ o ∈ ΔRC N := by
  classical
  simp only [optsC, List.mem_filter, decide_eq_true_eq, List.mem_flatMap, List.mem_map]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨o.1, ?_, o.2.1, mem_allSyms _, o.2.2.1, mem_allSyms _, o.2.2.2, ?_, rfl⟩, h⟩
    · rcases h with ⟨hh, h1, -⟩ | ⟨hh, c, h1, -⟩
      · rw [h1]; exact rd_mem_rcStates _
      · rw [h1]; exact ck_mem_rcStates _ _
    · rcases h with ⟨hh, -, h2, -⟩ | ⟨hh, c, -, -, -, c', -, h2 | ⟨-, h2⟩⟩
      · rw [h2]; exact rd_mem_rcStates _
      · rw [h2]; exact ck_mem_rcStates _ _
      · rw [h2]; exact ok_mem_rcStates

/-- **The input options.** -/
noncomputable def optsI (c₀ : Config (Fin k) (Option Bool)) (L : ℕ) : List (OK k) :=
  (List.range (L + 2)).flatMap fun i => (allSyms k).flatMap fun σ => (accE N).map fun e =>
    (.inp i, σ, some (mk c₀ i, e, e), .inp (min (i + 1) (L + 1)))

theorem mem_opts (c₀ : Config (Fin k) (Option Bool)) (L : ℕ) {o : OK k} :
    o ∈ optsI N c₀ L ++ optsC N ↔ o ∈ Δ N c₀ L := by
  rw [List.mem_append, mem_optsC]
  constructor
  · rintro (h | h)
    · simp only [optsI, List.mem_flatMap, List.mem_range, List.mem_map] at h
      obtain ⟨i, hi, σ, -, e, he, rfl⟩ := h
      exact Or.inl ⟨i, rfl, by omega, rfl, e, (mem_accE N).1 he, rfl⟩
    · exact Or.inr h
  · rintro (⟨i, h1, hi, h4, e, he, h3⟩ | h)
    · left
      obtain ⟨a, σ, τ, a'⟩ := o
      simp only at h1 h3 h4
      subst h1 h3 h4
      simp only [optsI, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨i, by omega, σ, mem_allSyms _, e, (mem_accE N).2 he, rfl⟩
    · exact Or.inr h

/-! ## The instance -/

/-- **The instance** of the machine `N` on the input `w`. -/
noncomputable def instOf (P E₁ E₂ : ℕ) (w : List Bool) : Inst k where
  S := 2 ^ P
  K := k + P + 2 * 2 ^ P - 1
  R := 2 ^ E₂
  n := 2 ^ E₁
  B := E₂ + 1
  L := w.length
  syms := allSyms k
  opts := optsI N (N.initConfig (w.map some)) w.length ++ optsC N

/-! ## Counting -/

theorem steps_append {P : Type} (a b : List (Option P)) :
    FSpec.steps (a ++ b) = FSpec.steps a + FSpec.steps b := by
  induction a with
  | nil => simp [FSpec.steps]
  | cons x a ih => rcases x with _ | p <;> simp [FSpec.steps, ih] <;> omega

theorem steps_sweep (S : ℕ) : FSpec.steps (sweep S) = S := by
  unfold sweep
  induction S with
  | zero => rfl
  | succ S ih => rw [List.replicate_succ, FSpec.steps, ih]

theorem steps_rnd (S : ℕ) : ∀ K, FSpec.steps (rnd S K) = (K + 2) * S := by
  intro K
  induction K with
  | zero => simp [rnd, steps_append, steps_sweep, FSpec.steps]; ring
  | succ K ih => rw [rnd, steps_append, steps_append, ih, steps_sweep]; simp [FSpec.steps]; ring

theorem steps_prog (S K : ℕ) : FSpec.steps (prog S K) = (K + 3) * S := by
  rw [prog, steps_append, steps_append, steps_rnd, steps_sweep]; simp [FSpec.steps]; ring

theorem tri_le (n : ℕ) : FSpec.tri n ≤ n * n := by
  induction n with
  | zero => simp [FSpec.tri]
  | succ n ih => simp only [FSpec.tri]; nlinarith

theorem size_add (M M' : Multiset (List (PA (SymK k) (OK k)))) :
    WSys.size (M + M') = WSys.size M + WSys.size M' := by
  simp [WSys.size]

theorem size_nsmul (n : ℕ) (c : List (PA (SymK k) (OK k))) : WSys.size (n • ({c} : Multiset _)) = n * c.length := by
  simp [WSys.size, Multiset.nsmul_singleton]

theorem size_sum_map {α : Type} (g : α → Multiset (List (PA (SymK k) (OK k)))) :
    ∀ l : List α, WSys.size (l.map g).sum = (l.map fun a => WSys.size (g a)).sum
  | [] => by simp [WSys.size]
  | a :: l => by simp only [List.map_cons, List.sum_cons, size_add, size_sum_map g l]

theorem sum_const_mul {α : Type} (l : List α) (c : ℕ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem length_cellR {Sym O : Type} (τ : Sym) (m : ℕ) : (FSpec.cellR (O := O) τ m).length = 2 * m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [FSpec.cellR, ih]; ring

/-- **The size of the pool.** -/
theorem size_pool (I : Inst k) :
    WSys.size (FSpec.liveR (Multiset.replicate I.S (none, I.S)) + I.supply) =
      I.S * (2 * I.S + 1) + I.n * (I.syms.length * (2 * I.S + 2) + I.opts.length) := by
  rw [size_add, Inst.supply, size_add, size_sum_map, size_sum_map]
  simp only [size_nsmul, FSpec.liveR, Multiset.map_replicate]
  simp only [WSys.size, Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul, length_cellR]
  have hl : ∀ τ, (I.X0.newCell τ).length = 2 * I.S + 2 := fun τ => by
    simp [FSpec.newCell, length_cellR, Inst.X0, spec, autSpec]
  simp only [hl, List.length_singleton, mul_one]
  rw [sum_const_mul, sum_const_mul]
  ring

/-! ## Good instances of a machine -/

theorem length_optsI (c₀ : Config (Fin k) (Option Bool)) (L : ℕ) :
    (optsI N c₀ L).length = (L + 2) * ((allSyms k).length * (accE N).length) := by
  simp [optsI, List.length_flatMap, sum_const_mul]

/-- The number of options of the instance. -/
theorem length_opts (P E₁ E₂ : ℕ) (w : List Bool) :
    (instOf N P E₁ E₂ w).opts.length =
      (w.length + 2) * ((allSyms k).length * (accE N).length) + (optsC N).length := by
  simp [instOf, length_optsI]

theorem mk_init_tail (w : List Bool) (j : ℕ) (hj : w.length + 1 ≤ j) :
    mk (N.initConfig (w.map some)) j = mk (N.initConfig (w.map some)) (w.length + 1) := by
  simp only [mk, NTM.initConfig]
  have h1 : (w.map some).getD j N.blank = N.blank := List.getD_eq_default _ _ (by simp; omega)
  have h2 : (w.map some).getD (w.length + 1) N.blank = N.blank :=
    List.getD_eq_default _ _ (by simp)
  rw [h1, h2, if_neg (by omega), if_neg (by omega)]

variable {N}

/-- **The instance is good** for large enough exponents. -/
theorem good_instOf {P E₁ E₂ : ℕ} (w : List Bool)
    (h1 : (k + P + 2 * 2 ^ P + 2) * 2 ^ P ≤ 2 ^ E₁) (h12 : E₁ ≤ E₂)
    (hSS : 2 ^ P * 2 ^ P < 2 ^ E₂) (hK : k + P + 2 * 2 ^ P < 2 ^ E₂)
    (h2 : 2 ^ P * (2 * 2 ^ P + 1) + 2 ^ E₁ * ((allSyms k).length * (2 * 2 ^ P + 2) +
      ((w.length + 2) * ((allSyms k).length * (accE N).length) + (optsC N).length)) ≤ 2 ^ E₂) :
    (instOf N P E₁ E₂ w).Good N (N.initConfig (w.map some)) := by
  have hS1 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
  have hE : 2 ^ E₂ < 2 ^ (E₂ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hSE : 2 ^ P < 2 ^ E₂ := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hSS
  have hK1 : k + P + 2 * 2 ^ P - 1 + 3 = k + P + 2 * 2 ^ P + 2 := by omega
  refine ⟨mem_allSyms, fun o => mem_opts N _ _, fun b => ?_, ?_, ?_, ?_, ?_⟩
  · cases b <;> simp only [Inst.cnt, instOf]
    · omega
    · omega
    · exact lt_of_le_of_lt (tri_le _) (by omega)
    · omega
    · omega
    · exact hE
    · omega
  · exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) h12) hE
  · simp only [instOf]; rw [steps_prog, hK1]; exact h1
  · simp only [instOf]; rw [steps_prog, hK1]; nlinarith
  · rw [size_pool, length_opts]; simpa [instOf] using h2

/-- **The description of a good instance plays the Savitch game** (strong OD). -/
theorem instOf_strongOD_iff {P E₁ E₂ : ℕ} {w : List Bool}
    (h : (instOf N P E₁ E₂ w).Good N (N.initConfig (w.map some))) :
    (instOf N P E₁ E₂ w).desc.toProblem.StrongODSolvable ↔
      ∃ c, c.state ∈ N.accept ∧ ATM.SavWin N (2 ^ P) (k + P + 2 * 2 ^ P) (N.initConfig (w.map some)) c := by
  haveI : Inhabited (Fin k) := ⟨N.init⟩
  rw [h.strongOD_iff]
  have e : k + P + 2 * 2 ^ P = (k + P + 2 * 2 ^ P - 1) + 1 := by
    have : 1 ≤ 2 ^ P := Nat.one_le_two_pow; omega
  rw [e]
  exact qi_prog_iff N _ _ _ (Nat.two_pow_pos P) _ rfl (mk_init_tail N w)

/-- **The description of a good instance plays the Savitch game** (MP strong). -/
theorem instOf_mpStrong_iff {P E₁ E₂ : ℕ} {w : List Bool}
    (h : (instOf N P E₁ E₂ w).Good N (N.initConfig (w.map some))) :
    (instOf N P E₁ E₂ w).desc.toProblem.MPStrongSolvable ↔
      ∃ c, c.state ∈ N.accept ∧ ATM.SavWin N (2 ^ P) (k + P + 2 * 2 ^ P) (N.initConfig (w.map some)) c := by
  haveI : Inhabited (Fin k) := ⟨N.init⟩
  rw [h.mpStrong_iff]
  have e : k + P + 2 * 2 ^ P = (k + P + 2 * 2 ^ P - 1) + 1 := by
    have : 1 ≤ 2 ^ P := Nat.one_le_two_pow; omega
  rw [e]
  exact qi_prog_iff N _ _ _ (Nat.two_pow_pos P) _ rfl (mk_init_tail N w)

end Sav

end AcycHard

end FOND
