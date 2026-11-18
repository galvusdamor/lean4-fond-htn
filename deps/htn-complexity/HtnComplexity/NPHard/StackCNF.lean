import HtnComplexity.NPHard.GJ
import ComplexityTheory.Complexity.CobhamTM.TMMicro
/-!
# The Cook–Levin tableau of a multi-stack machine

A deterministic machine with finitely many controls `C`, finitely many stacks `K` and a finite
stack alphabet `A`, whose step depends on the control and the top symbols of the stacks and acts
on every stack by at most one push or pop (`HTN.PTime.CobhamTM.TMSim.Act`).

The tableau formula `Tab.cnf` describes `T` steps of the machine on stacks of width `W`: the
input stack `k0` starts with the fixed word `pre` followed by a *free* word of at most `B` bits
(the certificate), the other stacks start empty, and the run must end in an accepting control
with the symbol `aT` on top of the stack `k1`.

* `HTN.NPHard.Tab.satisfiable_cnf_iff` — the formula is satisfiable exactly when some certificate
  of at most `B` bits leads to acceptance after `T` steps (provided `W` is large enough).
-/

namespace HTN.NPHard

open HTN.PTime.CobhamTM.TMSim (Act)

/-- **An explicit numbering** of a finite type: an injection into `{0, …, card - 1}` and a list of
all elements.  The tableau numbers its variables through it, so that for concrete types (`Fin n`,
`Bool`) the variables are explicit numbers. -/
class Ix (α : Type) where
  card : ℕ
  ix : α → ℕ
  ix_lt : ∀ a, ix a < card
  ix_inj : ∀ {a b : α}, ix a = ix b → a = b
  all : List α
  mem_all : ∀ a, a ∈ all

instance (n : ℕ) : Ix (Fin n) where
  card := n
  ix a := a.val
  ix_lt a := a.isLt
  ix_inj h := Fin.ext h
  all := List.finRange n
  mem_all a := List.mem_finRange a

instance : Ix Bool where
  card := 2
  ix b := if b then 1 else 0
  ix_lt b := by cases b <;> simp
  ix_inj {a b} h := by cases a <;> cases b <;> simp_all
  all := [false, true]
  mem_all b := by cases b <;> simp

variable {C K A : Type} [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K] [Fintype A]
  [DecidableEq A] [Ix C] [Ix K] [Ix A]

/-- The data of a tableau. -/
structure Tab (C K A : Type) where
  /-- The step: the new control and the actions on the stacks, given the control and the tops. -/
  step : C → (K → Option A) → C × (K → Act A)
  /-- The initial control. -/
  c0 : C
  /-- The input stack. -/
  k0 : K
  /-- The symbols of the bits `false` and `true` of the certificate. -/
  a0 : A
  a1 : A
  /-- The fixed beginning of the input stack. -/
  pre : List A
  /-- The bound on the length of the certificate. -/
  B : ℕ
  /-- The number of steps. -/
  T : ℕ
  /-- The width of the stacks. -/
  W : ℕ
  /-- The accepting controls. -/
  acc : List C
  /-- The output stack, and the symbol it must have on top. -/
  k1 : K
  aT : A

namespace Tab

variable (M : Tab C K A)

/-! ### The machine -/

/-- A configuration: the control and the stacks. -/
abbrev Cfg (C K A : Type) : Type := C × (K → List A)

/-- One step. -/
def next (g : Cfg C K A) : Cfg C K A :=
  let r := M.step g.1 (fun k => (g.2 k).head?)
  (r.1, fun k => (r.2 k).apply (g.2 k))

/-- The symbol of a certificate bit. -/
def bsym (b : Bool) : A := if b then M.a1 else M.a0

/-- The initial configuration on the certificate `w`. -/
def init (w : List Bool) : Cfg C K A :=
  (M.c0, fun k => if k = M.k0 then M.pre ++ w.map M.bsym else [])

/-- Acceptance of a configuration. -/
def Accepts (g : Cfg C K A) : Prop := g.1 ∈ M.acc ∧ (g.2 M.k1).head? = some M.aT

/-! ### Numbering of the variables -/

/-- The index of a control. -/
def ixC (c : C) : ℕ := Ix.ix c

/-- The index of a stack. -/
def ixK (k : K) : ℕ := Ix.ix k

/-- The number of cell values (the symbols and the blank). -/
def nO (A : Type) [Ix A] : ℕ := Ix.card A + 1

/-- The index of a cell value (the blank is `none`). -/
def ixO : Option A → ℕ
  | none => Ix.card A
  | some a => Ix.ix a

/-- The number of variables of one time slice. -/
def Z : ℕ := Ix.card C + Ix.card K * M.W * nO A

/-- The control variable. -/
def cvar (t : ℕ) (c : C) : ℕ := t * M.Z + ixC c

/-- The cell variable. -/
def svar (t : ℕ) (k : K) (p : ℕ) (o : Option A) : ℕ :=
  t * M.Z + (Ix.card C + ((ixK k * M.W + p) * nO A + ixO o))

/-- The number of variables. -/
def nV : ℕ := (M.T + 1) * M.Z

/-! ### The clauses -/

/-- The controls, the stacks, the cell values, the top vectors, as lists. -/
noncomputable def univC : List C := (Finset.univ : Finset C).toList
def univK : List K := Ix.all
noncomputable def univO : List (Option A) := (Finset.univ : Finset (Option A)).toList
noncomputable def univH : List (K → Option A) := (Finset.univ : Finset (K → Option A)).toList

/-- At most one control per time. -/
noncomputable def amoC : CNF :=
  (List.range (M.T + 1)).flatMap fun t => univC.flatMap fun c => univC.flatMap fun c' =>
    if ixC c < ixC c' then [[(M.cvar t c, false), (M.cvar t c', false)]] else []

/-- At most one value per cell. -/
noncomputable def amoS : CNF :=
  (List.range (M.T + 1)).flatMap fun t => univK.flatMap fun k => (List.range M.W).flatMap fun p =>
    univO.flatMap fun o => univO.flatMap fun o' =>
      if ixO o < ixO o' then [[(M.svar t k p o, false), (M.svar t k p o', false)]] else []

/-- The initial specification of a cell: `some o` for a fixed value, `none` for a free cell of
the certificate. -/
def cellInit (k : K) (p : ℕ) : Option (Option A) :=
  if k = M.k0 then
    (if p < M.pre.length then some (M.pre[p]?) else if p < M.pre.length + M.B then none
      else some none)
  else some none

/-- The clauses of the initial cell `(k, p)`. -/
noncomputable def initCell (k : K) (p : ℕ) : CNF :=
  match M.cellInit k p with
  | some o => [[(M.svar 0 k p o, true)]]
  | none => [[(M.svar 0 k p (some M.a0), true), (M.svar 0 k p (some M.a1), true),
      (M.svar 0 k p none, true)], [(M.svar 0 k p none, false), (M.svar 0 k (p + 1) none, true)]]

/-- The initial configuration. -/
noncomputable def initCNF : CNF :=
  [[(M.cvar 0 M.c0, true)]] ++ univK.flatMap fun k => (List.range M.W).flatMap fun p =>
    M.initCell k p

/-- The premise of a transition: control `c` and tops `h` at time `t`, as negated literals. -/
noncomputable def prem (t : ℕ) (c : C) (h : K → Option A) : List (ℕ × Bool) :=
  (M.cvar t c, false) :: univK.map fun k => (M.svar t k 0 (h k), false)

/-- The conclusion of a transition for the cell `(k, p)` of value `o`. -/
noncomputable def cellConcl (t : ℕ) (k : K) (p : ℕ) (o : Option A) : Act A → List (ℕ × Bool)
  | .keep => [(M.svar t k p o, false), (M.svar (t + 1) k p o, true)]
  | .pop => if p + 1 < M.W then [(M.svar t k (p + 1) o, false), (M.svar (t + 1) k p o, true)]
      else [(M.svar (t + 1) k p none, true)]
  | .push a => if p = 0 then [(M.svar (t + 1) k 0 (some a), true)]
      else [(M.svar t k (p - 1) o, false), (M.svar (t + 1) k p o, true)]

/-- The transitions. -/
noncomputable def transCNF : CNF :=
  (List.range M.T).flatMap fun t => univC.flatMap fun c => univH.flatMap fun h =>
    (M.prem t c h ++ [(M.cvar (t + 1) (M.step c h).1, true)]) ::
      univK.flatMap fun k => (List.range M.W).flatMap fun p => univO.map fun o =>
        M.prem t c h ++ M.cellConcl t k p o ((M.step c h).2 k)

/-- Acceptance. -/
noncomputable def accCNF : CNF :=
  [M.acc.map fun c => (M.cvar M.T c, true), [(M.svar M.T M.k1 0 (some M.aT), true)]]

/-- **The tableau formula.** -/
noncomputable def cnf : CNF := M.amoC ++ M.amoS ++ M.initCNF ++ M.transCNF ++ M.accCNF

/-! ### Injectivity of the numbering -/

theorem ixC_lt (c : C) : ixC c < Ix.card C := Ix.ix_lt c

theorem ixC_inj {c c' : C} (h : ixC c = ixC c') : c = c' := Ix.ix_inj h

theorem ixK_lt (k : K) : ixK k < Ix.card K := Ix.ix_lt k

theorem ixK_inj {k k' : K} (h : ixK k = ixK k') : k = k' := Ix.ix_inj h

theorem ixO_lt (o : Option A) : ixO o < nO A := by
  cases o with
  | none => simp [ixO, nO]
  | some a => have := Ix.ix_lt a; simp only [ixO, nO]; omega

theorem ixO_inj {o o' : Option A} (h : ixO o = ixO o') : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some a' => have := Ix.ix_lt a'; simp [ixO] at h; omega
  | some a =>
    cases o' with
    | none => have := Ix.ix_lt a; simp [ixO] at h; omega
    | some a' => simp only [ixO] at h; rw [Ix.ix_inj h]

theorem cell_lt (k : K) {p : ℕ} (hp : p < M.W) (o : Option A) :
    (ixK k * M.W + p) * nO A + ixO o < Ix.card K * M.W * nO A :=
  pair_lt (pair_lt (ixK_lt k) hp) (ixO_lt o)

theorem ixC_lt_Z (c : C) : ixC c < M.Z := by
  have := ixC_lt c; unfold Z; omega

theorem svar_off_lt (k : K) {p : ℕ} (hp : p < M.W) (o : Option A) :
    Ix.card C + ((ixK k * M.W + p) * nO A + ixO o) < M.Z := by
  have := M.cell_lt k hp o; unfold Z; omega

theorem cvar_inj {t t' : ℕ} {c c' : C} (h : M.cvar t c = M.cvar t' c') : t = t' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := pair_inj (M.ixC_lt_Z c) (M.ixC_lt_Z c') h
  exact ⟨h1, ixC_inj h2⟩

theorem svar_inj {t t' : ℕ} {k k' : K} {p p' : ℕ} {o o' : Option A} (hp : p < M.W)
    (hp' : p' < M.W) (h : M.svar t k p o = M.svar t' k' p' o') :
    t = t' ∧ k = k' ∧ p = p' ∧ o = o' := by
  obtain ⟨h1, h2⟩ := pair_inj (M.svar_off_lt k hp o) (M.svar_off_lt k' hp' o') h
  have h3 : (ixK k * M.W + p) * nO A + ixO o = (ixK k' * M.W + p') * nO A + ixO o' := by omega
  obtain ⟨h4, h5⟩ := pair_inj (ixO_lt o) (ixO_lt o') h3
  obtain ⟨h6, h7⟩ := pair_inj hp hp' h4
  exact ⟨h1, ixK_inj h6, h7, ixO_inj h5⟩

theorem cvar_ne_svar {t t' : ℕ} (c : C) (k : K) {p : ℕ} (hp : p < M.W) (o : Option A) :
    M.cvar t c ≠ M.svar t' k p o := by
  intro h
  obtain ⟨-, h2⟩ := pair_inj (M.ixC_lt_Z c) (M.svar_off_lt k hp o) h
  have := ixC_lt c; omega

theorem cvar_lt {t : ℕ} (ht : t ≤ M.T) (c : C) : M.cvar t c < M.nV := by
  have := pair_lt (show t < M.T + 1 by omega) (M.ixC_lt_Z c); exact this

theorem svar_lt {t : ℕ} (ht : t ≤ M.T) (k : K) {p : ℕ} (hp : p < M.W) (o : Option A) :
    M.svar t k p o < M.nV := by
  have := pair_lt (show t < M.T + 1 by omega) (M.svar_off_lt k hp o); exact this

/-! ### Membership in the lists of all elements -/

@[simp] theorem mem_univC (c : C) : c ∈ (univC : List C) := by simp [univC]
@[simp] theorem mem_univK (k : K) : k ∈ (univK : List K) := Ix.mem_all k
@[simp] theorem mem_univO (o : Option A) : o ∈ (univO : List (Option A)) := by simp [univO]
@[simp] theorem mem_univH (h : K → Option A) : h ∈ (univH : List (K → Option A)) := by simp [univH]

/-! ### Runs -/

/-- The cells after one action. -/
theorem getElem?_apply (a : Act A) (l : List A) (p : ℕ) :
    (a.apply l)[p]? = match a with
      | .keep => l[p]?
      | .pop => l[p + 1]?
      | .push b => if p = 0 then some b else l[p - 1]? := by
  cases a with
  | keep => rfl
  | pop => simp [Act.apply]
  | push b =>
    cases p with
    | zero => simp [Act.apply]
    | succ p => simp [Act.apply]

theorem length_apply_le (a : Act A) (l : List A) : (a.apply l).length ≤ l.length + 1 := by
  cases a <;> simp [Act.apply]; omega

theorem length_iterate_next_le (g : Cfg C K A) (k : K) (t : ℕ) :
    (((M.next)^[t] g).2 k).length ≤ (g.2 k).length + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have := length_apply_le ((M.step ((M.next)^[t] g).1 (fun k => (((M.next)^[t] g).2 k).head?)).2 k)
      (((M.next)^[t] g).2 k)
    simp only [next]; omega

theorem length_init_le {w : List Bool} (hw : w.length ≤ M.B) (k : K) :
    ((M.init w).2 k).length ≤ M.pre.length + M.B := by
  simp only [init]; split <;> simp; omega

/-! ### Completeness: the assignment of an accepting run -/

theorem sat_append {asg : ℕ → Bool} {φ ψ : CNF} : Sat asg (φ ++ ψ) ↔ Sat asg φ ∧ Sat asg ψ := by
  simp only [Sat, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

open Classical in
/-- The assignment describing a sequence of configurations. -/
noncomputable def asg (g : ℕ → Cfg C K A) (v : ℕ) : Bool :=
  decide ((∃ t ≤ M.T, ∃ c, v = M.cvar t c ∧ c = (g t).1) ∨
    (∃ t ≤ M.T, ∃ k p o, p < M.W ∧ v = M.svar t k p o ∧ o = ((g t).2 k)[p]?))

theorem asg_cvar (g : ℕ → Cfg C K A) {t : ℕ} (ht : t ≤ M.T) (c : C) :
    M.asg g (M.cvar t c) = decide (c = (g t).1) := by
  unfold asg
  rw [decide_eq_decide]
  constructor
  · rintro (⟨t', -, c', h, rfl⟩ | ⟨t', -, k, p, o, hp, h, -⟩)
    · obtain ⟨rfl, rfl⟩ := M.cvar_inj h; rfl
    · exact absurd h (M.cvar_ne_svar c k hp o)
  · intro h; exact Or.inl ⟨t, ht, c, rfl, h⟩

theorem asg_svar (g : ℕ → Cfg C K A) {t : ℕ} (ht : t ≤ M.T) (k : K) {p : ℕ} (hp : p < M.W)
    (o : Option A) : M.asg g (M.svar t k p o) = decide (o = ((g t).2 k)[p]?) := by
  unfold asg
  rw [decide_eq_decide]
  constructor
  · rintro (⟨t', -, c', h, -⟩ | ⟨t', -, k', p', o', hp', h, rfl⟩)
    · exact absurd h.symm (M.cvar_ne_svar c' k hp o)
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := M.svar_inj hp hp' h; rfl
  · intro h; exact Or.inr ⟨t, ht, k, p, o, hp, rfl, h⟩

theorem sat_amoC (g : ℕ → Cfg C K A) : Sat (M.asg g) M.amoC := by
  intro cl hcl
  simp only [amoC, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨t, ht, c, -, c', -, hc⟩ := hcl
  split_ifs at hc with hlt
  · simp only [List.mem_singleton] at hc; subst hc
    have hne : c ≠ c' := fun h => by subst h; omega
    by_cases h1 : c = (g t).1
    · refine ⟨(M.cvar t c', false), by simp, ?_⟩
      rw [M.asg_cvar g (by omega)]
      simp only [decide_eq_false_iff_not]
      intro h2; exact hne (h1.trans h2.symm)
    · exact ⟨(M.cvar t c, false), by simp, by rw [M.asg_cvar g (by omega)]; simpa using h1⟩
  · simp at hc

theorem sat_amoS (g : ℕ → Cfg C K A) : Sat (M.asg g) M.amoS := by
  intro cl hcl
  simp only [amoS, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨t, ht, k, -, p, hp, o, -, o', -, hc⟩ := hcl
  split_ifs at hc with hlt
  · simp only [List.mem_singleton] at hc; subst hc
    have hne : o ≠ o' := fun h => by subst h; omega
    by_cases h1 : o = ((g t).2 k)[p]?
    · refine ⟨(M.svar t k p o', false), by simp, ?_⟩
      rw [M.asg_svar g (by omega) k hp]
      simp only [decide_eq_false_iff_not]
      intro h2; exact hne (h1.trans h2.symm)
    · exact ⟨(M.svar t k p o, false), by simp, by rw [M.asg_svar g (by omega) k hp]; simpa using h1⟩
  · simp at hc

/-- The initial cells. -/
theorem cell_init {w : List Bool} (hw : w.length ≤ M.B) (k : K) (p : ℕ) :
    ((M.init w).2 k)[p]? = match M.cellInit k p with
      | some o => o
      | none => (w.map M.bsym)[p - M.pre.length]? := by
  unfold cellInit init
  by_cases hk : k = M.k0
  · subst hk
    simp only [↓reduceIte]
    by_cases h1 : p < M.pre.length
    · simp [h1, List.getElem?_append_left h1]
    · by_cases h2 : p < M.pre.length + M.B
      · simp [h1, h2, List.getElem?_append_right (show M.pre.length ≤ p by omega)]
      · simp only [h1, h2, ↓reduceIte]
        rw [List.getElem?_eq_none]; simp; omega
  · simp [hk]

theorem cellInit_none {k : K} {p : ℕ} (h : M.cellInit k p = none) :
    k = M.k0 ∧ M.pre.length ≤ p ∧ p < M.pre.length + M.B := by
  unfold cellInit at h
  split_ifs at h with h1 h2 h3 <;> simp_all

theorem sat_initCNF {w : List Bool} (hw : w.length ≤ M.B) (hW : M.pre.length + M.B < M.W)
    (g : ℕ → Cfg C K A) (hg : g 0 = M.init w) : Sat (M.asg g) M.initCNF := by
  intro cl hcl
  simp only [initCNF, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range] at hcl
  rcases hcl with rfl | ⟨k, -, p, hp, hc⟩
  · exact ⟨_, List.mem_singleton_self _, by rw [M.asg_cvar g (Nat.zero_le _), hg]; simp [init]⟩
  · have hcell := M.cell_init hw k p
    rw [← hg] at hcell
    unfold initCell at hc
    rcases hci : M.cellInit k p with _ | o
    · rw [hci] at hc hcell
      obtain ⟨rfl, hp1, hp2⟩ := M.cellInit_none hci
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rcases hwi : (w.map M.bsym)[p - M.pre.length]? with _ | a
        · refine ⟨(M.svar 0 M.k0 p none, true), by simp, ?_⟩
          rw [M.asg_svar g (Nat.zero_le _) _ hp, hcell, hwi]; simp
        · obtain ⟨b, -, rfl⟩ : ∃ b, b ∈ w ∧ M.bsym b = a := by
            rw [List.getElem?_map] at hwi
            rcases hb : w[p - M.pre.length]? with _ | b
            · rw [hb] at hwi; simp at hwi
            · rw [hb] at hwi; simp only [Option.map_some, Option.some.injEq] at hwi
              exact ⟨b, List.mem_of_getElem? hb, hwi⟩
          cases b
          · refine ⟨(M.svar 0 M.k0 p (some M.a0), true), by simp, ?_⟩
            rw [M.asg_svar g (Nat.zero_le _) _ hp, hcell, hwi]; simp [bsym]
          · refine ⟨(M.svar 0 M.k0 p (some M.a1), true), by simp, ?_⟩
            rw [M.asg_svar g (Nat.zero_le _) _ hp, hcell, hwi]; simp [bsym]
      · by_cases hn : ((g 0).2 M.k0)[p]? = none
        · refine ⟨(M.svar 0 M.k0 (p + 1) none, true), by simp, ?_⟩
          rw [M.asg_svar g (Nat.zero_le _) _ (by omega)]
          rw [List.getElem?_eq_none_iff] at hn
          simp only [decide_eq_true_eq]
          exact (List.getElem?_eq_none_iff.2 (by omega)).symm
        · refine ⟨(M.svar 0 M.k0 p none, false), by simp, ?_⟩
          rw [M.asg_svar g (Nat.zero_le _) _ hp]
          simpa [eq_comm] using hn
    · rw [hci] at hc hcell
      simp only [List.mem_singleton] at hc; subst hc
      exact ⟨_, List.mem_singleton_self _, by
        rw [M.asg_svar g (Nat.zero_le _) k hp]; simpa using hcell.symm⟩

theorem prem_sat (g : ℕ → Cfg C K A) {t : ℕ} (ht : t ≤ M.T) (hW0 : 0 < M.W) (c : C)
    (h : K → Option A) (hch : ¬ (c = (g t).1 ∧ h = fun k => ((g t).2 k).head?)) :
    ∃ l ∈ M.prem t c h, M.asg g l.1 = l.2 := by
  by_cases hc : c = (g t).1
  · have hh : h ≠ fun k => ((g t).2 k).head? := fun e => hch ⟨hc, e⟩
    obtain ⟨k, hk⟩ : ∃ k, h k ≠ ((g t).2 k).head? := by
      by_contra hne; push_neg at hne; exact hh (funext hne)
    refine ⟨(M.svar t k 0 (h k), false), ?_, ?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨k, mem_univK k, rfl⟩)
    · rw [M.asg_svar g ht k hW0, ← List.head?_eq_getElem?]; simpa using hk
  · exact ⟨(M.cvar t c, false), List.mem_cons_self, by rw [M.asg_cvar g ht]; simpa using hc⟩

theorem concl_sat (g : ℕ → Cfg C K A) {t : ℕ} (ht : t < M.T) (k : K) {p : ℕ} (hp : p < M.W)
    (o : Option A) (a : Act A) (h1 : (g (t + 1)).2 k = a.apply ((g t).2 k))
    (hlen : ((g t).2 k).length ≤ M.W) :
    ∃ l ∈ M.cellConcl t k p o a, M.asg g l.1 = l.2 := by
  have hsv : ∀ t', t' ≤ M.T → ∀ p', p' < M.W → ∀ o' : Option A,
      M.asg g (M.svar t' k p' o') = decide (o' = ((g t').2 k)[p']?) :=
    fun t' ht' p' hp' o' => M.asg_svar g ht' k hp' o'
  have hcell := getElem?_apply a ((g t).2 k) p
  rw [← h1] at hcell
  cases a with
  | keep =>
    simp only at hcell
    by_cases ho : o = ((g t).2 k)[p]?
    · exact ⟨(M.svar (t + 1) k p o, true), by simp [cellConcl],
        by rw [hsv _ (by omega) _ hp, hcell]; simpa using ho⟩
    · exact ⟨(M.svar t k p o, false), by simp [cellConcl], by rw [hsv _ (by omega) _ hp]; simpa using ho⟩
  | pop =>
    simp only at hcell
    by_cases hpW : p + 1 < M.W
    · by_cases ho : o = ((g t).2 k)[p + 1]?
      · exact ⟨(M.svar (t + 1) k p o, true), by simp [cellConcl, hpW],
          by rw [hsv _ (by omega) _ hp, hcell]; simpa using ho⟩
      · exact ⟨(M.svar t k (p + 1) o, false), by simp [cellConcl, hpW],
          by rw [hsv _ (by omega) _ hpW]; simpa using ho⟩
    · refine ⟨(M.svar (t + 1) k p none, true), by simp [cellConcl, hpW], ?_⟩
      rw [hsv _ (by omega) _ hp, hcell]
      simp only [decide_eq_true_eq]
      exact (List.getElem?_eq_none_iff.2 (by omega)).symm
  | push b =>
    simp only at hcell
    by_cases hp0 : p = 0
    · subst hp0
      exact ⟨(M.svar (t + 1) k 0 (some b), true), by simp [cellConcl],
        by rw [hsv _ (by omega) _ hp, hcell]; simp⟩
    · rw [if_neg hp0] at hcell
      by_cases ho : o = ((g t).2 k)[p - 1]?
      · exact ⟨(M.svar (t + 1) k p o, true), by simp [cellConcl, hp0],
          by rw [hsv _ (by omega) _ hp, hcell]; simpa using ho⟩
      · exact ⟨(M.svar t k (p - 1) o, false), by simp [cellConcl, hp0],
          by rw [hsv _ (by omega) _ (by omega)]; simpa using ho⟩

theorem sat_transCNF (g : ℕ → Cfg C K A) (hg : ∀ t < M.T, g (t + 1) = M.next (g t))
    (hlen : ∀ t < M.T, ∀ k, ((g t).2 k).length ≤ M.W) (hW0 : 0 < M.W) :
    Sat (M.asg g) M.transCNF := by
  intro cl hcl
  simp only [transCNF, List.mem_flatMap, List.mem_range, List.mem_cons] at hcl
  obtain ⟨t, ht, c, -, h, -, hc⟩ := hcl
  by_cases hch : c = (g t).1 ∧ h = fun k => ((g t).2 k).head?
  · obtain ⟨rfl, rfl⟩ := hch
    have hnext := hg t ht
    rcases hc with rfl | hc
    · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [M.asg_cvar g (by omega), hnext]; simp [next]
    · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hc
      obtain ⟨k, -, p, hp, o, -, rfl⟩ := hc
      obtain ⟨l, hl, hv⟩ := M.concl_sat g ht k hp o _ (by rw [hnext]; rfl) (hlen t ht k)
      exact ⟨l, List.mem_append_right _ hl, hv⟩
  · obtain ⟨l, hl, hv⟩ := M.prem_sat g (by omega) hW0 c h hch
    rcases hc with rfl | hc
    · exact ⟨l, List.mem_append_left _ hl, hv⟩
    · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hc
      obtain ⟨k, -, p, hp, o, -, rfl⟩ := hc
      exact ⟨l, List.mem_append_left _ hl, hv⟩

theorem sat_accCNF (g : ℕ → Cfg C K A) (hW0 : 0 < M.W) (hacc : M.Accepts (g M.T)) :
    Sat (M.asg g) M.accCNF := by
  intro cl hcl
  simp only [accCNF, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · exact ⟨(M.cvar M.T (g M.T).1, true), List.mem_map.2 ⟨_, hacc.1, rfl⟩,
      by rw [M.asg_cvar g le_rfl]; simp⟩
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [M.asg_svar g le_rfl _ hW0, ← List.head?_eq_getElem?, hacc.2]; simp

/-- **Completeness.** -/
theorem sat_of_accepts (hW : M.pre.length + M.B + M.T < M.W) {w : List Bool} (hw : w.length ≤ M.B)
    (hacc : M.Accepts ((M.next)^[M.T] (M.init w))) :
    Sat (M.asg fun t => (M.next)^[t] (M.init w)) M.cnf := by
  simp only [cnf, sat_append]
  refine ⟨⟨⟨⟨M.sat_amoC _, M.sat_amoS _⟩, M.sat_initCNF hw (by omega) _ rfl⟩,
    M.sat_transCNF _ (fun t _ => Function.iterate_succ_apply' _ _ _) (fun t ht k => ?_) (by omega)⟩,
    M.sat_accCNF _ (by omega) hacc⟩
  have h1 := M.length_iterate_next_le (M.init w) k t
  have h2 := M.length_init_le hw k
  omega

/-! ### Soundness: decoding a satisfying assignment -/

section Sound

variable {asg : ℕ → Bool}

theorem clause_sat {asg : ℕ → Bool} {φ : CNF} (h : Sat asg φ) {cl : List (ℕ × Bool)}
    (hcl : cl ∈ φ) : ∃ l ∈ cl, asg l.1 = l.2 := h cl hcl

theorem amo_ctrl (h : Sat asg M.amoC) {t : ℕ} (ht : t ≤ M.T) {c : C} (hc : asg (M.cvar t c) = true)
    (c' : C) : asg (M.cvar t c') = decide (c' = c) := by
  by_cases hcc : c' = c
  · subst hcc; simpa using hc
  · simp only [hcc, decide_false]
    by_contra hc'
    simp only [Bool.not_eq_false] at hc'
    have hne : ixC c ≠ ixC c' := fun e => hcc (ixC_inj e).symm
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨l, hl, hv⟩ := clause_sat h (cl := [(M.cvar t c, false), (M.cvar t c', false)])
        (by simp only [amoC, List.mem_flatMap, List.mem_range]
            exact ⟨t, by omega, c, mem_univC c, c', mem_univC c', by simp [hlt]⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp_all
    · obtain ⟨l, hl, hv⟩ := clause_sat h (cl := [(M.cvar t c', false), (M.cvar t c, false)])
        (by simp only [amoC, List.mem_flatMap, List.mem_range]
            exact ⟨t, by omega, c', mem_univC c', c, mem_univC c, by simp [hlt]⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp_all

theorem amo_cell (h : Sat asg M.amoS) {t : ℕ} (ht : t ≤ M.T) (k : K) {p : ℕ} (hp : p < M.W)
    {o : Option A} (ho : asg (M.svar t k p o) = true) (o' : Option A) :
    asg (M.svar t k p o') = decide (o' = o) := by
  by_cases hoo : o' = o
  · subst hoo; simpa using ho
  · simp only [hoo, decide_false]
    by_contra ho'
    simp only [Bool.not_eq_false] at ho'
    have hne : ixO o ≠ ixO o' := fun e => hoo (ixO_inj e).symm
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨l, hl, hv⟩ := clause_sat h (cl := [(M.svar t k p o, false), (M.svar t k p o', false)])
        (by simp only [amoS, List.mem_flatMap, List.mem_range]
            exact ⟨t, by omega, k, mem_univK k, p, hp, o, mem_univO o, o', mem_univO o', by simp [hlt]⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp_all
    · obtain ⟨l, hl, hv⟩ := clause_sat h (cl := [(M.svar t k p o', false), (M.svar t k p o, false)])
        (by simp only [amoS, List.mem_flatMap, List.mem_range]
            exact ⟨t, by omega, k, mem_univK k, p, hp, o', mem_univO o', o, mem_univO o, by simp [hlt]⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp_all

/-- The assignment describes the configuration `g` at time `t`. -/
def Enc (asg : ℕ → Bool) (t : ℕ) (g : Cfg C K A) : Prop :=
  (∀ c, asg (M.cvar t c) = decide (c = g.1)) ∧
    ∀ k, ∀ p < M.W, ∀ o, asg (M.svar t k p o) = decide (o = (g.2 k)[p]?)

theorem prem_false {t : ℕ} {g : Cfg C K A} (he : M.Enc asg t g) (hW0 : 0 < M.W) :
    ∀ l ∈ M.prem t g.1 (fun k => (g.2 k).head?), asg l.1 ≠ l.2 := by
  intro l hl
  simp only [prem, List.mem_cons, List.mem_map] at hl
  rcases hl with rfl | ⟨k, -, rfl⟩
  · simp [he.1]
  · simp [he.2 k 0 hW0, List.head?_eq_getElem?]

theorem concl_of_sat {t : ℕ} {g : Cfg C K A} (he : M.Enc asg t g) (hW0 : 0 < M.W)
    {X : List (ℕ × Bool)} (h : ∃ l ∈ M.prem t g.1 (fun k => (g.2 k).head?) ++ X, asg l.1 = l.2) :
    ∃ l ∈ X, asg l.1 = l.2 := by
  obtain ⟨l, hl, hv⟩ := h
  rcases List.mem_append.1 hl with hl | hl
  · exact absurd hv (M.prem_false he hW0 l hl)
  · exact ⟨l, hl, hv⟩

theorem cell_next_true {t : ℕ} {g : Cfg C K A} (he : M.Enc asg t g) (k : K) {p : ℕ} (hp : p < M.W)
    (a : Act A) (hX : ∀ o, ∃ l ∈ M.cellConcl t k p o a, asg l.1 = l.2)
    (hlen : (g.2 k).length ≤ M.W) :
    asg (M.svar (t + 1) k p ((a.apply (g.2 k))[p]?)) = true := by
  rw [getElem?_apply]
  cases a with
  | keep =>
    obtain ⟨l, hl, hv⟩ := hX ((g.2 k)[p]?)
    simp only [cellConcl, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp [he.2 k p hp] at hv
    · exact hv
  | pop =>
    simp only
    by_cases hpW : p + 1 < M.W
    · obtain ⟨l, hl, hv⟩ := hX ((g.2 k)[p + 1]?)
      simp only [cellConcl, hpW, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [he.2 k (p + 1) hpW] at hv
      · exact hv
    · obtain ⟨l, hl, hv⟩ := hX none
      simp only [cellConcl, hpW, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      rw [List.getElem?_eq_none_iff.2 (by omega)]; exact hv
  | push b =>
    simp only
    by_cases hp0 : p = 0
    · subst hp0
      obtain ⟨l, hl, hv⟩ := hX none
      simp only [cellConcl, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl; simpa using hv
    · obtain ⟨l, hl, hv⟩ := hX ((g.2 k)[p - 1]?)
      simp only [cellConcl, hp0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hl
      rw [if_neg hp0]
      rcases hl with rfl | rfl
      · simp [he.2 k (p - 1) (by omega)] at hv
      · exact hv

theorem enc_next (h : Sat asg M.cnf) {t : ℕ} (ht : t < M.T) {g : Cfg C K A} (he : M.Enc asg t g)
    (hlen : ∀ k, (g.2 k).length ≤ M.W) (hW0 : 0 < M.W) : M.Enc asg (t + 1) (M.next g) := by
  simp only [cnf, sat_append] at h
  obtain ⟨⟨⟨⟨hC, hS⟩, -⟩, hT⟩, -⟩ := h
  have hmem : ∀ X, X ∈ (M.prem t g.1 (fun k => (g.2 k).head?) ++
      [(M.cvar (t + 1) (M.step g.1 (fun k => (g.2 k).head?)).1, true)]) ::
      univK.flatMap (fun k => (List.range M.W).flatMap fun p => univO.map fun o =>
        M.prem t g.1 (fun k => (g.2 k).head?) ++
          M.cellConcl t k p o ((M.step g.1 (fun k => (g.2 k).head?)).2 k)) → X ∈ M.transCNF := by
    intro X hX
    simp only [transCNF, List.mem_flatMap, List.mem_range]
    exact ⟨t, ht, g.1, mem_univC _, _, mem_univH _, hX⟩
  constructor
  · obtain ⟨l, hl, hv⟩ := M.concl_of_sat he hW0 (hT _ (hmem _ List.mem_cons_self))
    simp only [List.mem_singleton] at hl; subst hl
    exact M.amo_ctrl hC (by omega) hv
  · intro k p hp o
    refine M.amo_cell hS (by omega) k hp (M.cell_next_true he k hp _ (fun o' => ?_) (hlen k)) o
    refine M.concl_of_sat he hW0 (hT _ (hmem _ (List.mem_cons_of_mem _ ?_)))
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨k, mem_univK k, p, hp, o', mem_univO o', rfl⟩

theorem cellInit_k0_free {p : ℕ} (h1 : M.pre.length ≤ p) (h2 : p < M.pre.length + M.B) :
    M.cellInit M.k0 p = none := by
  simp [cellInit, show ¬ p < M.pre.length by omega, h2]

theorem initCell_sub {k : K} {p : ℕ} (hp : p < M.W) {X : List (ℕ × Bool)}
    (hX : X ∈ M.initCell k p) : X ∈ M.initCNF := by
  simp only [initCNF, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨k, mem_univK k, p, hp, hX⟩

open Classical in
/-- The length of the decoded certificate: the first blank free cell. -/
noncomputable def decLen (asg : ℕ → Bool) : ℕ :=
  if h : ∃ i, i < M.B ∧ asg (M.svar 0 M.k0 (M.pre.length + i) none) = true then Nat.find h
  else M.B

/-- The decoded certificate. -/
noncomputable def decW (asg : ℕ → Bool) : List Bool :=
  (List.range (M.decLen asg)).map fun i => asg (M.svar 0 M.k0 (M.pre.length + i) (some M.a1))

theorem decLen_le : M.decLen asg ≤ M.B := by
  unfold decLen
  split
  · rename_i h; exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem not_blank_of_lt {i : ℕ} (hi : i < M.decLen asg) :
    asg (M.svar 0 M.k0 (M.pre.length + i) none) = false := by
  unfold decLen at hi
  split at hi
  · rename_i h
    have := Nat.find_min h hi
    simp only [not_and, Bool.not_eq_true] at this
    exact this (lt_of_lt_of_le hi (Nat.find_spec h).1.le)
  · rename_i h
    push_neg at h
    simpa using h i hi

theorem blank_of_ge (h : Sat asg M.cnf) (hW : M.pre.length + M.B < M.W) :
    ∀ j, M.decLen asg + j < M.B →
      asg (M.svar 0 M.k0 (M.pre.length + (M.decLen asg + j)) none) = true := by
  simp only [cnf, sat_append] at h
  have hI := h.1.1.2
  intro j
  induction j with
  | zero =>
    intro hj
    unfold decLen at hj ⊢
    split
    · rename_i hex; exact (Nat.find_spec hex).2
    · rename_i hex; simp only [hex, ↓reduceDIte] at hj; omega
  | succ j ih =>
    intro hj
    have hb := ih (by omega)
    set p := M.pre.length + (M.decLen asg + j) with hpdef
    have hfree := M.cellInit_k0_free (p := p) (by omega) (by omega)
    have hmem : [(M.svar 0 M.k0 p none, false), (M.svar 0 M.k0 (p + 1) none, true)] ∈ M.initCNF := by
      refine M.initCell_sub (k := M.k0) (p := p) (by omega) ?_
      unfold initCell; rw [hfree]; simp
    obtain ⟨l, hl, hv⟩ := hI _ hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp [hb] at hv
    · simpa [hpdef, Nat.add_assoc] using hv

theorem enc_init (h : Sat asg M.cnf) (hW : M.pre.length + M.B < M.W) :
    M.Enc asg 0 (M.init (M.decW asg)) := by
  have hw : (M.decW asg).length ≤ M.B := by simpa [decW] using M.decLen_le
  have h' := h
  simp only [cnf, sat_append] at h'
  obtain ⟨⟨⟨⟨hC, hS⟩, hI⟩, -⟩, -⟩ := h'
  constructor
  · obtain ⟨l, hl, hv⟩ := hI [(M.cvar 0 M.c0, true)] (by simp [initCNF])
    simp only [List.mem_singleton] at hl; subst hl
    intro c; rw [M.amo_ctrl hC (Nat.zero_le _) hv c]; rfl
  · intro k p hp o
    have hcell := M.cell_init hw k p
    rcases hci : M.cellInit k p with _ | o0
    · rw [hci] at hcell
      obtain ⟨rfl, hp1, hp2⟩ := M.cellInit_none hci
      rw [hcell]
      refine M.amo_cell hS (Nat.zero_le _) _ hp ?_ o
      set i := p - M.pre.length with hi
      have hpi : p = M.pre.length + i := by omega
      by_cases hlt : i < M.decLen asg
      · have hnb := M.not_blank_of_lt hlt
        rw [← hpi] at hnb
        have hmem : [(M.svar 0 M.k0 p (some M.a0), true), (M.svar 0 M.k0 p (some M.a1), true),
            (M.svar 0 M.k0 p none, true)] ∈ M.initCNF := by
          refine M.initCell_sub (k := M.k0) hp ?_
          unfold initCell; rw [hci]; simp
        obtain ⟨l, hl, hv⟩ := hI _ hmem
        have hget : (List.map M.bsym (M.decW asg))[i]? =
            some (M.bsym (asg (M.svar 0 M.k0 p (some M.a1)))) := by
          simp [decW, hlt, hpi]
        rw [hget]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        cases ha1 : asg (M.svar 0 M.k0 p (some M.a1))
        · rcases hl with rfl | rfl | rfl
          · simpa [bsym] using hv
          · simp [ha1] at hv
          · simp [hnb] at hv
        · simpa [bsym] using ha1
      · have hge := M.blank_of_ge h hW (i - M.decLen asg) (by omega)
        rw [show M.decLen asg + (i - M.decLen asg) = i by omega, ← hpi] at hge
        rw [List.getElem?_eq_none (by simp [decW]; omega)]
        exact hge
    · rw [hci] at hcell
      rw [hcell]
      obtain ⟨l, hl, hv⟩ := hI [(M.svar 0 k p o0, true)]
        (M.initCell_sub hp (by unfold initCell; rw [hci]; simp))
      simp only [List.mem_singleton] at hl; subst hl
      exact M.amo_cell hS (Nat.zero_le _) k hp hv o

end Sound

/-! ### The main theorem -/

/-- **The tableau formula is satisfiable exactly when some certificate is accepted.** -/
theorem satisfiable_cnf_iff (hW : M.pre.length + M.B + M.T < M.W) :
    Satisfiable M.cnf ↔
      ∃ w : List Bool, w.length ≤ M.B ∧ M.Accepts ((M.next)^[M.T] (M.init w)) := by
  constructor
  · rintro ⟨asg, h⟩
    refine ⟨M.decW asg, by simpa [decW] using M.decLen_le, ?_⟩
    have hw : (M.decW asg).length ≤ M.B := by simpa [decW] using M.decLen_le
    have henc : ∀ t ≤ M.T, M.Enc asg t ((M.next)^[t] (M.init (M.decW asg))) := by
      intro t
      induction t with
      | zero => intro _; exact M.enc_init h (by omega)
      | succ t ih =>
        intro ht
        rw [Function.iterate_succ_apply']
        refine M.enc_next h (by omega) (ih (by omega)) (fun k => ?_) (by omega)
        have h1 := M.length_iterate_next_le (M.init (M.decW asg)) k t
        have h2 := M.length_init_le hw k
        omega
    have he := henc M.T le_rfl
    simp only [cnf, sat_append] at h
    have hA := h.2
    obtain ⟨l1, hl1, hv1⟩ := hA _ (show M.acc.map (fun c => (M.cvar M.T c, true)) ∈ M.accCNF by
      simp [accCNF])
    obtain ⟨l2, hl2, hv2⟩ := hA _ (show [(M.svar M.T M.k1 0 (some M.aT), true)] ∈ M.accCNF by
      simp [accCNF])
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl1
    simp only [List.mem_singleton] at hl2; subst hl2
    rw [he.1] at hv1
    rw [he.2 _ _ (by omega)] at hv2
    simp only [decide_eq_true_eq] at hv1 hv2
    exact ⟨hv1 ▸ hc, by rw [List.head?_eq_getElem?, ← hv2]⟩
  · rintro ⟨w, hw, hacc⟩
    exact ⟨_, M.sat_of_accepts hW hw hacc⟩

/-- The variables are below `nV`. -/
theorem cnf_vars_lt (hW : M.pre.length + M.B < M.W) : ∀ c ∈ M.cnf, ∀ l ∈ c, l.1 < M.nV := by
  have hW0 : 0 < M.W := by omega
  intro cl hcl l hl
  simp only [cnf, List.mem_append] at hcl
  rcases hcl with (((hc | hc) | hc) | hc) | hc
  · simp only [amoC, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨t, ht, c, -, c', -, hc⟩ := hc
    split_ifs at hc
    · simp only [List.mem_singleton] at hc; subst hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> exact M.cvar_lt (by omega) _
    · simp at hc
  · simp only [amoS, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨t, ht, k, -, p, hp, o, -, o', -, hc⟩ := hc
    split_ifs at hc
    · simp only [List.mem_singleton] at hc; subst hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> exact M.svar_lt (by omega) _ hp _
    · simp at hc
  · simp only [initCNF, List.mem_append, List.mem_singleton, List.mem_flatMap,
      List.mem_range] at hc
    rcases hc with rfl | ⟨k, -, p, hp, hc⟩
    · simp only [List.mem_singleton] at hl; subst hl; exact M.cvar_lt (Nat.zero_le _) _
    · unfold initCell at hc
      rcases hci : M.cellInit k p with _ | o
      · rw [hci] at hc
        obtain ⟨rfl, hp1, hp2⟩ := M.cellInit_none hci
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        · rcases hl with rfl | rfl | rfl <;> exact M.svar_lt (Nat.zero_le _) _ hp _
        · rcases hl with rfl | rfl
          · exact M.svar_lt (Nat.zero_le _) _ hp _
          · exact M.svar_lt (Nat.zero_le _) _ (by omega) _
      · rw [hci] at hc
        simp only [List.mem_singleton] at hc; subst hc
        simp only [List.mem_singleton] at hl; subst hl
        exact M.svar_lt (Nat.zero_le _) _ hp _
  · simp only [transCNF, List.mem_flatMap, List.mem_range, List.mem_cons] at hc
    obtain ⟨t, ht, c, -, h, -, hc⟩ := hc
    have hprem : ∀ l ∈ M.prem t c h, l.1 < M.nV := by
      intro l hl
      simp only [prem, List.mem_cons, List.mem_map] at hl
      rcases hl with rfl | ⟨k, -, rfl⟩
      · exact M.cvar_lt (by omega) _
      · exact M.svar_lt (by omega) _ hW0 _
    rcases hc with rfl | hc
    · rcases List.mem_append.1 hl with hl | hl
      · exact hprem l hl
      · simp only [List.mem_singleton] at hl; subst hl; exact M.cvar_lt (by omega) _
    · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hc
      obtain ⟨k, -, p, hp, o, -, rfl⟩ := hc
      rcases List.mem_append.1 hl with hl | hl
      · exact hprem l hl
      · generalize (M.step c h).2 k = a at hl
        cases a with
        | keep =>
          simp only [cellConcl, List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> exact M.svar_lt (by omega) _ hp _
        | pop =>
          simp only [cellConcl] at hl
          split_ifs at hl with hpW
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact M.svar_lt (by omega) _ hpW _
            · exact M.svar_lt (by omega) _ hp _
          · simp only [List.mem_singleton] at hl; subst hl; exact M.svar_lt (by omega) _ hp _
        | push b =>
          simp only [cellConcl] at hl
          split_ifs at hl with hp0
          · simp only [List.mem_singleton] at hl; subst hl; exact M.svar_lt (by omega) _ hW0 _
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact M.svar_lt (by omega) _ (by omega) _
            · exact M.svar_lt (by omega) _ hp _
  · simp only [accCNF, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl; exact M.cvar_lt le_rfl _
    · simp only [List.mem_singleton] at hl; subst hl; exact M.svar_lt le_rfl _ hW0 _

/-- The clauses are nonempty when some control is accepting. -/
theorem cnf_ne_nil (hacc : M.acc ≠ []) : ∀ c ∈ M.cnf, c ≠ [] := by
  intro cl hcl
  simp only [cnf, List.mem_append] at hcl
  rcases hcl with (((hc | hc) | hc) | hc) | hc
  · simp only [amoC, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨t, ht, c, -, c', -, hc⟩ := hc
    split_ifs at hc
    · simp only [List.mem_singleton] at hc; subst hc; simp
    · simp at hc
  · simp only [amoS, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨t, ht, k, -, p, hp, o, -, o', -, hc⟩ := hc
    split_ifs at hc
    · simp only [List.mem_singleton] at hc; subst hc; simp
    · simp at hc
  · simp only [initCNF, List.mem_append, List.mem_singleton, List.mem_flatMap,
      List.mem_range] at hc
    rcases hc with rfl | ⟨k, -, p, hp, hc⟩
    · simp
    · unfold initCell at hc
      rcases hci : M.cellInit k p with _ | o
      · rw [hci] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp
      · rw [hci] at hc
        simp only [List.mem_singleton] at hc; subst hc; simp
  · simp only [transCNF, List.mem_flatMap, List.mem_range, List.mem_cons] at hc
    obtain ⟨t, ht, c, -, h, -, hc⟩ := hc
    rcases hc with rfl | hc
    · simp [prem]
    · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hc
      obtain ⟨k, -, p, hp, o, -, rfl⟩ := hc
      simp [prem]
  · simp only [accCNF, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simpa using hacc
    · simp

end Tab

end HTN.NPHard
