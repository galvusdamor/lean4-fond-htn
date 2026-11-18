import FondHtn.HardMP.Sem
import FondHtn.HardMP.Classes
/-!
# Grammars of instructions and their list game

The hardness construction of `FondHtn/TOHard2/` is a *grammar*: named instructions (lists of
alternative action specifications `FOND.HardMP.ASpec`, as in `FondHtn/HardMP/Encoding.lean`) and
named nonterminals with sequence bodies over symbols `(false, m)` (instruction `m`) and
`(true, m)` (nonterminal `m`).

* `FOND.TOHard2.LGH` — the leftmost list game of a grammar on configurations
  (`FOND.HardMP.Cfg`), graded by height; `FOND.TOHard2.LG` its ungraded version.  The
  calculus: sequential composition (`lgh_append`, `LG.append'`), programs of instructions
  (`lgh_prog`, `LG.prog`).
* `FOND.TOHard2.compile` — the FOND description of a grammar: instruction `m` becomes the
  compound task `2 m` with one single-action method per alternative, nonterminal `m` the
  compound task `2 m + 1`.
* **`FOND.TOHard2.mpStrong_compile_iff`** — strong method-based solvability of the compiled
  description is the list game of the grammar (via `FOND.Problem.mpStrongSolvable_iff_lrunH`).
* `FOND.TOHard2.compile_valid`, `FOND.TOHard2.compile_TO` — the compiled description is well
  formed and totally ordered.
-/

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

/-! ## Grammars -/

/-- A grammar: named instructions and named nonterminals with their bodies. -/
structure Gram where
  /-- The instructions (names must be distinct). -/
  insL : List (ℕ × List ASpec)
  /-- The methods of the nonterminals. -/
  methL : List (ℕ × List (Bool × ℕ))

/-- The symbols of a list of named instructions. -/
def syms (prog : List (ℕ × List ASpec)) : List (Bool × ℕ) := prog.map fun p => (false, p.1)

@[simp] theorem syms_nil : syms [] = [] := rfl
@[simp] theorem syms_cons (p : ℕ × List ASpec) (prog : List (ℕ × List ASpec)) :
    syms (p :: prog) = (false, p.1) :: syms prog := rfl
@[simp] theorem syms_append (p q : List (ℕ × List ASpec)) : syms (p ++ q) = syms p ++ syms q := by
  simp [syms]

/-- The instructions of a list of named instructions. -/
def inss (prog : List (ℕ × List ASpec)) : List (List ASpec) := prog.map Prod.snd

@[simp] theorem inss_nil : inss [] = [] := rfl
@[simp] theorem inss_cons (p : ℕ × List ASpec) (prog : List (ℕ × List ASpec)) :
    inss (p :: prog) = p.2 :: inss prog := rfl
@[simp] theorem inss_append (p q : List (ℕ × List ASpec)) : inss (p ++ q) = inss p ++ inss q := by
  simp [inss]

variable (G : Gram)

/-- **The list game of a grammar**, graded by height, with postcondition `Φ`. -/
inductive LGH : ℕ → List (Bool × ℕ) → Cfg → Set Cfg → Prop
  | nil {n : ℕ} {c : Cfg} {Φ : Set Cfg} (h : c ∈ Φ) : LGH n [] c Φ
  | ins {n m : ℕ} {I : List ASpec} {a : ASpec} {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg}
      (hI : (m, I) ∈ G.insL) (ha : a ∈ I) (happ : a.App c)
      (hall : ∀ c' ∈ a.Out c, LGH n xs c' Φ) : LGH (n + 1) ((false, m) :: xs) c Φ
  | comp {n m : ℕ} {bs xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg}
      (hb : (m, bs) ∈ G.methL) (h : LGH n (bs ++ xs) c Φ) : LGH (n + 1) ((true, m) :: xs) c Φ

/-- The ungraded list game. -/
def LG (xs : List (Bool × ℕ)) (c : Cfg) (Φ : Set Cfg) : Prop := ∃ n, LGH G n xs c Φ

variable {G}

theorem LGH.mono {n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg} (h : LGH G n xs c Φ) :
    ∀ {n' : ℕ} {Ψ : Set Cfg}, n ≤ n' → Φ ⊆ Ψ → LGH G n' xs c Ψ := by
  induction h with
  | nil h => exact fun _ hΦ => .nil (hΦ h)
  | ins hI ha happ _ ih =>
    intro n' Ψ hn hΦ
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .ins hI ha happ fun c' hc' => ih c' hc' (by omega) hΦ
  | comp hb _ ih =>
    intro n' Ψ hn hΦ
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .comp hb (ih (by omega) hΦ)

theorem not_lgh_zero {y : Bool × ℕ} {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg} :
    ¬ LGH G 0 (y :: xs) c Φ := fun h => by cases h

theorem lgh_nil_iff {n : ℕ} {c : Cfg} {Φ : Set Cfg} : LGH G n [] c Φ ↔ c ∈ Φ :=
  ⟨fun h => by cases h with | nil h => exact h, fun h => .nil h⟩

theorem lgh_comp_iff {n m : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg} :
    LGH G (n + 1) ((true, m) :: xs) c Φ ↔ ∃ bs, (m, bs) ∈ G.methL ∧ LGH G n (bs ++ xs) c Φ :=
  ⟨fun h => by cases h with | comp hb h => exact ⟨_, hb, h⟩, fun ⟨_, hb, h⟩ => .comp hb h⟩

/-- Instruction names are distinct. -/
def Gram.InsNodup (G : Gram) : Prop := (G.insL.map Prod.fst).Nodup

theorem Gram.InsNodup.uniq {G : Gram} (hnd : G.InsNodup) {m : ℕ} {I I' : List ASpec}
    (h : (m, I) ∈ G.insL) (h' : (m, I') ∈ G.insL) : I = I' := by
  have := List.inj_on_of_nodup_map hnd h h' rfl
  simpa using congrArg Prod.snd this

theorem lgh_ins_iff (hnd : G.InsNodup) {n m : ℕ} {I : List ASpec} (hI : (m, I) ∈ G.insL)
    {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg} :
    LGH G (n + 1) ((false, m) :: xs) c Φ ↔ c ∈ wpI I {c' | LGH G n xs c' Φ} := by
  constructor
  · intro h
    cases h with
    | ins hI' ha happ hall =>
      rw [hnd.uniq hI' hI] at ha
      exact ⟨_, ha, happ, hall⟩
  · rintro ⟨a, ha, happ, hall⟩
    exact .ins hI ha happ hall

/-- **Sequential composition**, soundness direction. -/
theorem lgh_append {n : ℕ} {l : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg} (h : LGH G n l c Φ) :
    ∀ {xs ys : List (Bool × ℕ)}, l = xs ++ ys → LGH G n xs c {c' | LGH G n ys c' Φ} := by
  induction h with
  | @nil n c Φ hs =>
    intro xs ys he
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 he.symm
    exact .nil (.nil hs)
  | @ins n m I a l c Φ hI ha happ hall ih =>
    intro xs ys he
    rcases xs with _ | ⟨y, xs⟩
    · exact .nil (by rw [List.nil_append] at he; rw [← he]; exact .ins hI ha happ hall)
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .ins hI ha happ fun c' hc' =>
        (ih c' hc' rfl).mono (by omega) fun _ h' => h'.mono (by omega) le_rfl
  | @comp n m bs l c Φ hb h ih =>
    intro xs ys he
    rcases xs with _ | ⟨y, xs⟩
    · exact .nil (by rw [List.nil_append] at he; rw [← he]; exact .comp hb h)
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .comp hb ((ih (by rw [List.append_assoc])).mono (by omega)
        fun _ h' => h'.mono (by omega) le_rfl)

/-- **Sequential composition**, graded completeness direction. -/
theorem lgh_append' {n m : ℕ} {xs ys : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg}
    (h : LGH G n xs c {c' | LGH G m ys c' Φ}) : LGH G (n + m) (xs ++ ys) c Φ := by
  generalize hΨ : {c' | LGH G m ys c' Φ} = Ψ at h
  induction h with
  | nil h => subst hΨ; exact (show LGH G m ys _ Φ from h).mono (by omega) le_rfl
  | ins hI ha happ _ ih =>
    rw [List.cons_append, show ∀ k, k + 1 + m = k + m + 1 from fun k => by omega]
    exact .ins hI ha happ fun c' hc' => ih c' hc' hΨ
  | comp hb _ ih =>
    rw [List.cons_append, show ∀ k, k + 1 + m = k + m + 1 from fun k => by omega]
    exact .comp hb (by rw [← List.append_assoc]; exact ih hΨ)

/-! ## The ungraded game -/

theorem exists_bound {α : Type} {P : α → ℕ → Prop} (hP : ∀ x n n', n ≤ n' → P x n → P x n') :
    ∀ l : List α, (∀ x ∈ l, ∃ n, P x n) → ∃ N, ∀ x ∈ l, P x N
  | [], _ => ⟨0, by simp⟩
  | x :: l, h => by
    obtain ⟨n, hn⟩ := h x (by simp)
    obtain ⟨N, hN⟩ := exists_bound hP l fun y hy => h y (by simp [hy])
    refine ⟨max n N, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hP _ _ _ (le_max_left _ _) hn
    · exact hP _ _ _ (le_max_right _ _) (hN y hy)

theorem LG.nil {c : Cfg} {Φ : Set Cfg} (h : c ∈ Φ) : LG G [] c Φ := ⟨0, .nil h⟩

theorem LG.mono {xs : List (Bool × ℕ)} {c : Cfg} {Φ Ψ : Set Cfg} (h : LG G xs c Φ) (hΦ : Φ ⊆ Ψ) :
    LG G xs c Ψ := let ⟨n, hn⟩ := h; ⟨n, hn.mono le_rfl hΦ⟩

theorem LG.ins {m : ℕ} {I : List ASpec} {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg}
    (hI : (m, I) ∈ G.insL) (h : c ∈ wpI I {c' | LG G xs c' Φ}) : LG G ((false, m) :: xs) c Φ := by
  obtain ⟨a, ha, happ, hall⟩ := h
  obtain ⟨N, hN⟩ := exists_bound (P := fun e n => LGH G n xs (a.eff e c) Φ)
    (fun _ _ _ hn h => h.mono hn le_rfl) a.effs fun e he => hall _ ⟨e, he, rfl⟩
  exact ⟨N + 1, .ins hI ha happ fun c' ⟨e, he, hc'⟩ => hc' ▸ hN e he⟩

theorem LG.comp {m : ℕ} {bs xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg}
    (hb : (m, bs) ∈ G.methL) (h : LG G (bs ++ xs) c Φ) : LG G ((true, m) :: xs) c Φ :=
  let ⟨n, hn⟩ := h; ⟨n + 1, .comp hb hn⟩

/-- **Sequential composition**, ungraded. -/
theorem LG.append' {xs ys : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg}
    (h : LG G xs c {c' | LG G ys c' Φ}) : LG G (xs ++ ys) c Φ := by
  obtain ⟨n, h⟩ := h
  generalize hΨ : {c' | LG G ys c' Φ} = Ψ at h
  induction h with
  | nil h => subst hΨ; simpa using h
  | @ins n m I a xs c Ψ hI ha happ _ ih =>
    exact LG.ins hI ⟨a, ha, happ, fun c' hc' => ih c' hc' hΨ⟩
  | comp hb _ ih =>
    show LG G (_ :: (_ ++ ys)) _ _
    exact LG.comp hb (by rw [← List.append_assoc]; exact ih hΨ)

theorem LG.of_append {xs ys : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg} (h : LG G (xs ++ ys) c Φ) :
    LG G xs c {c' | LG G ys c' Φ} := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, (lgh_append h rfl).mono le_rfl fun c' (hc' : LGH G n ys c' Φ) => (⟨n, hc'⟩ : LG G ys c' Φ)⟩

/-! ## Programs -/

/-- **A program of instructions**, soundness. -/
theorem lgh_prog (hnd : G.InsNodup) {prog : List (ℕ × List ASpec)} (hp : ∀ p ∈ prog, p ∈ G.insL) :
    ∀ {n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg},
      LGH G n (syms prog ++ xs) c Φ → c ∈ wpP (inss prog) {c' | LGH G n xs c' Φ} := by
  induction prog with
  | nil => intro n xs c Φ h; exact h
  | cons p prog ih =>
    intro n xs c Φ h
    rcases n with _ | n
    · exact absurd h not_lgh_zero
    rw [syms_cons, List.cons_append] at h
    have h' := (lgh_ins_iff hnd (hp p (by simp))).1 h
    rw [inss_cons, wpP_cons]
    exact wpI_mono (fun c' hc' => wpP_mono _ (fun c'' hc'' => hc''.mono (by omega) le_rfl)
      (ih (fun q hq => hp q (by simp [hq])) hc')) h'

/-- **A program of instructions**, completeness. -/
theorem LG.prog {prog : List (ℕ × List ASpec)} (hp : ∀ p ∈ prog, p ∈ G.insL) :
    ∀ {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg},
      c ∈ wpP (inss prog) {c' | LG G xs c' Φ} → LG G (syms prog ++ xs) c Φ := by
  induction prog with
  | nil => intro xs c Φ h; exact h
  | cons p prog ih =>
    intro xs c Φ h
    rw [inss_cons, wpP_cons] at h
    rw [syms_cons, List.cons_append]
    exact LG.ins (hp p (by simp)) (wpI_mono (fun c' hc' => ih (fun q hq => hp q (by simp [hq])) hc') h)

theorem lg_prog_iff (hnd : G.InsNodup) {prog : List (ℕ × List ASpec)} (hp : ∀ p ∈ prog, p ∈ G.insL)
    {xs : List (Bool × ℕ)} {c : Cfg} {Φ : Set Cfg} :
    LG G (syms prog ++ xs) c Φ ↔ c ∈ wpP (inss prog) {c' | LG G xs c' Φ} := by
  constructor
  · rintro ⟨n, h⟩
    exact wpP_mono _ (fun c' (hc' : LGH G n xs c' Φ) => (⟨n, hc'⟩ : LG G xs c' Φ)) (lgh_prog hnd hp h)
  · exact LG.prog hp

/-! ## Compilation into a FOND description -/

/-- The label of a symbol in the description: instruction `m` is the compound task `2 m`,
nonterminal `m` the compound task `2 m + 1`. -/
def symL (q : Bool × ℕ) : Bool × ℕ := (true, 2 * q.2 + q.1.toNat)

/-- The actions. -/
def actsG (G : Gram) : List FActDesc :=
  G.insL.flatMap fun p => (List.range p.2.length).map fun alt => toFAct (Nat.pair p.1 alt) (p.2.getI alt)

/-- The methods of the instruction tasks. -/
def insMeths (G : Gram) : List MethodDesc :=
  G.insL.flatMap fun p => (List.range p.2.length).map fun alt => meth (2 * p.1) [(false, Nat.pair p.1 alt)]

/-- The methods of the nonterminals. -/
def ntMeths (G : Gram) : List MethodDesc := G.methL.map fun q => meth (2 * q.1 + 1) (q.2.map symL)

/-- **The compiled description.** -/
def compile (G : Gram) (init : List ℕ) (root : List (Bool × ℕ)) : FProbDesc :=
  ((actsG G, insMeths G ++ ntMeths G), (init, seqTn (root.map symL)))

/-- Well-formed grammars. -/
structure Gram.Good (G : Gram) : Prop where
  nodup : G.InsNodup
  spec : ∀ p ∈ G.insL, ∀ a ∈ p.2, a.WF ∧ a.effs ≠ []

theorem name_toFAct (nm : ℕ) (a : ASpec) : FActDesc.name (toFAct nm a) = nm := rfl

theorem mem_actsG {a : FActDesc} : a ∈ actsG G ↔
    ∃ p ∈ G.insL, ∃ alt < p.2.length, a = toFAct (Nat.pair p.1 alt) (p.2.getI alt) := by
  simp only [actsG, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨fun ⟨p, hp, alt, ha, h⟩ => ⟨p, hp, alt, ha, h.symm⟩,
    fun ⟨p, hp, alt, ha, h⟩ => ⟨p, hp, alt, ha, h.symm⟩⟩

theorem names_actsG_nodup (hnd : G.InsNodup) : ((actsG G).map FActDesc.name).Nodup := by
  have : (actsG G).map FActDesc.name =
      G.insL.flatMap fun p => (List.range p.2.length).map fun alt => Nat.pair p.1 alt := by
    simp [actsG, List.map_flatMap, Function.comp_def, name_toFAct]
  rw [this, List.nodup_flatMap]
  refine ⟨fun p _ => (List.nodup_range).map fun a b h => by simpa using h, ?_⟩
  refine (List.pairwise_map.1 hnd).imp fun {p q} hpq => ?_
  rw [Function.onFun, List.disjoint_left]
  intro x hx hx'
  simp only [List.mem_map, List.mem_range] at hx hx'
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨a', -, h⟩ := hx'
  exact hpq (Nat.pair_eq_pair.1 h).1.symm

theorem δ_compile {init : List ℕ} {root : List (Bool × ℕ)} (hv : (compile G init root).Valid)
    {p : ℕ × List ASpec} (hp : p ∈ G.insL) {alt : ℕ} (halt : alt < p.2.length) :
    (compile G init root).toProblem.δ (Nat.pair p.1 alt) = (toFAct (Nat.pair p.1 alt) (p.2.getI alt)).toAction :=
  FProbDesc.δ_of_mem hv (mem_actsG.2 ⟨p, hp, alt, halt, rfl⟩)

theorem compile_valid (hG : G.Good) (init : List ℕ) (root : List (Bool × ℕ)) :
    (compile G init root).Valid where
  names_nodup := names_actsG_nodup hG.nodup
  effs_ne := by
    intro a ha
    obtain ⟨p, hp, alt, halt, rfl⟩ := mem_actsG.1 ha
    have := (hG.spec p hp _ (getI_memS halt)).2
    simpa [toFAct, FActDesc.effs, ASpec.effs] using this
  tnI := seqTn_valid fun q hq hf => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hq; simp [symL] at hf
  methods := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · simp only [insMeths, List.mem_flatMap, List.mem_map, List.mem_range] at he
      obtain ⟨p, hp, alt, halt, rfl⟩ := he
      refine seqTn_valid fun q hq hf => ?_
      simp only [List.mem_singleton] at hq; subst hq
      exact List.mem_map.2 ⟨_, mem_actsG.2 ⟨p, hp, alt, halt, rfl⟩, rfl⟩
    · simp only [ntMeths, List.mem_map] at he
      obtain ⟨q, -, rfl⟩ := he
      refine seqTn_valid fun r hr hf => ?_
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hr; simp [symL] at hf

theorem seqMeths_compile (init : List ℕ) (root : List (Bool × ℕ)) : SeqMeths (compile G init root) := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · simp only [insMeths, List.mem_flatMap, List.mem_map, List.mem_range] at he
    obtain ⟨p, -, alt, -, rfl⟩ := he; exact ⟨_, _, rfl⟩
  · simp only [ntMeths, List.mem_map] at he
    obtain ⟨q, -, rfl⟩ := he; exact ⟨_, _, rfl⟩

/-- **The compiled description is totally ordered.** -/
theorem compile_TO (init : List ℕ) (root : List (Bool × ℕ)) :
    FClass.TO (compile G init root).toProblem := to_of_seq (seqMeths_compile init root) rfl

/-! ## The bridge -/

theorem lab_symL (q : Bool × ℕ) : toLab (symL q) = Sum.inr (2 * q.2 + q.1.toNat) := by
  simp [symL, toLab]

theorem meth_mem_compile {init : List ℕ} {root : List (Bool × ℕ)} {c : ℕ} {ls : List (Bool × ℕ)} :
    meth c ls ∈ (compile G init root).methods ↔
      (∃ p ∈ G.insL, ∃ alt < p.2.length, c = 2 * p.1 ∧ ls = [(false, Nat.pair p.1 alt)]) ∨
      ∃ q ∈ G.methL, c = 2 * q.1 + 1 ∧ ls = q.2.map symL := by
  simp only [compile, FProbDesc.methods, List.mem_append, insMeths, ntMeths, List.mem_flatMap,
    List.mem_map, List.mem_range, meth_injS]
  constructor
  · rintro (⟨p, hp, alt, halt, h1, h2⟩ | ⟨q, hq, h1, h2⟩)
    · exact Or.inl ⟨p, hp, alt, halt, h1.symm, h2.symm⟩
    · exact Or.inr ⟨q, hq, h1.symm, h2.symm⟩
  · rintro (⟨p, hp, alt, halt, h1, h2⟩ | ⟨q, hq, h1, h2⟩)
    · exact Or.inl ⟨p, hp, alt, halt, h1.symm, h2.symm⟩
    · exact Or.inr ⟨q, hq, h1.symm, h2.symm⟩

section Bridge

variable {init : List ℕ} {root : List (Bool × ℕ)} (hG : G.Good)
  (hv : (compile G init root).Valid)
include hG hv

theorem lgh_of_lrunH : ∀ n {xs : List (Bool × ℕ)} {c : Cfg},
    (compile G init root).toProblem.LRunH n (xs.map (toLab ∘ symL)) c.enc Set.univ →
      LGH G n xs c Set.univ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro xs c h0
    rcases xs with _ | ⟨⟨b, m⟩, xs⟩
    · exact .nil trivial
    rcases n with _ | n
    · exact absurd h0 Problem.not_lrunH_zero_cons
    simp only [List.map_cons, Function.comp_apply, lab_symL] at h0
    obtain ⟨bs, hb, h⟩ := Problem.lrunH_comp_iff.1 h0
    clear h0
    obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff (seqMeths_compile init root)).1 hb
    rcases meth_mem_compile.1 hls with ⟨p, hp, alt, halt, he, rfl⟩ | ⟨q, hq, he, rfl⟩
    · obtain rfl : b = false := by cases b <;> simp at he ⊢; omega
      obtain rfl : m = p.1 := by simp at he; omega
      rcases n with _ | n
      · exact absurd h Problem.not_lrunH_zero_cons
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
        List.cons_append, List.nil_append] at h
      obtain ⟨happ, hall⟩ := Problem.lrunH_prim_iff.1 h
      have hwf := (hG.spec p hp _ (getI_memS halt)).1
      rw [δ_compile hv hp halt, applicable_enc] at happ
      rw [δ_compile hv hp halt, outcomes_enc _ hwf happ] at hall
      refine LGH.mono (.ins hp (getI_memS halt) happ fun c' hc' =>
        ih n (by omega) (hall _ ⟨c', hc', rfl⟩)) (by omega) le_rfl
    · obtain rfl : b = true := by cases b <;> simp at he ⊢; omega
      obtain rfl : m = q.1 := by simp at he; omega
      refine .comp hq (ih n (by omega) ?_)
      simpa [List.map_append, List.map_map] using h

theorem lrunH_of_lgh {n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} (h : LGH G n xs c Set.univ) :
    (compile G init root).toProblem.LRunH (2 * n) (xs.map (toLab ∘ symL)) c.enc Set.univ := by
  generalize hU : (Set.univ : Set Cfg) = U at h
  induction h with
  | nil => exact .nil trivial
  | @ins n m I a xs c Φ hI ha happ hall ih =>
    obtain ⟨alt, halt, rfl⟩ := exists_getI_of_mem ha
    have hwf := (hG.spec _ hI _ ha).1
    simp only [List.map_cons, Function.comp_apply, lab_symL, Bool.toNat_false, add_zero]
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring]
    refine .comp ((seqBodyF_iff (seqMeths_compile init root)).2
      ⟨_, meth_mem_compile.2 (Or.inl ⟨_, hI, alt, halt, rfl, rfl⟩), rfl⟩) ?_
    simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append]
    refine .prim ?_ fun s' hs' => ?_
    · rw [δ_compile hv hI halt, applicable_enc]; exact happ
    · rw [δ_compile hv hI halt, outcomes_enc _ hwf happ] at hs'
      obtain ⟨c', hc', rfl⟩ := hs'
      exact ih c' hc' hU
  | @comp n m bs xs c Φ hb h ih =>
    simp only [List.map_cons, Function.comp_apply, lab_symL, Bool.toNat_true]
    refine LRunH_mono' (.comp ((seqBodyF_iff (seqMeths_compile init root)).2
      ⟨_, meth_mem_compile.2 (Or.inr ⟨_, hb, rfl, rfl⟩), rfl⟩) ?_)
    simpa [List.map_append, List.map_map] using ih hU
where
  LRunH_mono' {k : ℕ} {l : List (ℕ ⊕ ℕ)} {s : Set ℕ}
      (h : (compile G init root).toProblem.LRunH (2 * k + 1) l s Set.univ) :
      (compile G init root).toProblem.LRunH (2 * (k + 1)) l s Set.univ :=
    h.mono (by omega) le_rfl

end Bridge

theorem methods_TO' {D : FProbDesc} (hD : SeqMeths D) :
    ∀ m ∈ D.toProblem.methods, m.subtasks.IsTotallyOrdered := by
  rintro m ⟨e, he, rfl⟩
  obtain ⟨c, ls, rfl⟩ := hD e he
  exact seqTn_isTO ls

theorem mpStrong_iff_lrun' {D : FProbDesc} (hv : D.Valid) (hD : SeqMeths D)
    {ls : List (Bool × ℕ)} (htn : D.tnI = seqTn ls) :
    D.toProblem.MPStrongSolvable ↔
      ∃ n, D.toProblem.LRunH n (ls.map toLab) {f | f ∈ D.init} Set.univ := by
  have hseq : D.toProblem.tnI.IsSeqNet (List.range ls.length) (ls.map toLab) := by
    have : D.toProblem.tnI = (seqTn ls).toTaskNetwork := by
      simp [FProbDesc.toProblem, htn]
    rw [this]; exact isSeqNet_seqTn ls
  exact Problem.mpStrongSolvable_iff_lrunH (FProbDesc.toProblem_wf hv) (methods_TO' hD) hseq

/-- **Strong method-based solvability of a compiled grammar is its list game.** -/
theorem mpStrong_compile_iff (hG : G.Good) {init : List ℕ} {root : List (Bool × ℕ)} {c₀ : Cfg}
    (hinit : {f | f ∈ init} = c₀.enc) :
    (compile G init root).toProblem.MPStrongSolvable ↔ LG G root c₀ Set.univ := by
  have hv := compile_valid hG init root
  rw [mpStrong_iff_lrun' hv (seqMeths_compile init root) (rfl : (compile G init root).tnI = _)]
  have hinit' : {f | f ∈ (compile G init root).init} = c₀.enc := hinit
  rw [hinit', List.map_map]
  constructor
  · rintro ⟨n, h⟩; exact ⟨n, lgh_of_lrunH hG hv n h⟩
  · rintro ⟨n, h⟩; exact ⟨_, lrunH_of_lgh hG hv h⟩

end TOHard2

end FOND
