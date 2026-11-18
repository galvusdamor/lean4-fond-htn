import HtnComplexity.Article.BinCount
/-!
# The tableau-checking problem (Thm. 4.3.6): the description

A totally ordered problem that checks entries of the tableau of a deterministic machine run.  The
state holds two `B`-bit counters, the time `t` and the cell `i` (`HTN.Article.cntS`).  The compound
task `chk a` (`HTN.Article.cChk`) has a refinement from the state `(t, i)` iff the tableau entry at
`(t, i)` has the code `a`, and every refinement restores the state:

* for `t = 0` the entry is the input: one method per cell `c < c₁` of the explicit prefix, checking
  `t = 0` and `i = c`; one per way to check `c₁ ≤ i < c₂` (the cells holding `1`); one per way
  to check `i ≥ c₂` (the blank cells) — comparisons with constants through the highest differing
  bit;
* for `t > 0`, one method per entry `(a, l, c, r)` of the local rule: decrement `t`, check `l`, `c`
  and `r` at the cells `i - 1`, `i`, `i + 1` (moving `i` in between), restore `i` and `t`; the
  cells `0` (no left neighbour) and `2 ^ B - 1` (the right neighbour is blank) have their own
  methods.

Increments and decrements of the counters are compound tasks (`cIncT j` adds `2 ^ j`: set bit `j`,
or clear it and add `2 ^ (j + 1)`).  The root guesses the bits of `i` and checks an accepting
entry at time `t = 2 ^ B - 1`, the time in the initial state.

The machine enters only through the lists `mid`, `lft`, `rgt` (the local rule), `acc` (the
accepting entries) and the codes of the first row (`baseU`, `codeTrue`, `codeNone`).

Action names are `kind + 16 · param` (`HTN.Article.aN`), and the action of a name is computed from
it (`HTN.Article.actOf`), so the action list is the deduplicated list of names used.  Compound names
are `kind + 8 · param` (`HTN.Article.cN`).
-/

namespace HTN

namespace Article

open Syn PTime

/-! ### Names -/

/-- Action names. -/
def aN (kind p : ℕ) : ℕ := kind + 16 * p

/-- Compound names. -/
def cN (kind p : ℕ) : ℕ := kind + 8 * p

def setN (f : ℕ) : ℕ := aN 0 f
def clrN (f : ℕ) : ℕ := aN 1 f
def noopN : ℕ := aN 2 0
def eqN (c : ℕ) : ℕ := aN 3 c
def tzN : ℕ := aN 4 0
def gt1N (j : ℕ) : ℕ := aN 5 j
def gt2N (j : ℕ) : ℕ := aN 6 j
def lt2N (j : ℕ) : ℕ := aN 7 j

def cIncT (j : ℕ) : ℕ := cN 0 j
def cDecT (j : ℕ) : ℕ := cN 1 j
def cIncI (j : ℕ) : ℕ := cN 2 j
def cDecI (j : ℕ) : ℕ := cN 3 j
def cGuess (j : ℕ) : ℕ := cN 4 j
def cChk (a : ℕ) : ℕ := cN 5 a
def rootN : ℕ := cN 6 0

theorem aN_mod {kind p : ℕ} (h : kind < 16) : aN kind p % 16 = kind := by unfold aN; omega
theorem aN_div {kind p : ℕ} (h : kind < 16) : aN kind p / 16 = p := by unfold aN; omega
theorem cN_mod {kind p : ℕ} (h : kind < 8) : cN kind p % 8 = kind := by unfold cN; omega
theorem cN_div {kind p : ℕ} (h : kind < 8) : cN kind p / 8 = p := by unfold cN; omega

/-! ### Actions -/

/-- Bit `m` of `c`, through the binary digits. -/
def bit (c m : ℕ) : Bool := (bitsOfNat c).getI m

theorem bit_eq (c m : ℕ) : bit c m = c.testBit m := getI_bitsOfNat c m

section Acts

variable (B : ℕ)

/-- The bits `m < B` of `i` that are set for `i = c`. -/
def eqPos (c : ℕ) : List ℕ := ((List.range B).filter fun m => bit c m).map iF
/-- The bits `m < B` of `i` that are unset for `i = c`. -/
def eqNeg (c : ℕ) : List ℕ := ((List.range B).filter fun m => !bit c m).map iF
/-- Agreement with `c` above `j`, set bits. -/
def abPos (c j : ℕ) : List ℕ := ((List.range B).filter fun m => decide (j < m) && bit c m).map iF
/-- Agreement with `c` above `j`, unset bits. -/
def abNeg (c j : ℕ) : List ℕ := ((List.range B).filter fun m => decide (j < m) && !bit c m).map iF

variable (c₁ c₂ : ℕ)

/-- **The action of a name.** -/
def actOf (n : ℕ) : ActDesc :=
  if n % 16 = 0 then (n, [], [n / 16], [n / 16], [])
  else if n % 16 = 1 then (n, [n / 16], [], [], [n / 16])
  else if n % 16 = 3 then (n, eqPos B (n / 16), eqNeg B (n / 16), [], [])
  else if n % 16 = 4 then (n, [], (List.range B).map tF, [], [])
  else if n % 16 = 5 then (n, iF (n / 16) :: abPos B c₁ (n / 16), abNeg B c₁ (n / 16), [], [])
  else if n % 16 = 6 then (n, iF (n / 16) :: abPos B c₂ (n / 16), abNeg B c₂ (n / 16), [], [])
  else if n % 16 = 7 then (n, abPos B c₂ (n / 16), iF (n / 16) :: abNeg B c₂ (n / 16), [], [])
  else (n, [], [], [], [])

variable (mx : ℕ)

/-- The action names used. -/
def actNames : List ℕ :=
  ((List.range (2 * B)).flatMap fun f => [setN f, clrN f]) ++ [noopN, tzN] ++
    ((List.range c₁ ++ [c₁, c₂, mx]).map eqN) ++
    (List.range B).flatMap fun j => [gt1N j, gt2N j, lt2N j]

/-- **The actions.** -/
def acts : List ActDesc := (actNames B c₁ c₂ mx).dedup.map (actOf B c₁ c₂)

end Acts

/-! ### Methods -/

/-- A method with a sequence network. -/
def meth (c : ℕ) (body : List (Bool × ℕ)) : MethodDesc := (c, seqTn body)

section Meths

variable (B : ℕ)

/-- The counter methods (increment, decrement, guessing bits of `i`). -/
def ctrMethods : List MethodDesc :=
  (List.range B).flatMap fun j =>
    [meth (cIncT j) [(false, setN (tF j))],
     meth (cIncT j) [(false, clrN (tF j)), (true, cIncT (j + 1))],
     meth (cDecT j) [(false, clrN (tF j))],
     meth (cDecT j) [(false, setN (tF j)), (true, cDecT (j + 1))],
     meth (cIncI j) [(false, setN (iF j))],
     meth (cIncI j) [(false, clrN (iF j)), (true, cIncI (j + 1))],
     meth (cDecI j) [(false, clrN (iF j))],
     meth (cDecI j) [(false, setN (iF j)), (true, cDecI (j + 1))],
     meth (cGuess j) [(false, noopN)],
     meth (cGuess j) [(false, setN (iF j))]]

/-- The body of a middle step. -/
def midBody (q : ℕ × ℕ × ℕ × ℕ) : List (Bool × ℕ) :=
  [(true, cDecT 0), (true, cDecI 0), (true, cChk q.2.1), (true, cIncI 0), (true, cChk q.2.2.1),
    (true, cIncI 0), (true, cChk q.2.2.2), (true, cDecI 0), (true, cIncT 0)]

/-- The body of a step at cell `0`. -/
def lftBody (q : ℕ × ℕ × ℕ) : List (Bool × ℕ) :=
  [(false, eqN 0), (true, cDecT 0), (true, cChk q.2.1), (true, cIncI 0), (true, cChk q.2.2),
    (true, cDecI 0), (true, cIncT 0)]

/-- The body of a step at the last cell `mx`. -/
def rgtBody (mx : ℕ) (q : ℕ × ℕ × ℕ) : List (Bool × ℕ) :=
  [(false, eqN mx), (true, cDecT 0), (true, cDecI 0), (true, cChk q.2.1), (true, cIncI 0),
    (true, cChk q.2.2), (true, cIncT 0)]

/-- The step methods. -/
def stepMethods (mx : ℕ) (mid : List (ℕ × ℕ × ℕ × ℕ)) (lft rgt : List (ℕ × ℕ × ℕ)) :
    List MethodDesc :=
  mid.map (fun q => meth (cChk q.1) (midBody q)) ++ lft.map (fun q => meth (cChk q.1) (lftBody q)) ++
    rgt.map (fun q => meth (cChk q.1) (rgtBody mx q))

/-- The ways to check `i ≥ c` (with `cg` the kind of the `>` actions). -/
def geNames (c : ℕ) (gN : ℕ → ℕ) : List ℕ := eqN c :: ((List.range B).filter fun j => !bit c j).map gN

/-- The ways to check `i < c₂`. -/
def ltNames (c₂ : ℕ) : List ℕ := ((List.range B).filter fun j => bit c₂ j).map lt2N

/-- The methods for the first row. -/
def baseMethods (c₁ c₂ : ℕ) (baseU : List ℕ) (codeTrue codeNone : ℕ) : List MethodDesc :=
  (List.range c₁).map (fun c => meth (cChk (baseU.getI c)) [(false, tzN), (false, eqN c)]) ++
    (geNames B c₁ gt1N).flatMap (fun X => (ltNames B c₂).map fun Y =>
      meth (cChk codeTrue) [(false, tzN), (false, X), (false, Y)]) ++
    (geNames B c₂ gt2N).map (fun X => meth (cChk codeNone) [(false, tzN), (false, X)])

/-- The body of the root: guess the bits of `i`, check `a`. -/
def rootBody (a : ℕ) : List (Bool × ℕ) := ((List.range B).map fun j => (true, cGuess j)) ++ [(true, cChk a)]

/-- The root methods. -/
def rootMethods (acc : List ℕ) : List MethodDesc := acc.map fun a => meth rootN (rootBody B a)

end Meths

/-- The data of the tableau check. -/
structure TabData where
  /-- The number of bits of the counters. -/
  B : ℕ
  /-- The length of the explicit prefix of the input. -/
  c₁ : ℕ
  /-- The end of the cells holding `1`. -/
  c₂ : ℕ
  /-- The codes of the first row on the prefix. -/
  baseU : List ℕ
  codeTrue : ℕ
  codeNone : ℕ
  /-- The local rule. -/
  mid : List (ℕ × ℕ × ℕ × ℕ)
  lft : List (ℕ × ℕ × ℕ)
  rgt : List (ℕ × ℕ × ℕ)
  /-- The accepting entries. -/
  acc : List ℕ
  /-- The last cell, `2 ^ B - 1`. -/
  mx : ℕ

namespace TabData

variable (d : TabData)

/-- The methods. -/
def methods : List MethodDesc :=
  ctrMethods d.B ++ stepMethods d.mx d.mid d.lft d.rgt ++
    baseMethods d.B d.c₁ d.c₂ d.baseU d.codeTrue d.codeNone ++ rootMethods d.B d.acc

/-- **The problem description**: the time counter is `2 ^ B - 1` (all bits set), the cell
counter `0`. -/
def desc : ProbDesc :=
  ((acts d.B d.c₁ d.c₂ d.mx, d.methods), ((List.range d.B).map tF, seqTn [(true, rootN)], [], []))

end TabData

/-! ### The actions of the description -/

theorem find_map_actOf {B c₁ c₂ : ℕ} {l : List ℕ} {n : ℕ} (hn : n ∈ l) :
    (l.map (actOf B c₁ c₂)).find? (fun x => x.name == n) = some (actOf B c₁ c₂ n) := by
  induction l with
  | nil => simp at hn
  | cons a l ih =>
    rw [List.map_cons, List.find?_cons]
    have hname : (actOf B c₁ c₂ a).name = a := by
      unfold actOf ActDesc.name; split_ifs <;> rfl
    by_cases h : a = n
    · subst h; simp [hname]
    · have : ((actOf B c₁ c₂ a).name == n) = false := by simp [hname, h]
      rw [this]
      exact ih ((List.mem_cons.1 hn).resolve_left (Ne.symm h))

theorem name_actOf (B c₁ c₂ n : ℕ) : (actOf B c₁ c₂ n).name = n := by
  unfold actOf ActDesc.name; split_ifs <;> rfl

namespace TabData

variable (d : TabData)

theorem δ_desc {n : ℕ} (hn : n ∈ actNames d.B d.c₁ d.c₂ d.mx) :
    d.desc.toProblem.δ n = (actOf d.B d.c₁ d.c₂ n).toAction := by
  show d.desc.δ n = _
  unfold ProbDesc.δ
  rw [show d.desc.actions = (actNames d.B d.c₁ d.c₂ d.mx).dedup.map (actOf d.B d.c₁ d.c₂) from rfl,
    find_map_actOf (List.mem_dedup.2 hn)]

theorem names_acts : (acts d.B d.c₁ d.c₂ d.mx).map ActDesc.name = (actNames d.B d.c₁ d.c₂ d.mx).dedup := by
  unfold acts
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (actNames d.B d.c₁ d.c₂ d.mx).dedup]
  exact List.map_congr_left fun n _ => name_actOf _ _ _ n

theorem declared_iff {n : ℕ} : d.desc.Declared n ↔ n ∈ actNames d.B d.c₁ d.c₂ d.mx := by
  unfold ProbDesc.Declared
  rw [show d.desc.actions = acts d.B d.c₁ d.c₂ d.mx from rfl, names_acts, List.mem_dedup]

/-! ### The names used -/

theorem setN_mem {f : ℕ} (h : f < 2 * d.B) : setN f ∈ actNames d.B d.c₁ d.c₂ d.mx := by
  unfold actNames; simp only [List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl (Or.inl ⟨f, h, by simp⟩))

theorem clrN_mem {f : ℕ} (h : f < 2 * d.B) : clrN f ∈ actNames d.B d.c₁ d.c₂ d.mx := by
  unfold actNames; simp only [List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl (Or.inl ⟨f, h, by simp⟩))

theorem noopN_mem : noopN ∈ actNames d.B d.c₁ d.c₂ d.mx := by
  unfold actNames; simp

theorem tzN_mem : tzN ∈ actNames d.B d.c₁ d.c₂ d.mx := by
  unfold actNames; simp

theorem eqN_mem {c : ℕ} (h : c < d.c₁ ∨ c = d.c₁ ∨ c = d.c₂ ∨ c = d.mx) :
    eqN c ∈ actNames d.B d.c₁ d.c₂ d.mx := by
  unfold actNames
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false]
  refine Or.inl (Or.inr ⟨c, ?_, rfl⟩)
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem gtlt_mem {j : ℕ} (h : j < d.B) : gt1N j ∈ actNames d.B d.c₁ d.c₂ d.mx ∧
    gt2N j ∈ actNames d.B d.c₁ d.c₂ d.mx ∧ lt2N j ∈ actNames d.B d.c₁ d.c₂ d.mx := by
  unfold actNames
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false]
  exact ⟨Or.inr ⟨j, h, Or.inl rfl⟩, Or.inr ⟨j, h, Or.inr (Or.inl rfl)⟩,
    Or.inr ⟨j, h, Or.inr (Or.inr rfl)⟩⟩

theorem mem_ctr {e : MethodDesc} : e ∈ ctrMethods d.B ↔
    ∃ j < d.B, e = meth (cIncT j) [(false, setN (tF j))] ∨
      e = meth (cIncT j) [(false, clrN (tF j)), (true, cIncT (j + 1))] ∨
      e = meth (cDecT j) [(false, clrN (tF j))] ∨
      e = meth (cDecT j) [(false, setN (tF j)), (true, cDecT (j + 1))] ∨
      e = meth (cIncI j) [(false, setN (iF j))] ∨
      e = meth (cIncI j) [(false, clrN (iF j)), (true, cIncI (j + 1))] ∨
      e = meth (cDecI j) [(false, clrN (iF j))] ∨
      e = meth (cDecI j) [(false, setN (iF j)), (true, cDecI (j + 1))] ∨
      e = meth (cGuess j) [(false, noopN)] ∨
      e = meth (cGuess j) [(false, setN (iF j))] := by
  simp only [ctrMethods, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false]

theorem mem_step {e : MethodDesc} : e ∈ stepMethods d.mx d.mid d.lft d.rgt ↔
    (∃ q ∈ d.mid, e = meth (cChk q.1) (midBody q)) ∨
    (∃ q ∈ d.lft, e = meth (cChk q.1) (lftBody q)) ∨
    (∃ q ∈ d.rgt, e = meth (cChk q.1) (rgtBody d.mx q)) := by
  simp only [stepMethods, List.mem_append, List.mem_map, or_assoc]
  simp only [eq_comm (a := e)]

theorem mem_base {e : MethodDesc} : e ∈ baseMethods d.B d.c₁ d.c₂ d.baseU d.codeTrue d.codeNone ↔
    (∃ c < d.c₁, e = meth (cChk (d.baseU.getI c)) [(false, tzN), (false, eqN c)]) ∨
    (∃ X ∈ geNames d.B d.c₁ gt1N, ∃ Y ∈ ltNames d.B d.c₂,
      e = meth (cChk d.codeTrue) [(false, tzN), (false, X), (false, Y)]) ∨
    (∃ X ∈ geNames d.B d.c₂ gt2N, e = meth (cChk d.codeNone) [(false, tzN), (false, X)]) := by
  simp only [baseMethods, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range, or_assoc]
  simp only [eq_comm (a := e)]

theorem mem_root {e : MethodDesc} : e ∈ rootMethods d.B d.acc ↔
    ∃ a ∈ d.acc, e = meth rootN (rootBody d.B a) := by
  simp only [rootMethods, List.mem_map]
  simp only [eq_comm (a := e)]

/-- The methods, classified. -/
theorem mem_methods {e : MethodDesc} : e ∈ d.methods ↔
    (∃ j < d.B, e = meth (cIncT j) [(false, setN (tF j))] ∨
      e = meth (cIncT j) [(false, clrN (tF j)), (true, cIncT (j + 1))] ∨
      e = meth (cDecT j) [(false, clrN (tF j))] ∨
      e = meth (cDecT j) [(false, setN (tF j)), (true, cDecT (j + 1))] ∨
      e = meth (cIncI j) [(false, setN (iF j))] ∨
      e = meth (cIncI j) [(false, clrN (iF j)), (true, cIncI (j + 1))] ∨
      e = meth (cDecI j) [(false, clrN (iF j))] ∨
      e = meth (cDecI j) [(false, setN (iF j)), (true, cDecI (j + 1))] ∨
      e = meth (cGuess j) [(false, noopN)] ∨
      e = meth (cGuess j) [(false, setN (iF j))]) ∨
    (∃ q ∈ d.mid, e = meth (cChk q.1) (midBody q)) ∨
    (∃ q ∈ d.lft, e = meth (cChk q.1) (lftBody q)) ∨
    (∃ q ∈ d.rgt, e = meth (cChk q.1) (rgtBody d.mx q)) ∨
    (∃ c < d.c₁, e = meth (cChk (d.baseU.getI c)) [(false, tzN), (false, eqN c)]) ∨
    (∃ X ∈ geNames d.B d.c₁ gt1N, ∃ Y ∈ ltNames d.B d.c₂,
      e = meth (cChk d.codeTrue) [(false, tzN), (false, X), (false, Y)]) ∨
    (∃ X ∈ geNames d.B d.c₂ gt2N, e = meth (cChk d.codeNone) [(false, tzN), (false, X)]) ∨
    (∃ a ∈ d.acc, e = meth rootN (rootBody d.B a)) := by
  unfold methods
  simp only [List.mem_append, or_assoc]
  rw [mem_ctr, mem_step, mem_base, mem_root]
  simp only [or_assoc]

/-! ### Well-formedness and the class -/

theorem methods_seq {e : MethodDesc} (he : e ∈ d.methods) : ∃ c body, e = meth c body := by
  rcases (d.mem_methods).1 he with ⟨j, -, h⟩ | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩ |
      ⟨c, -, rfl⟩ | ⟨X, -, Y, -, rfl⟩ | ⟨X, -, rfl⟩ | ⟨a, -, rfl⟩
  · rcases h with h | h | h | h | h | h | h | h | h | h <;> exact ⟨_, _, h⟩
  all_goals exact ⟨_, _, rfl⟩

/-- **All networks of the description are totally ordered.** -/
theorem methods_isTO {e : MethodDesc} (he : e ∈ d.methods) : e.2.toTaskNetwork.IsTotallyOrdered := by
  obtain ⟨c, body, rfl⟩ := d.methods_seq he
  exact seqTn_isTO body

theorem desc_isTO : d.desc.toProblem.IsTO := by
  refine ⟨seqTn_isTO _, fun m hm' => ?_⟩
  obtain ⟨⟨e, he, rfl⟩, -⟩ := hm'
  exact d.methods_isTO he

theorem tF_lt {j B : ℕ} (h : j < B) : tF j < 2 * B := by unfold tF; omega
theorem iF_lt {j B : ℕ} (h : j < B) : iF j < 2 * B := by unfold iF; omega

/-- The primitive labels of the methods are declared. -/
theorem methods_prim (hc₁ : 0 < d.c₁) {e : MethodDesc} (he : e ∈ d.methods) :
    ∃ c body, e = meth c body ∧ ∀ q ∈ body, q.1 = false → q.2 ∈ actNames d.B d.c₁ d.c₂ d.mx := by
  rcases (d.mem_methods).1 he with ⟨j, hj, h⟩ | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩ |
      ⟨c, hc, rfl⟩ | ⟨X, hX, Y, hY, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨a, -, rfl⟩
  · rcases h with h | h | h | h | h | h | h | h | h | h <;> refine ⟨_, _, h, fun q hq hf => ?_⟩ <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq <;>
      rcases hq with rfl | rfl <;> simp at hf ⊢
    all_goals first
      | exact d.setN_mem (tF_lt hj) | exact d.clrN_mem (tF_lt hj)
      | exact d.setN_mem (iF_lt hj) | exact d.clrN_mem (iF_lt hj) | exact d.noopN_mem
  · refine ⟨_, _, rfl, fun q hq hf => ?_⟩
    simp only [midBody, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hf
  · refine ⟨_, _, rfl, fun q hq hf => ?_⟩
    simp only [lftBody, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hf
    exact d.eqN_mem (Or.inl hc₁)
  · refine ⟨_, _, rfl, fun q hq hf => ?_⟩
    simp only [rgtBody, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hf
    exact d.eqN_mem (Or.inr (Or.inr (Or.inr rfl)))
  · refine ⟨_, _, rfl, fun q hq hf => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · exact d.tzN_mem
    · exact d.eqN_mem (Or.inl hc)
  · refine ⟨_, _, rfl, fun q hq hf => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact d.tzN_mem
    · simp only [geNames, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range] at hX
      rcases hX with rfl | ⟨j, ⟨hj, -⟩, rfl⟩
      · exact d.eqN_mem (Or.inr (Or.inl rfl))
      · exact (d.gtlt_mem hj).1
    · simp only [ltNames, List.mem_map, List.mem_filter, List.mem_range] at hY
      obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hY
      exact (d.gtlt_mem hj).2.2
  · refine ⟨_, _, rfl, fun q hq hf => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · exact d.tzN_mem
    · simp only [geNames, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range] at hX
      rcases hX with rfl | ⟨j, ⟨hj, -⟩, rfl⟩
      · exact d.eqN_mem (Or.inr (Or.inr (Or.inl rfl)))
      · exact (d.gtlt_mem hj).2.1
  · refine ⟨_, _, rfl, fun q hq hf => ?_⟩
    simp only [rootBody, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.mem_nil_iff, or_false] at hq
    rcases hq with ⟨j, -, rfl⟩ | rfl <;> simp at hf

/-- **The description is well-formed.** -/
theorem desc_valid (hc₁ : 0 < d.c₁) : d.desc.Valid := by
  refine ⟨?_, seqTn_valid (by simp), fun e he => ?_⟩
  · rw [show d.desc.actions = acts d.B d.c₁ d.c₂ d.mx from rfl, names_acts]
    exact List.nodup_dedup _
  · obtain ⟨c, body, rfl, hb⟩ := d.methods_prim hc₁ he
    exact seqTn_valid fun q hq hf => (d.declared_iff).2 (hb q hq hf)

end TabData

end Article

end HTN
