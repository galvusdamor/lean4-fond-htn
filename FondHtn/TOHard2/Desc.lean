import FondHtn.TOHard2.Auto
/-!
# The grammar of the 2-EXPTIME construction

Parameters `FOND.TOHard2.Par`: the counter width `b` (numbers have `D = 2 ^ b` digits), the
constants `cs` (lists of set digits: `cs[0] = c₁`, `cs[1] = c₂`, `cs[2 + c] = c` for the prefix
cells `c < c₁`) and the local rules of the tableau (`HTN.Article.TabData`).

Nonterminals (`kN t p = Nat.pair t p`):

* `rootN → [Ch(cpy, Ch(bits, K a)), assertTB]` for `a ∈ acc` — commit the cell `i`, claim `(2^D-1, i, a)`;
* `K a` — the **claim** "the entry is `a`" (time and cell digits at the challenged index in
  `TB`, `IB`):
  - `K a → [pick3, Sub(0, j)]` for the middle rule `j` with result `a`, `Sub(0, j) → [assertM L,
    Ch(inc T, Ch(inc I, K l))] | [assertM C, Ch(inc T, Ch(cpy, K c))] | [assertM R, Ch(inc T, Ch(dec I, K r))]`;
  - the rules at cell `0` (`pickCR`, modes `C, R`, then `assertIB false`) and at the last cell
    (`pickLC`, modes `L, C`, then `assertIB true`);
  - the first row: `K (baseU c) → [pickChk…, clrTB, guessIB, setEQ, ce (2 + c)]` (cell `c`),
    `K codeTrue → [Ch(cmp 0 ≥, Ch(cmp 1 <, BB))]`, `K codeNone → [Ch(cmp 1 ≥, Ch(cpy, BB))]` with
    `BB → [pickChk…, clrTB, guessIB]`;
* `Ch(A, y) → [Λ(A, acc, y), fin]` and the left recursion `Λ(A, σ, y)` of the component `A`.

**Deviations from `doc/notes_to_hard.md`.**  The claims are indexed by the entry (`K a`, no
`SYM` fields); the digit types are committed per register by nested left recursions (one chain
per relation, no product automata and no phase bits: the automaton is the grammar of `Λ`;
every claim uses exactly two nested chains, a copy chain where a register is unchanged); the
mode challenge precedes the commitment of the digit types (only the rule must be committed
before the challenge, the digit types only before the challenged index); the first row of the
prefix uses one guessed digit checked against the constant `c` (no chain).
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

/-- **The parameters.** -/
structure Par where
  b : ℕ
  cs : List (List ℕ)
  mid : List (ℕ × ℕ × ℕ × ℕ)
  lft : List (ℕ × ℕ × ℕ)
  rgt : List (ℕ × ℕ × ℕ)
  acc : List ℕ
  baseU : List ℕ
  codeTrue : ℕ
  codeNone : ℕ

instance decEqASpec : DecidableEq ASpec :=
  have _h1 : DecidableEq (List (Option (Bool × ℕ))) := inferInstance
  have _h2 : DecidableEq (List (Option (Bool × ℕ)) × List (Option (Bool × ℕ))) := inferInstance
  have _h3 : DecidableEq (List (List ℕ × List ℕ)) := inferInstance
  have _h4 : DecidableEq (List (List ℕ × List ℕ) × List (Option (Bool × ℕ)) ×
    List (Option (Bool × ℕ))) := inferInstance
  have _h5 : DecidableEq (List ℕ × List (List ℕ × List ℕ) × List (Option (Bool × ℕ)) ×
    List (Option (Bool × ℕ))) := inferInstance
  inferInstanceAs (DecidableEq (List ℕ × List ℕ × List (List ℕ × List ℕ) × List (Option (Bool × ℕ)) ×
    List (Option (Bool × ℕ))))

instance (priority := high) decEqInsP : DecidableEq (ℕ × List ASpec) := fun a b =>
  @instDecidableEqProd _ _ instDecidableEqNat (fun a b => @instDecidableEqList ASpec decEqASpec a b) a b

/-! ## Names -/

/-- Nonterminal names. -/
def kN (t p : ℕ) : ℕ := Nat.pair t p

def rootN : ℕ := kN 0 0
def KN (a : ℕ) : ℕ := kN 1 a
def subN (kind j : ℕ) : ℕ := kN 2 (Nat.pair kind j)
def bbN : ℕ := kN 3 0
def chN (A : Comp) (y : ℕ) : ℕ := kN 4 (Nat.pair A.code y)
def lamN (A : Comp) (σ y : ℕ) : ℕ := kN 5 (Nat.pair A.code (Nat.pair σ y))

@[simp] theorem kN_inj {t p t' p' : ℕ} : kN t p = kN t' p' ↔ t = t' ∧ p = p' := Nat.pair_eq_pair
@[simp] theorem KN_inj {a a' : ℕ} : KN a = KN a' ↔ a = a' := by simp [KN]
@[simp] theorem chN_inj {A A' : Comp} {y y' : ℕ} : chN A y = chN A' y' ↔ A = A' ∧ y = y' := by
  simp only [chN, kN_inj, true_and, Nat.pair_eq_pair]
  exact ⟨fun ⟨h1, h2⟩ => ⟨Comp.code_inj h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1 ▸ rfl, h2⟩⟩
@[simp] theorem lamN_inj {A A' : Comp} {σ σ' y y' : ℕ} :
    lamN A σ y = lamN A' σ' y' ↔ A = A' ∧ σ = σ' ∧ y = y' := by
  simp only [lamN, kN_inj, true_and, Nat.pair_eq_pair]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨Comp.code_inj h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1 ▸ rfl, h2, h3⟩⟩
@[simp] theorem subN_inj {k j k' j' : ℕ} : subN k j = subN k' j' ↔ k = k' ∧ j = j' := by
  simp [subN, Nat.pair_eq_pair]

/-! ## Methods -/

section Meths

variable (P : Par)

/-- The pick of the challenged index. -/
def pickChks : List (ℕ × List ASpec) := (List.range P.b).map pickChkI

/-- The body of a chain nonterminal. -/
def chBody (A : Comp) (y : ℕ) : List (Bool × ℕ) := [(true, lamN A A.aut.acc y), (false, finI.1)]

/-- The left recursion of a component. -/
def lamMeths (A : Comp) (y : ℕ) : List (ℕ × List (Bool × ℕ)) :=
  A.aut.trans.flatMap fun t =>
    (lamN A t.2.2 y, (true, lamN A t.1 y) :: syms (block P.b P.cs t.2.1)) ::
      (if t.1 = A.aut.init then [(lamN A t.2.2 y, (true, y) :: syms (block P.b P.cs t.2.1))] else [])

/-- The methods of a chain. -/
def chMeths (A : Comp) (y : ℕ) : List (ℕ × List (Bool × ℕ)) :=
  (chN A y, chBody A y) :: lamMeths P A y

/-- The components of the challenges `L, C, R`: time increment and the cell relation. -/
def modeBody (m x : ℕ) : List (Bool × ℕ) :=
  (false, (assertMI m).1) ::
    if m = 0 then [(true, chN (.inc true) (chN (.inc false) (KN x)))]
    else if m = 1 then [(true, chN (.inc true) (chN .cpy (KN x)))]
    else [(true, chN (.inc true) (chN (.dec false) (KN x)))]

/-- The chain methods of the challenges for the claim `x`. -/
def modeChMeths (x : ℕ) : List (ℕ × List (Bool × ℕ)) :=
  chMeths P (.inc true) (chN (.inc false) (KN x)) ++ chMeths P (.inc false) (KN x) ++
    chMeths P (.inc true) (chN .cpy (KN x)) ++ chMeths P .cpy (KN x) ++
    chMeths P (.inc true) (chN (.dec false) (KN x)) ++ chMeths P (.dec false) (KN x)

/-- The codes occurring as predecessors. -/
def predCodes : List ℕ :=
  P.mid.flatMap (fun q => [q.2.1, q.2.2.1, q.2.2.2]) ++ P.lft.flatMap (fun q => [q.2.1, q.2.2]) ++
    P.rgt.flatMap (fun q => [q.2.1, q.2.2])

/-- The body of the first-row claims of the cells after the prefix. -/
def bbBody : List (Bool × ℕ) := syms (pickChks P ++ [clrTBI, guessIBI])

/-- The body of the first-row claim of the prefix cell `c`. -/
def prefBody (c : ℕ) : List (Bool × ℕ) :=
  syms (pickChks P ++ [clrTBI, guessIBI, setEQ] ++ actP P.b P.cs (.ce (2 + c)))

/-- The methods of the root. -/
def rootMeths : List (ℕ × List (Bool × ℕ)) :=
  P.acc.map fun a => (rootN, [(true, chN .cpy (chN .bits (KN a))), (false, assertTBI.1)])

/-- The methods of the claims. -/
def kMeths : List (ℕ × List (Bool × ℕ)) :=
  (List.range P.mid.length).map (fun j => (KN (P.mid.getI j).1, [(false, pick3I.1), (true, subN 0 j)])) ++
  (List.range P.lft.length).map (fun j => (KN (P.lft.getI j).1, [(false, pickCRI.1), (true, subN 1 j)])) ++
  (List.range P.rgt.length).map (fun j => (KN (P.rgt.getI j).1, [(false, pickLCI.1), (true, subN 2 j)])) ++
  (List.range P.baseU.length).map (fun c => (KN (P.baseU.getI c), prefBody P c)) ++
  [(KN P.codeTrue, [(true, chN (.cmp 0 true) (chN (.cmp 1 false) bbN))]),
   (KN P.codeNone, [(true, chN (.cmp 1 true) (chN .cpy bbN))])]

/-- The methods of the challenge nonterminals. -/
def subMeths : List (ℕ × List (Bool × ℕ)) :=
  (List.range P.mid.length).flatMap (fun j => [(subN 0 j, modeBody 0 (P.mid.getI j).2.1),
    (subN 0 j, modeBody 1 (P.mid.getI j).2.2.1), (subN 0 j, modeBody 2 (P.mid.getI j).2.2.2)]) ++
  (List.range P.lft.length).flatMap (fun j => [(subN 1 j, modeBody 1 (P.lft.getI j).2.1 ++
      [(false, (assertIBI false).1)]),
    (subN 1 j, modeBody 2 (P.lft.getI j).2.2 ++ [(false, (assertIBI false).1)])]) ++
  (List.range P.rgt.length).flatMap (fun j => [(subN 2 j, modeBody 0 (P.rgt.getI j).2.1 ++
      [(false, (assertIBI true).1)]),
    (subN 2 j, modeBody 1 (P.rgt.getI j).2.2 ++ [(false, (assertIBI true).1)])])

/-- The methods of the chains. -/
def allChMeths : List (ℕ × List (Bool × ℕ)) :=
  (predCodes P).flatMap (modeChMeths P) ++
  (chMeths P (.cmp 0 true) (chN (.cmp 1 false) bbN) ++ chMeths P (.cmp 1 false) bbN ++
    chMeths P (.cmp 1 true) (chN .cpy bbN) ++ chMeths P .cpy bbN) ++
  P.acc.flatMap (fun a => chMeths P .cpy (chN .bits (KN a)) ++ chMeths P .bits (KN a))

/-- **All methods.** -/
def meths : List (ℕ × List (Bool × ℕ)) :=
  rootMeths P ++ kMeths P ++ subMeths P ++ [(bbN, bbBody P)] ++ allChMeths P

/-! ## Instructions -/

/-- All instructions (with repetitions). -/
def insRaw : List (ℕ × List ASpec) :=
  [setEQ, incI P.b, finI, f01I true, f01I false, f10I true, f10I false, bitI false, bitI true,
    cwAI, clrTBI, guessIBI, pick3I, pickLCI, pickCRI, assertMI 0, assertMI 1, assertMI 2,
    assertIBI false, assertIBI true, assertTBI] ++
  (List.range P.b).map cmpI ++ pickChks P ++
  (List.range P.cs.length).flatMap (fun k => actP P.b P.cs (.ce k) ++ actP P.b P.cs (.cw k) ++
    actP P.b P.cs (.cv k))

/-- **The grammar.** -/
def gram : Gram := ⟨(insRaw P).dedup, meths P⟩

/-- The initial facts: the encoding of the clean state (no field set). -/
def initFacts : List ℕ := [curF none]

/-- **The description.** -/
def desc : FProbDesc := compile (gram P) initFacts [(true, rootN)]

end Meths

/-- The initial state. -/
def s₀ : St := ⟨fun _ => false, fun _ => false, false, false, false, false, false, false, false⟩

theorem enc_s₀ : {f | f ∈ initFacts} = s₀.cfg.enc := by
  ext y
  simp only [initFacts, List.mem_singleton, Set.mem_setOf_eq]
  rcases fact_or_curF y with ⟨f, rfl⟩ | ⟨x, rfl⟩
  · rw [Cfg.fact_mem_enc]
    have : s₀.val f = false := by
      simp only [St.val, s₀]; split_ifs <;> rfl
    simp only [St.cfg_val, this, Bool.false_eq_true, iff_false]
    exact fact_ne_curF f none
  · rw [Cfg.curF_mem_enc, St.cfg_cur]
    exact ⟨fun h => (curF_inj h).symm, fun h => by rw [h]⟩

end TOHard2

end FOND
