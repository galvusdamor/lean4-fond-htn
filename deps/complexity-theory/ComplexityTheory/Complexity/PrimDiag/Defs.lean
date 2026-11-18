import ComplexityTheory.Complexity.PrimDiag.Universal
/-!
# The diagonal language: definitions and primitive recursiveness

The language `HTN.PrimDiag.dg` defeats, at infinitely many lengths each, every nondeterministic
verifier of Cobham's class with polynomial advice and certificates of length up to an iterated
exponential `tow j (p n)` of a polynomial (`ComplexityTheory/Complexity/PrimDiag/Diag.lean`).  This
file defines it and proves it **primitive recursive** (`HTN.PrimDiag.primrec_dg`).

At length `n` the candidate `cand n` (read off the first component of `Nat.unpair n`) consists of
a program for the universal evaluator `uevalB`, a number `m` (running time `(|args| + m) ^ m`,
advice length at most `(n + m) ^ m`), a level `j` and the coefficient list of a polynomial `p`
(certificates of length at most `tow j (p n)`).  With `R = (n + m) ^ m` and `K = R + 1`, the
language writes on the first `K` words of length `n` the first truth table `f < 2 ^ K` that no
advice string of length at most `R` produces (`fstar`); there are fewer than `2 ^ K` advice
strings, so such a table exists.  Every search is bounded, which is what makes the language
primitive recursive.
-/

namespace HTN.PrimDiag

open HTN.PTime HTN.PTime.CobhamTM HTN.PTime.CobhamTM.Prog

/-! ### Bounded searches -/

/-- "Some element of the list satisfies `f`". -/
def anyB {β : Type} (l : List β) (f : β → Bool) : Bool := l.foldr (fun b s => f b || s) false

/-- "Every element of the list satisfies `f`". -/
def allB {β : Type} (l : List β) (f : β → Bool) : Bool := l.foldr (fun b s => f b && s) true

theorem anyB_eq_true {β : Type} {l : List β} {f : β → Bool} :
    anyB l f = true ↔ ∃ b ∈ l, f b = true := by
  induction l with
  | nil => simp [anyB]
  | cons a l ih => simp only [anyB, List.foldr_cons, Bool.or_eq_true, List.mem_cons] at ih ⊢; rw [ih]; aesop

theorem allB_eq_true {β : Type} {l : List β} {f : β → Bool} :
    allB l f = true ↔ ∀ b ∈ l, f b = true := by
  induction l with
  | nil => simp [allB]
  | cons a l ih => simp only [allB, List.foldr_cons, Bool.and_eq_true, List.mem_cons] at ih ⊢; rw [ih]; aesop

/-- The first element of the list on which `p` fails (`0` if there is none). -/
def findF (l : List ℕ) (p : ℕ → Bool) : ℕ := l.foldr (fun f acc => cond (p f) acc f) 0

theorem findF_spec {l : List ℕ} {p : ℕ → Bool} (h : ∃ f ∈ l, p f = false) :
    findF l p ∈ l ∧ p (findF l p) = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [findF, List.foldr_cons] at ih ⊢
    cases ha : p a
    · simp [ha]
    · simp only [cond_true]
      obtain ⟨f, hf, hpf⟩ := h
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [ha] at hpf; cases hpf
      · obtain ⟨h1, h2⟩ := ih ⟨f, hf, hpf⟩
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩

variable {α β : Type} [Primcodable α] [Primcodable β]

theorem primrec_anyB {l : α → List β} {f : α → β → Bool} (hl : Primrec l) (hf : Primrec₂ f) :
    Primrec fun a => anyB (l a) (f a) :=
  Primrec.list_foldr hl (Primrec.const false)
    (Primrec.or.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem primrec_allB {l : α → List β} {f : α → β → Bool} (hl : Primrec l) (hf : Primrec₂ f) :
    Primrec fun a => allB (l a) (f a) :=
  Primrec.list_foldr hl (Primrec.const true)
    (Primrec.and.comp (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem primrec_findF {l : α → List ℕ} {p : α → ℕ → Bool} (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec fun a => findF (l a) (p a) :=
  Primrec.list_foldr hl (Primrec.const 0)
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)).to₂

/-! ### Arithmetic -/

theorem primrec_npow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := by
  have h : Primrec fun p : ℕ × ℕ => Nat.rec (motive := fun _ => ℕ) 1
      (fun y IH => (fun (p : ℕ × ℕ) (q : ℕ × ℕ) => p.1 * q.2) p (y, IH)) p.2 :=
    Primrec.nat_rec' Primrec.snd (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂
  refine Primrec₂.mk (h.of_eq fun p => ?_)
  obtain ⟨a, n⟩ := p
  simp only
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ← ih]; ring

/-- The iterated exponential: `tow 0 x = x`, `tow (j + 1) x = 2 ^ tow j x`. -/
def tow : ℕ → ℕ → ℕ
  | 0, x => x
  | j + 1, x => 2 ^ tow j x

theorem tow_eq_iterate (j x : ℕ) : tow j x = (fun y => 2 ^ y)^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ← ih]; rfl

theorem primrec_tow : Primrec₂ tow := by
  refine Primrec₂.mk (Primrec.of_eq (Primrec.nat_iterate Primrec.fst Primrec.snd
    (primrec_npow.comp (Primrec.const 2) Primrec.snd).to₂) fun p => ?_)
  rw [tow_eq_iterate]

/-- A polynomial given by its list of coefficients (constant coefficient first). -/
def polyL (l : List ℕ) (n : ℕ) : ℕ := l.foldr (fun a s => a + n * s) 0

theorem primrec_polyL : Primrec₂ polyL :=
  Primrec.list_foldr Primrec.fst (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

/-- Bit `i` of `f`. -/
def bitB (f i : ℕ) : Bool := f / 2 ^ i % 2 == 1

theorem primrec_bitB : Primrec₂ bitB :=
  Primrec.beq.comp (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.fst
    (primrec_npow.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 2)) (Primrec.const 1)

/-- The number written by a word in binary, least significant bit first. -/
def nob (x : List Bool) : ℕ := x.foldr (fun b s => (if b then 1 else 0) + 2 * s) 0

theorem primrec_nob : Primrec nob :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.const true)) (Primrec.const 1) (Primrec.const 0))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂

/-- The word of length `n` writing `i` (modulo `2 ^ n`) in binary. -/
def padW (n i : ℕ) : List Bool := (List.range n).map fun k => bitB i k

theorem primrec_padW : Primrec₂ padW :=
  Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (primrec_bitB.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

/-! ### Words -/

/-- All words of length `m`. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (words m).flatMap fun y => [false :: y, true :: y]

theorem words_eq_iterate (m : ℕ) :
    words m = (fun L : List (List Bool) => L.flatMap fun y => [false :: y, true :: y])^[m] [[]] := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ← ih]; rfl

theorem primrec_words : Primrec words :=
  Primrec.of_eq (Primrec.nat_iterate Primrec.id (Primrec.const [[]])
    (Primrec.list_flatMap Primrec.snd
      (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
        (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
          (Primrec.const []))).to₂).to₂) fun m => (words_eq_iterate m).symm

/-- All words of length at most `B`. -/
def upTo (B : ℕ) : List (List Bool) := (List.range (B + 1)).flatMap words

theorem primrec_upTo : Primrec upTo :=
  Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ) (primrec_words.comp Primrec.snd).to₂

/-! ### Candidates and the diagonal language -/

/-- A candidate: a program for `uevalB` with its numbers of stacks and arguments, the exponent
`m`, the level `j` and the coefficients of the certificate polynomial. -/
abbrev Cand : Type := (List Instr × ℕ × ℕ) × (ℕ × ℕ × List ℕ)

/-- The candidate attacked at length `n`. -/
def cand (n : ℕ) : Cand := (Encodable.decode (α := Cand) n.unpair.1).getD default

theorem primrec_cand : Primrec cand :=
  Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.const default)

/-- The size of a list of arguments (its longest entry). -/
theorem primrec_argSize : Primrec argSize := by
  have : Primrec fun args : Args => (args.map List.length).foldr (fun a s => max a s) 0 :=
    Primrec.list_foldr (Primrec.list_map Primrec.id (Primrec.list_length.comp Primrec.snd).to₂)
      (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact this.of_eq fun args => rfl

/-- The predicate of the candidate, run for `(|args| + m) ^ m` steps. -/
def Vc (c : Cand) (args : Args) : Bool :=
  uevalB c.1.1 c.1.2.1 c.1.2.2 ((argSize args + c.2.1) ^ c.2.1) args

theorem primrec_Vc : Primrec₂ Vc :=
  primrec_uevalB.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
    (Primrec.pair (primrec_npow.comp (Primrec.nat_add.comp (primrec_argSize.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd))

/-- The advice bound `(n + m) ^ m` of a candidate. -/
def Rc (c : Cand) (n : ℕ) : ℕ := (n + c.2.1) ^ c.2.1

theorem primrec_Rc : Primrec₂ Rc :=
  primrec_npow.comp (Primrec.nat_add.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))

/-- The certificate bound `tow j (p n)` of a candidate. -/
def Bc (c : Cand) (n : ℕ) : ℕ := tow c.2.2.1 (polyL c.2.2.2 n)

theorem primrec_Bc : Primrec₂ Bc :=
  primrec_tow.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    (primrec_polyL.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.snd)

/-- The candidate's answer on `y` with advice `a`: some certificate is accepted. -/
def gc (c : Cand) (n : ℕ) (a y : List Bool) : Bool :=
  anyB (upTo (Bc c n)) fun w => Vc c [y, a, w]

theorem primrec_gc : Primrec fun x : (Cand × ℕ) × (List Bool × List Bool) =>
    gc x.1.1 x.1.2 x.2.1 x.2.2 := by
  have hargs : Primrec fun z : ((Cand × ℕ) × (List Bool × List Bool)) × List Bool =>
      [z.1.2.2, z.1.2.1, z.2] :=
    Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
  have hf : Primrec₂ fun (x : (Cand × ℕ) × (List Bool × List Bool)) (w : List Bool) =>
      Vc x.1.1 [x.2.2, x.2.1, w] :=
    (primrec_Vc.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) hargs).to₂
  have hl : Primrec fun x : (Cand × ℕ) × (List Bool × List Bool) => upTo (Bc x.1.1 x.1.2) :=
    primrec_upTo.comp (primrec_Bc.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))
  exact primrec_anyB hl hf

/-- The table `f` (on the first `R + 1` words of length `n`) is produced by some advice of length
at most `R`. -/
def realizedB (c : Cand) (n f : ℕ) : Bool :=
  anyB (upTo (Rc c n)) fun a =>
    allB (List.range (Rc c n + 1)) fun i => cond (bitB f i) (gc c n a (padW n i)) (!gc c n a (padW n i))

theorem primrec_realizedB : Primrec fun x : (Cand × ℕ) × ℕ => realizedB x.1.1 x.1.2 x.2 := by
  have hleaf : Primrec₂ fun (z : ((Cand × ℕ) × ℕ) × List Bool) (i : ℕ) =>
      cond (bitB z.1.2 i) (gc z.1.1.1 z.1.1.2 z.2 (padW z.1.1.2 i))
        (!gc z.1.1.1 z.1.1.2 z.2 (padW z.1.1.2 i)) := by
    have hg : Primrec fun y : (((Cand × ℕ) × ℕ) × List Bool) × ℕ =>
        gc y.1.1.1.1 y.1.1.1.2 y.1.2 (padW y.1.1.1.2 y.2) := by
      have h1 : Primrec fun y : (((Cand × ℕ) × ℕ) × List Bool) × ℕ =>
          ((y.1.1.1.1, y.1.1.1.2), (y.1.2, padW y.1.1.1.2 y.2)) := Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.pair (Primrec.snd.comp Primrec.fst)
          (primrec_padW.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            Primrec.snd))
      exact (primrec_gc.comp h1).of_eq fun _ => rfl
    exact (Primrec.cond (primrec_bitB.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      Primrec.snd) hg (Primrec.not.comp hg)).to₂
  have hrow : Primrec₂ fun (x : (Cand × ℕ) × ℕ) (a : List Bool) =>
      allB (List.range (Rc x.1.1 x.1.2 + 1)) fun i =>
        cond (bitB x.2 i) (gc x.1.1 x.1.2 a (padW x.1.2 i)) (!gc x.1.1 x.1.2 a (padW x.1.2 i)) :=
    (primrec_allB (Primrec.list_range.comp (Primrec.succ.comp (primrec_Rc.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))) hleaf).to₂
  have hl : Primrec fun x : (Cand × ℕ) × ℕ => upTo (Rc x.1.1 x.1.2) :=
    primrec_upTo.comp (primrec_Rc.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))
  exact primrec_anyB hl hrow

/-- The first table that no advice produces. -/
def fstar (c : Cand) (n : ℕ) : ℕ := findF (List.range (2 ^ (Rc c n + 1))) (realizedB c n)

theorem primrec_fstar : Primrec₂ fstar := by
  unfold fstar
  exact primrec_findF (Primrec.list_range.comp (primrec_npow.comp (Primrec.const 2)
    (Primrec.succ.comp (primrec_Rc.comp Primrec.fst Primrec.snd))))
    (primrec_realizedB.comp (Primrec.pair Primrec.fst Primrec.snd)).to₂

/-- **The diagonal language**: on a word `x` of length `n` whose binary value `i` is below
`R + 1`, bit `i` of the first unproduced table. -/
def dg (x : List Bool) : Bool :=
  decide (nob x < Rc (cand x.length) x.length + 1) && bitB (fstar (cand x.length) x.length) (nob x)

/-- **The diagonal language is primitive recursive.** -/
theorem primrec_dg : Primrec dg := by
  unfold dg
  have hc : Primrec fun x : List Bool => cand x.length := primrec_cand.comp Primrec.list_length
  refine Primrec.and.comp ?_ (primrec_bitB.comp (primrec_fstar.comp hc Primrec.list_length)
    primrec_nob)
  have hp : PrimrecPred fun x : List Bool => nob x < Rc (cand x.length) x.length + 1 :=
    Primrec.nat_lt.comp primrec_nob (Primrec.succ.comp (primrec_Rc.comp hc Primrec.list_length))
  exact (Primrec.ite hp (Primrec.const true) (Primrec.const false)).of_eq fun x => by
    by_cases h : nob x < Rc (cand x.length) x.length + 1 <;> simp [h]

end HTN.PrimDiag
