import HtnComplexity.Complexity.GuardFamily
import ComplexityTheory.Complexity.Counter
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# A positional hardness family: one fact per position of the input word

`HtnComplexity/Complexity/GuardFamily.lean` inhabits the hardness field of the Karp–Lipton
bundle with a family whose instance description lists the *bits* of the input word as the two
facts `0` and `1`.  That encoding is a pure block code: no numeral in it depends on the input,
so the domain description cannot address an individual position of the word.  Every hardness
construction of the literature — the machine encodings behind Theorem 5.1 and Theorem 6.1 of
Alford, Bercher and Aha, *Tight Bounds for HTN Planning* — needs exactly that ability: the
input is written on a tape, one fact per cell, and the domain refers to the cells by index.

This file supplies the missing step: a family whose instance description mentions **one fact
per position** of the word, the position occurring in the fact as a *numeral*.  Writing such a
description in polynomial time means counting inside Cobham's class, which is what
`ComplexityTheory/Complexity/Counter.lean` made possible.

* `HTN.Syn.posFact` / `HTN.Syn.posFacts` — the fact `2 * (k + 1) + b` for the bit `b` at the
  position with `k` bits after it, and the list of those facts for a word.  The offset keeps
  every fact `≥ 2`, so its binary numeral begins with the bit itself and is never empty;
* `HTN.Syn.posSer` — the serialisation of the resulting instance description, given by a
  recursion on the word: `HTN.Syn.instSer_posEnc`;
* `HTN.Syn.cobham_posFnArgs` / `HTN.Syn.polyTimeCode_posEnc` — that recursion is a bounded
  recursion on notation of Cobham's class.  Its step writes the numeral of the current position
  by applying the binary successor to the length of the remaining word
  (`HTN.PTime.incFn`, `HTN.PTime.lenFn`) and serialising the result with the block code
  `HTN.Syn.bstrFn`; the bound is the cube of the padded input, since the serialisation is of
  quadratic length;
* `HTN.Syn.posFamily` — the family itself, for the language `HTN.Syn.LHeadTrue` of words whose
  *first* bit is `true`.  The domain description for length `n` is the guard domain with the
  single guard `2 * n + 1`, i.e. it names the leading position of a word of that length; this
  is a domain that genuinely depends on the input length, as the domains of the machine
  encodings do;
* `HTN.Syn.allTrueFamily` — a second family over the same encoding whose *domain* reads every
  position: for length `n` the guard lists the `n` facts of a `true` bit, so the domain
  description grows with the input length and mentions every position numeral, and the problem
  is solvable exactly when all bits of the word are `true` (`HTN.Syn.LAllTrue`);
* `HTN.Syn.Coded.nonempty_hardFamilyPT_pos_*`, `HTN.Syn.Coded.nonempty_hardFamilyPT_allTrue_*`
  — the two families in the three source classes of the eight open cells.

What is still missing for the constructions of Alford et al. is the *machine* — the actions and
methods simulating a transition — not the encoding of the input, which is what this file
settles.
-/

namespace HTN

namespace Syn

open PTime

/-! ### `bstr` is a block code -/

/-- The block serialising a `true` bit inside a self-delimiting string. -/
def bstrA : List Bool := [true, true]

/-- The block serialising a `false` bit inside a self-delimiting string. -/
def bstrB : List Bool := [true, false]

theorem bstr_eq_blockMap (z : List Bool) :
    bstr z = (z.flatMap fun b => bif b then bstrA else bstrB) ++ [false] := by
  induction z with
  | nil => simp
  | cons b z ih => cases b <;> simp [bstr_cons, ih, bstrA, bstrB, List.flatMap_cons]

/-- The self-delimiting form of the first argument, as a function of Cobham's class. -/
def bstrFn : Fn := compFn (blockFn bstrA bstrB) [proj 0, fun _ => [false]]

theorem bstrFn_apply (args : Args) : bstrFn args = bstr (args.getD 0 []) := by
  rw [bstrFn, compFn]
  simp [blockFn_apply, proj, bstr_eq_blockMap]

theorem cobham_bstrFn : Cobham bstrFn := by
  refine Cobham.comp (cobham_blockFn bstrA bstrB) ?_
  intro k hk
  rcases List.mem_cons.1 hk with rfl | hk
  · exact Cobham.proj 0
  · rw [List.mem_singleton.1 hk]
    exact cobham_const [false]

/-! ### The numeral of the current position -/

/-- The numeral `|x| + 1`, written self-delimitingly, where `x` is the first argument: the
length of the remaining word, incremented, serialised. -/
def posNumFn : Fn := compFn bstrFn [compFn incFnArgs [compFn lenFnArgs [proj 0]]]

theorem posNumFn_apply (args : Args) :
    posNumFn args = bstr (bitsOfNat ((args.getD 0 []).length + 1)) := by
  have h : incFnArgs [lenFnArgs [args.getD 0 []]] = bitsOfNat ((args.getD 0 []).length + 1) := by
    show incFn (lenFn (args.getD 0 [])) = _
    rw [lenFn_eq, incFn_bitsOfNat]
  simp only [posNumFn, compFn, List.map_cons, List.map_nil, bstrFn_apply, List.getD_cons_zero,
    proj]
  rw [h]

theorem cobham_posNumFn : Cobham posNumFn := by
  refine Cobham.comp cobham_bstrFn ?_
  intro k hk
  rw [List.mem_singleton.1 hk]
  refine Cobham.comp cobham_incFnArgs ?_
  intro j hj
  rw [List.mem_singleton.1 hj]
  refine Cobham.comp cobham_lenFnArgs ?_
  intro i hi
  rw [List.mem_singleton.1 hi]
  exact Cobham.proj 0

/-! ### The recursion -/

/-- Concatenation, as a function of Cobham's class. -/
def appendFn : Fn := fun args => args.getD 0 [] ++ args.getD 1 []

theorem cobham_appendFn : Cobham appendFn := cobham_append

/-- The step of the positional encoding at the bit `e`: the marker of a new list entry, the
first two bits of the numeral of the position (the entry marker of the self-delimiting numeral
and the bit `e` itself), the rest of that numeral, and the recursive value. -/
def posStep (e : Bool) : Fn :=
  compFn appendFn [(fun _ => [true, true, e]), compFn appendFn [posNumFn, proj 1]]

theorem posStep_apply (e : Bool) (args : Args) :
    posStep e args =
      true :: true :: e :: (bstr (bitsOfNat ((args.getD 0 []).length + 1)) ++
        args.getD 1 []) := by
  simp [posStep, compFn, appendFn, proj, posNumFn_apply]

theorem cobham_posStep (e : Bool) : Cobham (posStep e) := by
  refine Cobham.comp cobham_appendFn ?_
  intro k hk
  rcases List.mem_cons.1 hk with rfl | hk
  · exact cobham_const [true, true, e]
  · rw [List.mem_singleton.1 hk]
    refine Cobham.comp cobham_appendFn ?_
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact cobham_posNumFn
    · rw [List.mem_singleton.1 hj]
      exact Cobham.proj 1

/-- **The serialisation of the positional encoding**, as a recursion on the word. -/
def posSer : List Bool → List Bool
  | [] => guardTail
  | b :: x => true :: true :: b :: (bstr (bitsOfNat (x.length + 1)) ++ posSer x)

/-- The positional encoding, before the arguments are fixed. -/
def posFnArgs : Fn := brnFn (fun _ => guardTail) (posStep false) (posStep true)

theorem brnAux_pos (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => guardTail) (posStep false) (posStep true) x v = posSer x := by
  have key : ∀ (x : List Bool) (v : Args),
      brnAux (fun _ => guardTail) (posStep false) (posStep true) x v = posSer x := by
    intro x
    induction x with
    | nil => intro v; rfl
    | cons b x ih =>
      intro v
      cases b <;> simp [brnAux, posStep_apply, ih v, posSer]
  intro x
  exact key x v

theorem posFnArgs_apply (args : Args) : posFnArgs args = posSer (args.getD 0 []) := by
  rw [posFnArgs, brnFn, brnAux_pos]

/-! ### The bound of the recursion -/

/-- The padding constant of the bound: long enough that the cube of the padded input dominates
the quadratic length of the serialisation. -/
def posPad : List Bool := List.replicate (guardTail.length + 3) false

@[simp] theorem length_posPad : posPad.length = guardTail.length + 3 := by
  simp [posPad]

/-- The input, padded by a constant string. -/
def posPadFn : Fn := compFn appendFn [proj 0, fun _ => posPad]

theorem length_posPadFn (args : Args) :
    (posPadFn args).length = (args.getD 0 []).length + (guardTail.length + 3) := by
  simp [posPadFn, compFn, appendFn, proj]

theorem cobham_posPadFn : Cobham posPadFn := by
  refine Cobham.comp cobham_appendFn ?_
  intro k hk
  rcases List.mem_cons.1 hk with rfl | hk
  · exact Cobham.proj 0
  · rw [List.mem_singleton.1 hk]
    exact cobham_const posPad

/-- The bound of the recursion: the cube of the padded input. -/
def posBound : Fn := compFn smashFn [compFn smashFn [posPadFn, posPadFn], posPadFn]

theorem length_posBound (args : Args) :
    (posBound args).length =
      ((args.getD 0 []).length + (guardTail.length + 3)) *
        ((args.getD 0 []).length + (guardTail.length + 3)) *
        ((args.getD 0 []).length + (guardTail.length + 3)) := by
  simp [posBound, compFn, smashFn, length_posPadFn]

theorem cobham_posBound : Cobham posBound := by
  refine Cobham.comp Cobham.smash ?_
  intro k hk
  rcases List.mem_cons.1 hk with rfl | hk
  · refine Cobham.comp Cobham.smash ?_
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact cobham_posPadFn
    · rw [List.mem_singleton.1 hj]
      exact cobham_posPadFn
  · rw [List.mem_singleton.1 hk]
    exact cobham_posPadFn

/-- The serialisation is of quadratic length. -/
theorem length_posSer_le (x : List Bool) :
    (posSer x).length ≤ x.length * (2 * x.length + 6) + guardTail.length := by
  induction x with
  | nil => simp [posSer]
  | cons b x ih =>
    have hd : (bitsOfNat (x.length + 1)).length ≤ x.length + 1 :=
      length_bitsOfNat_le (x.length + 1)
    have hlen : (posSer (b :: x)).length =
        3 + (2 * (bitsOfNat (x.length + 1)).length + 1) + (posSer x).length := by
      simp [posSer, length_bstr]
      omega
    rw [hlen, List.length_cons]
    nlinarith [ih, hd, Nat.zero_le x.length]

theorem length_posFnArgs_le (args : Args) :
    (posFnArgs args).length ≤ (posBound args).length := by
  rw [posFnArgs_apply, length_posBound]
  set n := (args.getD 0 []).length with hn
  set T := guardTail.length with hT
  have h := length_posSer_le (args.getD 0 [])
  rw [← hn, ← hT] at h
  nlinarith [h, Nat.zero_le n, Nat.zero_le T]

/-- **The positional encoding belongs to Cobham's class.** -/
theorem cobham_posFnArgs : Cobham posFnArgs :=
  Cobham.brn (cobham_const guardTail) (cobham_posStep false) (cobham_posStep true)
    cobham_posBound length_posFnArgs_le

/-- **The serialisation of the positional encoding is a polynomial-time function of the
word.** -/
theorem polyTimeFun_posSer : PolyTimeFun posSer :=
  CobhamFun.polyTimeFun ⟨posFnArgs, cobham_posFnArgs, fun x => by rw [posFnArgs_apply]; simp⟩

/-! ### The encoding -/

/-- The fact coding the bit `b` at the position with `k` bits after it.  The offset `2` keeps
the fact away from `0` and `1`, so that its binary numeral is `b` followed by the numeral of
`k + 1` — which is what makes the serialisation a recursion with a counter. -/
def posFact (k : ℕ) (b : Bool) : ℕ := 2 * (k + 1) + (if b then 1 else 0)

/-- The facts coding a word: one per position, most significant position first. -/
def posFacts : List Bool → List ℕ
  | [] => []
  | b :: x => posFact x.length b :: posFacts x

@[simp] theorem posFacts_nil : posFacts [] = [] := rfl

@[simp] theorem posFacts_cons (b : Bool) (x : List Bool) :
    posFacts (b :: x) = posFact x.length b :: posFacts x := rfl

@[simp] theorem length_posFacts (x : List Bool) : (posFacts x).length = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [ih]

theorem posFacts_injective : Function.Injective posFacts := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons c y => simp [posFacts] at h
  | cons b x ih =>
    intro y h
    cases y with
    | nil => simp [posFacts] at h
    | cons c y =>
      simp only [posFacts_cons, List.cons.injEq] at h
      obtain ⟨hhead, htail⟩ := h
      have hxy : x = y := ih htail
      subst hxy
      have hbc : b = c := by
        rw [posFact, posFact] at hhead
        cases b <;> cases c <;> simp at hhead ⊢
      rw [hbc]

/-- **The instance description coding a word positionally.** -/
def posEnc (w : List Bool) : InstDesc := guardInst (posFacts w)

theorem posEnc_injective : Function.Injective posEnc := by
  intro w w' h
  exact posFacts_injective (congrArg InstDesc.initList h)

/-- The binary numeral of a fact of the encoding: the bit, followed by the numeral of the
position. -/
theorem bitsOfNat_posFact (k : ℕ) (b : Bool) :
    bitsOfNat (posFact k b) = b :: bitsOfNat (k + 1) := by
  cases b
  · have hm : posFact k false = 2 * k + 1 + 1 := by simp [posFact]; omega
    have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h1 : ¬ ((2 * k + 1 + 1) % 2 = 1) := by omega
    rw [hm, bitsOfNat_succ, h2]
    simp [h1]
  · have hm : posFact k true = 2 * k + 2 + 1 := by simp [posFact]; omega
    have h2 : (2 * k + 2 + 1) / 2 = k + 1 := by omega
    have h1 : (2 * k + 2 + 1) % 2 = 1 := by omega
    rw [hm, bitsOfNat_succ, h2]
    simp [h1]

/-- The tail of the serialisation of a guard instance, after the initial-state list. -/
def guardRest : List Bool := serNatList [] ++ tnSer (([0], [], [(0, true, 0)]) : TnDesc)

theorem guardTail_eq : guardTail = false :: guardRest := rfl

theorem instSer_guardInst (L : List ℕ) :
    instSer (guardInst L) = blist (L.map bitsOfNat) ++ guardRest := by
  rw [instSer, guardRest]
  simp [guardInst, InstDesc.initList, InstDesc.goalList, InstDesc.tnI, serNatList,
    List.append_assoc]

/-- **The serialisation of the positional encoding is the recursion `posSer`.** -/
theorem instSer_posEnc (w : List Bool) : instSer (posEnc w) = posSer w := by
  rw [posEnc, instSer_guardInst]
  induction w with
  | nil => rw [posFacts_nil]; simp [posSer, guardTail_eq]
  | cons b x ih =>
    rw [posFacts_cons, List.map_cons, blist_cons, bitsOfNat_posFact, bstr_cons, posSer]
    simp only [List.cons_append, List.append_assoc]
    rw [ih]

/-- **The positional encoding runs in polynomial time.** -/
theorem polyTimeCode_posEnc : PolyTimeCode codingSer posEnc :=
  ⟨posSer, polyTimeFun_posSer, fun w => by rw [codingSer_code, instSer_posEnc]⟩

/-! ### The family -/

/-- The language the family encodes: the words whose first bit is `true`. -/
def LHeadTrue (w : List Bool) : Prop := w.head? = some true

/-- The domain description for the inputs of length `n`: the guard domain whose single guard is
the fact naming the leading position of a word of that length. -/
def posDom (n : ℕ) : DomDesc := guardDom [[2 * n + 1]]

theorem posDom_eq (n : ℕ) :
    posDom n = ([((0 : ℕ), [2 * n + 1], ([] : List ℕ), ([] : List ℕ))],
      [((0 : ℕ), (([0], [], [(0, false, 0)]) : TnDesc))]) := rfl

theorem computable_posDom : Computable posDom := by
  have hnum : Primrec fun n : ℕ => 2 * n + 1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)
  have hlist : Primrec fun n : ℕ => [2 * n + 1] :=
    Primrec.list_cons.comp hnum (Primrec.const [])
  have hact : Primrec fun n : ℕ =>
      [((0 : ℕ), [2 * n + 1], ([] : List ℕ), ([] : List ℕ))] :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair hlist (Primrec.const ([], []))))
      (Primrec.const [])
  have h : Primrec posDom :=
    (Primrec.pair hact (Primrec.const
      [((0 : ℕ), (([0], [], [(0, false, 0)]) : TnDesc))])).of_eq fun n => (posDom_eq n).symm
  exact h.to_comp

/-- Every fact of the encoding of a word is smaller than the fact naming the leading
position. -/
theorem posFacts_lt (x : List Bool) : ∀ f ∈ posFacts x, f < 2 * x.length + 2 := by
  induction x with
  | nil => simp
  | cons b x ih =>
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · rw [posFact]
      cases b <;> simp
    · have := ih f hf
      simp only [List.length_cons]
      omega

theorem mem_posFacts_head (w : List Bool) :
    (2 * w.length + 1) ∈ posFacts w ↔ LHeadTrue w := by
  cases w with
  | nil => simp [LHeadTrue]
  | cons b x =>
    rw [posFacts_cons, LHeadTrue]
    constructor
    · intro h
      rcases List.mem_cons.1 h with heq | hmem
      · have hb : b = true := by
          rw [posFact] at heq
          cases b <;> simp at heq ⊢
        simp [hb]
      · have := posFacts_lt x _ hmem
        simp only [List.length_cons] at this
        omega
    · intro h
      have hb : b = true := by simpa using h
      refine List.mem_cons.2 (Or.inl ?_)
      rw [posFact, hb]
      simp [List.length_cons]

theorem solvable_posDom_iff (w : List Bool) :
    Solvable (posDom w.length) (posEnc w) ↔ LHeadTrue w := by
  rw [posDom, posEnc, solvable_guard_iff']
  constructor
  · rintro ⟨p, hp, hsub⟩
    have hp1 : p = [2 * w.length + 1] := by simpa using hp
    exact (mem_posFacts_head w).1 (hsub _ (by rw [hp1]; simp))
  · intro h
    refine ⟨[2 * w.length + 1], by simp, ?_⟩
    intro f hf
    have : f = 2 * w.length + 1 := by simpa using hf
    rw [this]
    exact (mem_posFacts_head w).2 h

theorem size_posDom (n : ℕ) : (posDom n).size = 5 := by
  simp [posDom, guardDom, DomDesc.size, DomDesc.actions, DomDesc.methods,
    ActionDesc.size, MethodDesc.size, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]

theorem size_posEnc (w : List Bool) : (posEnc w).size = w.length + 2 := by
  simp [posEnc, guardInst, InstDesc.size, InstDesc.initList, InstDesc.goalList, InstDesc.tnI,
    TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]

/-- **A polynomial-time hardness family whose instances mention one fact per position of the
input word**, for the language of words whose first bit is `true`.  The domain description
depends on the input length — it names the leading position — which is the feature the machine
encodings of the literature need and which the family of
`HtnComplexity/Complexity/GuardFamily.lean` does not have. -/
noncomputable def posFamily :
    Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root LHeadTrue where
  dom := posDom
  inst := posEnc
  bound := Polynomial.X + Polynomial.C 5
  dom_size := fun n => by simp [size_posDom]
  inst_size := fun w => by simp [size_posEnc]
  dom_ok := fun _ => domOk_guardDom_TO_HTN_AC_root
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := posEnc_injective
  correct := solvable_posDom_iff
  dom_computable := computable_posDom
  inst_polyTime := polyTimeCode_posEnc

/-! ### A domain that reads every position

The domain of `HTN.Syn.posFamily` names a single position.  A machine encoding names *all* of
them: its domain description grows with the input length and mentions every position numeral.
The family below does the same with the same instance encoding — the domain for length `n` is
the guard listing the facts of a `true` bit at each of the `n` positions — so the problem is
solvable exactly when every bit of the word is `true`. -/

/-- The language of words all of whose bits are `true`. -/
def LAllTrue (w : List Bool) : Prop := ∀ b ∈ w, b = true

/-- The guard for the inputs of length `n`: the fact of a `true` bit at every position. -/
def allGuard (n : ℕ) : List ℕ := (List.range n).map fun k => posFact k true

@[simp] theorem length_allGuard (n : ℕ) : (allGuard n).length = n := by simp [allGuard]

/-- The domain description for the inputs of length `n`: the guard domain reading every
position. -/
def allDom (n : ℕ) : DomDesc := guardDom [allGuard n]

theorem allDom_eq (n : ℕ) :
    allDom n = ([((0 : ℕ), allGuard n, ([] : List ℕ), ([] : List ℕ))],
      [((0 : ℕ), (([0], [], [(0, false, 0)]) : TnDesc))]) := rfl

theorem computable_allDom : Computable allDom := by
  have hstep : Primrec fun p : ℕ × ℕ => posFact p.2 true := by
    have h : Primrec fun p : ℕ × ℕ => 2 * (p.2 + 1) + 1 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))
        (Primrec.const 1)
    exact h.of_eq fun p => by simp [posFact]
  have hguard : Primrec allGuard := Primrec.list_map Primrec.list_range hstep.to₂
  have hact : Primrec fun n : ℕ =>
      [((0 : ℕ), allGuard n, ([] : List ℕ), ([] : List ℕ))] :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair hguard (Primrec.const ([], []))))
      (Primrec.const [])
  have h : Primrec allDom :=
    (Primrec.pair hact (Primrec.const
      [((0 : ℕ), (([0], [], [(0, false, 0)]) : TnDesc))])).of_eq fun n => (allDom_eq n).symm
  exact h.to_comp

theorem posFact_lt_posFact {k l : ℕ} (h : k < l) (b c : Bool) : posFact k b < posFact l c := by
  cases b <;> cases c <;> simp [posFact] <;> omega

/-- **The facts of a `true` bit at every position are all present exactly when every bit of the
word is `true`.** -/
theorem forall_mem_posFacts_true_iff (w : List Bool) :
    (∀ k < w.length, posFact k true ∈ posFacts w) ↔ LAllTrue w := by
  rw [LAllTrue]
  induction w with
  | nil => simp
  | cons b x ih =>
    constructor
    · intro h
      have hhead : b = true := by
        have hmem := h x.length (by simp)
        rw [posFacts_cons] at hmem
        rcases List.mem_cons.1 hmem with heq | hmem'
        · rw [posFact, posFact] at heq
          cases b <;> simp at heq ⊢
        · have hlt := posFacts_lt x _ hmem'
          rw [posFact] at hlt
          omega
      have htail : ∀ c ∈ x, c = true := by
        refine ih.1 fun k hk => ?_
        have hmem := h k (by simp only [List.length_cons]; omega)
        rw [posFacts_cons] at hmem
        rcases List.mem_cons.1 hmem with heq | hmem'
        · exact absurd heq (Nat.ne_of_lt (posFact_lt_posFact hk true b))
        · exact hmem'
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hhead
      · exact htail c hc
    · intro h k hk
      rw [posFacts_cons]
      simp only [List.length_cons] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · exact List.mem_cons_of_mem _ (ih.2 (fun c hc => h c (List.mem_cons_of_mem _ hc)) k hk')
      · have hb : b = true := h b (by simp)
        rw [hb]
        exact List.mem_cons_self ..

theorem solvable_allDom_iff (w : List Bool) :
    Solvable (allDom w.length) (posEnc w) ↔ LAllTrue w := by
  rw [allDom, posEnc, solvable_guard_iff']
  have hmem : (∀ f ∈ allGuard w.length, f ∈ posFacts w) ↔ LAllTrue w := by
    rw [← forall_mem_posFacts_true_iff]
    constructor
    · intro h k hk
      exact h _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
    · rintro h f hf
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hf
      exact h k (List.mem_range.1 hk)
  constructor
  · rintro ⟨p, hp, hsub⟩
    have hp1 : p = allGuard w.length := by simpa using hp
    exact hmem.1 (by rw [← hp1]; exact hsub)
  · intro h
    exact ⟨allGuard w.length, by simp, hmem.2 h⟩

theorem size_allDom (n : ℕ) : (allDom n).size = n + 4 := by
  simp [allDom, guardDom, DomDesc.size, DomDesc.actions, DomDesc.methods,
    ActionDesc.size, MethodDesc.size, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  omega

/-- **A polynomial-time hardness family whose domain description reads every position of the
input word.**  Both parts now depend on the input: the instance lists one fact per position,
and the domain — of size linear in the input length — names all of them.  This is the shape of
the machine encodings behind the hardness results of the literature. -/
noncomputable def allTrueFamily :
    Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root LAllTrue where
  dom := allDom
  inst := posEnc
  bound := Polynomial.X + Polynomial.C 4
  dom_size := fun n => by simp [size_allDom]
  inst_size := fun w => by simp [size_posEnc]
  dom_ok := fun _ => domOk_guardDom_TO_HTN_AC_root
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := posEnc_injective
  correct := solvable_allDom_iff
  dom_computable := computable_allDom
  inst_polyTime := polyTimeCode_posEnc

namespace Coded

/-- **The positional family, in `TO-HTN-AC`.** -/
theorem nonempty_hardFamilyPT_pos_TO_HTN_AC :
    Nonempty (HardFamilyPT codingSer SynClass.TO_HTN_AC_root LHeadTrue) := ⟨posFamily⟩

/-- … in `TO-HTN`. -/
theorem nonempty_hardFamilyPT_pos_TO_HTN :
    Nonempty (HardFamilyPT codingSer SynClass.TO_HTN_root LHeadTrue) :=
  ⟨posFamily.mono (S' := SynClass.TO_HTN_root) ⟨fun _ hd => hd.1, fun _ hq => hq⟩⟩

/-- … in `HTN-TR`. -/
theorem nonempty_hardFamilyPT_pos_HTN_TR :
    Nonempty (HardFamilyPT codingSer SynClass.HTN_TR_root LHeadTrue) :=
  ⟨posFamily.mono (S' := SynClass.HTN_TR_root)
    ⟨fun _ hd => SynClass.isAcyclic_isTailRec hd.2, fun _ hq => hq⟩⟩

/-- … in `HTN-AC`. -/
theorem nonempty_hardFamilyPT_pos_HTN_AC :
    Nonempty (HardFamilyPT codingSer SynClass.HTN_AC_root LHeadTrue) :=
  ⟨posFamily.mono (S' := SynClass.HTN_AC_root) ⟨fun _ hd => hd.2, fun _ hq => hq⟩⟩

/-- **The family whose domain reads every position, in `TO-HTN-AC`.** -/
theorem nonempty_hardFamilyPT_allTrue_TO_HTN_AC :
    Nonempty (HardFamilyPT codingSer SynClass.TO_HTN_AC_root LAllTrue) := ⟨allTrueFamily⟩

/-- … in `TO-HTN`. -/
theorem nonempty_hardFamilyPT_allTrue_TO_HTN :
    Nonempty (HardFamilyPT codingSer SynClass.TO_HTN_root LAllTrue) :=
  ⟨allTrueFamily.mono (S' := SynClass.TO_HTN_root) ⟨fun _ hd => hd.1, fun _ hq => hq⟩⟩

/-- … in `HTN-TR`. -/
theorem nonempty_hardFamilyPT_allTrue_HTN_TR :
    Nonempty (HardFamilyPT codingSer SynClass.HTN_TR_root LAllTrue) :=
  ⟨allTrueFamily.mono (S' := SynClass.HTN_TR_root)
    ⟨fun _ hd => SynClass.isAcyclic_isTailRec hd.2, fun _ hq => hq⟩⟩

/-- … in `HTN-AC`. -/
theorem nonempty_hardFamilyPT_allTrue_HTN_AC :
    Nonempty (HardFamilyPT codingSer SynClass.HTN_AC_root LAllTrue) :=
  ⟨allTrueFamily.mono (S' := SynClass.HTN_AC_root) ⟨fun _ hd => hd.2, fun _ hq => hq⟩⟩

end Coded

end Syn

end HTN
