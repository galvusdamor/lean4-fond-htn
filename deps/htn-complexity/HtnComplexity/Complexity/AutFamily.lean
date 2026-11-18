import HtnComplexity.Complexity.PosFamily
import HtnComplexity.Computable.BinDom
/-!
# A hardness family whose fixed part is a machine reading its input

`HtnComplexity/Complexity/PosFamily.lean` writes the input word into the *instance*
description, positionally, in polynomial time, and
`HtnCompilability/Complexity/MachineFamily.lean` puts a *machine* — a two-stack machine — into
the fixed *domain* description, with the input carried by the initial task network.  Neither
file has both features at once:

* the families of `PosFamily.lean` are in the rooted classes `TO-HTN`, `HTN-TR`, `HTN-AC` that
  the eight open cells use as their source, but their domain is a guard: it reads the input and
  computes nothing;
* the family of `MachineFamily.lean` computes, but its initial task network *is* the input, so
  it is a family in the unrestricted class `HTN`, and the machine gets its input from the
  network rather than from the state.

This file supplies the missing shape, for a *finite-state* machine: a family whose domain
description is a machine that **reads its input from the initial state** through guarded
methods, and whose instance description is the positional encoding `HTN.Syn.posEnc` — so the
initial task network is the single compound task `0` and the family lies in
`HTN.Syn.SynClass.TO_HTN_AC_root`, hence in all three source classes of the eight cells.

The machine is a nondeterministic automaton over the bit alphabet (`HTN.Syn.BitAut`).  Its
current state is carried by the *compound task name*, not by a fact: the domain for words of
length `n` has one compound task `tName A n k q` per pair of a state `q` and a number `k ≤ n` of
bits still to read, and one method

    tName A n (k+1) q  ⟶  aName k b · tName A n k q'

per transition `(q, b, q')`, where the action `aName k b` has the single precondition
`posFact k b` — the fact saying that the bit at the position with `k` bits after it is `b` — and
no effect.  The methods for `k = 0` decompose `tName A n 0 q`, for an accepting `q`, into the
empty network.  A refinement of the root task is therefore exactly a run of the automaton, and
it is executable exactly when the bits it guesses are the bits of the word:

    HTN.Syn.solvable_autDom_iff : Solvable (autDom A w.length) (posEnc w) ↔ A.Accepts w

The domain is totally ordered (every body is a chain of at most two tasks), acyclic (the rank of
`tName A n k q` is `k`), of size linear in `n`, and computable in `n`; the instance encoding is
the one of `PosFamily.lean`, already known to be injective and computable in polynomial time.
Hence `HTN.Syn.autFamily A : Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root A.Accepts` —
*every* language recognised by a finite automaton has a polynomial-time hardness family whose
fixed part is a machine, in each of `TO-HTN`, `HTN-TR` and `HTN-AC`.
-/

namespace HTN

namespace Syn

open Binarise

/-! ### Automata over the bit alphabet -/

/-- A **nondeterministic finite automaton over the alphabet `Bool`**: an initial state, a list of
accepting states and a list of transitions `(source, bit, target)`.  States are natural numbers;
only the finitely many mentioned in the lists matter. -/
structure BitAut where
  /-- The initial state. -/
  start : ℕ
  /-- The accepting states. -/
  accept : List ℕ
  /-- The transitions `(source, bit, target)`. -/
  trans : List (ℕ × Bool × ℕ)

namespace BitAut

/-- **Acceptance of a word from a state.** -/
inductive AccFrom (A : BitAut) : ℕ → List Bool → Prop
  /-- The empty word is accepted from an accepting state. -/
  | nil {q : ℕ} (h : q ∈ A.accept) : AccFrom A q []
  /-- A transition consumes the first bit. -/
  | cons {q : ℕ} {b : Bool} {q' : ℕ} {v : List Bool} (h : (q, b, q') ∈ A.trans)
      (h' : AccFrom A q' v) : AccFrom A q (b :: v)

/-- **The language of the automaton.** -/
def Accepts (A : BitAut) (w : List Bool) : Prop := A.AccFrom A.start w

end BitAut

/-! ### The names of the encoding -/

/-- The transposition of `0` and `a`, an involution of `ℕ`.  It is used to give the compound task
of the initial configuration the name `0`, which is the name the root task of `HTN.Syn.guardInst`
— hence of `HTN.Syn.posEnc` — carries. -/
def swapZero (a x : ℕ) : ℕ := if x = a then 0 else if x = 0 then a else x

theorem swapZero_swapZero (a x : ℕ) : swapZero a (swapZero a x) = x := by
  unfold swapZero
  by_cases hxa : x = a
  · subst hxa
    by_cases ha : x = 0 <;> simp [ha]
  · by_cases hx0 : x = 0
    · subst hx0
      simp
    · simp [hxa, hx0]

theorem swapZero_injective (a : ℕ) : Function.Injective (swapZero a) :=
  Function.LeftInverse.injective (swapZero_swapZero a)

/-- **The compound task standing for the configuration `(k, q)`** of the automaton `A` reading a
word of length `n`: the automaton is in the state `q` and `k` bits are still to be read.  The
configuration `(n, A.start)` is named `0`, the name of the root task of `HTN.Syn.posEnc`. -/
def tName (A : BitAut) (n k q : ℕ) : ℕ := swapZero (Nat.pair n A.start) (Nat.pair k q)

/-- The action reading the bit `b` at the position with `k` bits after it. -/
def aName (k : ℕ) (b : Bool) : ℕ := 2 * k + b.toNat

variable {A : BitAut}

@[simp] theorem tName_root (n : ℕ) : tName A n n A.start = 0 := by
  simp [tName, swapZero]

theorem tName_inj {n k q k' q' : ℕ} (h : tName A n k q = tName A n k' q') : k = k' ∧ q = q' :=
  Nat.pair_eq_pair.1 (swapZero_injective _ h)

theorem aName_inj {k k' : ℕ} {b b' : Bool} (h : aName k b = aName k' b') : k = k' ∧ b = b' := by
  cases b <;> cases b' <;> simp only [aName, Bool.toNat_false, Bool.toNat_true] at h
  · exact ⟨by omega, rfl⟩
  · exact absurd h (by omega)
  · exact absurd h (by omega)
  · exact ⟨by omega, rfl⟩

theorem posFact_aName (k : ℕ) (b : Bool) : posFact k b = aName k b + 2 := by
  cases b <;> simp only [posFact, aName, Bool.toNat_false, Bool.toNat_true, if_true, if_false,
    Bool.false_eq_true] <;> omega

theorem aName_lt {k n : ℕ} (h : k < n) (b : Bool) : aName k b < 2 * n := by
  cases b <;> simp only [aName, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem posFact_inj {i j : ℕ} {c e : Bool} (h : posFact i c = posFact j e) : i = j ∧ c = e := by
  rw [posFact_aName, posFact_aName] at h
  exact aName_inj (by omega)

/-! ### The domain description -/

/-- The actions of the encoding: for every index `i < 2 * n` the action `i`, whose single
precondition is the fact `i + 2` and which has no effect.  By `HTN.Syn.posFact_aName` these are
exactly the actions `aName k b` for `k < n`, guarded by the fact `posFact k b`. -/
def autActions (n : ℕ) : List ActionDesc :=
  (List.range (2 * n)).map fun i => (i, [i + 2], ([] : List ℕ), ([] : List ℕ))

/-- The reading methods: one per remaining length `k + 1 ≤ n` and per transition. -/
def autReadMethods (A : BitAut) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => A.trans.map fun t =>
    (tName A n (k + 1) t.1, pairBody (Sum.inl (aName k t.2.1)) (Sum.inr (tName A n k t.2.2)))

/-- The accepting methods: one per accepting state, decomposing the configuration with no bits
left into the empty network. -/
def autAccMethods (A : BitAut) (n : ℕ) : List MethodDesc :=
  A.accept.map fun q => (tName A n 0 q, TnDesc.nil)

/-- **The domain description of the encoding** for the words of length `n`. -/
def autDom (A : BitAut) (n : ℕ) : DomDesc :=
  (autActions n, autReadMethods A n ++ autAccMethods A n)

@[simp] theorem autDom_actions (n : ℕ) : (autDom A n).actions = autActions n := rfl

@[simp] theorem autDom_methods (n : ℕ) :
    (autDom A n).methods = autReadMethods A n ++ autAccMethods A n := rfl

theorem mem_autActions {n : ℕ} {e : ActionDesc} (he : e ∈ autActions n) :
    ∃ i < 2 * n, e = (i, [i + 2], ([] : List ℕ), ([] : List ℕ)) := by
  simp only [autActions, List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨i, hi, rfl⟩

theorem mem_autReadMethods {n : ℕ} {e : MethodDesc} (he : e ∈ autReadMethods A n) :
    ∃ k < n, ∃ t ∈ A.trans,
      e = (tName A n (k + 1) t.1,
        pairBody (Sum.inl (aName k t.2.1)) (Sum.inr (tName A n k t.2.2))) := by
  simp only [autReadMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, t, ht, rfl⟩ := he
  exact ⟨k, hk, t, ht, rfl⟩

theorem mem_autAccMethods {n : ℕ} {e : MethodDesc} (he : e ∈ autAccMethods A n) :
    ∃ q ∈ A.accept, e = (tName A n 0 q, TnDesc.nil) := by
  simp only [autAccMethods, List.mem_map] at he
  obtain ⟨q, hq, rfl⟩ := he
  exact ⟨q, hq, rfl⟩

/-! ### The domain is in the class -/

theorem nil_isSeqNet : (TnDesc.nil).toTaskNetwork.IsSeqNet [] [] := by
  refine ⟨List.nodup_nil, fun x => ?_, rfl, fun x y => ?_⟩
  · simp [TnDesc.nil, TnDesc.toTaskNetwork, TnDesc.ids]
  · simp [TnDesc.nil, TnDesc.toTaskNetwork, TnDesc.ordOf, TnDesc.ids]

theorem nil_isTO : (TnDesc.nil).toTaskNetwork.IsTotallyOrdered := nil_isSeqNet.isTotallyOrdered

theorem autDom_methodsTO (n : ℕ) : (autDom A n).MethodsTO := by
  intro e he
  rw [autDom_methods, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨k, -, t, -, rfl⟩ := mem_autReadMethods he
    exact pairBody_isTO _ _
  · obtain ⟨q, -, rfl⟩ := mem_autAccMethods he
    exact nil_isTO

/-- The rank of a compound task name: the number of bits still to be read. -/
def autRank (A : BitAut) (n c : ℕ) : ℕ := (Nat.unpair (swapZero (Nat.pair n A.start) c)).1

@[simp] theorem autRank_tName (n k q : ℕ) : autRank A n (tName A n k q) = k := by
  simp [autRank, tName, swapZero_swapZero]

theorem autDom_isAcyclic (n : ℕ) : (autDom A n).IsAcyclic := by
  refine ⟨autRank A n, ?_⟩
  intro e he t ht c hc
  rw [autDom_methods, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨k, -, tr, -, rfl⟩ := mem_autReadMethods he
    have ht' : t = 0 ∨ t = 1 := by
      simpa [TnDesc.toTaskNetwork, pairBody, TnDesc.ids] using ht
    rcases ht' with rfl | rfl
    · simp [TnDesc.toTaskNetwork] at hc
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      simp
  · obtain ⟨q, -, rfl⟩ := mem_autAccMethods he
    simp [TnDesc.nil, TnDesc.toTaskNetwork, TnDesc.ids] at ht

theorem autDom_domOk (n : ℕ) : SynClass.TO_HTN_AC_root.domOk (autDom A n) :=
  ⟨autDom_methodsTO n, autDom_isAcyclic n⟩

/-! ### The bodies the domain offers -/

/-- **The bodies a described domain offers for a task name.** -/
theorem seqBody_desc_iff {d : DomDesc} {c : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    d.toDomain.SeqBody c xs ↔
      ∃ e ∈ d.methods, e.1 = c ∧ Method.HasSeqBody ⟨e.1, e.2.toTaskNetwork⟩ xs := by
  constructor
  · rintro ⟨m, ⟨e, he, rfl⟩, hc, hbody⟩
    exact ⟨e, he, hc, hbody⟩
  · rintro ⟨e, he, hc, hbody⟩
    exact ⟨e.toMethod, ⟨e, he, rfl⟩, hc, hbody⟩

/-- **The bodies of the encoded domain**: a reading step, or the end of an accepting run. -/
theorem seqBody_autDom_iff {n k q : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (autDom A n).toDomain.SeqBody (tName A n k q) xs ↔
      (∃ j, j < n ∧ k = j + 1 ∧ ∃ b : Bool, ∃ q' : ℕ, (q, b, q') ∈ A.trans ∧
        xs = [Sum.inl (aName j b), Sum.inr (tName A n j q')]) ∨
      (k = 0 ∧ q ∈ A.accept ∧ xs = []) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rw [autDom_methods, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨j, hj, t, ht, rfl⟩ := mem_autReadMethods he
      obtain ⟨hk, hq⟩ := tName_inj hc
      subst hk
      refine Or.inl ⟨j, hj, rfl, t.2.1, t.2.2, ?_, ?_⟩
      · rw [← hq]
        exact ht
      · exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody
    · obtain ⟨q₀, hq₀, rfl⟩ := mem_autAccMethods he
      obtain ⟨hk, hq⟩ := tName_inj hc
      subst hk
      refine Or.inr ⟨rfl, ?_, ?_⟩
      · rw [← hq]
        exact hq₀
      · exact (Method.hasSeqBody_iff_of_isSeqNet nil_isSeqNet).1 hbody
  · rintro (⟨j, hj, rfl, b, q', ht, rfl⟩ | ⟨rfl, hq, rfl⟩)
    · refine ⟨(tName A n (j + 1) q,
        pairBody (Sum.inl (aName j b)) (Sum.inr (tName A n j q'))), ?_, rfl, ?_⟩
      · rw [autDom_methods, List.mem_append]
        refine Or.inl ?_
        simp only [autReadMethods, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨j, hj, (q, b, q'), ht, rfl⟩
      · exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl
    · refine ⟨(tName A n 0 q, TnDesc.nil), ?_, rfl, ?_⟩
      · rw [autDom_methods, List.mem_append]
        refine Or.inr ?_
        simp only [autAccMethods, List.mem_map]
        exact ⟨q, hq, rfl⟩
      · exact (Method.hasSeqBody_iff_of_isSeqNet nil_isSeqNet).2 rfl

/-! ### No action has an effect -/

theorem lookup_autActions_eff (n a : ℕ) :
    (((autActions n).lookup a).elim ([] : List ℕ) fun x => x.2.1) = [] ∧
      (((autActions n).lookup a).elim ([] : List ℕ) fun x => x.2.2) = [] := by
  rcases h : (autActions n).lookup a with _ | p
  · simp
  · obtain ⟨i, -, he⟩ := mem_autActions (mem_of_lookup_eq_some h)
    have hp : p = ([i + 2], ([] : List ℕ), ([] : List ℕ)) := congrArg Prod.snd he
    subst hp
    simp

theorem autDom_add (n a : ℕ) : (autDom A n).add a = ∅ := by
  simp only [DomDesc.add, autDom_actions, (lookup_autActions_eff n a).1]
  simp

theorem autDom_del (n a : ℕ) : (autDom A n).del a = ∅ := by
  simp only [DomDesc.del, autDom_actions, (lookup_autActions_eff n a).2]
  simp

theorem autDom_transition (n a : ℕ) (s : Set ℕ) :
    (autDom A n).toDomain.transition a s = s := by
  have hd : (autDom A n).toDomain.del a = ∅ := autDom_del n a
  have ha : (autDom A n).toDomain.add a = ∅ := autDom_add n a
  simp [ActionModel.transition, hd, ha]

theorem autDom_transitionSeq (n : ℕ) (as : List ℕ) (s : Set ℕ) :
    (autDom A n).toDomain.transitionSeq as s = s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => rw [ActionModel.transitionSeq_cons, autDom_transition, ih]

theorem autDom_seqApplicable_iff (n : ℕ) (as : List ℕ) (s : Set ℕ) :
    (autDom A n).toDomain.SeqApplicable as s ↔ ∀ a ∈ as, (autDom A n).prec a ⊆ s := by
  induction as generalizing s with
  | nil => simp [ActionModel.SeqApplicable]
  | cons a as ih =>
    rw [ActionModel.seqApplicable_cons, autDom_transition, ih]
    simp [ActionModel.Applicable]

/-- The precondition of a listed action is the single fact guarding it. -/
theorem prec_autDom {n k : ℕ} (hk : k < n) (b : Bool) :
    (autDom A n).prec (aName k b) = {posFact k b} := by
  have hlookup := lookup_range_map (n := 2 * n)
    (fun j => ([j + 2], ([] : List ℕ), ([] : List ℕ))) (aName_lt hk b)
  simp only [DomDesc.prec, autDom_actions, autActions]
  rw [hlookup]
  ext f
  simp [posFact_aName]

/-! ### The facts of the positional encoding -/

/-- **A position fact holds exactly when the word really has that bit at that position.** -/
theorem mem_posFacts_iff {W : List Bool} {i : ℕ} {c : Bool} :
    posFact i c ∈ posFacts W ↔ ∃ v : List Bool, (c :: v) <:+ W ∧ v.length = i := by
  induction W with
  | nil => simp [posFacts]
  | cons b x ih =>
    rw [posFacts_cons, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨v, hv, hl⟩)
      · obtain ⟨hi, hc⟩ := posFact_inj h
        exact ⟨x, by rw [hc], hi.symm⟩
      · exact ⟨v, hv.trans (List.suffix_cons _ _), hl⟩
    · rintro ⟨v, hv, rfl⟩
      rcases List.suffix_cons_iff.1 hv with heq | hsuf
      · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 heq
        exact Or.inl rfl
      · exact Or.inr ⟨v, hsuf, rfl⟩

/-! ### The simulation -/

/-- Two suffixes of the same length of one word coincide. -/
theorem eq_of_suffix_of_length_eq {W u v : List Bool} (hu : u <:+ W) (hv : v <:+ W)
    (h : u.length = v.length) : u = v := by
  rw [List.suffix_iff_eq_drop.1 hu, List.suffix_iff_eq_drop.1 hv, h]

/-- **The refinements of a configuration task that are executable in the encoded word are the
accepting runs of the automaton on the corresponding suffix.** -/
theorem yieldSeq_autDom_iff {W : List Bool} : ∀ {v : List Bool}, v <:+ W → ∀ q : ℕ,
    ((∃ as : List ℕ, (autDom A W.length).toDomain.YieldSeq
        [Sum.inr (tName A W.length v.length q)] as ∧
      ∀ a ∈ as, (autDom A W.length).prec a ⊆ {f | f ∈ posFacts W}) ↔ A.AccFrom q v) := by
  intro v
  induction v with
  | nil =>
    intro _ q
    constructor
    · rintro ⟨as, hy, -⟩
      cases hy with
      | comp hm h =>
        rcases seqBody_autDom_iff.1 hm with ⟨j, -, hj, -⟩ | ⟨-, hq, -⟩
        · exact absurd hj (by simp)
        · exact BitAut.AccFrom.nil hq
    · intro h
      cases h with
      | nil hq =>
        refine ⟨[], ?_, by simp⟩
        exact Domain.YieldSeq.comp (bs := []) (seqBody_autDom_iff.2 (Or.inr ⟨rfl, hq, rfl⟩))
          (by simp)
  | cons b v ih =>
    intro hv q
    have hvW : v <:+ W := (List.suffix_cons b v).trans hv
    have hlen : v.length < W.length := by
      have := hv.length_le
      simp only [List.length_cons] at this
      omega
    constructor
    · rintro ⟨as, hy, happ⟩
      simp only [List.length_cons] at hy
      cases hy with
      | comp hm h =>
        rcases seqBody_autDom_iff.1 hm with ⟨j, hj, hjeq, b', q', htr, rfl⟩ | ⟨hk, -, -⟩
        · have hjv : j = v.length := by omega
          subst hjv
          rw [List.cons_append, List.cons_append, List.nil_append] at h
          cases h with
          | prim h =>
            rename_i as'
            have hmem : posFact v.length b' ∈ posFacts W := by
              have := happ (aName v.length b') (by simp)
              rw [prec_autDom hlen] at this
              exact this rfl
            obtain ⟨u, hu, hul⟩ := mem_posFacts_iff.1 hmem
            have hbu : b' :: u = b :: v :=
              eq_of_suffix_of_length_eq hu hv (by simp [hul])
            obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 hbu
            refine BitAut.AccFrom.cons htr ((ih hvW q').1 ⟨as', h, ?_⟩)
            exact fun a ha => happ a (List.mem_cons_of_mem _ ha)
        · exact absurd hk (by simp)
    · intro h
      cases h with
      | cons htr h' =>
        rename_i q'
        obtain ⟨as', hy', happ'⟩ := (ih hvW q').2 h'
        refine ⟨aName v.length b :: as', ?_, ?_⟩
        · simp only [List.length_cons]
          refine Domain.YieldSeq.comp
            (bs := [Sum.inl (aName v.length b), Sum.inr (tName A W.length v.length q')])
            (seqBody_autDom_iff.2 (Or.inl ⟨v.length, hlen, rfl, b, q', htr, rfl⟩)) ?_
          rw [List.cons_append, List.cons_append, List.nil_append]
          exact Domain.YieldSeq.prim hy'
        · intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · rw [prec_autDom hlen]
            intro f hf
            rw [Set.mem_singleton_iff] at hf
            subst hf
            exact mem_posFacts_iff.2 ⟨v, hv, rfl⟩
          · exact happ' a ha

/-- **The encoded problem is solvable exactly when the automaton accepts the word.** -/
theorem solvable_autDom_iff (w : List Bool) :
    Solvable (autDom A w.length) (posEnc w) ↔ A.Accepts w := by
  have hseq : ((posEnc w).tnI).toTaskNetwork.IsSeqNet (TnDesc.lin (posEnc w).tnI)
      (TnDesc.seqBody (posEnc w).tnI) := TnDesc.isSeqNet_lin guardInst_isTO
  have hbody : TnDesc.seqBody (posEnc w).tnI = [Sum.inr 0] := rfl
  have hnorm := Problem.solvable_iff_yieldSeq (problem_wf (autDom A w.length) (posEnc w))
    (isTO_problem (autDom_methodsTO (A := A) w.length) guardInst_isTO).2 hseq
  rw [show Solvable (autDom A w.length) (posEnc w)
      = (problem (autDom A w.length) (posEnc w)).Solvable from rfl, hnorm, hbody]
  have key := yieldSeq_autDom_iff (A := A) (W := w) (List.suffix_refl w) A.start
  rw [tName_root] at key
  constructor
  · rintro ⟨as, hy, happ, -⟩
    exact key.1 ⟨as, hy,
      (autDom_seqApplicable_iff (A := A) w.length as {f | f ∈ posFacts w}).1 happ⟩
  · intro h
    obtain ⟨as, hy, happ⟩ := key.2 h
    refine ⟨as, hy,
      (autDom_seqApplicable_iff (A := A) w.length as {f | f ∈ posFacts w}).2 happ, ?_⟩
    intro f hf
    simp only [problem_goal, InstDesc.goalList, posEnc, guardInst, Set.mem_setOf_eq,
      List.not_mem_nil] at hf

/-! ### Size, computability, and the family -/

theorem size_autActions_le (n : ℕ) : ((autActions n).map ActionDesc.size).sum ≤ 4 * n := by
  have hb : ∀ x ∈ (autActions n).map ActionDesc.size, x ≤ 2 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨i, -, rfl⟩ := mem_autActions he
    simp [ActionDesc.size]
  have hlen : ((autActions n).map ActionDesc.size).length = 2 * n := by simp [autActions]
  have h := List.sum_le_card_nsmul _ 2 hb
  rw [hlen, smul_eq_mul] at h
  omega

theorem length_autReadMethods_le (n : ℕ) :
    (autReadMethods A n).length ≤ n * A.trans.length := by
  have h := length_flatMap_le (List.range n)
    (fun k => A.trans.map fun t =>
      (tName A n (k + 1) t.1,
        pairBody (Sum.inl (aName k t.2.1)) (Sum.inr (tName A n k t.2.2))))
    A.trans.length (fun _ _ => by simp)
  simp only [autReadMethods, List.length_range] at h ⊢
  exact h

theorem size_autReadMethods_le (n : ℕ) :
    ((autReadMethods A n).map MethodDesc.size).sum ≤ 6 * A.trans.length * n := by
  have hb : ∀ x ∈ (autReadMethods A n).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨k, -, t, -, rfl⟩ := mem_autReadMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  calc ((autReadMethods A n).map MethodDesc.size).sum ≤ (autReadMethods A n).length * 6 := h
    _ ≤ (n * A.trans.length) * 6 := Nat.mul_le_mul_right _ (length_autReadMethods_le n)
    _ = 6 * A.trans.length * n := by ring

theorem size_autAccMethods_le (n : ℕ) :
    ((autAccMethods A n).map MethodDesc.size).sum ≤ A.accept.length := by
  have hb : ∀ x ∈ (autAccMethods A n).map MethodDesc.size, x ≤ 1 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨q, -, rfl⟩ := mem_autAccMethods he
    simp [MethodDesc.size, TnDesc.size, TnDesc.nil, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have h := List.sum_le_card_nsmul _ 1 hb
  rw [List.length_map, smul_eq_mul, autAccMethods, List.length_map, mul_one] at h
  exact h

theorem size_autDom_le (n : ℕ) :
    (autDom A n).size ≤ (6 * A.trans.length + 4) * n + A.accept.length := by
  have hsplit : (autDom A n).size = ((autActions n).map ActionDesc.size).sum
      + (((autReadMethods A n).map MethodDesc.size).sum
        + ((autAccMethods A n).map MethodDesc.size).sum) := by
    simp [DomDesc.size, autDom, DomDesc.actions, DomDesc.methods, List.map_append,
      List.sum_append]
  rw [hsplit]
  calc ((autActions n).map ActionDesc.size).sum
        + (((autReadMethods A n).map MethodDesc.size).sum
          + ((autAccMethods A n).map MethodDesc.size).sum)
      ≤ 4 * n + (6 * A.trans.length * n + A.accept.length) :=
        Nat.add_le_add (size_autActions_le n)
          (Nat.add_le_add (size_autReadMethods_le n) (size_autAccMethods_le n))
    _ = (6 * A.trans.length + 4) * n + A.accept.length := by ring

theorem primrec_swapZero : Primrec₂ swapZero := by
  have h : Primrec fun p : ℕ × ℕ => if p.2 = p.1 then 0 else if p.2 = 0 then p.1 else p.2 := by
    apply Primrec.ite (c := fun p : ℕ × ℕ => p.2 = p.1)
    · exact PrimrecRel.comp Primrec.eq Primrec.snd Primrec.fst
    · exact Primrec.const 0
    · apply Primrec.ite (c := fun p : ℕ × ℕ => p.2 = 0)
      · exact PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0)
      · exact Primrec.fst
      · exact Primrec.snd
  exact h

theorem primrec_toNat : Primrec (fun b : Bool => b.toNat) := by
  have h : Primrec fun b : Bool => bif b then 1 else 0 :=
    Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)
  exact h.of_eq fun b => by cases b <;> rfl

theorem primrec_autActions : Primrec autActions := by
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)) ?_
  exact Primrec.pair Primrec.snd
    (Primrec.pair (Primrec.list_cons.comp
        (Primrec.nat_add.comp Primrec.snd (Primrec.const 2)) (Primrec.const []))
      (Primrec.const ([], [])))

theorem primrec_autAccMethods : Primrec (autAccMethods A) := by
  refine Primrec.list_map (Primrec.const A.accept) ?_
  refine Primrec.pair ?_ (Primrec.const TnDesc.nil)
  exact primrec_swapZero.comp
    (Primrec₂.natPair.comp Primrec.fst (Primrec.const A.start))
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd)

/-- The reading methods, with the two-task bodies written out. -/
theorem autReadMethods_raw (n : ℕ) :
    autReadMethods A n = List.flatMap (fun k => A.trans.map fun t =>
      ((swapZero (Nat.pair n A.start) (Nat.pair (k + 1) t.1) : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 2 * k + t.2.1.toNat),
            (1, true, swapZero (Nat.pair n A.start) (Nat.pair k t.2.2))] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := rfl

theorem primrec_autReadMethods : Primrec (autReadMethods A) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k => A.trans.map fun t =>
      ((swapZero (Nat.pair n A.start) (Nat.pair (k + 1) t.1) : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 2 * k + t.2.1.toNat),
            (1, true, swapZero (Nat.pair n A.start) (Nat.pair k t.2.2))] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const A.trans) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.1.1 := Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.1.2 := Primrec.snd.comp Primrec.fst
    have t1 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.2.1 := Primrec.fst.comp Primrec.snd
    have tb : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have t2 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hbase : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => Nat.pair w.1.1 A.start :=
      Primrec₂.natPair.comp nn (Primrec.const A.start)
    have hhead : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) =>
        swapZero (Nat.pair w.1.1 A.start) (Nat.pair (w.1.2 + 1) w.2.1) :=
      primrec_swapZero.comp hbase
        (Primrec₂.natPair.comp (Primrec.nat_add.comp kk (Primrec.const 1)) t1)
    have htail : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) =>
        swapZero (Nat.pair w.1.1 A.start) (Nat.pair w.1.2 w.2.2.2) :=
      primrec_swapZero.comp hbase (Primrec₂.natPair.comp kk t2)
    have hact : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => 2 * w.1.2 + w.2.2.1.toNat :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) kk)
        (primrec_toNat.comp tb)
    refine Primrec.pair hhead (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hact))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) htail))
        (Primrec.const []))
  exact key.of_eq fun n => (autReadMethods_raw n).symm

theorem computable_autDom : Computable (autDom A) :=
  (Primrec.pair primrec_autActions
    (Primrec.list_append.comp primrec_autReadMethods primrec_autAccMethods)).to_comp

variable (A)

/-- **A polynomial-time hardness family whose fixed part is a finite automaton reading its input
from the initial state**, for the language of that automaton, in `TO-HTN-AC` with a rooted
instance — hence in each of the three source classes of the eight open cells. -/
noncomputable def autFamily :
    Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root A.Accepts where
  dom := autDom A
  inst := posEnc
  bound := Polynomial.C (6 * A.trans.length + 4) * Polynomial.X +
    Polynomial.C (A.accept.length + 2)
  dom_size := fun n => by
    have h := size_autDom_le (A := A) n
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  inst_size := fun w => by
    have h := size_posEnc w
    have h2 : w.length ≤ (6 * A.trans.length + 4) * w.length :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  dom_ok := fun _ => autDom_domOk _
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := posEnc_injective
  correct := solvable_autDom_iff
  dom_computable := computable_autDom
  inst_polyTime := polyTimeCode_posEnc

/-- **The automaton family, in `TO-HTN`.** -/
theorem nonempty_hardFamilyPT_aut_TO_HTN :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN_root A.Accepts) :=
  ⟨(autFamily A).mono ⟨fun _ h => h.1, fun _ h => h⟩⟩

/-- … in `HTN-TR`. -/
theorem nonempty_hardFamilyPT_aut_HTN_TR :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_TR_root A.Accepts) :=
  ⟨(autFamily A).mono ⟨fun _ h => SynClass.isAcyclic_isTailRec h.2, fun _ h => h⟩⟩

/-- … in `HTN-AC`. -/
theorem nonempty_hardFamilyPT_aut_HTN_AC :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_AC_root A.Accepts) :=
  ⟨(autFamily A).mono ⟨fun _ h => h.2, fun _ h => h⟩⟩

/-! ### An example

The language `HTN.Syn.LAllTrue` of `HtnComplexity/Complexity/PosFamily.lean` — the words all
of whose bits are `true` — is the language of a one-state automaton, so the family of this file
specialises to a family for it.  Unlike `HTN.Syn.allTrueFamily`, whose domain is a guard that
reads the whole input at once, this one runs a machine over the positions. -/

/-- The one-state automaton accepting exactly the words all of whose bits are `true`. -/
def allTrueAut : BitAut := ⟨0, [0], [(0, true, 0)]⟩

theorem accFrom_allTrueAut (w : List Bool) :
    allTrueAut.AccFrom 0 w ↔ ∀ b ∈ w, b = true := by
  induction w with
  | nil =>
    exact ⟨fun _ _ h => absurd h (by simp),
      fun _ => BitAut.AccFrom.nil (by simp [allTrueAut])⟩
  | cons b w ih =>
    constructor
    · intro h
      cases h with
      | cons htr h' =>
        rename_i q'
        simp only [allTrueAut, List.mem_singleton, Prod.mk.injEq] at htr
        obtain ⟨-, hb, hq⟩ := htr
        subst hb
        subst hq
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · rfl
        · exact ih.1 h' c hc
    · intro h
      refine BitAut.AccFrom.cons (q' := 0) ?_
        (ih.2 fun c hc => h c (List.mem_cons_of_mem _ hc))
      rw [h b (by simp)]
      simp [allTrueAut]

theorem allTrueAut_accepts_iff (w : List Bool) : allTrueAut.Accepts w ↔ LAllTrue w :=
  accFrom_allTrueAut w

/-- **A polynomial-time hardness family for `LAllTrue` whose fixed part is a machine.** -/
theorem nonempty_hardFamilyPT_allTrue_machine :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root LAllTrue) := by
  have h : allTrueAut.Accepts = LAllTrue := funext fun w => propext (allTrueAut_accepts_iff w)
  exact h ▸ ⟨autFamily allTrueAut⟩

end Syn

end HTN
