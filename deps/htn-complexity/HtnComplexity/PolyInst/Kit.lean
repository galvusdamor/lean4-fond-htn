import HtnComplexity.Complexity.TOPlan.ReachB
import ComplexityTheory.PolyHier.Pack
import HtnComplexity.Complexity.Coding
/-!
# A kit for writing polynomial-time *translations* in Cobham's class

The existing toolkit (`HtnComplexity/Complexity/TOPlan/Kit.lean` and the files it builds on)
is made for *predicates* on serialised descriptions.  A polynomial-time translation of instance
descriptions has to *produce* a serialisation, so it needs constructs that emit strings.  This
file adds three:

* `HTN.PTime.cobham_fmTailsC` — **emission over the positions of a string**: the concatenation of
  chunks `G (s :: args)`, one per suffix `s` of a computed string (longest first), is a function
  of the class whenever the chunk is.  The polynomial bound bounded recursion needs is derived
  once and for all from the bound of the chunk (`HTN.PTime.Cobham.bound_first`);
* `HTN.PTime.cobham_flatMapFin` and `HTN.PTime.cobham_ifNil` — finite selections of chunks;
* `HTN.PTime.Mealy` and `HTN.PTime.Mealy.cobham_mealy` — **finite-state transducers** (Mealy
  machines that emit a chunk per input bit) are functions of the class.  Every *local* rewriting
  of a serialisation — mapping an affine function over a list of numerals, renaming labels — is
  such a transducer.

`HTN.Syn.polyTimeMap_of_cobham` finally turns a function of the class that maps codes to codes
into a polynomial-time translation in the sense of `HTN.Syn.PolyTimeMap codingSer`.
-/

namespace HTN

namespace PTime

open Syn.Compress

/-! ### A polynomial bound in terms of the first arguments -/

/-- The concatenation of the first `n` arguments. -/
def catFirst (n : ℕ) (args : Args) : List Bool :=
  ((List.range n).map fun i => args.getD i []).flatten

theorem catFirst_succ (n : ℕ) (args : Args) :
    catFirst (n + 1) args = catFirst n args ++ args.getD n [] := by
  simp [catFirst, List.range_succ]

theorem catFirst_succ_cons (n : ℕ) (a : List Bool) (v : Args) :
    catFirst (n + 1) (a :: v) = a ++ catFirst n v := by
  simp [catFirst, List.range_succ_eq_map, List.map_map, Function.comp_def]

theorem cobham_catFirst (n : ℕ) : Cobham (catFirst n) := by
  induction n with
  | zero => exact (cobham_const []).of_eq' fun args => by simp [catFirst]
  | succ n ih =>
    exact (PH.cobham_app ih (Cobham.proj n)).of_eq' fun args => by rw [catFirst_succ]; rfl

theorem length_catFirst_le_succ (n : ℕ) (args : Args) :
    (catFirst n args).length ≤ (catFirst (n + 1) args).length := by
  rw [catFirst_succ, List.length_append]; omega

theorem catFirst_getD_tail (n : ℕ) (args : Args) :
    catFirst n (args.getD 0 [] :: args.tail) = catFirst n args := by
  cases args with
  | nil =>
    simp only [catFirst, List.getD_nil]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    cases i <;> simp
  | cons a v => rfl

theorem argSize_le_flatten (L : Args) : argSize L ≤ L.flatten.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [argSize_cons, List.flatten_cons, List.length_append]
    omega

/-- **A function of the class is bounded by a polynomial in the total length of its first `n`
arguments**, for some `n`. -/
theorem Cobham.bound_first {G : Fn} (hG : Cobham G) :
    ∃ n, ∃ p : Polynomial ℕ, ∀ args, (G args).length ≤ p.eval (catFirst n args).length := by
  obtain ⟨n, hn⟩ := hG.readsFirst
  obtain ⟨p, hp⟩ := hG.poly_length
  refine ⟨n, p, fun args => ?_⟩
  rw [hn args]
  exact (hp _).trans (Polynomial.eval_mono_nat p (argSize_le_flatten _))

/-! ### Emission over the positions of a string -/

/-- The concatenation of the chunks `G (s :: v)` over the suffixes `s` of `x`, longest first. -/
def fmTailsL (G : Fn) (v : Args) (x : List Bool) : List Bool :=
  x.tails.flatMap fun s => G (s :: v)

@[simp] theorem fmTailsL_nil (G : Fn) (v : Args) : fmTailsL G v [] = G ([] :: v) := by
  simp [fmTailsL]

@[simp] theorem fmTailsL_cons (G : Fn) (v : Args) (b : Bool) (x : List Bool) :
    fmTailsL G v (b :: x) = G ((b :: x) :: v) ++ fmTailsL G v x := by
  simp [fmTailsL]

theorem length_fmTailsL_le {G : Fn} {n : ℕ} {p : Polynomial ℕ}
    (hb : ∀ args, (G args).length ≤ p.eval (catFirst n args).length) (v : Args) :
    ∀ x : List Bool, (fmTailsL G v x).length ≤
      (x.length + 1) * p.eval (catFirst (n + 1) (x :: v)).length := by
  intro x
  induction x with
  | nil =>
    rw [fmTailsL_nil]
    simpa using (hb _).trans (Polynomial.eval_mono_nat p (length_catFirst_le_succ n _))
  | cons b x ih =>
    rw [fmTailsL_cons, List.length_append]
    have hmono : p.eval (catFirst (n + 1) (x :: v)).length ≤
        p.eval (catFirst (n + 1) ((b :: x) :: v)).length := by
      apply Polynomial.eval_mono_nat
      rw [catFirst_succ_cons, catFirst_succ_cons]
      simp
    have h1 := (hb ((b :: x) :: v)).trans (Polynomial.eval_mono_nat p
      (length_catFirst_le_succ n ((b :: x) :: v)))
    have h2 := ih.trans (Nat.mul_le_mul_left (x.length + 1) hmono)
    simp only [List.length_cons]
    nlinarith

theorem cobham_fmTails0 {G : Fn} (hG : Cobham G) :
    Cobham fun args => fmTailsL G args.tail (args.getD 0 []) := by
  obtain ⟨n, p, hp⟩ := hG.bound_first
  set g : Fn := fun args => G ([] :: args) with hg
  set h : Bool → Fn := fun b args =>
    G ((b :: args.getD 0 []) :: args.drop 2) ++ args.getD 1 [] with hh
  have hgC : Cobham g := hG.subst fun i => by
    cases i with
    | zero => exact (cobham_const []).of_eq' fun _ => by simp
    | succ i => exact (Cobham.proj i).of_eq' fun args => by simp [proj]
  have hhC : ∀ b, Cobham (h b) := fun b => by
    refine PH.cobham_app (hG.subst fun i => ?_) (Cobham.proj 1)
    cases i with
    | zero => exact (Cobham.cons b).of_eq' fun args => by simp [consFn]
    | succ i =>
      refine (Cobham.proj (i + 2)).of_eq' fun args => ?_
      simp [proj, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
  have haux : ∀ (v : Args) (x : List Bool),
      brnAux g (h false) (h true) x v = fmTailsL G v x := by
    intro v x
    induction x with
    | nil => simp [brnAux, hg]
    | cons b x ih =>
      have hb : brnAux g (h false) (h true) (b :: x) v
          = h b (x :: brnAux g (h false) (h true) x v :: v) := by cases b <;> rfl
      rw [hb, ih]
      simp [hh]
  have hfin : brnFn g (h false) (h true) = fun args => fmTailsL G args.tail (args.getD 0 []) := by
    funext args; rw [brnFn, haux]
  set q : Polynomial ℕ := (Polynomial.X + 1) * p with hq
  have hcob : Cobham (brnFn g (h false) (h true)) := by
    refine Cobham.brn hgC (hhC false) (hhC true)
      (PH.cobham_zerosPoly q (cobham_catFirst (n + 1))) fun args => ?_
    rw [hfin, List.length_replicate]
    refine (length_fmTailsL_le hp args.tail (args.getD 0 [])).trans ?_
    rw [catFirst_getD_tail, hq, Polynomial.eval_mul]
    have hx : (args.getD 0 []).length ≤ (catFirst (n + 1) args).length := by
      rw [← catFirst_getD_tail, catFirst_succ_cons]; simp
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ (by omega)
  rwa [hfin] at hcob

/-- **Emission over the positions of a computed string.**  The chunk sees the suffix as its
first argument, followed by the ambient arguments. -/
theorem cobham_fmTailsC {G : Fn} (hG : Cobham G) {a : Fn} (ha : Cobham a) :
    Cobham fun args => fmTailsL G args (a args) :=
  (cobham_bind (cobham_fmTails0 hG) ha).of_eq' fun args => by simp

/-! ### Finite selections -/

/-- The concatenation of finitely many functions of the class. -/
theorem cobham_flatMapFin {α : Type} (L : List α) (F : α → Fn) (h : ∀ a ∈ L, Cobham (F a)) :
    Cobham fun args => L.flatMap fun a => F a args := by
  induction L with
  | nil => exact (cobham_const []).of_eq' fun _ => by simp
  | cons a L ih =>
    exact (PH.cobham_app (h a (by simp)) (ih fun b hb => h b (by simp [hb]))).of_eq'
      fun _ => by simp

/-- Definition by cases, for a predicate of the class. -/
theorem cobham_iteB {p : Args → Bool} (hp : CobhamB p) {F G : Fn} (hF : Cobham F)
    (hG : Cobham G) : Cobham fun args => if p args = true then F args else G args :=
  CobhamTM.cobham_ite hp hF hG

/-- A chunk emitted only when a predicate of the class holds. -/
theorem cobham_ifNil {p : Args → Bool} (hp : CobhamB p) {F : Fn} (hF : Cobham F) :
    Cobham fun args => if p args = true then F args else [] :=
  cobham_iteB hp hF Cobham.empty

/-- Selecting the chunk of a value from a duplicate-free list containing it. -/
theorem flatMap_sel {α : Type} [DecidableEq α] {k₀ : α} (F : α → List Bool) :
    ∀ (L : List α), L.Nodup → k₀ ∈ L →
      (L.flatMap fun k => if decide (k₀ = k) = true then F k else []) = F k₀ := by
  intro L hnd hk
  induction L with
  | nil => simp at hk
  | cons k L ih =>
    rw [List.flatMap_cons]
    by_cases hkk : k₀ = k
    · subst hkk
      have hnot : k₀ ∉ L := (List.nodup_cons.1 hnd).1
      have hrest : (L.flatMap fun k => if decide (k₀ = k) = true then F k else []) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro k hk
        have : k₀ ≠ k := fun h => hnot (h ▸ hk)
        simp [this]
      rw [hrest]; simp
    · have hkL : k₀ ∈ L := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h hkk
        · exact h
      rw [ih (List.nodup_cons.1 hnd).2 hkL]; simp [hkk]

/-! ### Finite-state transducers -/

/-- **A Mealy machine** on bits: a transition function and a chunk emitted per input bit. -/
structure Mealy (σ : Type) where
  /-- The transition function. -/
  step : σ → Bool → σ
  /-- The chunk emitted when reading a bit in a state. -/
  out : σ → Bool → List Bool

namespace Mealy

variable {σ : Type} (M : Mealy σ)

/-- The output of the machine started in `s` on the input `w`. -/
def outs : σ → List Bool → List Bool
  | _, [] => []
  | s, b :: w => M.out s b ++ outs (M.step s b) w

/-- The state reached from `s` on the input `w`. -/
def st (s : σ) (w : List Bool) : σ := w.foldl M.step s

@[simp] theorem outs_nil (s : σ) : M.outs s [] = [] := rfl

@[simp] theorem outs_cons (s : σ) (b : Bool) (w : List Bool) :
    M.outs s (b :: w) = M.out s b ++ M.outs (M.step s b) w := rfl

@[simp] theorem st_nil (s : σ) : M.st s [] = s := rfl

@[simp] theorem st_cons (s : σ) (b : Bool) (w : List Bool) :
    M.st s (b :: w) = M.st (M.step s b) w := rfl

theorem outs_append (s : σ) (u v : List Bool) :
    M.outs s (u ++ v) = M.outs s u ++ M.outs (M.st s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons b u ih => simp [ih, List.append_assoc]

theorem st_append (s : σ) (u v : List Bool) : M.st s (u ++ v) = M.st (M.st s u) v := by
  simp [st, List.foldl_append]

/-- The chunk emitted at a position: the output of the bit there, from the state the prefix
leads to, or the final chunk at the end. -/
def chunk (s₀ : σ) (fin : σ → List Bool) (w t : List Bool) : List Bool :=
  match t with
  | [] => fin (M.st s₀ (cutS w t))
  | b :: _ => M.out (M.st s₀ (cutS w t)) b

theorem outs_eq_fmTails (s₀ : σ) (fin : σ → List Bool) :
    ∀ (t u : List Bool), (t.tails.flatMap fun t' => M.chunk s₀ fin (u ++ t) t') =
      M.outs (M.st s₀ u) t ++ fin (M.st s₀ (u ++ t)) := by
  intro t
  induction t with
  | nil => intro u; simp [chunk, cutS]
  | cons b t ih =>
    intro u
    rw [List.tails_cons, List.flatMap_cons]
    have h1 : M.chunk s₀ fin (u ++ b :: t) (b :: t) = M.out (M.st s₀ u) b := by
      simp [chunk, cutS]
    have h2 : (t.tails.flatMap fun t' => M.chunk s₀ fin (u ++ b :: t) t') =
        (t.tails.flatMap fun t' => M.chunk s₀ fin ((u ++ [b]) ++ t) t') := by
      simp
    rw [h1, h2, ih (u ++ [b])]
    simp [st_append, List.append_assoc]

/-- **A finite-state transducer is a function of Cobham's class**: its output on a computed
string, followed by a chunk chosen by the final state. -/
theorem cobham_mealy [DecidableEq σ] (states : List σ) (s₀ : σ) (fin : σ → List Bool)
    (hinit : s₀ ∈ states) (hstep : ∀ s b, s ∈ states → M.step s b ∈ states)
    {a : Fn} (ha : Cobham a) :
    Cobham fun args => M.outs s₀ (a args) ++ fin (M.st s₀ (a args)) := by
  have hmem : ∀ w, M.st s₀ w ∈ states := by
    intro w
    induction w using List.reverseRecOn with
    | nil => exact hinit
    | append_singleton w b ih =>
      rw [st_append]; exact hstep _ _ ih
  -- the chunk, as a finite selection over the states
  set C : Fn := fun args => states.dedup.flatMap fun k =>
    if decide (M.st s₀ (cutS (a args.tail) (args.getD 0 [])) = k) = true then
      (if decide (args.getD 0 [] = []) = true then fin k else
        if (args.getD 0 []).headD false = true then M.out k true else M.out k false)
    else [] with hC
  have hCeq : ∀ args, C args = M.chunk s₀ fin (a args.tail) (args.getD 0 []) := by
    intro args
    rw [hC]
    refine (flatMap_sel (k₀ := M.st s₀ (cutS (a args.tail) (args.getD 0 [])))
      (fun k => if decide (args.getD 0 [] = []) = true then fin k else
        if (args.getD 0 []).headD false = true then M.out k true else M.out k false)
      _ (List.nodup_dedup states) (List.mem_dedup.2 (hmem _))).trans ?_
    rcases hx : args.getD 0 [] with _ | ⟨b, t⟩
    · simp [chunk]
    · cases b <;> simp [chunk]
  have hCC : Cobham C := by
    refine cobham_flatMapFin _ _ fun k _ => cobham_ifNil ?_ ?_
    · exact (Syn.cobhamB_of_dfa states s₀ M.step (fun s => decide (s = k)) hinit hstep
        (cobham_cut (cobham_tailArgs ha) cobham_var0)).of_eq fun args => rfl
    · exact cobham_iteB (cobhamB_null cobham_var0) (cobham_const _)
        (cobham_iteB (cobhamB_head cobham_var0) (cobham_const _) (cobham_const _))
  refine (cobham_fmTailsC hCC ha).of_eq' fun args => ?_
  rw [fmTailsL]
  have := M.outs_eq_fmTails s₀ fin (a args) []
  simp only [List.nil_append, st_nil] at this
  rw [← this]
  refine List.flatMap_congr fun s _ => ?_
  rw [hCeq]
  rfl

end Mealy

end PTime

namespace Syn

open PTime

/-- **A function of Cobham's class that maps codes to codes is a polynomial-time translation.** -/
theorem polyTimeMap_of_cobham {f : InstDesc → InstDesc} {F : Fn} (hF : Cobham F)
    (h : ∀ q, F [instSer q] = instSer (f q)) : PolyTimeMap codingSer f :=
  ⟨fun x => F [x], PolyTimeFun.of_cobham hF fun _ => rfl, fun q => h q⟩

end Syn

end HTN
