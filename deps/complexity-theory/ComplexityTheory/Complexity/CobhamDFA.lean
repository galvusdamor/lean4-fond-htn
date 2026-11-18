import ComplexityTheory.Complexity.CobhamTable
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Finite-state scans are polynomial time

The polynomial-time reading of the rooting schema needs functions of Cobham's class that *read*
a bit string.  The workhorse is this file's theorem: **a scan of the input with finitely many
states is a function of Cobham's class**, in both directions of travel.

* `HTN.PTime.cobham_foldrBits` — the bit-level form: a fold over the input whose accumulator is a
  bit string of bounded length, the step being a finite table, is in the class.  This is the
  recursion on notation of Cobham's class with a constant bound;
* `HTN.PTime.polyTimeFun_dfaFoldr` — the same with an abstract state space, the states given as a
  list containing the initial state and closed under the transition:
  `fun x => [out (x.foldr step init)]` is polynomial time.  A state is coded in unary — as many
  `false`s as its position in the list, then a `true` — which makes the transition a finite
  table in the sense of `HTN.PTime.cobham_ofTake`;
* `HTN.PTime.polyTimeFun_dfaFoldl` — the left-to-right version, obtained by reversal
  (`HTN.PTime.polyTimeFun_reverse`).  This is the form in which self-delimiting codes are read: a
  deterministic automaton walks the string from the left, and the answer is a function of the
  state it stops in.

Nothing here is specific to descriptions.
-/

namespace HTN

namespace PTime

/-! ### The bit-level fold -/

/-- **A fold with a bounded bit-string accumulator belongs to Cobham's class.** -/
theorem cobham_foldrBits (k : ℕ) (init : List Bool) (step : Bool → List Bool → List Bool)
    (hinit : init.length ≤ k) (hstep : ∀ b s, (step b s).length ≤ k)
    (hdep : ∀ b s, step b s = step b (s.take k)) :
    Cobham (fun args => (args.getD 0 []).foldr step init) := by
  have htab : ∀ b, Cobham (fun args : Args => step b (args.getD 0 [])) :=
    fun b => cobham_ofTake k k (step b) (hdep b) (hstep b)
  have hrec : ∀ b, Cobham (compFn (fun args : Args => step b (args.getD 0 [])) [proj 1]) :=
    fun b => Cobham.comp (htab b) (by
      intro h hh
      rw [List.mem_singleton.1 hh]
      exact Cobham.proj 1)
  have happ : ∀ (b : Bool) (args : Args),
      compFn (fun args : Args => step b (args.getD 0 [])) [proj 1] args
        = step b (args.getD 1 []) := by
    intro b args
    simp [compFn, proj]
  have haux : ∀ (v : Args) (x : List Bool),
      brnAux (fun _ => init) (compFn (fun args : Args => step false (args.getD 0 [])) [proj 1])
        (compFn (fun args : Args => step true (args.getD 0 [])) [proj 1]) x v
        = x.foldr step init := by
    intro v x
    induction x with
    | nil => rfl
    | cons b x ih => cases b <;> exact congrArg _ ih
  have hfn : brnFn (fun _ => init)
      (compFn (fun args : Args => step false (args.getD 0 [])) [proj 1])
      (compFn (fun args : Args => step true (args.getD 0 [])) [proj 1])
      = fun args : Args => (args.getD 0 []).foldr step init := by
    funext args
    rw [brnFn, haux]
  have hlen : ∀ x : List Bool, (x.foldr step init).length ≤ k := by
    intro x
    induction x with
    | nil => exact hinit
    | cons b x _ => exact hstep b _
  have hb : ∀ args : Args,
      (brnFn (fun _ => init)
        (compFn (fun args : Args => step false (args.getD 0 [])) [proj 1])
        (compFn (fun args : Args => step true (args.getD 0 [])) [proj 1]) args).length ≤
      ((fun _ : Args => List.replicate k false) args).length := by
    intro args
    rw [hfn]
    simpa using hlen _
  have hcob := Cobham.brn (cobham_const init) (hrec false) (hrec true)
    (cobham_const (List.replicate k false)) hb
  rwa [hfn] at hcob

/-! ### Abstract finite state spaces -/

variable {σ : Type} [DecidableEq σ]

/-- The unary code of a state: as many `false`s as its position in the list of states, then a
`true`. -/
def stEnc (states : List σ) (s : σ) : List Bool :=
  List.replicate (states.idxOf s) false ++ [true]

/-- The state a code denotes: the state at the position of its first `true`. -/
def stDec (states : List σ) (dflt : σ) (code : List Bool) : σ :=
  states.getD (code.idxOf true) dflt

theorem idxOf_true_replicate (m : ℕ) :
    (List.replicate m false ++ [true]).idxOf true = m := by
  induction m with
  | zero => rfl
  | succ m ih => simpa [List.replicate_succ, List.idxOf_cons] using ih

theorem length_stEnc_le {states : List σ} {s : σ} (h : s ∈ states) :
    (stEnc states s).length ≤ states.length := by
  have := List.idxOf_lt_length_of_mem h
  simp only [stEnc, List.length_append, List.length_replicate, List.length_singleton]
  omega

omit [DecidableEq σ] in
theorem stDec_mem {states : List σ} {dflt : σ} (h : dflt ∈ states) (code : List Bool) :
    stDec states dflt code ∈ states := by
  rw [stDec]
  by_cases hlt : code.idxOf true < states.length
  · rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  · rw [List.getD_eq_default _ _ (by omega)]
    exact h

theorem stDec_stEnc {states : List σ} {dflt s : σ} (h : s ∈ states) :
    stDec states dflt (stEnc states s) = s := by
  have hlt := List.idxOf_lt_length_of_mem h
  rw [stDec, stEnc, idxOf_true_replicate, List.getD_eq_getElem _ _ hlt]
  exact List.getElem_idxOf hlt

/-- **A finite-state scan of the input, from the right, is polynomial time.** -/
theorem polyTimeFun_dfaFoldr (states : List σ) (init : σ) (step : Bool → σ → σ)
    (out : σ → Bool) (hinit : init ∈ states) (hstep : ∀ b s, s ∈ states → step b s ∈ states) :
    PolyTimeFun (fun x : List Bool => [out (x.foldr step init)]) := by
  classical
  set k := states.length with hk
  set dec : List Bool → σ := fun code => stDec states init (code.take k) with hdec
  set bstep : Bool → List Bool → List Bool :=
    fun b code => stEnc states (step b (dec code)) with hbstep
  -- the coded fold
  have hdepb : ∀ b s, bstep b s = bstep b (s.take k) := by
    intro b s
    simp [hbstep, hdec, List.take_take]
  have hdecmem : ∀ code, dec code ∈ states := fun code => stDec_mem hinit _
  have hlenb : ∀ b s, (bstep b s).length ≤ k :=
    fun b s => length_stEnc_le (hstep b _ (hdecmem s))
  have hinitlen : (stEnc states init).length ≤ k := length_stEnc_le hinit
  have hfold : Cobham (fun args : Args =>
      (args.getD 0 []).foldr bstep (stEnc states init)) :=
    cobham_foldrBits k (stEnc states init) bstep hinitlen hlenb hdepb
  -- the coded fold really codes the fold
  have hmemfold : ∀ x : List Bool, x.foldr step init ∈ states := by
    intro x
    induction x with
    | nil => exact hinit
    | cons b x ih => exact hstep b _ ih
  have hd : ∀ s : σ, s ∈ states → dec (stEnc states s) = s := by
    intro s hs
    have hle : (stEnc states s).length ≤ k := length_stEnc_le hs
    show stDec states init ((stEnc states s).take k) = s
    rw [List.take_of_length_le hle]
    exact stDec_stEnc hs
  have hcode : ∀ x : List Bool,
      x.foldr bstep (stEnc states init) = stEnc states (x.foldr step init) := by
    intro x
    induction x with
    | nil => rfl
    | cons b x ih =>
      show stEnc states (step b (dec (x.foldr bstep (stEnc states init)))) = _
      rw [ih, hd _ (hmemfold x)]
      rfl
  -- the final table lookup
  have htab : Cobham (fun args : Args => [out (stDec states init ((args.getD 0 []).take k))]) :=
    cobham_ofTake k 1 (fun x => [out (stDec states init (x.take k))])
      (fun x => by simp [List.take_take]) (fun x => by simp)
  refine CobhamFun.polyTimeFun ⟨compFn (fun args : Args => [out (stDec states init ((args.getD 0 []).take k))])
    [fun args => (args.getD 0 []).foldr bstep (stEnc states init)], Cobham.comp htab ?_, ?_⟩
  · intro h hh
    rw [List.mem_singleton.1 hh]
    exact hfold
  · intro x
    have hle : (stEnc states (x.foldr step init)).length ≤ k :=
      length_stEnc_le (hmemfold x)
    simp only [compFn, List.map_cons, List.map_nil, List.getD_cons_zero]
    rw [hcode x, List.take_of_length_le hle, stDec_stEnc (hmemfold x)]

/-- **A finite-state scan of the input, from the left, is polynomial time.**  This is the form a
self-delimiting code is read in. -/
theorem polyTimeFun_dfaFoldl (states : List σ) (init : σ) (step : σ → Bool → σ)
    (out : σ → Bool) (hinit : init ∈ states) (hstep : ∀ s b, s ∈ states → step s b ∈ states) :
    PolyTimeFun (fun x : List Bool => [out (x.foldl step init)]) := by
  have hrev := polyTimeFun_dfaFoldr states init (fun b s => step s b) out hinit
    (fun b s hs => hstep s b hs)
  have hcomp := hrev.comp polyTimeFun_reverse
  have hEq : (fun x : List Bool => [out (x.reverse.foldr (fun b s => step s b) init)])
      = fun x : List Bool => [out (x.foldl step init)] := by
    funext x
    simp [List.foldr_reverse]
  rwa [hEq] at hcomp

/-! ### The convenient form: a finite state type -/

/-- **A finite-state scan from the left, for a state type that is finite.**  This is the form the
applications use: no list of states has to be exhibited. -/
theorem polyTimeFun_dfa [Fintype σ] (init : σ) (step : σ → Bool → σ) (out : σ → Bool) :
    PolyTimeFun (fun x : List Bool => [out (x.foldl step init)]) :=
  polyTimeFun_dfaFoldl (Finset.univ : Finset σ).toList init step out
    (by simp) (by intro s b _; simp)

end PTime

end HTN
