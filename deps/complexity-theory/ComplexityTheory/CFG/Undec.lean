import ComplexityTheory.CFG.TSMGram
import ComplexityTheory.Undec.TM.Reduce
/-!
# The intersection problem of context-free grammars is undecidable

* `HTN.CFG.primrec_gram` — the grammar of a stack (`ComplexityTheory/CFG/TSMGram.lean`) is
  primitive recursive in the initial content of the stack;
* `HTN.CFG.not_computablePred_inter_stack` — the same, restricted to the binary grammar pairs
  `(gram₁, gram undecTSM true s)` of the reduction, as a problem on `s`;
* **`HTN.CFG.not_computablePred_inter`** — no algorithm decides, given two context-free grammars,
  whether their languages intersect.  The statement holds already for grammars all of whose
  right-hand sides have at most two symbols (`HTN.CFG.not_computablePred_inter_binary`), and for
  pairs whose first grammar is one fixed grammar (`HTN.CFG.not_computablePred_inter_fixed`).

The reduction is from the halting problem of the two-stack machine `HTN.Undec.undecTSM`
(`ComplexityTheory/Undec/TM/Reduce.lean`): it halts on `([0], redStack n)` iff the grammars of
its two stacks, started with these contents, have a common word (`HTN.CFG.halts_iff_inter`).
This is the fact Bercher et al. cite for Thm. 4.1.1 (Hopcroft–Ullman, Thm. 8.10).
-/

namespace HTN

namespace CFG

open Undec Undec.Sim Undec.TMChain

variable (M : TSM)

private theorem primrec_ntI : Primrec fun x : ℕ × ℕ × ℕ => ntI x.1 x.2.1 x.2.2 :=
  Primrec₂.natPair.comp (Primrec.const 5) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

private theorem primrec_ntN : Primrec fun x : ℕ × ℕ × ℕ => ntN x.1 x.2.1 x.2.2 :=
  Primrec₂.natPair.comp (Primrec.const 2) (Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

private theorem primrec_ntE : Primrec fun x : ℕ × ℕ => ntE x.1 x.2 :=
  Primrec₂.natPair.comp (Primrec.const 1) (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

/-- One rule `I p i q → N p (s[i]) r · I r (i+1) q`, as a function of `((((s, i), p), q), r)`. -/
def ruleI (x : (((List ℕ × ℕ) × ℕ) × ℕ) × ℕ) : Rule :=
  (ntI x.1.1.2 x.1.1.1.2 x.1.2,
    [Sum.inr (ntN x.1.1.2 (x.1.1.1.1.getD x.1.1.1.2 0) x.2), Sum.inr (ntI x.2 (x.1.1.1.2 + 1) x.1.2)])

/-- One rule `I p |s| q → E p q`, as a function of `((s, p), q)`. -/
def ruleIEnd (x : (List ℕ × ℕ) × ℕ) : Rule :=
  (ntI x.1.2 x.1.1.length x.2, [Sum.inr (ntE x.1.2 x.2)])

set_option maxHeartbeats 1000000 in
theorem primrec_ruleI : Primrec ruleI := by
  have hs : Primrec fun x : (((List ℕ × ℕ) × ℕ) × ℕ) × ℕ => x.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hi : Primrec fun x : (((List ℕ × ℕ) × ℕ) × ℕ) × ℕ => x.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hp : Primrec fun x : (((List ℕ × ℕ) × ℕ) × ℕ) × ℕ => x.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec fun x : (((List ℕ × ℕ) × ℕ) × ℕ) × ℕ => x.1.2 := Primrec.snd.comp Primrec.fst
  have hr : Primrec fun x : (((List ℕ × ℕ) × ℕ) × ℕ) × ℕ => x.2 := Primrec.snd
  have h1 := primrec_ntI.comp (hp.pair (hi.pair hq))
  have h2 := (Primrec.sumInr (α := ℕ) (β := ℕ)).comp (primrec_ntN.comp (hp.pair (((Primrec.list_getD 0).comp hs hi).pair hr)))
  have h3 := (Primrec.sumInr (α := ℕ) (β := ℕ)).comp (primrec_ntI.comp (hr.pair ((Primrec.succ.comp hi).pair hq)))
  exact h1.pair (Primrec.list_cons.comp h2 (Primrec.list_cons.comp h3 (Primrec.const [])))

theorem primrec_ruleIEnd : Primrec ruleIEnd := by
  have hs : Primrec fun x : (List ℕ × ℕ) × ℕ => x.1.1 := Primrec.fst.comp Primrec.fst
  have hp : Primrec fun x : (List ℕ × ℕ) × ℕ => x.1.2 := Primrec.snd.comp Primrec.fst
  have hq : Primrec fun x : (List ℕ × ℕ) × ℕ => x.2 := Primrec.snd
  exact (primrec_ntI.comp (hp.pair ((Primrec.list_length.comp hs).pair hq))).pair
    (Primrec.list_cons.comp ((Primrec.sumInr (α := ℕ) (β := ℕ)).comp (primrec_ntE.comp (hp.pair hq)))
      (Primrec.const []))

theorem rulesI_eq (s : List ℕ) : rulesI M s =
    ((List.range s.length).flatMap fun i => (states M).flatMap fun p =>
      (states M).flatMap fun q => (states M).map fun r => ruleI ((((s, i), p), q), r)) ++
    (states M).flatMap fun p => (states M).map fun q => ruleIEnd ((s, p), q) := rfl

/-- The rules of `ntI` are primitive recursive in the initial stack. -/
theorem primrec_rulesI : Primrec (rulesI M) := by
  have e : rulesI M = fun s => ((List.range s.length).flatMap fun i => (states M).flatMap fun p =>
      (states M).flatMap fun q => (states M).map fun r => ruleI ((((s, i), p), q), r)) ++
    (states M).flatMap fun p => (states M).map fun q => ruleIEnd ((s, p), q) :=
    funext (rulesI_eq M)
  rw [e]
  refine Primrec.list_append.comp ?_ ?_
  · refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) ?_
    refine Primrec.list_flatMap (Primrec.const _) ?_
    refine Primrec.list_flatMap (Primrec.const _) ?_
    exact Primrec.list_map (Primrec.const _) (primrec_ruleI.comp
      ((((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair (Primrec.snd.comp Primrec.fst)
        |>.pair Primrec.snd))
  · refine Primrec.list_flatMap (Primrec.const _) ?_
    exact Primrec.list_map (Primrec.const _) (primrec_ruleIEnd.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))

/-- **The grammar of a stack is primitive recursive in the initial stack.** -/
theorem primrec_gram (b : Bool) : Primrec (gram M b) := by
  unfold gram
  exact Primrec.pair (Primrec.const _) (Primrec.list_append.comp (Primrec.const _)
    (primrec_rulesI M))

/-- The fixed first grammar of the reduction. -/
noncomputable def gram₁ : Grammar := gram undecTSM false [0]

/-- **The reduction**: the grammars of the two stacks of `undecTSM`, started with `[0]` and
`redStack n`, have a common word iff `undecTSM` halts on `([0], redStack n)`. -/
theorem inter_gram_iff (n : ℕ) :
    Inter gram₁ (gram undecTSM true (redStack n)) ↔ undecTSM.Halts [0] (redStack n) :=
  halts_iff_inter.symm

/-- **A decider for the intersection problem at the fixed first grammar, restricted to the
second grammars of the reduction, would decide the halting problem.** -/
theorem not_computable_inter_gram {f : Grammar → Bool} (hf : Computable f)
    (hfeq : ∀ s, f (gram undecTSM true s) = true ↔ Inter gram₁ (gram undecTSM true s)) : False := by
  refine ComputablePred.halting_problem 0 ?_
  refine ComputablePred.computable_iff.2
    ⟨fun c : Nat.Partrec.Code => f (gram undecTSM true (redStack (Encodable.encode c))), ?_, ?_⟩
  · exact hf.comp ((primrec_gram undecTSM true).comp (primrec_redStack.comp Primrec.encode)).to_comp
  · funext c
    have hu := undecTSM_halts_iff (Encodable.encode c)
    rw [univFun, Denumerable.ofNat_encode] at hu
    simp only [eq_iff_iff]
    rw [← hu, ← inter_gram_iff, ← hfeq]

/-- **Intersection is undecidable on the grammar pairs of the reduction**, as a function of the
initial second stack. -/
theorem not_computablePred_inter_stack :
    ¬ ComputablePred fun s : List ℕ => Inter gram₁ (gram undecTSM true s) := by
  intro h
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.1 h
  refine ComputablePred.halting_problem 0 ?_
  refine ComputablePred.computable_iff.2
    ⟨fun c : Nat.Partrec.Code => f (redStack (Encodable.encode c)), ?_, ?_⟩
  · exact hf.comp (primrec_redStack.comp Primrec.encode).to_comp
  · funext c
    have hu := undecTSM_halts_iff (Encodable.encode c)
    rw [univFun, Denumerable.ofNat_encode] at hu
    have := congrFun hfeq (redStack (Encodable.encode c))
    simp only at this
    simp only [eq_iff_iff]
    rw [← hu, ← inter_gram_iff, this]

/-- **Intersection is undecidable even with the first grammar fixed.** -/
theorem not_computablePred_inter_fixed :
    ¬ ComputablePred fun g : Grammar => Inter gram₁ g := by
  intro h
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.1 h
  exact not_computable_inter_gram hf fun s => by
    have := congrFun hfeq (gram undecTSM true s); simp only at this; rw [this]

/-- **The intersection problem of context-free grammars is undecidable.** -/
theorem not_computablePred_inter :
    ¬ ComputablePred fun gg : Grammar × Grammar => Inter gg.1 gg.2 := by
  intro h
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.1 h
  refine not_computable_inter_gram (f := fun g => f (gram₁, g))
    (hf.comp ((Computable.const _).pair Computable.id)) fun s => ?_
  have := congrFun hfeq (gram₁, gram undecTSM true s); simp only at this; rw [this]

/-- **Undecidable already for grammars whose right-hand sides have at most two symbols.** -/
theorem not_computablePred_inter_binary :
    ¬ ∃ f : Grammar × Grammar → Bool, Computable f ∧
      ∀ g₁ g₂, g₁.IsBinary → g₂.IsBinary → (f (g₁, g₂) = true ↔ Inter g₁ g₂) := by
  rintro ⟨f, hf, hfeq⟩
  exact not_computable_inter_gram (f := fun g => f (gram₁, g))
    (hf.comp ((Computable.const _).pair Computable.id)) fun s =>
      hfeq _ _ isBinary_gram isBinary_gram

end CFG

end HTN
