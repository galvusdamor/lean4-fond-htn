import ComplexityTheory.Petri.CharDec
/-!
# Concrete alternatives of the decomposition steps

For each decomposition step the alternatives are computed on concrete blocks, and decoding
commutes with them (`*_dec` lemmas: the abstract alternatives of the decoded block are the decoded
concrete alternatives).
-/

namespace HTN

namespace Petri

namespace KLM

open Finset Euler Comp Classical

variable {d : ℕ}

@[simp] theorem cPre_mk (p : CV) (i : CW) (c : CC) (o : CW) : cPre (p, i, c, o) = p := rfl
@[simp] theorem cInp_mk (p : CV) (i : CW) (c : CC) (o : CW) : cInp (p, i, c, o) = i := rfl
@[simp] theorem cComp_mk (p : CV) (i : CW) (c : CC) (o : CW) : cComp (p, i, c, o) = c := rfl
@[simp] theorem cOut_mk (p : CV) (i : CW) (c : CC) (o : CW) : cOut (p, i, c, o) = o := rfl

/-! ### Sub-components -/

/-- The concrete sub-component. -/
def csub (c : CC) (p : ℕ → Bool) (q : CE → Bool) (s t : ℕ) : CC :=
  ((cNodes c).filter p, cLabs c, (cEdges c).filter q, s, t)

theorem decC_csub (c : CC) (p : ℕ → Bool) (q : CE → Bool) (s t : ℕ) (P : ℕ → Prop)
    [DecidablePred P] (Q : Edge (Fin d) → Prop) [DecidablePred Q] (hp : ∀ n, P n ↔ p n = true)
    (hq : ∀ e, Q (decE d e) ↔ q e = true) :
    decC d (csub c p q s t) = (decC d c).sub P Q s t := by
  simp only [decC, csub, Comp.sub, cNodes, cLabs, cEdges, cEntry, cExit, Comp.mk.injEq, true_and,
    and_true]
  refine ⟨List.filter_congr fun n _ => by simp [hp n], ?_⟩
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun e _ => by simp [Function.comp, hq e]

/-! ### Pruning -/

/-- Concrete restriction of a block to a set of nodes, with given entry and exit. -/
def crestr (b : CB) (R : ℕ → Bool) (s t : ℕ) : CC :=
  csub (cComp b) R (fun e => R e.1 && R e.2.2) s t

theorem decC_crestr (b : CB) (R : List ℕ) (s t : ℕ) :
    decC d (crestr b (fun n => decide (n ∈ R)) s t) = (decB d b).restr (· ∈ R) s t := by
  unfold crestr Block.restr
  rw [decC_csub (P := (· ∈ R)) (Q := fun e => e.1 ∈ R ∧ e.2.2 ∈ R)]
  · rfl
  · intro n; simp
  · intro e; simp [decE]

/-- Concrete pruning alternatives. -/
def cprune (b : CB) (R : List ℕ) : List (List CB) :=
  if cExit (cComp b) ∈ R then
    [[(cPre b, cInp b, crestr b (fun n => decide (n ∈ R)) (cEntry (cComp b)) (cExit (cComp b)),
      cOut b)]]
  else []

theorem prune_dec (b : CB) (R : List ℕ) :
    pruneAlts (decB d b) (· ∈ R) = (cprune b R).map (List.map (decB d)) := by
  unfold pruneAlts cprune
  split_ifs with h1 h2 h2
  · rw [List.map_singleton, List.map_singleton]
    show [[Block.mk _ _ _ _]] = [[Block.mk _ _ _ _]]
    simp only [cPre_mk, cInp_mk, cComp_mk, cOut_mk, decC_crestr]
    rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-! ### Splitting -/

/-- Concrete split alternatives. -/
def csplit (b : CB) (S : List ℕ) : List (List CB) :=
  if cExit (cComp b) ∈ S then
    [[(cPre b, cInp b, crestr b (fun n => decide (n ∈ S)) (cEntry (cComp b)) (cExit (cComp b)),
      cOut b)]]
  else ((cEdges (cComp b)).filter fun e => decide (e.1 ∈ S ∧ e.2.2 ∉ S)).map fun e =>
    [(cPre b, cInp b, crestr b (fun n => decide (n ∈ S)) (cEntry (cComp b)) e.1,
        (cLabs (cComp b)).getD e.1 []),
      (e.2.1, (cLabs (cComp b)).getD e.2.2 [],
        crestr b (fun n => decide (n ∉ S)) e.2.2 (cExit (cComp b)), cOut b)]

theorem decC_crestr_not (b : CB) (S : List ℕ) (s t : ℕ) :
    decC d (crestr b (fun n => decide (n ∉ S)) s t) = (decB d b).restr (fun v => ¬ v ∈ S) s t := by
  unfold crestr Block.restr
  rw [decC_csub (P := fun v => ¬ v ∈ S) (Q := fun e => ¬ e.1 ∈ S ∧ ¬ e.2.2 ∈ S)]
  · rfl
  · intro n; simp
  · intro e; simp [decE]

theorem split_dec (b : CB) (S : List ℕ) :
    splitAlts (decB d b) (· ∈ S) = (csplit b S).map (List.map (decB d)) := by
  unfold splitAlts csplit
  split_ifs with h1 h2 h2
  · rw [List.map_singleton, List.map_singleton]
    show [[Block.mk _ _ _ _]] = [[Block.mk _ _ _ _]]
    simp only [cPre_mk, cInp_mk, cComp_mk, cOut_mk, decC_crestr]
    rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · simp only [decB_comp, decC_edges, List.map_map]
    rw [List.filter_map, List.map_map]
    rw [List.filter_congr (q := fun e => decide (e.1 ∈ S ∧ e.2.2 ∉ S)) fun e _ => by simp [decE]]
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp, List.map_cons, List.map_nil, splitFst, splitSnd]
    show [Block.mk _ _ _ _, Block.mk _ _ _ _] = [Block.mk _ _ _ _, Block.mk _ _ _ _]
    simp only [cPre_mk, cInp_mk, cComp_mk, cOut_mk, decC_crestr, decC_crestr_not]
    rfl

/-! ### Bounded edges -/

/-- The concrete component without the edge `ce` (decoded equality), with given entry and exit. -/
def cminus (d : ℕ) (b : CB) (ce : CE) (s t : ℕ) : CC :=
  csub (cComp b) (fun _ => true) (fun e => !ceqB d e ce) s t

theorem decC_cminus {_ : DecidableEq (Edge (Fin d))} (b : CB) (ce : CE) (s t : ℕ) :
    decC d (cminus d b ce s t) = (decB d b).minus (decE d ce) s t := by
  unfold cminus Block.minus
  rw [decC_csub (P := fun _ => True) (Q := (· ≠ decE d ce))]
  · rfl
  · intro n; simp
  · intro e
    rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, ne_eq, ceqB_iff]

/-- The concrete chain. -/
def cchain (d : ℕ) (b : CB) (ce : CE) (pre : CV) (inp : CW) (u : ℕ) : ℕ → List CB
  | 0 => [(pre, inp, cminus d b ce u (cExit (cComp b)), cOut b)]
  | n + 1 => (pre, inp, cminus d b ce u ce.1, (cLabs (cComp b)).getD ce.1 []) ::
      cchain d b ce ce.2.1 ((cLabs (cComp b)).getD ce.2.2 []) ce.2.2 n

theorem chain_dec {inst : DecidableEq (Edge (Fin d))} (b : CB) (ce : CE) (pre : CV) (inp : CW) (u : ℕ) : ∀ n,
    chainFrom (decB d b) (decE d ce) (decV d pre) (decW d inp) u n =
      (cchain d b ce pre inp u n).map (decB d)
  | 0 => by
    simp only [chainFrom, cchain, List.map_cons, List.map_nil]
    show [Block.mk _ _ _ _] = [Block.mk _ _ _ _]
    simp only [cPre_mk, cInp_mk, cComp_mk, cOut_mk, decC_cminus]
    rfl
  | n + 1 => by
    have ih := chain_dec (inst := inst) b ce ce.2.1 ((cLabs (cComp b)).getD ce.2.2 []) ce.2.2 n
    simp only [chainFrom, cchain, List.map_cons]
    show Block.mk _ _ _ _ :: chainFrom (decB d b) (decE d ce) (decV d ce.2.1)
      (decW d ((cLabs (cComp b)).getD ce.2.2 [])) ce.2.2 n = _
    rw [ih]
    show Block.mk _ _ _ _ :: _ = Block.mk _ _ _ _ :: _
    simp only [cPre_mk, cInp_mk, cComp_mk, cOut_mk, decC_cminus]
    rfl

/-- Concrete alternatives for a bounded edge. -/
def cedgeAlts (d : ℕ) (b : CB) (ce : CE) (B : ℕ) : List (List CB) :=
  (List.range (B + 1)).map (cchain d b ce (cPre b) (cInp b) (cEntry (cComp b)))

theorem edge_dec {_ : DecidableEq (Edge (Fin d))} (b : CB) (ce : CE) (B : ℕ) :
    edgeAlts (decB d b) (decE d ce) B = (cedgeAlts d b ce B).map (List.map (decB d)) := by
  unfold edgeAlts cedgeAlts
  rw [List.map_map]
  refine List.map_congr_left fun n _ => ?_
  exact chain_dec b ce _ _ _ n

/-! ### Bounded boundary coordinates -/

/-- Setting coordinate `j` of an `ω`-vector to `k`. -/
def cupd (d : ℕ) (w : CW) (j k : ℕ) : CW :=
  (List.range d).map fun i => if i = j then some k else w.getD i none

theorem decW_cupd {_ : DecidableEq (Fin d)} (w : CW) (j : Fin d) (k : ℕ) :
    decW d (cupd d w j k) = Function.update (decW d w) j (k : ℕ∞) := by
  funext i
  simp only [decW, cupd]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  by_cases h : i = j
  · subst h; simp [decO]
  · rw [if_neg (fun h' => h (Fin.ext h')), Function.update_of_ne h]
    rfl

/-- Concrete alternatives for a bounded input coordinate. -/
def cinpAlts (d : ℕ) (b : CB) (j B : ℕ) : List (List CB) :=
  (List.range (B + 1)).map fun k => [(cPre b, cupd d (cInp b) j k, cComp b, cOut b)]

/-- Concrete alternatives for a bounded output coordinate. -/
def coutAlts (d : ℕ) (b : CB) (j B : ℕ) : List (List CB) :=
  (List.range (B + 1)).map fun k => [(cPre b, cInp b, cComp b, cupd d (cOut b) j k)]

theorem inp_dec {_ : DecidableEq (Fin d)} (b : CB) (j : Fin d) (B : ℕ) :
    inpAlts (decB d b) j B = (cinpAlts d b j B).map (List.map (decB d)) := by
  unfold inpAlts cinpAlts
  rw [List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, List.map_cons, List.map_nil]
  show [Block.mk _ _ _ _] = [Block.mk _ _ _ _]
  simp only [cPre_mk, cInp_mk, cComp_mk, cOut_mk, decW_cupd]
  rfl

theorem out_dec {_ : DecidableEq (Fin d)} (b : CB) (j : Fin d) (B : ℕ) :
    outAlts (decB d b) j B = (coutAlts d b j B).map (List.map (decB d)) := by
  unfold outAlts coutAlts
  rw [List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, List.map_cons, List.map_nil]
  show [Block.mk _ _ _ _] = [Block.mk _ _ _ _]
  simp only [cPre_mk, cInp_mk, cComp_mk, cOut_mk, decW_cupd]
  rfl

end KLM

end Petri

end HTN
