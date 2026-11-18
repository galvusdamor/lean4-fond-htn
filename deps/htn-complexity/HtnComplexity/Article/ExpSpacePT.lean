import HtnComplexity.Article.ExpSpaceNum
import HtnComplexity.Article.StripsHard
/-!
# The tail-recursive encoding is computed in polynomial time

The written-out bodies `HTN.SpaceEnc.nbP` of the rendering `HTN.SpaceEnc.rendP` are given
explicitly in terms of numbers (`HTN.SpaceEnc.nbN`, with the action descriptions `wbD`, `rbD`,
…), and are computed in polynomial time from `m` and `n'` given in unary
(`HTN.SpaceEnc.pt_nbN`).
-/

namespace HTN

namespace SpaceEnc

open TM Syn Syn.PolyDom PTime Article

/-! ### The facts and actions as numbers -/

def fpc (s : ℕ) : ℕ := Nat.pair 2 s
def fcb (j x : ℕ) : ℕ := Nat.pair 3 (Nat.pair j x)
def fhb (j x : ℕ) : ℕ := Nat.pair 4 (Nat.pair j x)
def fst (q : ℕ) : ℕ := Nat.pair 5 q
def fsym (g : ℕ) : ℕ := Nat.pair 6 g
def fmv (μ : ℕ) : ℕ := Nat.pair 7 μ
def fpar (p : ℕ) : ℕ := Nat.pair 8 p
def ffirst : ℕ := Nat.pair 9 0
def fu (j : ℕ) : ℕ := Nat.pair 10 j
def feq : ℕ := Nat.pair 11 0
def fneq : ℕ := Nat.pair 12 0
def fdrain : ℕ := Nat.pair 13 0
def fboot : ℕ := Nat.pair 0 0
def finp (i b : ℕ) : ℕ := Nat.pair 1 (Nat.pair i b)

/-- The symbols of `Option Bool`, as a list. -/
noncomputable def symL : List (Option Bool) := (Finset.univ : Finset (Option Bool)).toList

/-- The facts of all symbols. -/
noncomputable def symF : List ℕ := symL.map fun g => fsym (symCode g)

section Acts

variable (m n' : ℕ)

def bootD (q₀ : ℕ) : ActionDesc :=
  (Nat.pair 0 0, [fboot], [fpc 0, fst q₀, fpar 1, ffirst, fu 0, feq] ++
    (List.range m).map (fcb · 0) ++ (List.range m).map (fhb · 0), [fboot])
def wsD (p : Bool) : ActionDesc := (Nat.pair 1 p.toNat, [fpc 0, fpar p.toNat], [fpc 1], [fpc 0])
def wbD (p : Bool) (j : ℕ) (x e : Bool) : ActionDesc :=
  (Nat.pair 2 (Nat.pair (Nat.pair p.toNat j) (Nat.pair x.toNat e.toNat)),
    [fpc (j + 1), fcb j x.toNat, fhb j (if e then x else !x).toNat, fpar p.toNat],
    [fpc (j + 2)] ++ (if e then [] else [fneq]), [fpc (j + 1)] ++ (if e then [] else [feq]))
def rbD (p : Bool) (j : ℕ) (x : Bool) : ActionDesc :=
  (Nat.pair 3 (Nat.pair (Nat.pair p.toNat j) x.toNat), [fpc (2 * m + 1 - j), fcb j x.toNat],
    [fpc (2 * m + 2 - j)], [fpc (2 * m + 1 - j)])
noncomputable def rvD (p : Bool) (g : ℕ) : ActionDesc :=
  (Nat.pair 4 (Nat.pair p.toNat g), [fpc (m + 1), fpar (!p).toNat], [fpc (m + 2), fsym g],
    [fpc (m + 1)] ++ symF)
noncomputable def riD (i : ℕ) (b : Bool) : ActionDesc :=
  (Nat.pair 5 (Nat.pair i b.toNat), [fpc (m + 1), ffirst, fu i, finp i b.toNat],
    [fpc (2 * m + 2), fu (i + 1), fsym (symCode (some b))], [fpc (m + 1), fu i] ++ symF)
noncomputable def rblankD (gb : ℕ) : ActionDesc :=
  (Nat.pair 6 0, [fpc (m + 1), ffirst, fu n'], [fpc (2 * m + 2), fsym gb], [fpc (m + 1)] ++ symF)
def cpD (p : Bool) (g : ℕ) : ActionDesc :=
  (Nat.pair 7 (Nat.pair p.toNat g), [fpc (2 * m + 2), fneq, fsym g, fpar p.toNat],
    [fpc (2 * m + 3)], [fpc (2 * m + 2)])
def trD (p : Bool) (d : ℕ × ℕ × ℕ × ℕ × ℕ) : ActionDesc :=
  (Nat.pair 8 (Nat.pair (Nat.pair p.toNat d.1) (Nat.pair (Nat.pair d.2.1 d.2.2.1)
      (Nat.pair d.2.2.2.1 d.2.2.2.2))),
    [fpc (2 * m + 2), feq, fsym d.2.1, fst d.1, fpar p.toNat],
    [fpc (2 * m + 3), fst d.2.2.1, fmv d.2.2.2.2], [fpc (2 * m + 2), fst d.1])
def incD (p : Bool) (j : ℕ) : ActionDesc :=
  (Nat.pair 9 (Nat.pair p.toNat j), [fpc (2 * m + 3), fpar p.toNat, fcb j 0] ++
      (List.range j).map (fcb · 1),
    [fpc 0, fcb j 1, feq] ++ (List.range j).map (fcb · 0),
    [fpc (2 * m + 3), fcb j 0, fneq] ++ (List.range j).map (fcb · 1))
def wrapD (p : Bool) : ActionDesc :=
  (Nat.pair 10 p.toNat, [fpc (2 * m + 3), fpar p.toNat] ++ (List.range m).map (fcb · 1),
    [fpc (2 * m + 4), feq] ++ (List.range m).map (fcb · 0),
    [fpc (2 * m + 3), fneq] ++ (List.range m).map (fcb · 1))
def hincD (p : Bool) (j : ℕ) : ActionDesc :=
  (Nat.pair 11 (Nat.pair p.toNat j), [fpc (2 * m + 4), fpar p.toNat, fmv 2, fhb j 0] ++
      (List.range j).map (fhb · 1),
    [fpc 0, fpar (!p).toNat, fhb j 1] ++ (List.range j).map (fhb · 0),
    [fpc (2 * m + 4), fpar p.toNat, fmv 2, ffirst, fhb j 0] ++ (List.range j).map (fhb · 1))
def hdecD (p : Bool) (j : ℕ) : ActionDesc :=
  (Nat.pair 12 (Nat.pair p.toNat j), [fpc (2 * m + 4), fpar p.toNat, fmv 0, fhb j 1] ++
      (List.range j).map (fhb · 0),
    [fpc 0, fpar (!p).toNat, fhb j 0] ++ (List.range j).map (fhb · 1),
    [fpc (2 * m + 4), fpar p.toNat, fmv 0, ffirst, fhb j 1] ++ (List.range j).map (fhb · 0))
def hdec0D (p : Bool) : ActionDesc :=
  (Nat.pair 13 p.toNat, [fpc (2 * m + 4), fpar p.toNat, fmv 0] ++ (List.range m).map (fhb · 0),
    [fpc 0, fpar (!p).toNat], [fpc (2 * m + 4), fpar p.toNat, fmv 0, ffirst])
def hstayD (p : Bool) : ActionDesc :=
  (Nat.pair 14 p.toNat, [fpc (2 * m + 4), fpar p.toNat, fmv 1], [fpc 0, fpar (!p).toNat],
    [fpc (2 * m + 4), fpar p.toNat, fmv 1, ffirst])
def finD (q : ℕ) : ActionDesc :=
  (Nat.pair 15 q, [fpc 0, fst q] ++ (List.range m).map (fcb · 0),
    [fpc (m + 1), fdrain, fpar 1, fpar 0] ++ (List.range m).map (fcb · 1) ++
      (List.range m).map (fcb · 0), [fpc 0])
def drnD : ActionDesc := (Nat.pair 16 0, [fpc (2 * m + 2), fdrain], [fpc (m + 1)], [fpc (2 * m + 2)])

end Acts

/-! ### The actions of the encoding are these -/

section Eq

variable {k : ℕ} (m n' : ℕ) (N : NTM (Fin k) (Option Bool))

theorem symFacts_eq : (symFacts : List (Fct (Fin k) (Option Bool))).map cFP = symF := by
  simp [symFacts, symF, symL, List.map_map, Function.comp_def, cFP, fsym]

theorem actDP_boot : actDP m n' N Act.boot = bootD m N.init.val := by
  simp [actDP, precL, addL, delL, cFP, cAP, bootD, fboot, fpc, fst, fpar, ffirst, fu, feq, fcb,
    fhb, List.map_map, Function.comp_def]

theorem actDP_ws (p : Bool) : actDP m n' N (Act.ws p) = wsD p := by
  simp [actDP, precL, addL, delL, cFP, cAP, wsD, fpc, fpar]

theorem actDP_wb (p : Bool) (j : ℕ) (x e : Bool) : actDP m n' N (Act.wb p j x e) = wbD p j x e := by
  cases e <;> simp [actDP, precL, addL, delL, cFP, cAP, wbD, fpc, fpar, fcb, fhb, feq, fneq]

theorem actDP_rb (p : Bool) (j : ℕ) (x : Bool) : actDP m n' N (Act.rb p j x) = rbD m p j x := by
  simp [actDP, precL, addL, delL, cFP, cAP, rbD, fpc, fcb]

theorem actDP_rv (p : Bool) (g : Option Bool) : actDP m n' N (Act.rv p g) = rvD m p (symCode g) := by
  simp [actDP, precL, addL, delL, cFP, cAP, rvD, fpc, fpar, fsym, symFacts_eq]

theorem actDP_ri (i : ℕ) (b : Bool) : actDP m n' N (Act.ri i b) = riD m i b := by
  simp [actDP, precL, addL, delL, cFP, cAP, riD, fpc, ffirst, fu, finp, fsym, symFacts_eq]

theorem actDP_rblank : actDP m n' N Act.rblank = rblankD m n' (symCode N.blank) := by
  simp [actDP, precL, addL, delL, cFP, cAP, rblankD, fpc, ffirst, fu, fsym, symFacts_eq]

theorem actDP_cp (p : Bool) (g : Option Bool) : actDP m n' N (Act.cp p g) = cpD m p (symCode g) := by
  simp [actDP, precL, addL, delL, cFP, cAP, cpD, fpc, fneq, fsym, fpar]

theorem actDP_tr (p : Bool) (q₀ : Fin k) (g₀ : Option Bool) (q₁ : Fin k) (g₁ : Option Bool)
    (μ : Move) : actDP m n' N (Act.tr p q₀ g₀ q₁ g₁ μ) =
      trD m p (q₀.val, symCode g₀, q₁.val, symCode g₁, moveCode μ) := by
  simp [actDP, precL, addL, delL, cFP, cAP, trD, fpc, feq, fsym, fst, fpar, fmv]

theorem actDP_inc (p : Bool) (j : ℕ) : actDP m n' N (Act.inc p j) = incD m p j := by
  simp [actDP, precL, addL, delL, cFP, cAP, incD, fpc, fpar, fcb, feq, fneq, List.map_map,
    Function.comp_def]

theorem actDP_wrap (p : Bool) : actDP m n' N (Act.wrap p) = wrapD m p := by
  simp [actDP, precL, addL, delL, cFP, cAP, wrapD, fpc, fpar, fcb, feq, fneq, List.map_map,
    Function.comp_def]

theorem actDP_hinc (p : Bool) (j : ℕ) : actDP m n' N (Act.hinc p j) = hincD m p j := by
  simp [actDP, precL, addL, delL, cFP, cAP, hincD, fpc, fpar, fhb, fmv, ffirst, moveCode,
    List.map_map, Function.comp_def]

theorem actDP_hdec (p : Bool) (j : ℕ) : actDP m n' N (Act.hdec p j) = hdecD m p j := by
  simp [actDP, precL, addL, delL, cFP, cAP, hdecD, fpc, fpar, fhb, fmv, ffirst, moveCode,
    List.map_map, Function.comp_def]

theorem actDP_hdec0 (p : Bool) : actDP m n' N (Act.hdec0 p) = hdec0D m p := by
  simp [actDP, precL, addL, delL, cFP, cAP, hdec0D, fpc, fpar, fhb, fmv, ffirst, moveCode,
    List.map_map, Function.comp_def]

theorem actDP_hstay (p : Bool) : actDP m n' N (Act.hstay p) = hstayD m p := by
  simp [actDP, precL, addL, delL, cFP, cAP, hstayD, fpc, fpar, fmv, ffirst, moveCode]

theorem actDP_fin (q : Fin k) : actDP m n' N (Act.fin q) = finD m q.val := by
  simp [actDP, precL, addL, delL, cFP, cAP, finD, fpc, fst, fcb, fdrain, fpar, List.map_map,
    Function.comp_def]

theorem actDP_drn : actDP m n' N Act.drn = drnD m := by
  simp [actDP, precL, addL, delL, cFP, cAP, drnD, fpc, fdrain]

end Eq

/-! ### The bodies as numbers -/

section Bodies

variable (m n' : ℕ)

/-- The bodies of one loop parity, as numbers. -/
noncomputable def bodiesPN (p : Bool) (transN : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : List NBody :=
  [(eCP (.loop p), [[Sum.inr (eCP (.block p)), Sum.inr (eCP (.loop p))]]), (eCP (.loop p), []),
    (eCP (.block p), [[Sum.inr (eCP (.tree p m))], [Sum.inr (eCP (.reT p))]]),
    (eCP (.tree p 0), [[Sum.inl (wsD p), Sum.inr (eCP (.bit p 0))]])] ++
  (List.range m).map (fun j => (eCP (.tree p (j + 1)),
    [[Sum.inr (eCP (.tree p j))], [Sum.inr (eCP (.tree p j))]])) ++
  (List.range m).flatMap (fun j => [true, false].flatMap fun x => [true, false].map fun e =>
    (eCP (.bit p j), [[Sum.inl (wbD p j x e), Sum.inr (eCP (.bit p (j + 1))), Sum.inl (rbD m p j x)]])) ++
  [(eCP (.bit p m), if p then [[Sum.inr (eCP .rd0), Sum.inr (eCP (.core p))]]
    else [[Sum.inr (eCP (.core p))]])] ++
  symL.map (fun g => (eCP (.core p), [[Sum.inl (cpD m p (symCode g)), Sum.inr (eCP (.incT p)),
    Sum.inl (rvD m p (symCode g))]])) ++
  transN.map (fun t => (eCP (.core p), [[Sum.inl (trD m p t), Sum.inr (eCP (.incT p)),
    Sum.inl (rvD m p t.2.2.2.1)]])) ++
  (List.range m).map (fun j => (eCP (.incT p), [[Sum.inl (incD m p j)]])) ++
  [(eCP (.incT p), [[Sum.inl (wrapD m p)]])] ++
  (List.range m).map (fun j => (eCP (.reT p), [[Sum.inl (hincD m p j)]])) ++
  (List.range m).map (fun j => (eCP (.reT p), [[Sum.inl (hdecD m p j)]])) ++
  [(eCP (.reT p), [[Sum.inl (hdec0D m p)]]), (eCP (.reT p), [[Sum.inl (hstayD m p)]])]

/-- **The bodies of the encoding, as numbers.** -/
noncomputable def nbN (q₀ gb : ℕ) (transN : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (accN : List ℕ) :
    List NBody :=
  [(eCP .root, [[Sum.inl (bootD m q₀), Sum.inr (eCP .main)]]),
    (eCP .main, [[Sum.inr (eCP (.loop true))], [Sum.inr (eCP (.loop false))], [Sum.inr (eCP .finish)]]),
    (eCP .rd0, []), (eCP .rd0, [[Sum.inl (rblankD m n' gb)]])] ++
  (List.range n').flatMap (fun i => [true, false].map fun b => (eCP .rd0, [[Sum.inl (riD m i b)]])) ++
  bodiesPN m true transN ++ bodiesPN m false transN ++
  accN.map (fun q => (eCP .finish, [[Sum.inl (finD m q), Sum.inr (eCP .drainT)]])) ++
  [(eCP .drainT, [[Sum.inl (drnD m), Sum.inr (eCP .drainT)]]), (eCP .drainT, [])]

variable {k : ℕ} (N : NTM (Fin k) (Option Bool))

/-- The transitions, as numbers. -/
noncomputable def transN : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (transL N).map fun d => (d.1.val, symCode d.2.1, d.2.2.1.val, symCode d.2.2.2.1, moveCode d.2.2.2.2)

/-- The accepting states, as numbers. -/
noncomputable def accN : List ℕ := (accL N).map Fin.val

theorem bodiesP_map (p : Bool) :
    (bodiesP m N p).map (fun b => (eCP b.1, b.2.map (·.map (Sum.map (actDP m n' N) eCP)))) =
      bodiesPN m p (transN N) := by
  cases p <;>
  simp [bodiesP, bodiesPN, transN, symL, List.map_map, Function.comp_def, List.map_flatMap,
    actDP_ws, actDP_wb, actDP_rb, actDP_cp, actDP_rv, actDP_tr, actDP_inc, actDP_wrap, actDP_hinc,
    actDP_hdec, actDP_hdec0, actDP_hstay]

/-- **The written-out bodies are the bodies as numbers.** -/
theorem nbP_eq : nbP m n' N = nbN m n' N.init.val (symCode N.blank) (transN N) (accN N) := by
  unfold nbP bodies nbN
  simp only [List.map_append]
  rw [bodiesP_map, bodiesP_map]
  simp [accN, List.map_map, Function.comp_def, List.map_flatMap, actDP_boot, actDP_rblank,
    actDP_ri, actDP_fin, actDP_drn]

end Bodies

/-! ### Polynomial time -/

section PTime

variable {α : Type} [BEnc α]

theorem pt_toNat {b : α → Bool} (hb : PT b) : PT fun a => (b a).toNat :=
  (PT.cond hb (PT.const 1) (PT.const 0)).of_eq fun a => by cases b a <;> rfl

theorem pt_pairC (c : ℕ) {f : α → ℕ} (hf : PT f) : PT fun a => Nat.pair c (f a) :=
  PT.natPair (PT.const c) hf

theorem length_filter_range_le (n k : ℕ) :
    ((List.range n).filter fun j => decide (k ≤ j)).length = n - k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : k ≤ n <;> simp [h] <;> omega

/-- A length minus a number. -/
theorem pt_lenSub {l : α → List Unit} {k : α → ℕ} (hl : PT l) (hk : PT k) :
    PT fun a => (l a).length - k a :=
  (PT.length (PT.filter (p := fun a (j : ℕ) => decide (k a ≤ j)) (PT.rangeLength hl)
    (PT.le (hk.comp PT.fst) PT.snd))).of_eq fun a => length_filter_range_le _ _

theorem range_eq_filter : ∀ {m j : ℕ}, j ≤ m →
    List.range j = (List.range m).filter fun i => decide (i < j) := by
  intro m
  induction m with
  | zero => intro j h; obtain rfl : j = 0 := by omega
            rfl
  | succ m ih =>
    intro j h
    rcases Nat.lt_or_ge m j with hj | hj
    · obtain rfl : j = m + 1 := by omega
      rw [List.filter_eq_self.2 fun i hi => by simp at hi ⊢; omega]
    · rw [List.range_succ, List.filter_append, ← ih hj]
      simp; omega

theorem pt_addC (c : ℕ) {f : α → ℕ} (hf : PT f) : PT fun a => f a + c :=
  (PT.affine 1 c hf).of_eq fun a => by ring

theorem pt_affC (c d : ℕ) {f : α → ℕ} (hf : PT f) : PT fun a => c * f a + d := PT.affine c d hf

/-- The action descriptions with the list `range j` given as an argument. -/
def incDr (m : ℕ) (p : Bool) (j : ℕ) (r : List ℕ) : ActionDesc :=
  (Nat.pair 9 (Nat.pair p.toNat j), [fpc (2 * m + 3), fpar p.toNat, fcb j 0] ++ r.map (fcb · 1),
    [fpc 0, fcb j 1, feq] ++ r.map (fcb · 0), [fpc (2 * m + 3), fcb j 0, fneq] ++ r.map (fcb · 1))
def hincDr (m : ℕ) (p : Bool) (j : ℕ) (r : List ℕ) : ActionDesc :=
  (Nat.pair 11 (Nat.pair p.toNat j), [fpc (2 * m + 4), fpar p.toNat, fmv 2, fhb j 0] ++ r.map (fhb · 1),
    [fpc 0, fpar (!p).toNat, fhb j 1] ++ r.map (fhb · 0),
    [fpc (2 * m + 4), fpar p.toNat, fmv 2, ffirst, fhb j 0] ++ r.map (fhb · 1))
def hdecDr (m : ℕ) (p : Bool) (j : ℕ) (r : List ℕ) : ActionDesc :=
  (Nat.pair 12 (Nat.pair p.toNat j), [fpc (2 * m + 4), fpar p.toNat, fmv 0, fhb j 1] ++ r.map (fhb · 0),
    [fpc 0, fpar (!p).toNat, fhb j 0] ++ r.map (fhb · 1),
    [fpc (2 * m + 4), fpar p.toNat, fmv 0, ffirst, fhb j 1] ++ r.map (fhb · 0))

variable {L : α → List Unit} (hL : PT L)
include hL

theorem pt_m : PT fun a => (L a).length := PT.length hL

theorem pt_bootD (q₀ : ℕ) : PT fun a => bootD (L a).length q₀ := by
  unfold bootD fcb fhb
  exact PT.pair (PT.const _) (PT.pair (PT.const _) (PT.pair (PT.append (PT.append (PT.const _)
    (PT.map (PT.rangeLength hL) (pt_pairC 3 (PT.natPair PT.snd (PT.const 0)))))
    (PT.map (PT.rangeLength hL) (pt_pairC 4 (PT.natPair PT.snd (PT.const 0))))) (PT.const _)))

theorem pt_rbD (p x : Bool) {j : α → ℕ} (hj : PT j) : PT fun a => rbD (L a).length p (j a) x := by
  have h1 : PT fun a => 2 * (L a).length + 1 - j a :=
    (pt_lenSub (PT.append (PT.append hL hL) (PT.const [()])) hj).of_eq fun a => by simp; ring_nf
  have h2 : PT fun a => 2 * (L a).length + 2 - j a :=
    (pt_lenSub (PT.append (PT.append hL hL) (PT.const [(), ()])) hj).of_eq fun a => by simp; ring_nf
  unfold rbD fpc fcb
  exact PT.pair (pt_pairC 3 (PT.natPair (pt_pairC _ hj) (PT.const _))) (PT.pair
    (PT.cons (pt_pairC 2 h1) (PT.single (pt_pairC 3 (PT.natPair hj (PT.const _)))))
    (PT.pair (PT.single (pt_pairC 2 h2)) (PT.single (pt_pairC 2 h1))))

theorem pt_rvD (p : Bool) {g : α → ℕ} (hg : PT g) : PT fun a => rvD (L a).length p (g a) := by
  have hm := pt_m hL
  unfold rvD fpc fsym
  exact PT.pair (pt_pairC 4 (PT.natPair (PT.const _) hg)) (PT.pair
    (PT.cons (pt_pairC 2 (pt_addC 1 hm)) (PT.const _))
    (PT.pair (PT.cons (pt_pairC 2 (pt_addC 2 hm)) (PT.single (pt_pairC 6 hg)))
      (PT.append (PT.single (pt_pairC 2 (pt_addC 1 hm))) (PT.const _))))

theorem pt_riD {i : α → ℕ} (hi : PT i) (b : Bool) : PT fun a => riD (L a).length (i a) b := by
  have hm := pt_m hL
  unfold riD fpc fu finp
  exact PT.pair (pt_pairC 5 (PT.natPair hi (PT.const _))) (PT.pair
    (PT.cons (pt_pairC 2 (pt_addC 1 hm)) (PT.cons (PT.const _) (PT.cons (pt_pairC 10 hi)
      (PT.single (pt_pairC 1 (PT.natPair hi (PT.const _)))))))
    (PT.pair (PT.cons (pt_pairC 2 (pt_affC 2 2 hm)) (PT.cons (pt_pairC 10 (pt_addC 1 hi))
      (PT.const _)))
      (PT.append (PT.cons (pt_pairC 2 (pt_addC 1 hm)) (PT.single (pt_pairC 10 hi))) (PT.const _))))

theorem pt_rblankD {L' : α → List Unit} (hL' : PT L') (gb : ℕ) :
    PT fun a => rblankD (L a).length (L' a).length gb := by
  have hm := pt_m hL
  unfold rblankD fpc fu
  exact PT.pair (PT.const _) (PT.pair
    (PT.cons (pt_pairC 2 (pt_addC 1 hm)) (PT.cons (PT.const _) (PT.single (pt_pairC 10
      (PT.length hL')))))
    (PT.pair (PT.cons (pt_pairC 2 (pt_affC 2 2 hm)) (PT.const _))
      (PT.append (PT.single (pt_pairC 2 (pt_addC 1 hm))) (PT.const _))))

theorem pt_cpD (p : Bool) {g : α → ℕ} (hg : PT g) : PT fun a => cpD (L a).length p (g a) := by
  have hm := pt_m hL
  unfold cpD fpc fsym
  exact PT.pair (pt_pairC 7 (PT.natPair (PT.const _) hg)) (PT.pair
    (PT.cons (pt_pairC 2 (pt_affC 2 2 hm)) (PT.cons (PT.const _) (PT.cons (pt_pairC 6 hg)
      (PT.const _))))
    (PT.pair (PT.single (pt_pairC 2 (pt_affC 2 3 hm))) (PT.single (pt_pairC 2 (pt_affC 2 2 hm)))))

theorem pt_trD (p : Bool) {t : α → ℕ × ℕ × ℕ × ℕ × ℕ} (ht : PT t) :
    PT fun a => trD (L a).length p (t a) := by
  have hm := pt_m hL
  have h1 := PT.fst' ht
  have h2 := PT.fst' (PT.snd' ht)
  have h3 := PT.fst' (PT.snd' (PT.snd' ht))
  have h4 := PT.fst' (PT.snd' (PT.snd' (PT.snd' ht)))
  have h5 := PT.snd' (PT.snd' (PT.snd' (PT.snd' ht)))
  unfold trD fpc fsym fst fmv
  exact PT.pair (pt_pairC 8 (PT.natPair (pt_pairC _ h1) (PT.natPair (PT.natPair h2 h3)
    (PT.natPair h4 h5)))) (PT.pair
    (PT.cons (pt_pairC 2 (pt_affC 2 2 hm)) (PT.cons (PT.const _) (PT.cons (pt_pairC 6 h2)
      (PT.cons (pt_pairC 5 h1) (PT.const _)))))
    (PT.pair (PT.cons (pt_pairC 2 (pt_affC 2 3 hm)) (PT.cons (pt_pairC 5 h3)
      (PT.single (pt_pairC 7 h5))))
      (PT.cons (pt_pairC 2 (pt_affC 2 2 hm)) (PT.single (pt_pairC 5 h1)))))

theorem pt_incDr (p : Bool) {j : α → ℕ} {r : α → List ℕ} (hj : PT j) (hr : PT r) :
    PT fun a => incDr (L a).length p (j a) (r a) := by
  have hm := pt_m hL
  unfold incDr fpc fcb
  exact PT.pair (pt_pairC 9 (PT.natPair (PT.const _) hj)) (PT.pair
    (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 3 hm)) (PT.cons (PT.const _)
      (PT.single (pt_pairC 3 (PT.natPair hj (PT.const _))))))
      (PT.map hr (pt_pairC 3 (PT.natPair PT.snd (PT.const _)))))
    (PT.pair (PT.append (PT.cons (PT.const _) (PT.cons (pt_pairC 3 (PT.natPair hj (PT.const _)))
      (PT.const _))) (PT.map hr (pt_pairC 3 (PT.natPair PT.snd (PT.const _)))))
      (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 3 hm)) (PT.cons (pt_pairC 3 (PT.natPair hj
        (PT.const _))) (PT.const _))) (PT.map hr (pt_pairC 3 (PT.natPair PT.snd (PT.const _)))))))

theorem pt_wrapD (p : Bool) : PT fun a => wrapD (L a).length p := by
  have hm := pt_m hL
  have hR := PT.rangeLength hL
  unfold wrapD fpc fcb
  exact PT.pair (PT.const _) (PT.pair
    (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 3 hm)) (PT.const _))
      (PT.map hR (pt_pairC 3 (PT.natPair PT.snd (PT.const _)))))
    (PT.pair (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.const _))
      (PT.map hR (pt_pairC 3 (PT.natPair PT.snd (PT.const _)))))
      (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 3 hm)) (PT.const _))
        (PT.map hR (pt_pairC 3 (PT.natPair PT.snd (PT.const _)))))))

theorem pt_hincDr (p : Bool) {j : α → ℕ} {r : α → List ℕ} (hj : PT j) (hr : PT r) :
    PT fun a => hincDr (L a).length p (j a) (r a) := by
  have hm := pt_m hL
  unfold hincDr fpc fhb
  exact PT.pair (pt_pairC 11 (PT.natPair (PT.const _) hj)) (PT.pair
    (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.cons (PT.const _) (PT.cons (PT.const _)
      (PT.single (pt_pairC 4 (PT.natPair hj (PT.const _)))))))
      (PT.map hr (pt_pairC 4 (PT.natPair PT.snd (PT.const _)))))
    (PT.pair (PT.append (PT.cons (PT.const _) (PT.cons (PT.const _)
      (PT.single (pt_pairC 4 (PT.natPair hj (PT.const _))))))
      (PT.map hr (pt_pairC 4 (PT.natPair PT.snd (PT.const _)))))
      (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.cons (PT.const _) (PT.cons (PT.const _)
        (PT.cons (PT.const _) (PT.single (pt_pairC 4 (PT.natPair hj (PT.const _))))))))
        (PT.map hr (pt_pairC 4 (PT.natPair PT.snd (PT.const _)))))))

theorem pt_hdecDr (p : Bool) {j : α → ℕ} {r : α → List ℕ} (hj : PT j) (hr : PT r) :
    PT fun a => hdecDr (L a).length p (j a) (r a) := by
  have hm := pt_m hL
  unfold hdecDr fpc fhb
  exact PT.pair (pt_pairC 12 (PT.natPair (PT.const _) hj)) (PT.pair
    (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.cons (PT.const _) (PT.cons (PT.const _)
      (PT.single (pt_pairC 4 (PT.natPair hj (PT.const _)))))))
      (PT.map hr (pt_pairC 4 (PT.natPair PT.snd (PT.const _)))))
    (PT.pair (PT.append (PT.cons (PT.const _) (PT.cons (PT.const _)
      (PT.single (pt_pairC 4 (PT.natPair hj (PT.const _))))))
      (PT.map hr (pt_pairC 4 (PT.natPair PT.snd (PT.const _)))))
      (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.cons (PT.const _) (PT.cons (PT.const _)
        (PT.cons (PT.const _) (PT.single (pt_pairC 4 (PT.natPair hj (PT.const _))))))))
        (PT.map hr (pt_pairC 4 (PT.natPair PT.snd (PT.const _)))))))

theorem pt_hdec0D (p : Bool) : PT fun a => hdec0D (L a).length p := by
  have hm := pt_m hL
  unfold hdec0D fpc fhb
  exact PT.pair (PT.const _) (PT.pair
    (PT.append (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.const _))
      (PT.map (PT.rangeLength hL) (pt_pairC 4 (PT.natPair PT.snd (PT.const _)))))
    (PT.pair (PT.const _) (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.const _))))

theorem pt_hstayD (p : Bool) : PT fun a => hstayD (L a).length p := by
  have hm := pt_m hL
  unfold hstayD fpc
  exact PT.pair (PT.const _) (PT.pair (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.const _))
    (PT.pair (PT.const _) (PT.cons (pt_pairC 2 (pt_affC 2 4 hm)) (PT.const _))))

theorem pt_finD {q : α → ℕ} (hq : PT q) : PT fun a => finD (L a).length (q a) := by
  have hm := pt_m hL
  have hR := PT.rangeLength hL
  unfold finD fpc fst fcb
  exact PT.pair (pt_pairC 15 hq) (PT.pair
    (PT.append (PT.cons (PT.const _) (PT.single (pt_pairC 5 hq)))
      (PT.map hR (pt_pairC 3 (PT.natPair PT.snd (PT.const _)))))
    (PT.pair (PT.append (PT.append (PT.cons (pt_pairC 2 (pt_addC 1 hm)) (PT.const _))
      (PT.map hR (pt_pairC 3 (PT.natPair PT.snd (PT.const _)))))
      (PT.map hR (pt_pairC 3 (PT.natPair PT.snd (PT.const _))))) (PT.const _)))

theorem pt_drnD : PT fun a => drnD (L a).length := by
  have hm := pt_m hL
  unfold drnD fpc
  exact PT.pair (PT.const _) (PT.pair (PT.cons (pt_pairC 2 (pt_affC 2 2 hm)) (PT.const _))
    (PT.pair (PT.single (pt_pairC 2 (pt_addC 1 hm))) (PT.single (pt_pairC 2 (pt_affC 2 2 hm)))))

theorem pt_wbD (p : Bool) (x e : Bool) {j : α → ℕ} (hj : PT j) : PT fun a => wbD p (j a) x e := by
  unfold wbD fpc fcb fhb fpar
  exact PT.pair (pt_pairC 2 (PT.natPair (pt_pairC _ hj) (PT.const _))) (PT.pair
    (PT.cons (pt_pairC 2 (pt_addC 1 hj)) (PT.cons (pt_pairC 3 (PT.natPair hj (PT.const _)))
      (PT.cons (pt_pairC 4 (PT.natPair hj (PT.const _))) (PT.const _))))
    (PT.pair (PT.append (PT.single (pt_pairC 2 (pt_addC 2 hj))) (PT.const _))
      (PT.append (PT.single (pt_pairC 2 (pt_addC 1 hj))) (PT.const _))))

omit hL in
theorem pt_eCP_tree (p : Bool) {β : Type} [BEnc β] {f : β → ℕ} (hf : PT f) :
    PT fun x => eCP (.tree p (f x)) :=
  (PT.succ (pt_pairC 4 (PT.natPair (PT.const _) hf))).of_eq fun _ => rfl

omit hL in
theorem pt_eCP_bit (p : Bool) {β : Type} [BEnc β] {f : β → ℕ} (hf : PT f) :
    PT fun x => eCP (.bit p (f x)) :=
  (PT.succ (pt_pairC 5 (PT.natPair (PT.const _) hf))).of_eq fun _ => rfl

omit hL in
theorem map_range_congr_of_lt {β : Type} {m : ℕ} {f g : ℕ → β} (h : ∀ j < m, f j = g j) :
    (List.range m).map f = (List.range m).map g :=
  List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

theorem pt_bodiesPN (p : Bool) (tN : List (ℕ × ℕ × ℕ × ℕ × ℕ)) :
    PT fun a => bodiesPN (L a).length p tN := by
  have hm := pt_m hL
  have hR := PT.rangeLength hL
  have hL1 : PT fun q : α × ℕ => L q.1 := hL.comp PT.fst
  have hRf : PT fun q : α × ℕ => (List.range (L q.1).length).filter fun i => decide (i < q.2) :=
    PT.filter (PT.rangeLength hL1) (PT.lt PT.snd (PT.snd.comp PT.fst))
  unfold bodiesPN
  refine PT.append (PT.append (PT.append (PT.append (PT.append (PT.append (PT.append (PT.append
    (PT.append (PT.append ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact PT.cons (PT.const _) (PT.cons (PT.const _) (PT.cons (PT.pair (PT.const _)
      (PT.cons (PT.single (PT.inr (pt_eCP_tree p hm))) (PT.const _))) (PT.const _)))
  · exact PT.map hR (PT.pair (pt_eCP_tree p (PT.succ PT.snd)) (PT.cons (PT.single (PT.inr
      (pt_eCP_tree p PT.snd))) (PT.single (PT.single (PT.inr (pt_eCP_tree p PT.snd))))))
  · have h := PT.flatMap (g := fun (a : α) (j : ℕ) =>
        [true, false].flatMap fun x => [true, false].map fun e =>
          ((eCP (.bit p j), [[Sum.inl (wbD p j x e), Sum.inr (eCP (.bit p (j + 1))),
            Sum.inl (rbD (L a).length p j x)]]) : NBody)) hR ?_
    · exact h
    have hrow : ∀ x e : Bool, PT fun q : α × ℕ => ((eCP (.bit p q.2), [[Sum.inl (wbD p q.2 x e),
        Sum.inr (eCP (.bit p (q.2 + 1))), Sum.inl (rbD (L q.1).length p q.2 x)]]) : NBody) :=
      fun x e => PT.pair (pt_eCP_bit p PT.snd) (PT.single (PT.cons (PT.inl (pt_wbD hL1 p x e PT.snd))
        (PT.cons (PT.inr (pt_eCP_bit p (PT.succ PT.snd))) (PT.single (PT.inl
          (pt_rbD hL1 p x PT.snd))))))
    exact (PT.cons (hrow true true) (PT.cons (hrow true false) (PT.cons (hrow false true)
      (PT.single (hrow false false))))).of_eq fun q => by simp
  · exact PT.single (PT.pair (pt_eCP_bit p hm) (PT.const _))
  · exact PT.map (PT.const symL) (PT.pair (PT.const _) (PT.single (PT.cons (PT.inl
      (pt_cpD (L := fun q : α × Option Bool => L q.1) (hL.comp PT.fst) p (pt_symCode PT.snd)))
      (PT.cons (PT.const _) (PT.single (PT.inl (pt_rvD (L := fun q : α × Option Bool => L q.1)
        (hL.comp PT.fst) p (pt_symCode PT.snd))))))))
  · exact PT.map (PT.const tN) (PT.pair (PT.const _) (PT.single (PT.cons (PT.inl
      (pt_trD (L := fun q : α × (ℕ × ℕ × ℕ × ℕ × ℕ) => L q.1) (hL.comp PT.fst) p PT.snd))
      (PT.cons (PT.const _) (PT.single (PT.inl (pt_rvD
        (L := fun q : α × (ℕ × ℕ × ℕ × ℕ × ℕ) => L q.1) (hL.comp PT.fst) p
        (PT.fst' (PT.snd' (PT.snd' (PT.snd' PT.snd)))))))))))
  · refine (PT.map (g := fun (a : α) (j : ℕ) => ((eCP (.incT p), [[Sum.inl (incDr (L a).length p j
      ((List.range (L a).length).filter fun i => decide (i < j)))]]) : NBody)) hR
      (PT.pair (PT.const _) (PT.single (PT.single (PT.inl
      (pt_incDr hL1 p PT.snd hRf)))))).of_eq fun a => map_range_congr_of_lt fun j hj => ?_
    simp only [incD, incDr, ← range_eq_filter hj.le]
  · exact PT.single (PT.pair (PT.const _) (PT.single (PT.single (PT.inl (pt_wrapD hL p)))))
  · refine (PT.map (g := fun (a : α) (j : ℕ) => ((eCP (.reT p), [[Sum.inl (hincDr (L a).length p j
      ((List.range (L a).length).filter fun i => decide (i < j)))]]) : NBody)) hR
      (PT.pair (PT.const _) (PT.single (PT.single (PT.inl
      (pt_hincDr hL1 p PT.snd hRf)))))).of_eq fun a => map_range_congr_of_lt fun j hj => ?_
    simp only [hincD, hincDr, ← range_eq_filter hj.le]
  · refine (PT.map (g := fun (a : α) (j : ℕ) => ((eCP (.reT p), [[Sum.inl (hdecDr (L a).length p j
      ((List.range (L a).length).filter fun i => decide (i < j)))]]) : NBody)) hR
      (PT.pair (PT.const _) (PT.single (PT.single (PT.inl
      (pt_hdecDr hL1 p PT.snd hRf)))))).of_eq fun a => map_range_congr_of_lt fun j hj => ?_
    simp only [hdecD, hdecDr, ← range_eq_filter hj.le]
  · exact PT.cons (PT.pair (PT.const _) (PT.single (PT.single (PT.inl (pt_hdec0D hL p)))))
      (PT.single (PT.pair (PT.const _) (PT.single (PT.single (PT.inl (pt_hstayD hL p))))))

/-- **The bodies as numbers are computed in polynomial time.** -/
theorem pt_nbN {L' : α → List Unit} (hL' : PT L') (q₀ gb : ℕ) (tN : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (aN : List ℕ) : PT fun a => nbN (L a).length (L' a).length q₀ gb tN aN := by
  have hm := pt_m hL
  have hL1 : PT fun q : α × ℕ => L q.1 := hL.comp PT.fst
  unfold nbN
  refine PT.append (PT.append (PT.append (PT.append (PT.append ?_ ?_) ?_) ?_) ?_) ?_
  · exact PT.cons (PT.pair (PT.const _) (PT.single (PT.cons (PT.inl (pt_bootD hL q₀))
      (PT.const _)))) (PT.cons (PT.const _) (PT.cons (PT.const _) (PT.single (PT.pair (PT.const _)
        (PT.single (PT.single (PT.inl (pt_rblankD hL hL' gb))))))))
  · exact (PT.flatMap (g := fun (a : α) (i : ℕ) => ([(eCP .rd0, [[Sum.inl (riD (L a).length i true)]]),
      (eCP .rd0, [[Sum.inl (riD (L a).length i false)]])] : List NBody)) (PT.rangeLength hL') (PT.cons (PT.pair (PT.const _) (PT.single (PT.single
      (PT.inl (pt_riD hL1 PT.snd true))))) (PT.single (PT.pair (PT.const _) (PT.single (PT.single
        (PT.inl (pt_riD hL1 PT.snd false)))))))).of_eq fun a => by simp
  · exact pt_bodiesPN hL true tN
  · exact pt_bodiesPN hL false tN
  · exact PT.map (PT.const aN) (PT.pair (PT.const _) (PT.single (PT.cons (PT.inl
      (pt_finD (L := fun q : α × ℕ => L q.1) hL1 PT.snd)) (PT.const _))))
  · exact PT.cons (PT.pair (PT.const _) (PT.single (PT.cons (PT.inl (pt_drnD hL)) (PT.const _))))
      (PT.const _)

end PTime

end SpaceEnc

end HTN
