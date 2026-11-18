import HtnComplexity.Computable.AcNum
/-!
# The method bodies of the compiled acyclic domain, as lists

`HTN.ToAc.bodies` is a *set* of method bodies for every compound task of the compiled domain.
For a description the bodies have to be produced as a **list**, by numeric operations on the
number of the compound task.  This file does that.

`HTN.Syn.Ac.bodyNum V UA UC tuples bound t` is the list of bodies of the compiled task whose
number is `t`, each body a list of rows and each row a list of described labels
(`(false, a)` for an action, `(true, c)` for a compound task).  The four data it needs from the
source are

* `V` — the facts of the source, numbered (the list `vars` of the construction),
* `UA`, `UC` — the action names and the compound task names of the source, numbered,
* `tuples` — one triple `(c, x, y)` for every method `c ↦ x y` of the source, numbered.

`HTN.Syn.Ac.mem_bodyNum` is the correctness theorem: evaluated at `HTN.ToAc.encTask f a c t`,
the list `bodyNum` contains exactly the numberings of the elements of `HTN.ToAc.bodies`.
-/

namespace HTN

namespace Syn

namespace Ac

/-- A described method body: a list of rows of described labels. -/
abbrev EBody : Type := List (List (Bool × ℕ))

/-- An action, as a described label. -/
def pAct (x : ℕ) : Bool × ℕ := (false, x)

/-- A compound task, as a described label. -/
def pTsk (x : ℕ) : Bool × ℕ := (true, x)

/-! ### The bodies, one compiled task at a time -/

/-- The bodies of `SEL^i`. -/
def bodySEL (n i : ℕ) : List EBody := [[[pTsk (tSELn n i)]]]

/-- The bodies of `SEL_m^i`. -/
def bodySELn (V : List ℕ) (m i : ℕ) : List EBody :=
  if m = 0 then [[]]
  else match V[m - 1]? with
    | none => []
    | some v => [[[pAct (aSetV v i), pTsk (tSELn (m - 1) i)]],
                 [[pAct (aDelV v i), pTsk (tSELn (m - 1) i)]]]

/-- The bodies of `EQ^{i,j}`. -/
def bodyEQ (n i j : ℕ) : List EBody := [[[pTsk (tEQn n i j)]]]

/-- The bodies of `EQ_m^{i,j}`. -/
def bodyEQn (V : List ℕ) (m i j : ℕ) : List EBody :=
  if m = 0 then [[]]
  else match V[m - 1]? with
    | none => []
    | some v => [[[pAct (aPrePV v i j), pTsk (tEQn (m - 1) i j)]],
                 [[pAct (aPreNV v i j), pTsk (tEQn (m - 1) i j)]]]

/-- The bodies of `STATE_m^1`. -/
def bodySTATE1 (V : List ℕ) (n m : ℕ) : List EBody :=
  if m = 0 then [[[pTsk (tSTATE3 n)]]]
  else match V[m - 1]? with
    | none => []
    | some v => [[[pAct (aPrePV v 0 0), pTsk (tSTATE1 (m - 1)), pAct (aSetV v 3)]],
                 [[pAct (aPreNV v 0 0), pTsk (tSTATE1 (m - 1)), pAct (aDelV v 3)]]]

/-- The body of `STATE_0^3` that stores the source task name `t`. -/
def stateBody (t : ℕ) : EBody :=
  [[pAct (aPreC t), pAct (aDone rwWrite), pAct (aAccept rwRead), pAct (aSetC t)]]

/-- The bodies of `STATE_m^3`. -/
def bodySTATE3 (V UA UC : List ℕ) (m : ℕ) : List EBody :=
  if m = 0 then (UA.map fun u => stateBody (nA u)) ++ (UC.map fun u => stateBody (nC u))
  else match V[m - 1]? with
    | none => []
    | some v => [[[pAct (aPrePV v 2 2), pTsk (tSTATE3 (m - 1)), pAct (aSetV v 4)]],
                 [[pAct (aPreNV v 2 2), pTsk (tSTATE3 (m - 1)), pAct (aDelV v 4)]]]

/-- The bodies of `MEM`. -/
def bodyMEM (n : ℕ) : List EBody :=
  [[[pAct (aAccept rwWrite), pTsk (tSTATE1 n), pAct (aDone rwRead)]]]

/-- The bodies of `WRITE`. -/
def bodyWRITE : List EBody := [[[pAct (aAsk rwWrite), pAct (aWait rwWrite)]]]

/-- The bodies of `READ`. -/
def bodyREAD : List EBody := [[[pAct (aAsk rwRead), pAct (aWait rwRead)]]]

/-- The body of `TUPLE` that applies the source method `c ↦ x y`. -/
def tupleBodyM (bound c x y : ℕ) : EBody :=
  [[pAct aLock, pTsk (tSEL 0), pTsk (tSEL 1), pTsk (tSEL 2),
    pTsk tREAD, pTsk (tEQ 0 3), pTsk (tEQ 1 4), pAct (aPreC x),
    pTsk tREAD, pTsk (tEQ 1 3), pTsk (tEQ 2 4), pAct (aPreC y),
    pAct (aSetC c), pTsk (tCnt tWRITE bound), pAct aUnlock]]

/-- The body of `TUPLE` that applies the source operator `o`. -/
def tupleBodyO (bound o : ℕ) : EBody :=
  [[pAct aLock, pTsk (tSEL 0), pTsk (tSEL 1), pTsk (tSEL 2),
    pTsk (tEQ 0 1), pAct (aOp2 o), pTsk (tEQ 1 2),
    pAct (aSetC (nA o)), pTsk (tCnt tWRITE bound), pAct aUnlock]]

/-- The bodies of `TUPLE`. -/
def bodyTUPLE (UA : List ℕ) (tuples : List (ℕ × ℕ × ℕ)) (bound : ℕ) : List EBody :=
  (tuples.map fun p => tupleBodyM bound p.1 p.2.1 p.2.2) ++ (UA.map fun o => tupleBodyO bound o)

/-- The bodies of `𝔠̄^k_T`. -/
def bodyCnt (t k : ℕ) : List EBody :=
  if k = 0 then [[]]
  else if k = 1 then [[[pTsk t]], []]
  else if k % 2 = 0 then [[[pTsk (tCnt t (k / 2)), pTsk (tCnt t (k / 2))]]]
  else [[[pTsk t, pTsk (tCnt t (k - 1))]], [[pTsk (tCnt t (k - 1))]]]

/-- The bodies of `𝔠^k_T`. -/
def bodyCntPar (t k : ℕ) : List EBody :=
  if k = 0 then [[]]
  else if k = 1 then [[[pTsk t]], []]
  else if k % 2 = 0 then [[[pTsk (tCntPar t (k / 2))], [pTsk (tCntPar t (k / 2))]]]
  else [[[pTsk t], [pTsk (tCntPar t (k - 1))]], [[pTsk (tCntPar t (k - 1))]]]

/-- The bodies of `t_I`. -/
def bodyTI (bound : ℕ) : List EBody :=
  [[[pTsk (tCntPar tMEM bound)], [pTsk (tCntPar tTUPLE bound)]]]

/-- **The bodies of the compiled compound task numbered `t`.** -/
def bodyNum (V UA UC : List ℕ) (tuples : List (ℕ × ℕ × ℕ)) (bound t : ℕ) : List EBody :=
  if tag t = 0 then bodySEL V.length (payload t)
  else if tag t = 1 then bodySELn V (payload t / 5) (payload t % 5)
  else if tag t = 2 then bodyEQ V.length (payload t / 5) (payload t % 5)
  else if tag t = 3 then
    bodyEQn V (payload t / 25) (payload t % 25 / 5) (payload t % 5)
  else if tag t = 4 then bodySTATE1 V V.length (payload t)
  else if tag t = 5 then bodySTATE3 V UA UC (payload t)
  else if tag t = 6 then bodyMEM V.length
  else if tag t = 7 then bodyWRITE
  else if tag t = 8 then bodyREAD
  else if tag t = 9 then bodyTUPLE UA tuples bound
  else if tag t = 10 then bodyCnt (Nat.unpair (payload t)).1 (Nat.unpair (payload t)).2
  else if tag t = 11 then bodyCntPar (Nat.unpair (payload t)).1 (Nat.unpair (payload t)).2
  else if tag t = 12 then bodyTI bound
  else []

/-! ### Correctness -/

section Correct

open ToAc

variable {F A C I : Type} {f : F → ℕ} {a : A → ℕ} {c : C → ℕ} {D : Domain F A C I}
  {vars : List F} {bound : ℕ} {V UA UC : List ℕ} {tuples : List (ℕ × ℕ × ℕ)}

/-- A method body of the compiled domain, numbered. -/
def encBody (f : F → ℕ) (a : A → ℕ) (c : C → ℕ)
    (ls : List (List (AcAct F A C ⊕ AcTask F A C))) : EBody :=
  ls.map fun row => row.map (encLabel (encAct f a c) (encTask f a c))

@[simp] lemma encBody_nil : encBody f a c [] = [] := rfl

@[simp] lemma encLabel_inl (x : AcAct F A C) :
    encLabel (encAct f a c) (encTask f a c) (Sum.inl x) = pAct (encAct f a c x) := rfl

@[simp] lemma encLabel_inr (x : AcTask F A C) :
    encLabel (encAct f a c) (encTask f a c) (Sum.inr x) = pTsk (encTask f a c x) := rfl

/-- The data the source contributes to `bodyNum`. -/
structure SourceData (f : F → ℕ) (a : A → ℕ) (c : C → ℕ) (D : Domain F A C I) (vars : List F)
    (V UA UC : List ℕ) (tuples : List (ℕ × ℕ × ℕ)) : Prop where
  /-- `V` is the list of source facts, numbered. -/
  facts : V = vars.map f
  /-- Every source action name is listed in `UA`. -/
  actions_mem : ∀ o : A, a o ∈ UA
  /-- Every entry of `UA` is a source action name. -/
  actions_onto : ∀ u ∈ UA, ∃ o : A, a o = u
  /-- Every source compound task name is listed in `UC`. -/
  names_mem : ∀ y : C, c y ∈ UC
  /-- Every entry of `UC` is a source compound task name. -/
  names_onto : ∀ u ∈ UC, ∃ y : C, c y = u
  /-- `tuples` lists exactly the binary methods of the source. -/
  tuples_spec : ∀ p : ℕ × ℕ × ℕ, p ∈ tuples ↔
    ∃ (c₀ : C) (x y : A ⊕ C), D.SeqBody c₀ [x, y] ∧
      p = (nC (c c₀), encName a c x, encName a c y)

/-- The shape shared by the four families of bodies that are indexed by a fact of the
source. -/
lemma pair_body_iff {vars : List F} (hV : V = vars.map f) (m : ℕ)
    (g1 g2 : ℕ → EBody) (G1 G2 : F → List (List (AcAct F A C ⊕ AcTask F A C)))
    (hg1 : ∀ v, g1 (f v) = encBody f a c (G1 v)) (hg2 : ∀ v, g2 (f v) = encBody f a c (G2 v))
    (b : EBody) :
    (b ∈ (match V[m]? with | none => ([] : List EBody) | some v => [g1 v, g2 v])) ↔
      ∃ ls ∈ {ls | ∃ v ∈ vars[m]?, ls = G1 v ∨ ls = G2 v}, b = encBody f a c ls := by
  subst hV
  rw [List.getElem?_map]
  cases hv : vars[m]? with
  | none => simp
  | some v => simp [hg1, hg2]

/-- **The described bodies are the bodies.** -/
theorem mem_bodyNum (h : SourceData f a c D vars V UA UC tuples) (t : AcTask F A C)
    (b : EBody) :
    b ∈ bodyNum V UA UC tuples bound (encTask f a c t) ↔
      ∃ ls ∈ bodies D vars bound t, b = encBody f a c ls := by
  have hV : V.length = vars.length := by rw [h.facts, List.length_map]
  cases t with
  | SEL i =>
      simp [bodyNum, bodySEL, bodies, encBody, hV, pTsk]
  | SELn n i =>
      have hi : (i : ℕ) < 5 := i.isLt
      have h5 : (5 * n + (i : ℕ)) / 5 = n := by omega
      have h5' : (5 * n + (i : ℕ)) % 5 = (i : ℕ) := by omega
      simp only [enc_tSELn, bodyNum, tag_tSELn, payload_tSELn, h5, h5']
      norm_num
      rw [bodySELn]
      by_cases hn : n = 0
      · subst hn; simp [bodies]
      · rw [if_neg hn]
        simp only [bodies, if_neg hn]
        exact pair_body_iff h.facts _ _ _
          (fun v => [[Sum.inl (AcAct.setV v i), Sum.inr (AcTask.SELn (n - 1) i)]])
          (fun v => [[Sum.inl (AcAct.delV v i), Sum.inr (AcTask.SELn (n - 1) i)]])
          (fun v => by simp [encBody]) (fun v => by simp [encBody]) b
  | EQ i j =>
      have hj : (j : ℕ) < 5 := j.isLt
      have h5 : (5 * (i : ℕ) + (j : ℕ)) / 5 = (i : ℕ) := by omega
      have h5' : (5 * (i : ℕ) + (j : ℕ)) % 5 = (j : ℕ) := by omega
      simp only [enc_tEQ, bodyNum, tag_tEQ, payload_tEQ, h5, h5']
      norm_num
      simp [bodyEQ, bodies, encBody, hV, pTsk]
  | EQn n i j =>
      have hi : (i : ℕ) < 5 := i.isLt
      have hj : (j : ℕ) < 5 := j.isLt
      have h1 : (25 * n + 5 * (i : ℕ) + (j : ℕ)) / 25 = n := by omega
      have h2 : (25 * n + 5 * (i : ℕ) + (j : ℕ)) % 25 / 5 = (i : ℕ) := by omega
      have h3 : (25 * n + 5 * (i : ℕ) + (j : ℕ)) % 5 = (j : ℕ) := by omega
      simp only [enc_tEQn, bodyNum, tag_tEQn, payload_tEQn, h1, h2, h3]
      norm_num
      rw [bodyEQn]
      by_cases hn : n = 0
      · subst hn; simp [bodies]
      · rw [if_neg hn]
        simp only [bodies, if_neg hn]
        exact pair_body_iff h.facts _ _ _
          (fun v => [[Sum.inl (AcAct.prePV v i j), Sum.inr (AcTask.EQn (n - 1) i j)]])
          (fun v => [[Sum.inl (AcAct.preNV v i j), Sum.inr (AcTask.EQn (n - 1) i j)]])
          (fun v => by simp [encBody]) (fun v => by simp [encBody]) b
  | STATE1 n =>
      simp only [enc_tSTATE1, bodyNum, tag_tSTATE1, payload_tSTATE1]
      norm_num
      rw [bodySTATE1]
      by_cases hn : n = 0
      · subst hn; simp [bodies, encBody, hV, pTsk]
      · rw [if_neg hn]
        simp only [bodies, if_neg hn]
        exact pair_body_iff h.facts _ _ _
          (fun v => [[Sum.inl (AcAct.prePV v 0 0), Sum.inr (AcTask.STATE1 (n - 1)),
            Sum.inl (AcAct.setV v 3)]])
          (fun v => [[Sum.inl (AcAct.preNV v 0 0), Sum.inr (AcTask.STATE1 (n - 1)),
            Sum.inl (AcAct.delV v 3)]])
          (fun v => by simp [encBody]) (fun v => by simp [encBody]) b
  | STATE3 n =>
      simp only [enc_tSTATE3, bodyNum, tag_tSTATE3, payload_tSTATE3]
      norm_num
      rw [bodySTATE3]
      by_cases hn : n = 0
      · subst hn
        simp only [bodies, if_true, List.mem_append, List.mem_map]
        constructor
        · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
          · obtain ⟨o, rfl⟩ := h.actions_onto u hu
            exact ⟨_, ⟨Sum.inl o, rfl⟩, by simp [encBody, stateBody]⟩
          · obtain ⟨y, rfl⟩ := h.names_onto u hu
            exact ⟨_, ⟨Sum.inr y, rfl⟩, by simp [encBody, stateBody]⟩
        · rintro ⟨ls, ⟨t', rfl⟩, rfl⟩
          cases t' with
          | inl o => exact Or.inl ⟨a o, h.actions_mem o, by simp [encBody, stateBody]⟩
          | inr y => exact Or.inr ⟨c y, h.names_mem y, by simp [encBody, stateBody]⟩
      · rw [if_neg hn]
        simp only [bodies, if_neg hn]
        exact pair_body_iff h.facts _ _ _
          (fun v => [[Sum.inl (AcAct.prePV v 2 2), Sum.inr (AcTask.STATE3 (n - 1)),
            Sum.inl (AcAct.setV v 4)]])
          (fun v => [[Sum.inl (AcAct.preNV v 2 2), Sum.inr (AcTask.STATE3 (n - 1)),
            Sum.inl (AcAct.delV v 4)]])
          (fun v => by simp [encBody]) (fun v => by simp [encBody]) b
  | MEM => simp [bodyNum, bodyMEM, bodies, encBody, hV, pAct, pTsk]
  | WRITE => simp [bodyNum, bodyWRITE, bodies, encBody, pAct]
  | READ => simp [bodyNum, bodyREAD, bodies, encBody, pAct]
  | TUPLE =>
      simp only [enc_tTUPLE, bodyNum, tag_tTUPLE]
      norm_num
      simp only [bodyTUPLE, List.mem_append, List.mem_map, bodies, Set.mem_union,
        Set.mem_setOf_eq]
      constructor
      · rintro (⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩)
        · obtain ⟨c₀, x, y, hsb, rfl⟩ := (h.tuples_spec p).1 hp
          refine ⟨_, Or.inl ⟨c₀, x, y, hsb, rfl⟩, ?_⟩
          simp [encBody, tupleBodyM]
        · obtain ⟨o', rfl⟩ := h.actions_onto o ho
          refine ⟨_, Or.inr ⟨o', rfl⟩, ?_⟩
          simp [encBody, tupleBodyO]
      · rintro ⟨ls, ⟨c₀, x, y, hsb, rfl⟩ | ⟨o, rfl⟩, rfl⟩
        · refine Or.inl ⟨(nC (c c₀), encName a c x, encName a c y),
            (h.tuples_spec _).2 ⟨c₀, x, y, hsb, rfl⟩, ?_⟩
          simp [encBody, tupleBodyM]
        · exact Or.inr ⟨a o, h.actions_mem o, by simp [encBody, tupleBodyO]⟩
  | cnt t' k =>
      simp only [enc_tCnt, bodyNum, tag_tCnt, payload_tCnt, Nat.unpair_pair]
      norm_num
      rw [bodyCnt]
      simp only [bodies]
      split_ifs with h0 h1 he
      · simp [encBody]
      · simp [encBody]
      · simp [encBody]
      · simp [encBody]
  | cntPar t' k =>
      simp only [enc_tCntPar, bodyNum, tag_tCntPar, payload_tCntPar, Nat.unpair_pair]
      norm_num
      rw [bodyCntPar]
      simp only [bodies]
      split_ifs with h0 h1 he
      · simp [encBody]
      · simp [encBody]
      · simp [encBody]
      · simp [encBody]
  | tI => simp [bodyNum, bodyTI, bodies, encBody, pTsk]

end Correct

end Ac

end Syn

end HTN
