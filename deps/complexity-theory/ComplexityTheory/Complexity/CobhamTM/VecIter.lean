import ComplexityTheory.Complexity.CobhamTM.Kit
/-!
# Simultaneous iteration of a vector of functions of Cobham's class

`cobham_iterate` iterates one step function on one string.  Simulating a machine needs a
*vector* of strings (a control word and one string per stack) updated simultaneously.  This
file packs a vector of strings, each no longer than a bound `L`, into one string of fixed-width
blocks (`encVec`), unpacks it (`getVec`), and derives `cobham_iterVec`: the components of the
`t`-fold iterate of a vector of step functions of the class are functions of the class, provided
the iterates stay below a bound of the class.
-/

namespace HTN.PTime.CobhamTM

open HTN.PTime

/-! ### Fixed-width blocks -/

/-- A string padded on the left to a block of length `L + 1`: `false`s, a `true`, the string.
Strings longer than `L` are replaced by the empty string. -/
def padBlk (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L then List.replicate (L - s.length) false ++ true :: s
  else List.replicate L false ++ [true]

theorem length_padBlk (L : ℕ) (s : List Bool) : (padBlk L s).length = L + 1 := by
  unfold padBlk; split <;> simp <;> omega

/-- Undo the padding. -/
def unpadBlk (u : List Bool) : List Bool := (u.dropWhile (fun b => !b)).tail

theorem dropWhile_replicate_false (n : ℕ) (u : List Bool) :
    (List.replicate n false ++ true :: u).dropWhile (fun b => !b) = true :: u := by
  induction n with
  | zero => simp
  | succ n ih => simpa [List.replicate_succ] using ih

theorem unpadBlk_padBlk {L : ℕ} {s : List Bool} (h : s.length ≤ L) : unpadBlk (padBlk L s) = s := by
  simp [unpadBlk, padBlk, h, dropWhile_replicate_false]

/-- A vector of strings packed into one string of blocks. -/
def encVec (L : ℕ) (cs : List (List Bool)) : List Bool := (cs.map (padBlk L)).flatten

/-- The `i`-th component of a packed vector. -/
def getVec (L : ℕ) (code : List Bool) (i : ℕ) : List Bool :=
  unpadBlk ((code.drop (i * (L + 1))).take (L + 1))

theorem drop_flatten_blocks {m : ℕ} :
    ∀ (bs : List (List Bool)) (i : ℕ), (∀ b ∈ bs, b.length = m) →
      bs.flatten.drop (i * m) = (bs.drop i).flatten
  | [], i, _ => by simp
  | b :: bs, 0, _ => by simp
  | b :: bs, i + 1, h => by
    have hb : b.length = m := h b (by simp)
    have key : (b ++ bs.flatten).drop ((i + 1) * m) = bs.flatten.drop (i * m) := by
      rw [show (i + 1) * m = b.length + i * m by rw [hb]; ring, ← List.drop_drop, List.drop_left]
    rw [List.flatten_cons, key, List.drop_succ_cons]
    exact drop_flatten_blocks bs i fun c hc => h c (by simp [hc])

theorem getVec_encVec (L : ℕ) (cs : List (List Bool)) (hcs : ∀ c ∈ cs, c.length ≤ L) (i : ℕ) :
    getVec L (encVec L cs) i = cs.getD i [] := by
  unfold getVec encVec
  rw [drop_flatten_blocks _ i (fun b hb => by
    simp only [List.mem_map] at hb
    obtain ⟨c, -, rfl⟩ := hb
    exact length_padBlk L c)]
  rw [← List.map_drop]
  cases h : cs.drop i with
  | nil =>
    have : cs.length ≤ i := by simpa using h
    simp [unpadBlk, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
  | cons c rest =>
    have hc : cs.getD i [] = c := by
      have hi := congrArg List.head? h
      rw [List.head?_drop] at hi
      simp [List.getD_eq_getElem?_getD, hi]
    have hcL : c.length ≤ L := hcs c (by
      have : c ∈ cs.drop i := by rw [h]; simp
      exact List.mem_of_mem_drop this)
    rw [hc, List.map_cons, List.flatten_cons,
      List.take_append_of_le_length (by rw [length_padBlk]),
      List.take_of_length_le (by rw [length_padBlk]), unpadBlk_padBlk hcL]

theorem length_encVec (L : ℕ) (cs : List (List Bool)) :
    (encVec L cs).length = cs.length * (L + 1) := by
  induction cs with
  | nil => simp [encVec]
  | cons c cs ih =>
    simp only [encVec, List.map_cons, List.flatten_cons, List.length_append, length_padBlk] at ih ⊢
    rw [ih, List.length_cons]; ring

/-! ### Packing and unpacking in the class -/

theorem cobham_padBlk {bd s : Fn} (hbd : Cobham bd) (hs : Cobham s) :
    Cobham fun args => padBlk (bd args).length (s args) := by
  refine (cobham_ite (cobB_lenLE hs hbd)
    (cobham_append' (cobham_dropBy hs (cobham_falses hbd)) (cobham_cons' true hs))
    (cobham_appendConst (cobham_falses hbd) [true])).of_fun_eq fun args => ?_
  simp only [padBlk, decide_eq_true_eq, List.drop_replicate]

theorem cobham_encVec {bd : Fn} (hbd : Cobham bd) (fs : List Fn) (hfs : ∀ f ∈ fs, Cobham f) :
    Cobham fun args => encVec (bd args).length (fs.map fun f => f args) := by
  induction fs with
  | nil => exact Cobham.empty
  | cons f fs ih =>
    refine (cobham_append' (cobham_padBlk hbd (hfs f (by simp)))
      (ih fun g hg => hfs g (by simp [hg]))).of_fun_eq fun args => ?_
    simp [encVec]

theorem cobham_dropBlocks {bd a : Fn} (hbd : Cobham bd) (ha : Cobham a) (i : ℕ) :
    Cobham fun args => (a args).drop (i * ((bd args).length + 1)) := by
  induction i with
  | zero => simpa using ha
  | succ i ih =>
    refine (cobham_dropBy (cobham_cons' true hbd) ih).of_fun_eq fun args => ?_
    simp only [List.drop_drop, List.length_cons]
    congr 1; ring

theorem cobham_getVec {bd a : Fn} (hbd : Cobham bd) (ha : Cobham a) (i : ℕ) :
    Cobham fun args => getVec (bd args).length (a args) i := by
  refine (cobham_tail' (cobham_dropFalses (cobham_takeBy (cobham_cons' true hbd)
    (cobham_dropBlocks hbd ha i)))).of_fun_eq fun args => ?_
  simp [getVec, unpadBlk]

/-! ### Simultaneous iteration -/

/-- The initial vector. -/
def initV (inits : List Fn) (args : Args) : List (List Bool) := inits.map fun f => f args

/-- One simultaneous step: every component function reads the whole vector, followed by the
ambient arguments. -/
def stepV (steps : List Fn) (args : Args) (cs : List (List Bool)) : List (List Bool) :=
  steps.map fun f => f (cs ++ args)

theorem length_stepV (steps : List Fn) (args : Args) (cs : List (List Bool)) :
    (stepV steps args cs).length = steps.length := by simp [stepV]

theorem length_iterate_stepV (inits steps : List Fn) (hlen : steps.length = inits.length)
    (args : Args) (t : ℕ) : ((stepV steps args)^[t] (initV inits args)).length = inits.length := by
  cases t with
  | zero => simp [initV]
  | succ t => rw [Function.iterate_succ_apply', length_stepV, hlen]

/-- **Simultaneous iteration.**  The components of the iterate of a vector of step functions of
the class, as many times as a computed string is long, are functions of the class, provided all
iterates up to that count stay below a bound of the class. -/
theorem cobham_iterVec (inits steps : List Fn) (hlen : steps.length = inits.length)
    (hinits : ∀ f ∈ inits, Cobham f) (hsteps : ∀ f ∈ steps, Cobham f) {cnt bd : Fn}
    (hcnt : Cobham cnt) (hbd : Cobham bd)
    (hb : ∀ args t, t ≤ (cnt args).length →
      ∀ c ∈ (stepV steps args)^[t] (initV inits args), c.length ≤ (bd args).length) (i : ℕ) :
    Cobham fun args => ((stepV steps args)^[(cnt args).length] (initV inits args)).getD i [] := by
  set n := inits.length with hn
  -- the packed initial value and the packed step
  set init' : Fn := fun args => encVec (bd args).length (initV inits args) with hinit'
  set dec : Args → List (List Bool) := fun args' =>
    (List.range n).map fun j => getVec (bd args'.tail).length (args'.getD 0 []) j with hdec
  set step' : Fn := fun args' =>
    encVec (bd args'.tail).length (stepV steps args'.tail (dec args')) with hstep'
  set bd' : Fn := fun args => (List.replicate n (true :: bd args)).flatten with hbd'
  have hinitC : Cobham init' := cobham_encVec hbd inits hinits
  have hbdT : Cobham fun args' : Args => bd args'.tail :=
    (cobham_dropArgs hbd 1).of_fun_eq fun _ => by rw [List.drop_one]
  have hdecC : ∀ j, Cobham fun args' : Args =>
      getVec (bd args'.tail).length (args'.getD 0 []) j := fun j =>
    cobham_getVec hbdT (Cobham.proj 0) j
  have hstepC : Cobham step' := by
    have hcomp : ∀ f ∈ steps, Cobham fun args' : Args => f (dec args' ++ args'.tail) := by
      intro f hf
      refine cobham_subst (hsteps f hf) fun j => ?_
      by_cases hj : j < n
      · refine (hdecC j).of_fun_eq fun args' => ?_
        symm
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa [hdec] using hj)]
        simp [hdec, hj]
      · refine (Cobham.proj (j - n + 1)).of_fun_eq fun args' => ?_
        symm
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hdec]; omega)]
        rcases args' with _ | ⟨c, args⟩
        · simp [PTime.proj]
        · simp only [hdec, PTime.proj, List.length_map, List.length_range, List.tail_cons,
            List.getD_eq_getElem?_getD]
          rw [show j - n + 1 = (j - n) + 1 from rfl, List.getElem?_cons_succ]
    refine (cobham_encVec hbdT (steps.map fun f => fun args' : Args => f (dec args' ++ args'.tail))
      (by
        intro h hh
        simp only [List.mem_map] at hh
        obtain ⟨f, hf, rfl⟩ := hh
        exact hcomp f hf)).of_fun_eq fun args' => ?_
    simp [hstep', stepV, List.map_map, Function.comp_def]
  have hbd'C : Cobham bd' := by
    have : ∀ m, Cobham fun args => (List.replicate m (true :: bd args)).flatten := by
      intro m
      induction m with
      | zero => exact Cobham.empty
      | succ m ih =>
        exact (cobham_append' (cobham_cons' true hbd) ih).of_fun_eq fun args => by
          simp [List.replicate_succ]
    exact this n
  have hlen_bd' : ∀ args, (bd' args).length = n * ((bd args).length + 1) := by
    intro args; simp [hbd']
  have hit := cobham_iterate hinitC hstepC hcnt hbd'C
    (fun args => by rw [hlen_bd', hinit', length_encVec]; simp [initV, hn])
    (fun c args => by
      rw [hlen_bd', hstep', length_encVec, length_stepV, hlen]; simp)
  -- the packed iteration tracks the vector iteration
  have track : ∀ args t, t ≤ (cnt args).length →
      (fun c => step' (c :: args))^[t] (init' args) =
        encVec (bd args).length ((stepV steps args)^[t] (initV inits args)) := by
    intro args t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      simp only [hstep', List.tail_cons]
      congr 2
      simp only [hdec, List.getD_cons_zero]
      have hbt := hb args t (by omega)
      rw [List.ext_getElem_iff]
      refine ⟨by simp [length_iterate_stepV inits steps hlen, hn], fun j hj1 hj2 => ?_⟩
      simp only [List.getElem_map, List.getElem_range, List.tail_cons]
      rw [getVec_encVec _ _ hbt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2]
      rfl
  refine (cobham_getVec hbd hit i).of_fun_eq fun args => ?_
  rw [track args _ le_rfl, getVec_encVec _ _ (hb args _ le_rfl)]

end HTN.PTime.CobhamTM
