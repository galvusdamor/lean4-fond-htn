import HtnComplexity.PT.Search
import HtnComplexity.PT.Pred
/-!
# AND-OR games of bounded depth are decided in polynomial (exponential) space

An *AND-OR game* on an input `a : α` has configurations `c : σ`; a configuration is accepting
(`acc`), universal (`uni = true`) or existential (`uni = false`), and has the successor list
`succs (a, c)`.  `HTN.Syn.PolyDom.gameVal acc uni succs a k c` is the value of the game from `c`
with depth budget `k`.

* **`HTN.Syn.PolyDom.inPSpace_codeLang_of_game`** — if the depth and the sizes of the successor
  lists met during the evaluation are polynomial in the size of `a`, the language of the codes of
  the inputs whose game is won from some initial configuration is in `PSPACE`.
* **`HTN.Syn.PolyDom.inExpSpace_codeLang_of_game`** — the same with exponential size bounds (the
  depth is any polynomial-time computable number) gives `EXPSPACE`.

Proof: a depth-first evaluation is a nondeterministic search (`inPSpace_codeLang_of_search`,
`inExpSpace_codeLang_of_search`) over stacks of *goals* `(k, c)` ("`c` wins within `k`").  A step
pops the top goal and either discards it (if accepting), or replaces it by all goals of its
successors (universal), or by the goal of one guessed successor (existential)
(`HTN.Syn.PolyDom.dfsStep`).  The empty stack accepts.  Every goal of a stack from which the
empty stack is reachable is won (`dfs_sound`); conversely, a won goal is discharged by a run whose
stacks stay below `sz rest + k * C` (`dfs_complete`).
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

section Game

set_option linter.unusedSectionVars false

variable {α σ : Type} [BEnc α] [BDec α] [BEnc σ] [BDec σ] [DecidableEq σ]

/-- Value of the game with depth budget `k`: accepting, or a universal node all of whose
successors win within `k-1`, or an existential node with a winning successor. -/
def gameVal (acc uni : α × σ → Bool) (succs : α × σ → List σ) (a : α) : ℕ → σ → Bool
  | 0, c => acc (a, c)
  | k + 1, c => acc (a, c) || (bif uni (a, c) then (succs (a, c)).all (gameVal acc uni succs a k)
      else (succs (a, c)).any (gameVal acc uni succs a k))

/-- `c'` is reachable from `c` by exactly `n` successor steps. -/
def GameReach (succs : α × σ → List σ) (a : α) : ℕ → σ → σ → Prop
  | 0, c, c' => c' = c
  | n + 1, c, c' => ∃ c₁ ∈ succs (a, c), GameReach succs a n c₁ c'

/-- One step of the depth-first evaluation from the stack `g :: rest` to `S'`. -/
def dfsFrom (acc uni : α × σ → Bool) (succs : α × σ → List σ) (a : α) (g : ℕ × σ)
    (rest S' : List (ℕ × σ)) : Bool :=
  (acc (a, g.2) && decide (S' = rest)) ||
    (decide (0 < g.1) && bif uni (a, g.2) then
        decide (S' = (succs (a, g.2)).map (fun c => (g.1 - 1, c)) ++ rest)
      else (succs (a, g.2)).any fun c => decide (S' = (g.1 - 1, c) :: rest))

/-- The step relation of the depth-first evaluation on `(a, S, S')`. -/
def dfsStep (acc uni : α × σ → Bool) (succs : α × σ → List σ)
    (x : α × List (ℕ × σ) × List (ℕ × σ)) : Bool :=
  x.2.1.any fun g => decide (x.2.1 = g :: x.2.1.tail) && dfsFrom acc uni succs x.1 g x.2.1.tail x.2.2

variable {acc uni : α × σ → Bool} {succs : α × σ → List σ}

theorem dfsStep_nil (a : α) (S' : List (ℕ × σ)) : dfsStep acc uni succs (a, [], S') = false := rfl

theorem dfsStep_cons (a : α) (g : ℕ × σ) (rest S' : List (ℕ × σ)) :
    dfsStep acc uni succs (a, g :: rest, S') = dfsFrom acc uni succs a g rest S' := by
  rw [Bool.eq_iff_iff]
  simp only [dfsStep, List.tail_cons, List.any_cons, decide_true, Bool.true_and, Bool.or_eq_true,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.cons.injEq, and_true]
  constructor
  · rintro (h | ⟨g', -, rfl, h⟩) <;> exact h
  · exact Or.inl

/-! ### Polynomial time -/

theorem pt_dfsFrom (ha : PT acc) (hu : PT uni) (hs : PT succs) :
    PT fun y : α × (ℕ × σ) × List (ℕ × σ) × List (ℕ × σ) =>
      dfsFrom acc uni succs y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  have hc : PT fun y : α × (ℕ × σ) × List (ℕ × σ) × List (ℕ × σ) => (y.1, y.2.1.2) :=
    PT.pair PT.fst (PT.snd.comp (PT.fst.comp PT.snd))
  have hk : PT fun y : α × (ℕ × σ) × List (ℕ × σ) × List (ℕ × σ) => y.2.1.1 :=
    PT.fst.comp (PT.fst.comp PT.snd)
  have hr : PT fun y : α × (ℕ × σ) × List (ℕ × σ) × List (ℕ × σ) => y.2.2.1 :=
    PT.fst.comp (PT.snd.comp PT.snd)
  have hS : PT fun y : α × (ℕ × σ) × List (ℕ × σ) × List (ℕ × σ) => y.2.2.2 :=
    PT.snd.comp (PT.snd.comp PT.snd)
  have hsc := hs.comp hc
  unfold dfsFrom
  exact PT.or (PT.and (ha.comp hc) (PT.eq hS hr))
    (PT.and (PT.lt (PT.const 0) hk) (PT.cond (hu.comp hc)
      (PT.eq hS (PT.append (PT.map hsc (PT.pair (PT.pred (hk.comp PT.fst)) PT.snd)) hr))
      (PT.any hsc (PT.eq (hS.comp PT.fst)
        (PT.cons (PT.pair (PT.pred (hk.comp PT.fst)) PT.snd) (hr.comp PT.fst))))))

theorem pt_dfsStep (ha : PT acc) (hu : PT uni) (hs : PT succs) :
    PT (dfsStep (α := α) acc uni succs) := by
  have hS : PT fun x : α × List (ℕ × σ) × List (ℕ × σ) => x.2.1 := PT.fst.comp PT.snd
  unfold dfsStep
  exact PT.any hS (PT.and (PT.eq (hS.comp PT.fst) (PT.cons PT.snd (PT.tail (hS.comp PT.fst))))
    ((pt_dfsFrom ha hu hs).comp (PT.pair (PT.fst.comp PT.fst) (PT.pair PT.snd
      (PT.pair (PT.tail (hS.comp PT.fst)) (PT.snd.comp (PT.snd.comp PT.fst)))))))

/-! ### Soundness -/

theorem gameVal_of_acc {a : α} {c : σ} (h : acc (a, c) = true) (k : ℕ) :
    gameVal acc uni succs a k c = true := by
  cases k <;> simp [gameVal, h]

/-- Every goal of a stack from which the evaluation empties the stack is won. -/
theorem dfs_sound {a : α} {R : List (ℕ × σ) → List (ℕ × σ) → Prop}
    (hR : ∀ S S', R S S' → dfsStep acc uni succs (a, S, S') = true) {S : List (ℕ × σ)}
    (h : Relation.ReflTransGen R S []) : ∀ g ∈ S, gameVal acc uni succs a g.1 g.2 = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => simp
  | @head S S' hst _ ih =>
    have hst := hR _ _ hst
    cases S with
    | nil => simp [dfsStep_nil] at hst
    | cons g rest =>
      rw [dfsStep_cons] at hst
      obtain ⟨k, c⟩ := g
      simp only [dfsFrom, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hst
      rcases hst with ⟨hac, rfl⟩ | ⟨hk, hst⟩
      · intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · exact gameVal_of_acc hac _
        · exact ih g hg
      · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hst ih
        cases hu : uni (a, c) <;> rw [hu] at hst <;> simp only [cond_true, cond_false,
          decide_eq_true_eq, List.any_eq_true] at hst
        · obtain ⟨c', hc', rfl⟩ := hst
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg
          · simp only [gameVal, hu, cond_false, Bool.or_eq_true, List.any_eq_true]
            exact Or.inr ⟨c', hc', ih _ (List.mem_cons_self ..)⟩
          · exact ih g (List.mem_cons_of_mem _ hg)
        · subst hst
          intro g hg
          rcases List.mem_cons.1 hg with rfl | hg
          · simp only [gameVal, hu, cond_true, Bool.or_eq_true, List.all_eq_true]
            exact Or.inr fun c' hc' => ih (k, c') (List.mem_append_left _ (List.mem_map.2 ⟨c', hc', rfl⟩))
          · exact ih g (List.mem_append_right _ hg)

/-! ### Completeness -/

theorem sz_append_add (l m : List (ℕ × σ)) : sz (l ++ m) + 1 = sz l + sz m := by
  induction l with
  | nil => simp [sz_nil]; omega
  | cons g l ih => simp only [List.cons_append, sz_cons]; omega

theorem sz_map_pair (k : ℕ) (l : List σ) :
    sz (l.map fun c => (k, c)) = sz l + 2 * l.length * sz k := by
  induction l with
  | nil => simp [sz_nil]
  | cons c l ih => simp only [List.map_cons, sz_cons, sz_prod, ih, List.length_cons]; ring

/-- The stack space per level of the evaluation. -/
def dfsCost (B K : ℕ) : ℕ := B + 2 * B * K + 2 * K + 2 * B + 2

theorem dfsCost_ge (B K : ℕ) : B + 2 * (B * K) ≤ dfsCost B K ∧ 2 * K + 2 * B + 2 ≤ dfsCost B K := by
  unfold dfsCost; constructor <;> nlinarith

/-- A won goal is discharged by a run whose stacks stay below `sz rest + k * dfsCost B K`, where
`B` bounds the successor lists met and `K` the remaining depths. -/
theorem dfs_complete {a : α} {B K N : ℕ} :
    ∀ (k : ℕ) (c : σ) (rest : List (ℕ × σ)), gameVal acc uni succs a k c = true →
      (∀ k' ≤ k, sz k' ≤ K) →
      (∀ n < k, ∀ c', GameReach succs a n c c' → sz (succs (a, c')) ≤ B) →
      sz rest + k * dfsCost B K ≤ N →
      Relation.ReflTransGen (fun S S' => dfsStep acc uni succs (a, S, S') = true ∧ sz S' ≤ N)
        ((k, c) :: rest) rest := by
  intro k
  induction k with
  | zero =>
    intro c rest hw _ _ hN
    refine Relation.ReflTransGen.single ⟨?_, by omega⟩
    simp only [gameVal] at hw
    simp [dfsStep_cons, dfsFrom, hw]
  | succ k ih =>
    intro c rest hw hK hB hN
    by_cases hac : acc (a, c) = true
    · refine Relation.ReflTransGen.single ⟨?_, le_trans (Nat.le_add_right _ _) hN⟩
      simp [dfsStep_cons, dfsFrom, hac]
    have hB0 : sz (succs (a, c)) ≤ B := hB 0 (by omega) c rfl
    have hKk : sz k ≤ K := hK k (by omega)
    have hK' : ∀ k' ≤ k, sz k' ≤ K := fun k' h => hK k' (by omega)
    have hB' : ∀ c₁ ∈ succs (a, c), ∀ n < k, ∀ c', GameReach succs a n c₁ c' →
        sz (succs (a, c')) ≤ B := fun c₁ h₁ n hn c' hr => hB (n + 1) (by omega) c' ⟨c₁, h₁, hr⟩
    have hC : (k + 1) * dfsCost B K = k * dfsCost B K + dfsCost B K := by ring
    obtain ⟨hD1, hD2⟩ := dfsCost_ge B K
    have h0 := Nat.zero_le (k * dfsCost B K)
    simp only [gameVal, hac, Bool.false_or] at hw
    cases hu : uni (a, c) <;> rw [hu] at hw <;>
      simp only [cond_true, cond_false, List.any_eq_true, List.all_eq_true] at hw
    · obtain ⟨c', hc', hw'⟩ := hw
      have hc'B : sz c' ≤ B := (sz_le_of_mem hc').trans hB0
      refine Relation.ReflTransGen.head ⟨?_, ?_⟩ (ih c' rest hw' hK' (hB' c' hc') ?_)
      · simp only [dfsStep_cons, dfsFrom, hu, hac, Bool.false_and, Bool.false_or, cond_false,
          Nat.add_sub_cancel, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
        exact ⟨by omega, c', hc', rfl⟩
      · simp only [sz_cons, sz_prod]
        linarith
      · linarith
    · -- the children are discharged one after the other
      have key : ∀ l : List σ, sz l ≤ B → (∀ c' ∈ l, c' ∈ succs (a, c)) →
          Relation.ReflTransGen (fun S S' => dfsStep acc uni succs (a, S, S') = true ∧ sz S' ≤ N)
            ((l.map fun c' => (k, c')) ++ rest) rest := by
        intro l
        induction l with
        | nil => intro _ _; exact .refl
        | cons c' l ihl =>
          intro hl hsub
          have hlB : sz l ≤ B := by rw [sz_cons] at hl; omega
          have hlen : l.length ≤ B := (length_le_sz l).trans hlB
          have hc' := hsub c' (List.mem_cons_self ..)
          refine Relation.ReflTransGen.trans (ih c' ((l.map fun c' => (k, c')) ++ rest) (hw c' hc') hK' (hB' c' hc') ?_)
            (ihl hlB fun c'' h => hsub c'' (List.mem_cons_of_mem _ h))
          have h1 := sz_append_add (l.map fun c' => (k, c')) rest
          rw [sz_map_pair] at h1
          have h2 : l.length * sz k ≤ B * K := Nat.mul_le_mul hlen hKk
          linarith
      refine Relation.ReflTransGen.head ⟨?_, ?_⟩ (key _ hB0 fun _ h => h)
      · simp [dfsStep_cons, dfsFrom, hu, hac]
      · have h1 := sz_append_add ((succs (a, c)).map fun c' => (k, c')) rest
        rw [sz_map_pair] at h1
        have h2 : (succs (a, c)).length * sz k ≤ B * K :=
          Nat.mul_le_mul ((length_le_sz _).trans hB0) hKk
        linarith

/-! ### The search -/

/-- The initial stacks: the single goal `(depth a, c₀)` for an initial configuration `c₀`. -/
def dfsInit (init : α × σ → Bool) (depth : α → ℕ) (x : α × List (ℕ × σ)) : Bool :=
  decide (x.2.length = 1) && x.2.all fun g => decide (g.1 = depth x.1) && init (x.1, g.2)

/-- The accepting stack: the empty one. -/
def dfsAcc (x : α × List (ℕ × σ)) : Bool := x.2.isEmpty

theorem pt_dfsInit {init : α × σ → Bool} {depth : α → ℕ} (hi : PT init) (hd : PT depth) :
    PT (dfsInit (σ := σ) init depth) := by
  unfold dfsInit
  exact PT.and (PT.eq (PT.length PT.snd) (PT.const 1)) (PT.all PT.snd
    (PT.and (PT.eq (PT.fst.comp PT.snd) (hd.comp (PT.fst.comp PT.fst)))
      (hi.comp (PT.pair (PT.fst.comp PT.fst) (PT.snd.comp PT.snd)))))

theorem pt_dfsAcc : PT (dfsAcc (α := α) (σ := σ)) := PT.isEmpty PT.snd

theorem dfsInit_iff {init : α × σ → Bool} {depth : α → ℕ} (a : α) (S : List (ℕ × σ)) :
    dfsInit init depth (a, S) = true ↔ ∃ c₀, S = [(depth a, c₀)] ∧ init (a, c₀) = true := by
  rcases S with _ | ⟨⟨k, c⟩, _ | ⟨g, S⟩⟩
  · simp [dfsInit]
  · simp [dfsInit, and_assoc]
  · simp [dfsInit]

theorem sz_le_sz_of_le {k D : ℕ} (h : k ≤ D) : sz k ≤ sz D := by
  rw [sz_nat, sz_nat]
  have := length_bits_le_of_lt (lt_of_le_of_lt h (lt_two_pow_length_bits D))
  omega

theorem sz_nat_le (D : ℕ) : sz D ≤ 2 * D + 1 := by
  rw [sz_nat]
  have := length_bits_le_of_lt (Nat.lt_two_pow_self (n := D))
  omega

theorem dfs_bound_le {D K B M : ℕ} (hD : D ≤ M) (hK : K + 1 ≤ M) (hB : B ≤ M) :
    D * dfsCost B K + 2 * (K + B) + 3 ≤ 16 * M ^ 3 := by
  have hM : 1 ≤ M := by omega
  have hBK : B * K ≤ M * M := Nat.mul_le_mul hB (by omega)
  have hc : dfsCost B K ≤ 9 * M ^ 2 := by unfold dfsCost; nlinarith
  have h1 : D * dfsCost B K ≤ M * (9 * M ^ 2) := Nat.mul_le_mul hD hc
  have h2 : M ≤ M ^ 3 := by nlinarith [Nat.pow_le_pow_right hM (show 1 ≤ 3 by omega)]
  have h3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
  omega

/-- **The game as a search**: for one input `a`, membership is the existence of a run of the
depth-first evaluation through stacks of size at most `L`. -/
theorem game_iff_search {Q : α → Prop} {init : α × σ → Bool} {depth : α → ℕ} (a : α) (B L : ℕ)
    (hQ : Q a ↔ ∃ c₀, sz c₀ ≤ B ∧ init (a, c₀) = true ∧
      gameVal acc uni succs a (depth a) c₀ = true)
    (hb : ∀ c₀, init (a, c₀) = true → sz c₀ ≤ B ∧
      ∀ n < depth a, ∀ c, GameReach succs a n c₀ c → sz (succs (a, c)) ≤ B)
    (hL : depth a * dfsCost B (sz (depth a)) + 2 * (sz (depth a) + B) + 3 ≤ L) :
    Q a ↔ ∃ S₀ S, sz S₀ ≤ L ∧ dfsInit init depth (a, S₀) = true ∧
      Relation.ReflTransGen (fun S S' => sz S' ≤ L ∧ dfsStep acc uni succs (a, S, S') = true)
        S₀ S ∧ dfsAcc (a, S) = true := by
  have hsz : ∀ c₀ : σ, sz [(depth a, c₀)] = 2 * (sz (depth a) + sz c₀) + 3 := fun c₀ => by
    simp only [sz_cons, sz_nil, sz_prod]; ring
  rw [hQ]
  constructor
  · rintro ⟨c₀, hc₀, hi₀, hw⟩
    refine ⟨[(depth a, c₀)], [], by rw [hsz]; omega, (dfsInit_iff a _).2 ⟨c₀, rfl, hi₀⟩, ?_, rfl⟩
    have h := dfs_complete (N := L) (depth a) c₀ [] hw (fun k' h => sz_le_sz_of_le h)
      (hb c₀ hi₀).2 (by rw [sz_nil]; omega)
    exact h.mono fun S S' h => ⟨h.2, h.1⟩
  · rintro ⟨S₀, S, -, hi, hr, hac⟩
    obtain ⟨c₀, rfl, hi₀⟩ := (dfsInit_iff a _).1 hi
    obtain rfl : S = [] := List.isEmpty_iff.1 hac
    exact ⟨c₀, (hb c₀ hi₀).1, hi₀,
      dfs_sound (R := fun S S' => sz S' ≤ L ∧ dfsStep acc uni succs (a, S, S') = true)
        (fun _ _ h => h.2) hr _ (List.mem_singleton_self _)⟩

/-! ### The complexity bounds -/

/-- **AND-OR games of polynomial depth over polynomial-size successor lists are decided in
polynomial space.** -/
theorem inPSpace_codeLang_of_game {Q : α → Prop} {init : α × σ → Bool} {depth : α → ℕ}
    (hi : PT init) (ha : PT acc) (hu : PT uni) (hs : PT succs) (hd : PT depth)
    (q : Polynomial ℕ)
    (hbound : ∀ a, depth a ≤ q.eval (sz a) ∧ ∀ c₀, init (a, c₀) = true →
      sz c₀ ≤ q.eval (sz a) ∧
        ∀ n < depth a, ∀ c, GameReach succs a n c₀ c → sz (succs (a, c)) ≤ q.eval (sz a))
    (hQ : ∀ a, Q a ↔ ∃ c₀, sz c₀ ≤ q.eval (sz a) ∧ init (a, c₀) = true ∧
      gameVal acc uni succs a (depth a) c₀ = true) :
    Cx.PSPACE (codeLang α Q) := by
  refine inPSpace_codeLang_of_search (pt_dfsInit hi hd) (pt_dfsStep ha hu hs) pt_dfsAcc
    (Polynomial.C 16 * (Polynomial.C 2 * q + Polynomial.C 2) ^ 3) fun a => ?_
  refine game_iff_search a (q.eval (sz a)) _ (hQ a) (hbound a).2 ?_
  have hD := (hbound a).1
  have hK := sz_nat_le (depth a)
  have := dfs_bound_le (D := depth a) (K := sz (depth a)) (M := 2 * q.eval (sz a) + 2) (B := q.eval (sz a)) (by omega)
    (show sz (depth a) + 1 ≤ _ by omega) (by omega)
  simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_C]
    using this

/-- **AND-OR games of polynomial-time computable depth over exponential-size successor lists are
decided in exponential space.** -/
theorem inExpSpace_codeLang_of_game {Q : α → Prop} {init : α × σ → Bool} {depth : α → ℕ}
    (hi : PT init) (ha : PT acc) (hu : PT uni) (hs : PT succs) (hd : PT depth)
    (q : Polynomial ℕ)
    (hbound : ∀ a c₀, init (a, c₀) = true → sz c₀ ≤ 2 ^ q.eval (sz a) ∧
      ∀ n < depth a, ∀ c, GameReach succs a n c₀ c → sz (succs (a, c)) ≤ 2 ^ q.eval (sz a))
    (hQ : ∀ a, Q a ↔ ∃ c₀, sz c₀ ≤ 2 ^ q.eval (sz a) ∧ init (a, c₀) = true ∧
      gameVal acc uni succs a (depth a) c₀ = true) :
    Cx.EXPSPACE (codeLang α Q) := by
  obtain ⟨e, d, hde⟩ := hd.pb
  let p : Polynomial ℕ := Polynomial.C 3 * (Polynomial.C d * (Polynomial.X + 1) ^ e + q) +
    Polynomial.C 5
  refine inExpSpace_codeLang_of_search (pt_dfsInit hi hd) (pt_dfsStep ha hu hs) pt_dfsAcc p
    fun a => ?_
  set P := d * (sz a + 1) ^ e with hP
  set E := q.eval (sz a) with hE
  have hpe : p.eval (sz a) = 3 * (P + E) + 5 := by
    simp [p, hP, hE, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add]
  have hpos : 0 < 2 ^ p.eval (sz a) := Nat.two_pow_pos _
  have hlt : ∀ n : ℕ, n < 2 ^ p.eval (sz a) ↔ n ≤ 2 ^ p.eval (sz a) - 1 := fun n => by omega
  simp only [hlt]
  refine game_iff_search a (2 ^ E) _ (hQ a) (hbound a) ?_
  have hDs : sz (depth a) ≤ P := hde a
  have hD : depth a ≤ 2 ^ P := by
    have h1 := lt_two_pow_length_bits (depth a)
    have h2 : (bitsOfNat (depth a)).length ≤ P := by rw [sz_nat] at hDs; omega
    exact (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) h2)).le
  have hPl : P + 1 ≤ 2 ^ P := Nat.lt_two_pow_self
  have hM1 : 2 ^ P ≤ 2 ^ (P + E) := Nat.pow_le_pow_right (by omega) (by omega)
  have hM2 : 2 ^ E ≤ 2 ^ (P + E) := Nat.pow_le_pow_right (by omega) (by omega)
  have := dfs_bound_le (D := depth a) (M := 2 ^ (P + E)) (B := 2 ^ E) (K := sz (depth a)) (by omega)
    (by omega) hM2
  have h16 : 16 * (2 ^ (P + E)) ^ 3 + 1 ≤ 2 ^ p.eval (sz a) := by
    rw [hpe, ← pow_mul, show 3 * (P + E) + 5 = (P + E) * 3 + 4 + 1 by ring, pow_succ, pow_add]
    have := Nat.one_le_two_pow (n := (P + E) * 3)
    omega
  omega

end Game

end PolyDom

end Syn

end HTN
