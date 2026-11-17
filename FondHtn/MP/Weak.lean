import FondHtn.Transfer.Deterministic
/-!
# Weak method-based policies = weak fixed-method (LD) solutions ([CB22, Prop. 2])

**Theorem** (`FOND.Problem.mpWeakSolvable_iff_weakLDSolvable`).  For a well-formed problem over an
infinite type of task ids, a weak solution with method-based policies [CB22, Def. 7] exists iff a
weak LD solution with fixed methods [CB21, Def. 2.7] exists.

Both directions go through the *weak path game* `WPathN n x`: a path of length `n` from the node
`x` to a goal node, each step decomposing some compound task or executing some unconstrained
applicable primitive task with *one chosen* outcome (`WStepL`).

* `⟹`: a reachable goal node of the execution structure gives such a path (every edge of the
  execution structure is a `WStepL` step).  From the path, the decompositions done after an
  execution are moved before it (`HTN.decomposesTo_progress_lift`, after renaming them away from
  the executed id with `HTN.decomposesTo_avoid`), giving an achievable primitive network with a
  weak belief state (`WPathN.toWeakBelief`), hence a weak LD solution.  This generalises
  `FOND.Problem.det_of_mpAndOr` from the deterministic case.
* `⟸`: a weak LD solution gives a path.  We take a path of **minimal length** `n`; its nodes are
  pairwise non-isomorphic (otherwise the part between two isomorphic nodes could be cut out, using
  that the path game is invariant under isomorphism, `WPathN.sim`).  The policy `pathPolicy` is
  defined exactly on the (concrete) nodes of the path and gives there the instruction of the path,
  so it is well-defined in the sense of [CB22, Def. 5].  Every reachable node of its execution
  structure is isomorphic to a node of the path or to an outcome of a primitive step of the path
  (finitely many, as actions have finitely many effects), so `[L]` is finite, and the last node
  of the path is a reachable terminal goal node.

**Gap G18 / deviation.**  The paper's proof does not mention that the path must be chosen
repetition-free modulo isomorphism (a weak LD solution may decompose a recursive task back into
an isomorphic network, and the policy could not give two different instructions at isomorphic
nodes with the same state); we choose a shortest path.  Note also that a policy instruction is
transported along *every* isomorphism of the stored entry (`MPInstr`), including the non-trivial
automorphisms, so the execution structure contains more nodes than the path; this is why
finiteness needs the invariant above rather than just the path.
-/

namespace FOND

open HTN HTN.TaskNetwork

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable {P : Problem F A C I} [DecidableEq I]

/-! ## The weak path game -/

variable (P) in
/-- A labelled step of the weak path game: either `l = (t, ε)` and the unconstrained primitive
task `t` is executed with the outcome `y.state`, or `l = (t, m)` and `t` is decomposed with `m`. -/
def WStepL (x : MPNode F A C I) (l : I × Option (Method I A C)) (y : MPNode F A C I) : Prop :=
  (l.2 = none ∧ ∃ a, x.net.Unconstrained l.1 ∧ x.net.α l.1 = Sum.inl a ∧
      (P.δ a).Applicable x.state ∧ y.state ∈ (P.δ a).outcomes x.state ∧
      y.net = x.net.progress l.1) ∨
    (∃ m, l.2 = some m ∧ DecompStep P.methods x.net l.1 m y.net ∧ y.state = x.state)

variable (P) in
/-- `WPathN n x`: a path of `n` steps of the weak path game leads from `x` to a goal node. -/
inductive WPathN : ℕ → MPNode F A C I → Prop
  | zero {y : MPNode F A C I} (h : y.IsGoal) : WPathN 0 y
  | succ {n : ℕ} {y z : MPNode F A C I} {l : I × Option (Method I A C)} (hs : P.WStepL y l z)
      (h : WPathN n z) : WPathN (n + 1) y

lemma WStepL.wf {x y : MPNode F A C I} {l : I × Option (Method I A C)} (h : P.WStepL x l y)
    (hx : x.net.WF) : y.net.WF := by
  rcases h with ⟨-, a, hu, -, -, -, he⟩ | ⟨m, -, hd, -⟩
  · rw [he]; exact progress_wf hx hu
  · exact hd.wf hx

lemma WStepL.mem {x y : MPNode F A C I} {l : I × Option (Method I A C)} (h : P.WStepL x l y) :
    l.1 ∈ x.net.T := by
  rcases h with ⟨-, a, hu, -⟩ | ⟨m, -, hd, -⟩
  · exact hu.1
  · exact hd.2.1

/-- Steps of the weak path game can be replayed at isomorphic nodes. -/
theorem WStepL.sim [Infinite I] {x x' y : MPNode F A C I} {l : I × Option (Method I A C)}
    (h : P.WStepL x l y) (hx : x.net.WF) (hx' : x'.net.WF) (hiso : x.Iso x') :
    ∃ l' y', P.WStepL x' l' y' ∧ y.Iso y' := by
  obtain ⟨hst, τ, hτ⟩ := hiso
  replace hτ : IsoVia τ x.net x'.net := hτ
  rcases h with ⟨-, a, hu, hα, happ, hs', he⟩ | ⟨m, -, hd, hst'⟩
  · refine ⟨(τ l.1, none), ⟨x'.net.progress (τ l.1), y.state⟩,
      Or.inl ⟨rfl, a, hτ.unconstrained hu, (hτ.α_eq hu.1).trans hα, hst ▸ happ, hst ▸ hs', rfl⟩,
      rfl, τ, ?_⟩
    rw [he]; exact hτ.progress hu.1
  · obtain ⟨u', hd', hiso'⟩ := hd.isoVia hx hx' hτ
    exact ⟨(τ l.1, some m), ⟨u', x'.state⟩, Or.inr ⟨m, rfl, hd', rfl⟩, hst'.trans hst, hiso'⟩

/-- The weak path game is invariant under isomorphism. -/
theorem WPathN.sim [Infinite I] {n : ℕ} {y : MPNode F A C I} (h : P.WPathN n y) :
    ∀ {y' : MPNode F A C I}, y.net.WF → y'.net.WF → y.Iso y' → P.WPathN n y' := by
  induction h with
  | zero hg =>
    intro y' _ _ hiso
    obtain ⟨-, σ, hσ⟩ := hiso
    exact .zero ((show IsoVia σ _ _ from hσ).empty hg)
  | succ hs _ ih =>
    intro y' hy hy' hiso
    obtain ⟨l', z', hs', hz⟩ := hs.sim hy hy' hiso
    exact .succ hs' (ih (hs.wf hy) (hs'.wf hy') hz)

/-- A path of the weak path game as a sequence of nodes and labels. -/
theorem WPathN.path [Nonempty I] {n : ℕ} {y : MPNode F A C I} (h : P.WPathN n y) :
    ∃ (xs : ℕ → MPNode F A C I) (ls : ℕ → I × Option (Method I A C)), xs 0 = y ∧
      (∀ i < n, P.WStepL (xs i) (ls i) (xs (i + 1))) ∧ (xs n).IsGoal := by
  induction h with
  | @zero y hg =>
    exact ⟨fun _ => y, fun _ => (Classical.arbitrary I, none), rfl, fun i hi => absurd hi
      (Nat.not_lt_zero _), hg⟩
  | @succ n y z l hs _ ih =>
    obtain ⟨xs, ls, h0, hst, hg⟩ := ih
    refine ⟨fun i => match i with | 0 => y | k + 1 => xs k,
      fun i => match i with | 0 => l | k + 1 => ls k, rfl, fun i hi => ?_, hg⟩
    cases i with
    | zero => simpa [h0] using hs
    | succ k => exact hst k (by omega)

section Path

variable {xs : ℕ → MPNode F A C I} {ls : ℕ → I × Option (Method I A C)} {n : ℕ}

lemma wPathN_suffix (hs : ∀ i < n, P.WStepL (xs i) (ls i) (xs (i + 1))) (hg : (xs n).IsGoal) :
    ∀ k i, i + k = n → P.WPathN k (xs i)
  | 0, i, h => by
    rw [Nat.add_zero] at h; subst h; exact .zero hg
  | k + 1, i, h => .succ (hs i (by omega)) (wPathN_suffix hs hg k (i + 1) (by omega))

lemma wPathN_prefix (hs : ∀ i < n, P.WStepL (xs i) (ls i) (xs (i + 1))) :
    ∀ i ≤ n, ∀ m, P.WPathN m (xs i) → P.WPathN (i + m) (xs 0)
  | 0, _, m, h => by simpa using h
  | i + 1, hi, m, h => by
    have := wPathN_prefix hs i (by omega) (m + 1) (.succ (hs i (by omega)) h)
    rwa [show i + (m + 1) = i + 1 + m by omega] at this

end Path

/-! ## Weak MP solutions give paths -/

lemma exists_wStepL_of_mpStep {π : MPPolicy F A C I} {x y : MPNode F A C I}
    (h : P.MPStep π x y) : ∃ l, P.WStepL x l y := by
  cases h with
  | @prim t a s' _ hu hα happ hs' => exact ⟨(t, none), Or.inl ⟨rfl, a, hu, hα, happ, hs', rfl⟩⟩
  | @decomp t m tn' _ hd => exact ⟨(t, some m), Or.inr ⟨m, rfl, hd, rfl⟩⟩

lemma exists_wPathN_of_mpStep_star {π : MPPolicy F A C I} {x y : MPNode F A C I}
    (h : Relation.ReflTransGen (P.MPStep π) x y) (hg : y.IsGoal) : ∃ n, P.WPathN n x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .zero hg⟩
  | head hstep _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨l, hl⟩ := exists_wStepL_of_mpStep hstep
    exact ⟨n + 1, .succ hl hn⟩

/-- **Paths give weak belief states after decomposition** (generalises `det_of_mpAndOr`):
decompositions done after executing a task can be done before it. -/
theorem WPathN.toWeakBelief [Infinite I] {n : ℕ} {y : MPNode F A C I} (h : P.WPathN n y)
    (hwf : y.net.WF) :
    ∃ tn', HTN.DecomposesTo P.methods y.net tn' ∧ tn'.IsPrimitive ∧ P.WeakBelief tn' y.state := by
  induction h with
  | @zero y he =>
    have he' : y.net.T = ∅ := he
    exact ⟨_, Relation.ReflTransGen.refl, fun t ht => by simp [he'] at ht, .empty he'⟩
  | @succ n y z l hs _ ih =>
    rcases hs with ⟨-, a, hu, hα, happ, hs', he⟩ | ⟨m, -, hd, hst⟩
    · obtain ⟨Y₂, hY₂, hprim, hwb⟩ := ih (by rw [he]; exact progress_wf hwf hu)
      rw [he] at hY₂
      obtain ⟨Y₂', σ, hav, hσ, -, -⟩ := decomposesTo_avoid hY₂ (progress_wf hwf hu) {l.1}
        (Finset.disjoint_singleton_left.2 (fun h => (mem_progress_T.1 h).1 rfl))
      obtain ⟨X₂, hX₂, hp, hu₂, hα₂, -⟩ := decomposesTo_progress_lift hwf hu hav
      refine ⟨X₂, hX₂, fun t' ht' => ?_, .step hu₂ (hα₂.trans hα) happ hs' ?_⟩
      · by_cases hyt : t' = l.1
        · subst hyt; exact ⟨a, hα₂.trans hα⟩
        · have hy' : t' ∈ (X₂.progress l.1).T := mem_progress_T.2 ⟨hyt, ht'⟩
          rw [hp] at hy'
          obtain ⟨y₀, hy₀, rfl⟩ := hσ.surj hy'
          obtain ⟨b, hb⟩ := hprim y₀ hy₀
          exact ⟨b, by rw [← progress_α X₂ l.1, hp, hσ.α_eq hy₀, hb]⟩
      · rw [hp]; exact hwb.isoVia hσ
    · obtain ⟨tn', h1, h2, h3⟩ := ih (hd.wf hwf)
      exact ⟨tn', .head ⟨_, _, hd⟩ h1, h2, hst ▸ h3⟩

/-- **Weak MP solvability implies weak LD solvability.** -/
theorem weakLDSolvable_of_mpWeakSolvable [Infinite I] (hwf : P.tnI.WF) (h : P.MPWeakSolvable) :
    P.WeakLDSolvable := by
  obtain ⟨π, -, -, x, hx, -, hg⟩ := h
  obtain ⟨n, hn⟩ := exists_wPathN_of_mpStep_star hx hg
  obtain ⟨tn, hd, hprim, hwb⟩ := hn.toWeakBelief hwf
  obtain ⟨l, as, hl, has, hex⟩ := weakExec_of_weakBelief hwb
  exact ⟨tn, l, ⟨hd, hprim⟩, hl, as, has, hex⟩

/-! ## Weak LD solutions give paths -/

lemma exists_wPathN_of_weakBelief {tn : TaskNetwork I A C} {s : Set F} (h : P.WeakBelief tn s) :
    ∃ n, P.WPathN n ⟨tn, s⟩ := by
  induction h with
  | empty h => exact ⟨0, .zero h⟩
  | @step tn s s' t a hu hα happ hs' _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .succ (l := (t, none)) (Or.inl ⟨rfl, a, hu, hα, happ, hs', rfl⟩) hn⟩

lemma exists_wPathN_of_decomposesTo {tn tn' : TaskNetwork I A C} {s : Set F}
    (hd : HTN.DecomposesTo P.methods tn tn') (h : ∃ n, P.WPathN n ⟨tn', s⟩) :
    ∃ n, P.WPathN n ⟨tn, s⟩ := by
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hstep _ ih =>
    rename_i a c _
    obtain ⟨t, m, hs⟩ := hstep
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .succ (z := ⟨c, s⟩) (l := (t, some m)) (Or.inr ⟨m, rfl, hs, rfl⟩) hn⟩

lemma exists_wPathN_of_weakLDSolvable (hwf : P.tnI.WF) (h : P.WeakLDSolvable) :
    ∃ n, P.WPathN n P.mpInit := by
  obtain ⟨tn, l, hach, hl, as, has, hex⟩ := h
  exact exists_wPathN_of_decomposesTo hach.1
    (exists_wPathN_of_weakBelief (weakBelief_of_weakExec (hach.wf hwf).irrefl hl has hex))

/-! ## The policy of a path -/

open Classical in
/-- The policy following a path: defined exactly on the nodes `xs i` (`i < n`), with the
instruction `ls i`. -/
noncomputable def pathPolicy (n : ℕ) (xs : ℕ → MPNode F A C I)
    (ls : ℕ → I × Option (Method I A C)) : MPPolicy F A C I := fun tn s =>
  if h : ∃ i < n, xs i = ⟨tn, s⟩ then some (ls (Classical.choose h)) else none

omit [DecidableEq I] in
lemma pathPolicy_eq_some {n : ℕ} {xs : ℕ → MPNode F A C I} {ls : ℕ → I × Option (Method I A C)}
    {tn : TaskNetwork I A C} {s : Set F} {l : I × Option (Method I A C)}
    (h : pathPolicy n xs ls tn s = some l) : ∃ i < n, xs i = ⟨tn, s⟩ ∧ ls i = l := by
  unfold pathPolicy at h
  split_ifs at h with hc
  · exact ⟨_, (Classical.choose_spec hc).1, (Classical.choose_spec hc).2, Option.some_inj.1 h⟩

omit [DecidableEq I] in
lemma pathPolicy_at {n : ℕ} {xs : ℕ → MPNode F A C I} {ls : ℕ → I × Option (Method I A C)}
    (hinj : ∀ i < n, ∀ j < n, xs i = xs j → i = j) {i : ℕ} (hi : i < n) :
    pathPolicy n xs ls (xs i).net (xs i).state = some (ls i) := by
  have hc : ∃ j < n, xs j = ⟨(xs i).net, (xs i).state⟩ := ⟨i, hi, rfl⟩
  unfold pathPolicy
  rw [dif_pos hc]
  rw [hinj _ (Classical.choose_spec hc).1 _ hi (Classical.choose_spec hc).2]

/-- **Weak LD solvability implies weak MP solvability**: the policy of a shortest path. -/
theorem mpWeakSolvable_of_exists_wPathN [Infinite I] (hP : P.WF)
    (hex : ∃ n, P.WPathN n P.mpInit) : P.MPWeakSolvable := by
  classical
  obtain ⟨n, hnspec, hmin⟩ : ∃ n, P.WPathN n P.mpInit ∧ ∀ m < n, ¬ P.WPathN m P.mpInit :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  obtain ⟨xs, ls, h0, hs, hg⟩ := hnspec.path
  have hwf : ∀ i ≤ n, (xs i).net.WF := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact hP.tnI
    | succ i ih => intro hi; exact (hs i (by omega)).wf (ih (by omega))
  -- the nodes of a shortest path are pairwise non-isomorphic
  have key : ∀ i j, i < j → j ≤ n → ¬ (xs i).Iso (xs j) := by
    intro i j hij hj hiso
    have h1 : P.WPathN (n - j) (xs j) := wPathN_suffix hs hg (n - j) j (by omega)
    have h2 : P.WPathN (n - j) (xs i) := h1.sim (hwf j hj) (hwf i (by omega)) hiso.symm
    have h3 := wPathN_prefix hs i (by omega) _ h2
    rw [h0] at h3
    exact hmin _ (by omega) h3
  have hiso_eq : ∀ i ≤ n, ∀ j ≤ n, (xs i).Iso (xs j) → i = j := by
    intro i hi j hj hiso
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hiso (key i j h hj)
    · exact h
    · exact absurd hiso.symm (key j i h hi)
  have hinj : ∀ i < n, ∀ j < n, xs i = xs j → i = j := fun i hi j hj he =>
    hiso_eq i hi.le j hj.le (he ▸ MPNode.Iso.refl _)
  set π := pathPolicy n xs ls with hπdef
  have hpol : ∀ i < n, π (xs i).net (xs i).state = some (ls i) := fun i hi => pathPolicy_at hinj hi
  -- well-definedness
  have hwd : π.WellDefined := by
    intro tn tn' s h h' hiso
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 h'
    obtain ⟨i, hi, hxi, -⟩ := pathPolicy_eq_some hl
    obtain ⟨j, hj, hxj, -⟩ := pathPolicy_eq_some hl'
    have : i = j := hiso_eq i hi.le j hj.le (by rw [hxi, hxj]; exact ⟨rfl, hiso⟩)
    subst this
    rw [hxi] at hxj
    exact congrArg MPNode.net hxj
  -- the path is reachable
  have hreach : ∀ i ≤ n, P.MPReach π (xs i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact .refl
    | succ i ih =>
      intro hi
      refine (ih (by omega)).tail ?_
      have hst := hs i (by omega)
      have hinstr : MPInstr π (xs i) (ls i).1 (ls i).2 :=
        ⟨(xs i).net, id, (ls i).1, IsoVia.refl _, hst.mem, hpol i (by omega), rfl⟩
      rcases hst with ⟨hl, a, hu, hα, happ, hs', he⟩ | ⟨m, hl, hd, hst'⟩
      · rw [hl] at hinstr
        have e : xs (i + 1) = ⟨(xs i).net.progress (ls i).1, (xs (i + 1)).state⟩ := by rw [← he]
        rw [e]
        exact MPStep.prim hinstr hu hα happ hs'
      · rw [hl] at hinstr
        have e : xs (i + 1) = ⟨(xs (i + 1)).net, (xs i).state⟩ := by rw [← hst']
        rw [e]
        exact MPStep.decomp hinstr hd
  -- the last node is terminal
  have hterm : P.MPTerminal π (xs n) := by
    intro y hy
    have hg' : (xs n).net.T = ∅ := hg
    have hi : ∃ t mo, MPInstr π (xs n) t mo := by
      cases hy with
      | prim hi => exact ⟨_, _, hi⟩
      | decomp hi => exact ⟨_, _, hi⟩
    obtain ⟨t, mo, tn', σ, t', hσ, ht', -, -⟩ := hi
    have := hσ.mem ht'
    rw [hg'] at this
    simp at this
  -- finiteness
  let outs : ℕ → Set (Set F) := fun i =>
    Sum.elim (fun a => (P.δ a).outcomes (xs i).state) (fun _ => ∅) ((xs i).net.α (ls i).1)
  have houts : ∀ i, (outs i).Finite := by
    intro i
    simp only [outs]
    rcases (xs i).net.α (ls i).1 with a | c
    · exact Action.outcomes_finite (hP.actions a) _
    · exact Set.finite_empty
  let S : Set (MPNode F A C I) := xs '' Set.Iic n ∪
    ⋃ i ∈ Set.Iio n, (fun s' => (⟨(xs i).net.progress (ls i).1, s'⟩ : MPNode F A C I)) '' outs i
  have hSfin : S.Finite :=
    ((Set.finite_Iic n).image xs).union ((Set.finite_Iio n).biUnion fun i _ => (houts i).image _)
  have hinv : ∀ y, P.MPReach π y → y.net.WF ∧ ∃ z ∈ S, y.Iso z := by
    intro y hy
    induction hy with
    | refl => exact ⟨hP.tnI, xs 0, Or.inl ⟨0, by simp, rfl⟩, by rw [h0]; exact MPNode.Iso.refl _⟩
    | @tail y y' _ hstep ih =>
      obtain ⟨hywf, -⟩ := ih
      cases hstep with
      | @prim t a s' hi hu hα happ hs' =>
        obtain ⟨tn', σ, t', hσ, ht', hπ, rfl⟩ := hi
        obtain ⟨j, hj, hxj, hlj⟩ := pathPolicy_eq_some hπ
        refine ⟨progress_wf hywf hu, ⟨(xs j).net.progress (ls j).1, s'⟩, Or.inr ?_, rfl, ?_⟩
        · refine Set.mem_biUnion (x := j) hj ⟨s', ?_, rfl⟩
          simp only [outs, hxj, hlj]
          rw [← hσ.α_eq ht', hα]
          exact hs'
        · rw [hxj, hlj]
          exact (hσ.progress ht').iso.symm
      | @decomp t m tn'' hi hd =>
        obtain ⟨tn', σ, t', hσ, ht', hπ, rfl⟩ := hi
        obtain ⟨j, hj, hxj, hlj⟩ := pathPolicy_eq_some hπ
        refine ⟨hd.wf hywf, xs (j + 1), Or.inl ⟨j + 1, by simp; omega, rfl⟩, ?_⟩
        rcases hs j hj with ⟨hl, -⟩ | ⟨m', hl, hd', hst'⟩
        · rw [hlj] at hl; exact absurd hl (by simp)
        · rw [hlj] at hl hd'
          cases hl
          have hwfj := hwf j hj.le
          rw [hxj] at hd' hst' hwfj
          refine ⟨hst'.symm, ?_⟩
          exact (DecompStep.iso_of_isoVia hd' hd rfl hwfj hywf hσ).symm
  exact ⟨π, hwd, ⟨S, hSfin, fun y hy => (hinv y hy).2⟩, xs n, hreach n le_rfl, hterm, hg⟩

/-- **[CB22, Prop. 2]**: weak solvability with method-based policies coincides with weak LD
solvability with fixed methods. -/
theorem mpWeakSolvable_iff_weakLDSolvable [Infinite I] (hP : P.WF) :
    P.MPWeakSolvable ↔ P.WeakLDSolvable :=
  ⟨weakLDSolvable_of_mpWeakSolvable hP.tnI, fun h =>
    mpWeakSolvable_of_exists_wPathN hP (exists_wPathN_of_weakLDSolvable hP.tnI h)⟩

end Problem

end FOND
