import HtnComplexity.Computable.RegSim
import HtnComplexity.Computable.AcDecide
/-!
# Plan existence is decidable for regular domain descriptions

The hierarchy of a regular domain description may be **cyclic**, so there is no bound on the
length of a solution — but there *is* a bound on the length of a **shortest** solution, and this
file turns it into a decision procedure.

* `HTN.Syn.PPath d c cs` — the configurations `cs` visited by a run of the search of
  `HtnComplexity/Computable/PoSearch.lean` starting at `c`, and `HTN.Syn.endOf c cs` the
  configuration it ends in;
* `HTN.Syn.replay` — a run can be replayed from every *similar* configuration
  (`HtnComplexity/Computable/RegSim.lean`), with the same length;
* `HTN.Syn.exists_short_ppath` — hence a solving run can be shortened until its length is below
  `(HTN.Syn.allCfgs d q).length`: a longer run visits two configurations with the same normal
  form (`HtnComplexity/Computable/RegNorm.lean`), which are similar, so the tail of the run
  can be replayed from the earlier one;
* `HTN.Syn.regSolvableB` and `HTN.Syn.regSolvableB_iff` — **the decision procedure**: the
  bounded breadth-first search `HTN.Syn.bfs` of `HtnComplexity/Computable/AcDecide.lean`,
  run for `(HTN.Syn.allCfgs d q).length` rounds.
-/

namespace HTN

namespace Syn

/-! ### Runs of the search -/

/-- `PPath d c cs` says that `cs` lists the configurations a run of the search visits after
`c`. -/
def PPath (d : DomDesc) : PConfig → List PConfig → Prop
  | _, [] => True
  | c, x :: xs => PStep d c x ∧ PPath d x xs

/-- The configuration a run ends in. -/
def endOf : PConfig → List PConfig → PConfig
  | c, [] => c
  | _, x :: xs => endOf x xs

@[simp] theorem endOf_nil (c : PConfig) : endOf c [] = c := rfl

@[simp] theorem endOf_cons (c x : PConfig) (xs : List PConfig) :
    endOf c (x :: xs) = endOf x xs := rfl

theorem endOf_append (c : PConfig) (l₁ l₂ : List PConfig) :
    endOf c (l₁ ++ l₂) = endOf (endOf c l₁) l₂ := by
  induction l₁ generalizing c with
  | nil => rfl
  | cons x xs ih => exact ih x

theorem PPath.append {d : DomDesc} {c : PConfig} {l₁ l₂ : List PConfig}
    (h₁ : PPath d c l₁) (h₂ : PPath d (endOf c l₁) l₂) : PPath d c (l₁ ++ l₂) := by
  induction l₁ generalizing c with
  | nil => exact h₂
  | cons x xs ih => exact ⟨h₁.1, ih h₁.2 h₂⟩

theorem PPath.take {d : DomDesc} {c : PConfig} {cs : List PConfig} (h : PPath d c cs) (i : ℕ) :
    PPath d c (cs.take i) := by
  induction i generalizing c cs with
  | zero => exact trivial
  | succ n ih =>
    match cs with
    | [] => exact trivial
    | x :: xs => exact ⟨h.1, ih h.2⟩

theorem PPath.drop {d : DomDesc} {c : PConfig} {cs : List PConfig} (h : PPath d c cs) (i : ℕ) :
    PPath d (endOf c (cs.take i)) (cs.drop i) := by
  induction i generalizing c cs with
  | zero => exact h
  | succ n ih =>
    match cs with
    | [] => exact trivial
    | x :: xs => exact ih h.2

theorem endOf_take_drop (c : PConfig) (cs : List PConfig) (i : ℕ) :
    endOf (endOf c (cs.take i)) (cs.drop i) = endOf c cs := by
  rw [← endOf_append, List.take_append_drop]

/-- A run witnesses reachability. -/
theorem pReach_of_ppath {d : DomDesc} {c : PConfig} :
    ∀ {cs : List PConfig}, PPath d c cs → PReach d c (endOf c cs) := by
  intro cs
  induction cs generalizing c with
  | nil => exact fun _ => Relation.ReflTransGen.refl
  | cons x xs ih => exact fun h => Relation.ReflTransGen.head h.1 (ih h.2)

/-- Conversely, reachability is witnessed by a run. -/
theorem exists_ppath_of_pReach {d : DomDesc} {c c' : PConfig} (h : PReach d c c') :
    ∃ cs, PPath d c cs ∧ endOf c cs = c' := by
  induction h with
  | refl => exact ⟨[], trivial, rfl⟩
  | @tail b c'' hr hstep ih =>
    obtain ⟨cs, hcs, hend⟩ := ih
    refine ⟨cs ++ [c''], hcs.append ?_, ?_⟩
    · rw [hend]
      exact ⟨hstep, trivial⟩
    · rw [endOf_append, hend]
      rfl

/-- Any invariant preserved by the search holds along a run. -/
theorem inv_ppath {d : DomDesc} {P : PConfig → Prop} {c : PConfig}
    (hpres : ∀ {c c' : PConfig}, P c → PStep d c c' → P c')
    (h : P c) {cs : List PConfig} (hcs : PPath d c cs) : P (endOf c cs) := by
  induction cs generalizing c with
  | nil => exact h
  | cons x xs ih => exact ih (hpres h hcs.1) hcs.2

theorem ok_of_ppath {d : DomDesc} {c : PConfig} (h : PNet.Ok c.2) {cs : List PConfig}
    (hcs : PPath d c cs) : PNet.Ok (endOf c cs).2 := ok_of_pReach h (pReach_of_ppath hcs)

/-! ### Replaying a run from a similar configuration -/

/-- **A run can be replayed from every similar configuration.** -/
theorem replay {d : DomDesc} {q : InstDesc} : ∀ (cs : List PConfig) (c₁ c₂ : PConfig),
    PNet.Ok c₁.2 → PNet.Ok c₂.2 → Sim c₁ c₂ → PPath d c₂ cs →
    ∃ cs', PPath d c₁ cs' ∧ cs'.length = cs.length ∧ Sim (endOf c₁ cs') (endOf c₂ cs) := by
  intro cs
  induction cs with
  | nil => exact fun c₁ c₂ _ _ hsim _ => ⟨[], trivial, rfl, hsim⟩
  | cons x xs ih =>
    intro c₁ c₂ h₁ h₂ hsim hpath
    obtain ⟨c₁', hstep', hsim'⟩ := exists_pStep_of_sim (q := q) h₁ h₂ hsim hpath.1
    have h₁' : PNet.Ok c₁'.2 := ok_of_pStep h₁ hstep'
    have h₂' : PNet.Ok x.2 := ok_of_pStep h₂ hpath.1
    obtain ⟨cs', hcs', hlen, hend⟩ := ih c₁' x h₁' h₂' hsim' hpath.2
    exact ⟨c₁' :: cs', ⟨hstep', hcs'⟩, by simpa using hlen, hend⟩

/-! ### Shortening a solving run -/

/-- **A solving run can be shortened** below the number of normal forms: a longer run visits two
configurations with the same normal form, and the tail of the run can be replayed from the
earlier of the two. -/
theorem exists_short_ppath {d : DomDesc} {q : InstDesc} {B : ℕ} {P : PConfig → Prop}
    (hPI : ∀ {c : PConfig}, P c → CfgInv d q B c)
    (hpres : ∀ {c c' : PConfig}, P c → PStep d c c' → P c') :
    ∀ (n : ℕ) (cs : List PConfig) (c : PConfig), cs.length ≤ n → P c → PPath d c cs →
      isGoalB q (endOf c cs) = true →
      ∃ cs', PPath d c cs' ∧ cs'.length ≤ (allCfgs d q B).length ∧
        isGoalB q (endOf c cs') = true := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro cs c hn hinv hcs hgoal
    by_cases hle : cs.length ≤ (allCfgs d q B).length
    · exact ⟨cs, hcs, hle, hgoal⟩
    -- the run is longer than the number of normal forms, so it repeats one
    push_neg at hle
    have hinvAt : ∀ i, CfgInv d q B (endOf c (cs.take i)) := fun i =>
      hPI (inv_ppath hpres hinv (hcs.take i))
    have hmaps : ∀ i ∈ Finset.range (cs.length + 1),
        normCfg d q (endOf c (cs.take i)) ∈ (allCfgs d q B).toFinset := by
      intro i _
      exact List.mem_toFinset.2 (mem_allCfgs (hinvAt i))
    have hcard : (allCfgs d q B).toFinset.card < (Finset.range (cs.length + 1)).card := by
      have h1 : (allCfgs d q B).toFinset.card ≤ (allCfgs d q B).length := List.toFinset_card_le _
      simp only [Finset.card_range]
      omega
    obtain ⟨a, ha, b, hb, hab, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    -- put the two indices in order
    have key : ∀ i j : ℕ, i < j → j ≤ cs.length →
        normCfg d q (endOf c (cs.take i)) = normCfg d q (endOf c (cs.take j)) →
        ∃ cs', PPath d c cs' ∧ cs'.length < cs.length ∧ isGoalB q (endOf c cs') = true := by
      intro i j hij hj hnorm
      set u := endOf c (cs.take i) with hu
      set v := endOf c (cs.take j) with hv
      have hsim : Sim u v :=
        ((sim_normCfg (hinvAt i)).symm.trans (hnorm ▸ Sim.refl _)).trans (sim_normCfg (hinvAt j))
      have hpathv : PPath d v (cs.drop j) := hcs.drop j
      have hgoalv : isGoalB q (endOf v (cs.drop j)) = true := by
        rw [endOf_take_drop]
        exact hgoal
      obtain ⟨cs'', hpath'', hlen'', hsim''⟩ :=
        replay (q := q) (cs.drop j) u v (hinvAt i).ok (hinvAt j).ok hsim hpathv
      refine ⟨cs.take i ++ cs'', (hcs.take i).append (by rw [← hu]; exact hpath''), ?_, ?_⟩
      · rw [List.length_append, hlen'', List.length_drop, List.length_take]
        omega
      · rw [endOf_append, ← hu]
        exact isGoalB_of_sim hsim'' hgoalv
    have hba : a ≤ cs.length := by
      have := Finset.mem_range.1 ha
      omega
    have hbb : b ≤ cs.length := by
      have := Finset.mem_range.1 hb
      omega
    have hshort : ∃ cs', PPath d c cs' ∧ cs'.length < cs.length ∧
        isGoalB q (endOf c cs') = true := by
      rcases lt_or_gt_of_ne hab with h | h
      · exact key a b h hbb heq
      · exact key b a h hba heq.symm
    obtain ⟨cs', hcs', hlt, hgoal'⟩ := hshort
    exact ih cs'.length (by omega) cs' c le_rfl hinv hcs' hgoal'

/-! ### The decision procedure -/

/-- A configuration a short run reaches is found by the bounded breadth-first search. -/
theorem mem_bfs_of_ppath {d : DomDesc} {c : PConfig} {cs : List PConfig} (h : PPath d c cs) :
    ∀ n, cs.length ≤ n → endOf c cs ∈ bfs d c n := by
  induction cs generalizing c with
  | nil => exact fun n _ => mem_bfs_start d c n
  | cons x xs ih =>
    intro n hn
    match n with
    | 0 => simp at hn
    | m + 1 =>
      have hx : endOf x xs ∈ bfs d x m := ih h.2 m (by simpa using hn)
      -- a run from a successor stays inside the search from `c`
      have hsub : ∀ k, ∀ y ∈ bfs d x k, y ∈ bfs d c (k + 1) := by
        intro k
        induction k with
        | zero =>
          intro y hy
          rw [show bfs d x 0 = [x] from rfl, List.mem_singleton] at hy
          subst hy
          exact List.mem_append.2 (Or.inr (List.mem_flatMap.2
            ⟨c, mem_bfs_start d c 0, h.1⟩))
        | succ k ihk =>
          intro y hy
          rcases List.mem_append.1 hy with hy' | hy'
          · exact List.mem_append.2 (Or.inl (ihk y hy'))
          · obtain ⟨b, hb, hby⟩ := List.mem_flatMap.1 hy'
            exact List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨b, ihk b hb, hby⟩))
      exact hsub m _ hx

/-- **The bounded search as a decision procedure**, for any bound `B` on the number of tasks a
reachable configuration may have left. -/
def solvableB (d : DomDesc) (q : InstDesc) (B : ℕ) : Bool :=
  (bfs d (initConfig q) (cfgBound d q B)).any (isGoalB q)

/-- **The bounded search is correct** whenever the generic invariant with bound `B` holds
initially and is preserved by the search. -/
theorem solvableB_iff {d : DomDesc} {q : InstDesc} {B : ℕ} {P : PConfig → Prop}
    (hPI : ∀ {c : PConfig}, P c → CfgInv d q B c)
    (hinit : P (initConfig q))
    (hpres : ∀ {c c' : PConfig}, P c → PStep d c c' → P c') :
    solvableB d q B = true ↔ Solvable d q := by
  constructor
  · intro h
    obtain ⟨c, hc, hg⟩ := List.any_eq_true.1 h
    exact solvable_of_pReach (pReach_of_mem_bfs _ hc) hg
  · intro h
    obtain ⟨c, hr, hg⟩ := exists_pReach_of_solvable h
    obtain ⟨cs, hcs, hend⟩ := exists_ppath_of_pReach hr
    obtain ⟨cs', hcs', hlen, hg'⟩ :=
      exists_short_ppath hPI hpres cs.length cs _ le_rfl hinit hcs (by rw [hend]; exact hg)
    exact List.any_eq_true.2
      ⟨_, mem_bfs_of_ppath hcs' _ (le_trans hlen (length_allCfgs_le d q B)), hg'⟩

/-- **The decision procedure for regular domain descriptions.** -/
def regSolvableB (d : DomDesc) (q : InstDesc) : Bool := solvableB d q (bnd d q)

/-- **The decision procedure is correct.** -/
theorem regSolvableB_iff {d : DomDesc} {q : InstDesc} (hd : d.MethodsReg) :
    regSolvableB d q = true ↔ Solvable d q := by
  refine solvableB_iff (P := RegInv d q) (fun h => h.toCfgInv) (regInv_initConfig d q) ?_
  intro c c' hc hstep
  exact hc.step hd hstep

end Syn

end HTN
