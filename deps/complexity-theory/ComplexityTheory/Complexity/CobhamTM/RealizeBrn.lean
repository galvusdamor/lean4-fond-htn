import ComplexityTheory.Complexity.CobhamTM.Realize
/-!
# Realizing bounded recursion on notation

The program for `brnFn g h0 h1` uses five scratch stacks starting at `base`:
`X = base` (the bits of the recursion argument still to be processed, reversed),
`Suf = base + 1` (the suffix processed so far), `R = base + 2` (the value of the recursion on
that suffix), `R' = base + 3` (the next value) and `T = base + 4` (a temporary); the
sub-programs use the scratch stacks from `base + 5` on.
-/

namespace HTN.PTime.CobhamTM

open HTN.PTime

namespace Prog

theorem readsFirst_brn {g h0 h1 : Fn} {M : ℕ} (hg : ReadsFirst M g) (h0' : ReadsFirst (M + 2) h0)
    (h1' : ReadsFirst (M + 2) h1) : ReadsFirst (M + 1) (brnFn g h0 h1) := by
  have claim : ∀ (x : List Bool) (v : Args),
      brnAux g h0 h1 x v = brnAux g h0 h1 x (padArgs M v) := by
    intro x
    induction x with
    | nil => intro v; exact hg v
    | cons b x ih =>
      intro v
      have hb : ∀ w : Args, brnAux g h0 h1 (b :: x) w
          = (bif b then h1 else h0) (x :: brnAux g h0 h1 x w :: w) := fun _ => rfl
      rw [hb, hb, ← ih v]
      cases b
      · show h0 _ = h0 _
        rw [h0' (x :: brnAux g h0 h1 x v :: v), padArgs_cons, padArgs_cons]
      · show h1 _ = h1 _
        rw [h1' (x :: brnAux g h0 h1 x v :: v), padArgs_cons, padArgs_cons]
  intro args
  simp only [brnFn]
  rw [padArgs_getD_zero, padArgs_succ_tail]
  exact claim _ _

theorem argsOf_succ (M : ℕ) (inp : ℕ → ℕ) (S : Store) :
    argsOf (M + 1) inp S = S (inp 0) :: argsOf M (fun i => inp (i + 1)) S := by
  simp [argsOf, List.range_succ_eq_map]

theorem argSize_argsOf_le_of_getD {A : ℕ} {inp : ℕ → ℕ} {S : Store} {L : Args}
    (h : ∀ i < A, S (inp i) = L.getD i []) : argSize (argsOf A inp S) ≤ argSize L :=
  argSize_le_of fun x hx => by
    simp only [argsOf, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [h i hi]; exact length_getD_le_argSize L i

noncomputable section

/-- The inputs of the step functions: the suffix, the recursive value, then the parameters. -/
def brnInp (inpv : ℕ → ℕ) (base : ℕ) : ℕ → ℕ
  | 0 => base + 1
  | 1 => base + 2
  | i + 2 => inpv i

/-- One round of the recursion, for a bit `b` on top of `X`. -/
def brnB (Ph : (ℕ → ℕ) → ℕ → ℕ → Prog) (inpv : ℕ → ℕ) (base : ℕ) (b : Bool) : Prog :=
  seq (pop base) (seq (Ph (brnInp inpv base) (base + 3) (base + 5))
    (seq (clear (base + 2)) (seq (copy (base + 3) (base + 2) (base + 4))
      (seq (clear (base + 3)) (push (base + 1) b)))))

/-- The body of the main loop. -/
def brnBody (Ph0 Ph1 : (ℕ → ℕ) → ℕ → ℕ → Prog) (inpv : ℕ → ℕ) (base : ℕ) : Prog :=
  ifTop base skip (brnB Ph0 inpv base false) (brnB Ph1 inpv base true)

/-- The store with given contents of `X`, `Suf` and `R`. -/
def setXYR (S : Store) (base : ℕ) (z y r : List Bool) : Store :=
  Function.update (Function.update (Function.update S base z) (base + 1) y) (base + 2) r

theorem setXYR_apply (S : Store) (base : ℕ) (z y r : List Bool) (j : ℕ) :
    setXYR S base z y r j =
      if j = base then z else if j = base + 1 then y else if j = base + 2 then r else S j := by
  simp only [setXYR, Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem runs_brnB {h : Fn} (Rh : Realizer h) (inpv : ℕ → ℕ) (M base : ℕ) (hA : Rh.A ≤ M + 2)
    (hinp : ∀ i < M, inpv i < base) (S : Store) (hc : Clean base S) (b : Bool)
    (z y r : List Bool) :
    Runs (brnB Rh.P inpv base b) (setXYR S base (b :: z) y r)
      (setXYR S base z (b :: y) (h (y :: r :: argsOf M inpv S)))
      (Rh.time.eval (argSize (y :: r :: argsOf M inpv S)) + 2 * r.length +
        11 * (h (y :: r :: argsOf M inpv S)).length + 6) := by
  set v := argsOf M inpv S with hv
  set r' := h (y :: r :: v) with hr'
  set S₁ := setXYR S base z y r with hS₁
  have r1 : Runs (pop base) (setXYR S base (b :: z) y r) S₁ 1 := by
    refine (Runs.pop base _).of_eq ?_
    funext j
    simp only [hS₁, Function.update_apply, setXYR_apply]
    split_ifs <;> rfl
  have hinph : ∀ i < Rh.A, brnInp inpv base i < base + 3 := by
    intro i hi
    match i, hi with
    | 0, _ => simp [brnInp]
    | 1, _ => simp [brnInp]
    | i + 2, hi => simp only [brnInp]; have := hinp i (by omega); omega
  have hget : ∀ i < Rh.A, S₁ (brnInp inpv base i) = (y :: r :: v).getD i [] := by
    intro i hi
    match i, hi with
    | 0, _ => simp [brnInp, hS₁, setXYR_apply]
    | 1, _ => simp [brnInp, hS₁, setXYR_apply]
    | i + 2, hi =>
      have := hinp i (by omega)
      simp only [brnInp, hS₁, setXYR_apply, List.getD_cons_succ]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hv, getD_argsOf (by omega)]
  have r2 := Rh.spec (brnInp inpv base) (base + 3) (base + 5) S₁
    (fun i hi => by have := hinph i hi; omega) (by omega)
    (fun i hi => by have := hinph i hi; omega)
    (by simp only [hS₁, setXYR_apply]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact hc _ (by omega))
    (fun j hj => by
      simp only [hS₁, setXYR_apply]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hc _ (by omega))
  have hargs : h (argsOf Rh.A (brnInp inpv base) S₁) = r' :=
    (Rh.reads.congr fun i hi => by rw [getD_argsOf hi, hget i hi, getD_padArgs hi]).trans (Rh.reads _).symm
  have hsz : argSize (argsOf Rh.A (brnInp inpv base) S₁) ≤ argSize (y :: r :: v) :=
    argSize_argsOf_le_of_getD hget
  rw [hargs] at r2
  set S₂ := Function.update S₁ (base + 3) r' with hS₂
  have r3 := runs_clear (base + 2) S₂
  have e3 : S₂ (base + 2) = r := by simp [hS₂, hS₁, setXYR_apply]
  rw [e3] at r3
  set S₃ := Function.update S₂ (base + 2) [] with hS₃
  have r4 := runs_copy (show base + 3 ≠ base + 2 by omega) (show base + 3 ≠ base + 4 by omega)
    (show base + 2 ≠ base + 4 by omega) S₃
    (by simp only [hS₃, hS₂, hS₁, Function.update_apply, setXYR_apply]
        simp only [show base + 4 ≠ base + 2 by omega, show base + 4 ≠ base + 3 by omega,
          show base + 4 ≠ base by omega, show base + 4 ≠ base + 1 by omega, if_false]
        exact hc (base + 4) (by omega))
  have e4a : S₃ (base + 3) = r' := by simp [hS₃, hS₂]
  have e4b : S₃ (base + 2) = [] := by simp [hS₃]
  rw [e4a, e4b, List.append_nil] at r4
  set S₄ := Function.update S₃ (base + 2) r' with hS₄
  have r5 := runs_clear (base + 3) S₄
  have e5 : S₄ (base + 3) = r' := by simp [hS₄, e4a]
  rw [e5] at r5
  set S₅ := Function.update S₄ (base + 3) [] with hS₅
  have r6 := Runs.push (base + 1) b S₅
  have e6 : S₅ (base + 1) = y := by simp [hS₅, hS₄, hS₃, hS₂, hS₁, setXYR_apply]
  rw [e6] at r6
  refine ((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_).of_eq ?_
  · have := Polynomial.eval_mono_nat Rh.time hsz
    omega
  · funext j
    simp only [hS₅, hS₄, hS₃, hS₂, hS₁, Function.update_apply, setXYR_apply]
    split_ifs <;> first | rfl | omega | (subst_vars; exact (hc _ (by omega)).symm)

theorem runs_loop_inv {X : ℕ} {body : Prog} (Mk : List Bool → List Bool → Store)
    (hX : ∀ z y, Mk z y X = z) (K c : ℕ)
    (hstep : ∀ b z y, (b :: z).length + y.length ≤ K → Runs body (Mk (b :: z) y) (Mk z (b :: y)) c) :
    ∀ z y, z.length + y.length ≤ K →
      Runs (loop X body) (Mk z y) (Mk [] (z.reverse ++ y)) (z.length * (c + 1) + 1) := by
  intro z
  induction z with
  | nil => intro y _; exact ⟨1, by simp, by simpa using Eval.loopNil (p := body) (hX [] y)⟩
  | cons b z ih =>
    intro y hK
    obtain ⟨t₁, ht₁, e₁⟩ := hstep b z y hK
    obtain ⟨t₂, ht₂, e₂⟩ := ih (b :: y) (by simp at hK ⊢; omega)
    refine ⟨t₁ + t₂ + 1, ?_, ?_⟩
    · simp only [List.length_cons]; nlinarith
    · have := Eval.loopCons (by rw [hX]; simp) e₁ e₂
      simpa using this

theorem runs_brnBody {h0 h1 : Fn} (Rh0 : Realizer h0) (Rh1 : Realizer h1) (inpv : ℕ → ℕ)
    (M base : ℕ) (hA0 : Rh0.A ≤ M + 2) (hA1 : Rh1.A ≤ M + 2) (hinp : ∀ i < M, inpv i < base)
    (S : Store) (hc : Clean base S) (b : Bool) (z y r : List Bool) :
    Runs (brnBody Rh0.P Rh1.P inpv base) (setXYR S base (b :: z) y r)
      (setXYR S base z (b :: y) ((bif b then h1 else h0) (y :: r :: argsOf M inpv S)))
      (Rh0.time.eval (argSize (y :: r :: argsOf M inpv S)) +
        Rh1.time.eval (argSize (y :: r :: argsOf M inpv S)) + 2 * r.length +
        11 * ((bif b then h1 else h0) (y :: r :: argsOf M inpv S)).length + 7) := by
  have hX : setXYR S base (b :: z) y r base = b :: z := by simp [setXYR_apply]
  cases b
  · obtain ⟨t, ht, e⟩ := runs_brnB Rh0 inpv M base hA0 hinp S hc false z y r
    exact ⟨t + 1, by simp only [cond_false] at ht ⊢; omega, Eval.ifF hX e⟩
  · obtain ⟨t, ht, e⟩ := runs_brnB Rh1 inpv M base hA1 hinp S hc true z y r
    exact ⟨t + 1, by simp only [cond_true] at ht ⊢; omega, Eval.ifT hX e⟩

theorem brnInp_lt {inpv : ℕ → ℕ} {M base A : ℕ} (hA : A ≤ M + 2) (hinp : ∀ i < M, inpv i < base)
    {i : ℕ} (hi : i < A) : brnInp inpv base i < base + 3 := by
  match i, hi with
  | 0, _ => simp [brnInp]
  | 1, _ => simp [brnInp]
  | i + 2, hi => simp only [brnInp]; have := hinp i (by omega); omega

theorem length_brnAux_le {g h0 h1 : Fn} {pb : Polynomial ℕ}
    (hpb : ∀ args, (brnFn g h0 h1 args).length ≤ pb.eval (argSize args)) (y : List Bool)
    (v : Args) : (brnAux g h0 h1 y v).length ≤ pb.eval (argSize (y :: v)) := hpb (y :: v)

/-- The program for bounded recursion on notation. -/
def brnProg (Pg Ph0 Ph1 : (ℕ → ℕ) → ℕ → ℕ → Prog) (inp : ℕ → ℕ) (out base : ℕ) : Prog :=
  seq (copy (inp 0) (base + 3) (base + 4)) (seq (moveRev (base + 3) base)
    (seq (Pg (fun i => inp (i + 1)) (base + 2) (base + 5))
    (seq (loop base (brnBody Ph0 Ph1 (fun i => inp (i + 1)) base))
    (seq (copy (base + 2) out (base + 4)) (seq (clear (base + 2)) (clear (base + 1)))))))

theorem brnProg_bound {g h0 h1 : Fn} (Rg : Realizer g) (Rh0 : Realizer h0) (Rh1 : Realizer h1)
    (M : ℕ) (hg : Rg.A ≤ M) (hA0 : Rh0.A ≤ M + 2) (hA1 : Rh1.A ≤ M + 2) (inp : ℕ → ℕ)
    (out base : ℕ) (hinp : ∀ i < M + 1, inp i < base) (hout : out < base) :
    maxStack (brnProg Rg.P Rh0.P Rh1.P inp out base) ≤ base + (5 + max Rg.W (max Rh0.W Rh1.W)) := by
  have hinpv : ∀ i < M, inp (i + 1) < base := fun i hi => hinp (i + 1) (by omega)
  have h0 := hinp 0 (by omega)
  have bg := Rg.bound (fun i => inp (i + 1)) (base + 2) (base + 5)
    (fun i hi => by have := hinpv i (by omega); dsimp only; omega) (by omega)
  have b0 := Rh0.bound (brnInp (fun i => inp (i + 1)) base) (base + 3) (base + 5)
    (fun i hi => by have := brnInp_lt hA0 hinpv hi; omega) (by omega)
  have b1 := Rh1.bound (brnInp (fun i => inp (i + 1)) base) (base + 3) (base + 5)
    (fun i hi => by have := brnInp_lt hA1 hinpv hi; omega) (by omega)
  have w1 := le_max_left Rg.W (max Rh0.W Rh1.W)
  have w2 := (le_max_left Rh0.W Rh1.W).trans (le_max_right Rg.W (max Rh0.W Rh1.W))
  have w3 := (le_max_right Rh0.W Rh1.W).trans (le_max_right Rg.W (max Rh0.W Rh1.W))
  generalize max Rg.W (max Rh0.W Rh1.W) = W at w1 w2 w3
  simp only [brnProg, maxStack, brnBody, brnB, maxStack_copy, maxStack_moveRev, maxStack_clear,
    max_le_iff]
  and_intros <;> omega

theorem brnProg_spec {g h0 h1 : Fn} (Rg : Realizer g) (Rh0 : Realizer h0) (Rh1 : Realizer h1)
    (pb : Polynomial ℕ) (hpb : ∀ args, (brnFn g h0 h1 args).length ≤ pb.eval (argSize args))
    (M : ℕ) (hg : Rg.A ≤ M) (hA0 : Rh0.A ≤ M + 2) (hA1 : Rh1.A ≤ M + 2) (inp : ℕ → ℕ)
    (out base : ℕ) (S : Store) (hinp : ∀ i < M + 1, inp i < base) (hout : out < base)
    (hS : S out = []) (hc : Clean base S) :
    Runs (brnProg Rg.P Rh0.P Rh1.P inp out base) S
      (Function.update S out (brnFn g h0 h1 (argsOf (M + 1) inp S)))
      ((Rg.time + Polynomial.X * (Rh0.time.comp (Polynomial.X + pb) +
        Rh1.time.comp (Polynomial.X + pb) + 13 * pb + 8) + 11 * pb + 15 * Polynomial.X + 8).eval
        (argSize (argsOf (M + 1) inp S))) := by
  have hinpv : ∀ i < M, inp (i + 1) < base := fun i hi => hinp (i + 1) (by omega)
  have hi0 := hinp 0 (by omega)
  have hb0 : S base = [] := hc _ (by omega)
  have hb1 : S (base + 1) = [] := hc _ (by omega)
  have hb2 : S (base + 2) = [] := hc _ (by omega)
  have hb3 : S (base + 3) = [] := hc _ (by omega)
  have hb4 : S (base + 4) = [] := hc _ (by omega)
  rw [argsOf_succ M inp S]
  set x := S (inp 0) with hx
  set v := argsOf M (fun i => inp (i + 1)) S with hv
  show Runs _ S (Function.update S out (brnAux g h0 h1 x v)) _
  set n := argSize (x :: v) with hn
  have hxn : x.length ≤ n := by rw [hn, argSize_cons]; exact le_max_left _ _
  have hvn : argSize v ≤ n := by rw [hn, argSize_cons]; exact le_max_right _ _
  have hRn : ∀ y : List Bool, y.length ≤ n → (brnAux g h0 h1 y v).length ≤ pb.eval n :=
    fun y hy => (length_brnAux_le hpb y v).trans
      (Polynomial.eval_mono_nat _ (by rw [argSize_cons]; omega))
  -- copy the recursion argument to `R'`
  have c1 := runs_copy (show inp 0 ≠ base + 3 by omega) (show inp 0 ≠ base + 4 by omega)
    (show base + 3 ≠ base + 4 by omega) S hb4
  rw [hb3, List.append_nil, ← hx] at c1
  set S₁ := Function.update S (base + 3) x with hS₁
  -- reverse it onto `X`
  have c2 := runs_moveRev (show base + 3 ≠ base by omega) S₁
  have e2a : S₁ (base + 3) = x := by rw [hS₁, update_same']
  rw [e2a] at c2
  have e2 : Function.update (Function.update S₁ (base + 3) []) base (x.reverse ++ S₁ base) =
      setXYR S base x.reverse [] [] := by
    funext j
    simp only [hS₁, Function.update_apply, setXYR_apply]
    split_ifs <;> first | rfl | omega | (subst_vars; simp [hb0, hb1, hb2, hb3])
  rw [e2] at c2
  -- the base case
  set S₂ := setXYR S base x.reverse [] [] with hS₂
  have eargs : argsOf Rg.A (fun i => inp (i + 1)) S₂ = argsOf Rg.A (fun i => inp (i + 1)) S :=
    argsOf_congr fun i hi => by
      have := hinpv i (by omega)
      simp only [hS₂, setXYR_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have c3 := Rg.spec (fun i => inp (i + 1)) (base + 2) (base + 5) S₂
    (fun i hi => by have := hinpv i (by omega); dsimp only; omega) (by omega)
    (fun i hi => by have := hinpv i (by omega); dsimp only; omega)
    (by simp [hS₂, setXYR_apply])
    (fun j hj => by
      simp only [hS₂, setXYR_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact hc _ (by omega))
  have hg3 : g (argsOf Rg.A (fun i => inp (i + 1)) S₂) = brnAux g h0 h1 [] v := by
    rw [eargs, ← readsFirst_argsOf Rg.reads hg]; rfl
  have hsz3 : argSize (argsOf Rg.A (fun i => inp (i + 1)) S₂) ≤ n := by
    rw [eargs]; exact (argSize_argsOf_mono hg _ S).trans hvn
  rw [hg3] at c3
  set Mk : List Bool → List Bool → Store := fun z y => setXYR S base z y (brnAux g h0 h1 y v)
    with hMk
  have e3 : Function.update S₂ (base + 2) (brnAux g h0 h1 [] v) = Mk x.reverse [] := by
    simp only [hS₂, hMk, setXYR, Function.update_idem]
  rw [e3] at c3
  -- the main loop
  set c := Rh0.time.eval (n + pb.eval n) + Rh1.time.eval (n + pb.eval n) + 13 * pb.eval n + 7
    with hc_def
  have c4 := runs_loop_inv (X := base) (body := brnBody Rh0.P Rh1.P (fun i => inp (i + 1)) base)
    Mk (fun z y => by simp [hMk, setXYR_apply]) x.length c (fun b z y hK => by
      have hy : (b :: y).length ≤ n := by simp at hK ⊢; omega
      have hr := hRn y (by simp at hy; omega)
      have hr' : ((bif b then h1 else h0) (y :: brnAux g h0 h1 y v :: v)).length ≤ pb.eval n :=
        hRn (b :: y) hy
      have hsz : argSize (y :: brnAux g h0 h1 y v :: v) ≤ n + pb.eval n := by
        rw [argSize_cons, argSize_cons]; simp at hy; omega
      have t0 := Polynomial.eval_mono_nat Rh0.time hsz
      have t1 := Polynomial.eval_mono_nat Rh1.time hsz
      refine ((runs_brnBody Rh0 Rh1 (fun i => inp (i + 1)) M base hA0 hA1 hinpv S hc b z y
        (brnAux g h0 h1 y v)).mono ?_).of_eq ?_
      · rw [← hv]; omega
      · rw [← hv]; rfl) x.reverse [] (by simp)
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at c4
  -- copy the result out and clean up
  set R := brnAux g h0 h1 x v with hR
  have c5 := runs_copy (show base + 2 ≠ out by omega) (show base + 2 ≠ base + 4 by omega)
    (show out ≠ base + 4 by omega) (Mk [] x) (by simp [hMk, setXYR_apply, hb4])
  have e5a : Mk [] x (base + 2) = R := by simp [hMk, setXYR_apply, hR]
  have e5b : Mk [] x out = [] := by
    simp only [hMk, setXYR_apply]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hS]
  rw [e5a, e5b, List.append_nil] at c5
  have c6 := runs_clear (base + 2) (Function.update (Mk [] x) out R)
  rw [update_ne' _ (by omega), e5a] at c6
  have c7 := runs_clear (base + 1) (Function.update (Function.update (Mk [] x) out R) (base + 2) [])
  have e7 : Function.update (Function.update (Mk [] x) out R) (base + 2) [] (base + 1) = x := by
    rw [update_ne' _ (by omega), update_ne' _ (by omega)]; simp [hMk, setXYR_apply]
  rw [e7] at c7
  refine ((c1.seq (c2.seq (c3.seq (c4.seq (c5.seq (c6.seq c7)))))).mono ?_).of_eq ?_
  · have tg := Polynomial.eval_mono_nat Rg.time hsz3
    have hR' : R.length ≤ pb.eval n := hRn x hxn
    have hmul : x.length * (c + 1) ≤ n * (Rh0.time.eval (n + pb.eval n) +
        Rh1.time.eval (n + pb.eval n) + 13 * pb.eval n + 8) :=
      (Nat.mul_le_mul_right _ hxn).trans (le_of_eq (by rw [hc_def]))
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    clear_value c R Mk S₂ S₁ n v x
    omega
  · funext j
    simp only [hMk, Function.update_apply, setXYR_apply]
    split_ifs <;> first | rfl | omega | (subst_vars; simp [hb0, hb1, hb2])

/-- Bounded recursion on notation, given a polynomial bound on the length of its values. -/
def realizer_brn {g h0 h1 : Fn} (Rg : Realizer g) (Rh0 : Realizer h0) (Rh1 : Realizer h1)
    (pb : Polynomial ℕ) (hpb : ∀ args, (brnFn g h0 h1 args).length ≤ pb.eval (argSize args)) :
    Realizer (brnFn g h0 h1) where
  A := max Rg.A (max Rh0.A Rh1.A) + 1
  P := brnProg Rg.P Rh0.P Rh1.P
  W := 5 + max Rg.W (max Rh0.W Rh1.W)
  time := Rg.time + Polynomial.X * (Rh0.time.comp (Polynomial.X + pb) +
    Rh1.time.comp (Polynomial.X + pb) + 13 * pb + 8) + 11 * pb + 15 * Polynomial.X + 8
  reads := readsFirst_brn (Rg.reads.mono (le_max_left _ _))
    (Rh0.reads.mono (by have := le_max_left Rh0.A Rh1.A; have := le_max_right Rg.A (max Rh0.A Rh1.A); omega))
    (Rh1.reads.mono (by have := le_max_right Rh0.A Rh1.A; have := le_max_right Rg.A (max Rh0.A Rh1.A); omega))
  bound inp out base hinp hout := brnProg_bound Rg Rh0 Rh1 _ (le_max_left _ _)
    (by have := le_max_left Rh0.A Rh1.A; have := le_max_right Rg.A (max Rh0.A Rh1.A); omega)
    (by have := le_max_right Rh0.A Rh1.A; have := le_max_right Rg.A (max Rh0.A Rh1.A); omega)
    inp out base hinp hout
  spec inp out base S hinp hout _ hS hc := brnProg_spec Rg Rh0 Rh1 pb hpb _ (le_max_left _ _)
    (by have := le_max_left Rh0.A Rh1.A; have := le_max_right Rg.A (max Rh0.A Rh1.A); omega)
    (by have := le_max_right Rh0.A Rh1.A; have := le_max_right Rg.A (max Rh0.A Rh1.A); omega)
    inp out base S hinp hout hS hc

end

end Prog

end HTN.PTime.CobhamTM
