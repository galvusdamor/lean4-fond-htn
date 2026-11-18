import ComplexityTheory.Undec.Sim.Forward
/-!
# From a halting run of the two-stack machine to a halting run of the Turing machine

The simulating machine is *deterministic* in the sense that in every control state exactly one
transition matches the top of the stack it reads.  Rather than proving that, the converse
direction is obtained by a backwards induction along the accepting run: the predicate `Claim`
below says "if this configuration is a legitimate simulation state, then the simulated machine
halts from the corresponding configuration", it holds trivially at the accepting configuration,
and it is preserved by taking a step backwards.
-/

namespace HTN

namespace Undec

namespace Sim

open Turing

open scoped Classical

variable {Γ : Type*} [Inhabited Γ] [Fintype Γ] {Λ : Type*} [Inhabited Λ]
variable {N : TM0.Machine Γ Λ} {S : Finset Λ} {q0 : Λ}

/-! ### Reading a stack -/

omit [Inhabited Γ] in
theorem encL_ne_nil (L : List Γ) : encL L ≠ [] := by
  cases L <;> simp [encL]

omit [Inhabited Γ] in
theorem encL_eq_zero_cons {R : List Γ} {rest : List ℕ} (h : encL R = 0 :: rest) :
    R = [] ∧ rest = [] := by
  cases R with
  | nil =>
      simp only [encL, List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, h.symm⟩
  | cons d R =>
      simp only [encL_cons, List.cons.injEq] at h
      exact absurd h.1 (symCode_ne_zero d)

omit [Inhabited Γ] in
theorem encL_eq_symCode_cons {R : List Γ} {c : Γ} {rest : List ℕ}
    (h : encL R = symCode c :: rest) : ∃ R', R = c :: R' ∧ rest = encL R' := by
  cases R with
  | nil =>
      simp only [encL, List.map_nil, List.nil_append, List.cons.injEq] at h
      exact absurd h.1.symm (symCode_ne_zero c)
  | cons d R =>
      simp only [encL_cons, List.cons.injEq] at h
      exact ⟨R, by rw [symCode_injective h.1], h.2.symm⟩

/-! ### Steps of the simulated machine -/

omit [Fintype Γ] in
theorem tm0_step_none {q : Λ} {a : Γ} (h : N q a = none) (L R : List Γ) :
    TM0.step N ⟨q, tapeOf a L R⟩ = none := by
  simp [TM0.step, tapeOf, h]

omit [Fintype Γ] in
theorem tm0_step_write {q q' : Λ} {a b : Γ} (h : N q a = some (q', TM0.Stmt.write b))
    (L R : List Γ) : TM0.step N ⟨q, tapeOf a L R⟩ = some ⟨q', tapeOf b L R⟩ := by
  simp only [TM0.step, tapeOf, h, Option.map_some]
  exact congrArg some (congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_write b a L R))

omit [Fintype Γ] in
theorem tm0_step_right {q q' : Λ} {a : Γ} (h : N q a = some (q', TM0.Stmt.move Dir.right))
    (L R : List Γ) :
    TM0.step N ⟨q, tapeOf a L R⟩ = some ⟨q', tapeOf R.headI (a :: L) R.tail⟩ := by
  simp only [TM0.step, tapeOf, h, Option.map_some]
  exact congrArg some (congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_move_right a L R))

omit [Fintype Γ] in
theorem tm0_step_left {q q' : Λ} {a : Γ} (h : N q a = some (q', TM0.Stmt.move Dir.left))
    (L R : List Γ) :
    TM0.step N ⟨q, tapeOf a L R⟩ = some ⟨q', tapeOf L.headI L.tail (a :: R)⟩ := by
  simp only [TM0.step, tapeOf, h, Option.map_some]
  exact congrArg some (congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_move_left a L R))

omit [Fintype Γ] in
theorem dom_of_none {c : TM0.Cfg Γ Λ} (h : TM0.step N c = none) :
    (Turing.eval (TM0.step N) c).Dom :=
  Part.dom_iff_mem.2 ⟨c, Turing.mem_eval.2 ⟨Relation.ReflTransGen.refl, h⟩⟩

omit [Fintype Γ] in
theorem dom_of_step {c c' : TM0.Cfg Γ Λ} (h : TM0.step N c = some c')
    (hd : (Turing.eval (TM0.step N) c').Dom) : (Turing.eval (TM0.step N) c).Dom := by
  rw [Turing.reaches_eval (Relation.ReflTransGen.single (b := c') h)]
  exact hd

/-! ### The invariant -/

/-- The claim carried backwards along an accepting run: if the configuration is a legitimate
simulation state, then the simulated machine halts from the corresponding configuration. -/
def Claim (N : TM0.Machine Γ Λ) (S : Finset Λ) (q0 : Λ) (c : Cfg) : Prop :=
  (∀ q ∈ S, ∀ (a : Γ) (L R : List Γ), c.st = stCode S (St.run q a) → c.s1 = encL L →
      c.s2 = encL R → (Turing.eval (TM0.step N) ⟨q, tapeOf a L R⟩).Dom) ∧
  (∀ q ∈ S, ∀ (y b : Γ) (L R : List Γ), c.st = stCode S (St.pl q y b) → c.s1 = encL L →
      c.s2 = encL R → (Turing.eval (TM0.step N) ⟨q, tapeOf y (b :: L) R⟩).Dom) ∧
  (∀ q ∈ S, ∀ (y b : Γ) (L R : List Γ), c.st = stCode S (St.pr q y b) → c.s1 = encL L →
      c.s2 = encL R → (Turing.eval (TM0.step N) ⟨q, tapeOf y L (b :: R)⟩).Dom) ∧
  (∀ L R : List Γ, c.st = 0 → c.s1 = encL L → c.s2 = encL R →
      (Turing.eval (TM0.step N) ⟨q0, tapeOf R.headI L R.tail⟩).Dom)

theorem claim_acc : Claim N S q0 ⟨3, [], []⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _ L _ _ hs1 _; exact absurd hs1.symm (encL_ne_nil L)
  · intro _ _ _ _ L _ _ hs1 _; exact absurd hs1.symm (encL_ne_nil L)
  · intro _ _ _ _ L _ _ hs1 _; exact absurd hs1.symm (encL_ne_nil L)
  · intro L _ _ hs1 _; exact absurd hs1.symm (encL_ne_nil L)

/-- Reading off the transitions available in a given control state. -/
theorem step_dest {s : St Γ Λ} (hs : StOk S s) {c c' : Cfg} (hc : c.st = stCode S s)
    (h : (simTSM N S q0).Step c c') :
    ∃ t ∈ trsOf N S q0 s,
      ((t.stk = false ∧ ∃ rest, c.s1 = t.pop :: rest ∧ c' = ⟨t.tgt, t.push ++ rest, c.s2⟩) ∨
        (t.stk = true ∧ ∃ rest, c.s2 = t.pop :: rest ∧ c' = ⟨t.tgt, c.s1, t.push ++ rest⟩)) := by
  obtain ⟨t, ht, hsrc, hcase⟩ := h
  exact ⟨t, mem_trsOf_of_mem_trans hs ht (hsrc.symm.trans hc), hcase⟩

/-- **The invariant is preserved by a step backwards.** -/
theorem claim_of_step
    (hcl : ∀ {q : Λ} {a : Γ} {q' : Λ} {st : TM0.Stmt Γ}, (q', st) ∈ N q a → q ∈ S → q' ∈ S)
    (hq0 : q0 ∈ S) {c c' : Cfg} (hstep : (simTSM N S q0).Step c c')
    (hc' : Claim N S q0 c') : Claim N S q0 c := by
  obtain ⟨ih1, ih2, ih3, -⟩ := hc'
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- a `run` state
    intro q hq a L R hst hs1 hs2
    match hN : N q a with
    | none => exact dom_of_none (tm0_step_none hN L R)
    | some (q', TM0.Stmt.write b) =>
        have hq' : q' ∈ S := hcl (by rw [hN]; rfl) hq
        obtain ⟨t, ht, hcase⟩ := step_dest (s := St.run q a) hq hst hstep
        rw [trsOf_run_write (q0 := q0) hN] at ht
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 ht
        rcases hcase with ⟨-, rest, hpop, rfl⟩ | ⟨hstk, -⟩
        · refine dom_of_step (tm0_step_write hN L R) (ih1 q' hq' b L R rfl ?_ hs2)
          show [x] ++ rest = encL L
          rw [List.singleton_append, ← hpop, hs1]
        · exact absurd hstk (by simp)
    | some (q', TM0.Stmt.move Dir.right) =>
        have hq' : q' ∈ S := hcl (by rw [hN]; rfl) hq
        obtain ⟨t, ht, hcase⟩ := step_dest (s := St.run q a) hq hst hstep
        rw [trsOf_run_right (q0 := q0) hN] at ht
        refine dom_of_step (tm0_step_right hN L R) ?_
        simp only [List.mem_cons, List.mem_map] at ht
        rcases ht with rfl | ⟨c₀, -, rfl⟩
        · rcases hcase with ⟨hstk, -⟩ | ⟨-, rest, hpop, rfl⟩
          · exact absurd hstk (by simp)
          · rw [hs2] at hpop
            obtain ⟨hR, hrest⟩ := encL_eq_zero_cons hpop
            subst hR; subst hrest
            exact ih2 q' hq' default a L [] rfl hs1 rfl
        · rcases hcase with ⟨hstk, -⟩ | ⟨-, rest, hpop, rfl⟩
          · exact absurd hstk (by simp)
          · rw [hs2] at hpop
            obtain ⟨R', hR, hrest⟩ := encL_eq_symCode_cons hpop
            subst hR; subst hrest
            exact ih2 q' hq' c₀ a L R' rfl hs1 rfl
    | some (q', TM0.Stmt.move Dir.left) =>
        have hq' : q' ∈ S := hcl (by rw [hN]; rfl) hq
        obtain ⟨t, ht, hcase⟩ := step_dest (s := St.run q a) hq hst hstep
        rw [trsOf_run_left (q0 := q0) hN] at ht
        refine dom_of_step (tm0_step_left hN L R) ?_
        simp only [List.mem_cons, List.mem_map] at ht
        rcases ht with rfl | ⟨c₀, -, rfl⟩
        · rcases hcase with ⟨-, rest, hpop, rfl⟩ | ⟨hstk, -⟩
          · rw [hs1] at hpop
            obtain ⟨hL, hrest⟩ := encL_eq_zero_cons hpop
            subst hL; subst hrest
            exact ih3 q' hq' default a [] R rfl rfl hs2
          · exact absurd hstk (by simp)
        · rcases hcase with ⟨-, rest, hpop, rfl⟩ | ⟨hstk, -⟩
          · rw [hs1] at hpop
            obtain ⟨L', hL, hrest⟩ := encL_eq_symCode_cons hpop
            subst hL; subst hrest
            exact ih3 q' hq' c₀ a L' R rfl rfl hs2
          · exact absurd hstk (by simp)
  · -- a `pl` state
    intro q hq y b L R hst hs1 hs2
    obtain ⟨t, ht, hcase⟩ := step_dest (s := St.pl q y b) hq hst hstep
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ht
    rcases hcase with ⟨-, rest, hpop, rfl⟩ | ⟨hstk, -⟩
    · refine ih1 q hq y (b :: L) R rfl ?_ hs2
      show [symCode b, x] ++ rest = encL (b :: L)
      rw [encL_cons, ← hs1, hpop]
      rfl
    · exact absurd hstk (by simp)
  · -- a `pr` state
    intro q hq y b L R hst hs1 hs2
    obtain ⟨t, ht, hcase⟩ := step_dest (s := St.pr q y b) hq hst hstep
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ht
    rcases hcase with ⟨hstk, -⟩ | ⟨-, rest, hpop, rfl⟩
    · exact absurd hstk (by simp)
    · refine ih1 q hq y L (b :: R) rfl hs1 ?_
      show [symCode b, x] ++ rest = encL (b :: R)
      rw [encL_cons, ← hs2, hpop]
      rfl
  · -- the initial state
    intro L R hst hs1 hs2
    obtain ⟨t, ht, hcase⟩ := step_dest (s := St.start (Γ := Γ) (Λ := Λ)) trivial hst hstep
    simp only [trsOf, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨c₀, -, rfl⟩
    · rcases hcase with ⟨hstk, -⟩ | ⟨-, rest, hpop, rfl⟩
      · exact absurd hstk (by simp)
      · rw [hs2] at hpop
        obtain ⟨hR, hrest⟩ := encL_eq_zero_cons hpop
        subst hR; subst hrest
        exact ih1 q0 hq0 default L [] rfl hs1 rfl
    · rcases hcase with ⟨hstk, -⟩ | ⟨-, rest, hpop, rfl⟩
      · exact absurd hstk (by simp)
      · rw [hs2] at hpop
        obtain ⟨R', hR, hrest⟩ := encL_eq_symCode_cons hpop
        subst hR; subst hrest
        exact ih1 q0 hq0 c₀ L R' rfl hs1 rfl

/-- **If the two-stack machine halts, the Turing machine halts.** -/
theorem dom_of_halts
    (hcl : ∀ {q : Λ} {a : Γ} {q' : Λ} {st : TM0.Stmt Γ}, (q', st) ∈ N q a → q ∈ S → q' ∈ S)
    (hq0 : q0 ∈ S) (l : List Γ)
    (h : (simTSM N S q0).Halts (encL ([] : List Γ)) (encL l)) :
    (Turing.eval (TM0.step N) ⟨q0, Tape.mk₁ l⟩).Dom := by
  have hclaim : ∀ {c : Cfg}, (simTSM N S q0).Reaches c ⟨3, [], []⟩ → Claim N S q0 c := by
    intro c hc
    induction hc using Relation.ReflTransGen.head_induction_on with
    | refl => exact claim_acc
    | head hstep _ ih => exact claim_of_step hcl hq0 hstep ih
  have := (hclaim h).2.2.2 [] l rfl rfl rfl
  rwa [← tapeOf_mk₁] at this

end Sim

end Undec

end HTN
