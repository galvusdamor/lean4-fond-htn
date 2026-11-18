import ComplexityTheory.Undec.Sim.Step
/-!
# From a halting run of the Turing machine to a halting run of the two-stack machine

If the `TM0` machine `N` halts, started in a control state listed in `S`, then the simulating
two-stack machine reaches its accepting state with both stacks empty.
-/

namespace HTN

namespace Undec

namespace Sim

open Turing

open scoped Classical

variable {Γ : Type*} [Inhabited Γ] [Fintype Γ] {Λ : Type*} [Inhabited Λ]
variable {N : TM0.Machine Γ Λ} {S : Finset Λ} {q0 : Λ}

/-! ### One step of the simulation -/

/-- A transition that pops a symbol off the first stack and pushes it straight back only
changes the control state. -/
theorem step_id_left {s : St Γ Λ} (hs : StOk S s) (tgt : ℕ)
    (ht : ∀ x ∈ allSyms Γ, (⟨stCode S s, false, x, [x], tgt⟩ : Tr) ∈ trsOf N S q0 s)
    (L : List Γ) (s2 : List ℕ) :
    (simTSM N S q0).Step ⟨stCode S s, encL L, s2⟩ ⟨tgt, encL L, s2⟩ := by
  cases L with
  | nil =>
      have := step_of_left (N := N) (q0 := q0) hs (ht 0 zero_mem_allSyms) rfl [] s2
      simpa [encL_nil] using this
  | cons c L =>
      have := step_of_left (N := N) (q0 := q0) hs (ht _ (symCode_mem_allSyms c)) rfl (encL L) s2
      simpa [encL_cons] using this

theorem step_run_halt {q : Λ} {a : Γ} (hq : q ∈ S) (h : N q a = none) (L : List Γ)
    (s2 : List ℕ) :
    (simTSM N S q0).Step ⟨stCode S (St.run q a), encL L, s2⟩ ⟨1, encL L, s2⟩ := by
  refine step_id_left (N := N) (q0 := q0) (s := St.run q a) hq 1 (fun x hx => ?_) L s2
  rw [trsOf_run_none (q0 := q0) h]
  exact List.mem_map_of_mem hx

theorem step_run_write {q q' : Λ} {a b : Γ} (hq : q ∈ S)
    (h : N q a = some (q', TM0.Stmt.write b)) (L : List Γ) (s2 : List ℕ) :
    (simTSM N S q0).Step ⟨stCode S (St.run q a), encL L, s2⟩
      ⟨stCode S (St.run q' b), encL L, s2⟩ := by
  refine step_id_left (N := N) (q0 := q0) (s := St.run q a) hq _ (fun x hx => ?_) L s2
  rw [trsOf_run_write (q0 := q0) h]
  exact List.mem_map_of_mem hx

theorem step_run_right {q q' : Λ} {a : Γ} (hq : q ∈ S)
    (h : N q a = some (q', TM0.Stmt.move Dir.right)) (L R : List Γ) :
    (simTSM N S q0).Step ⟨stCode S (St.run q a), encL L, encL R⟩
      ⟨stCode S (St.pl q' R.headI a), encL L, encL R.tail⟩ := by
  cases R with
  | nil =>
      have ht : (⟨stCode S (St.run q a), true, 0, [0], stCode S (St.pl q' default a)⟩ : Tr) ∈
          trsOf N S q0 (St.run q a) := by
        rw [trsOf_run_right (q0 := q0) h]; exact List.mem_cons_self ..
      have := step_of_right (N := N) (q0 := q0) (s := St.run q a) hq ht rfl (encL L) []
      simpa [encL_nil] using this
  | cons c R =>
      have ht : (⟨stCode S (St.run q a), true, symCode c, [], stCode S (St.pl q' c a)⟩ : Tr) ∈
          trsOf N S q0 (St.run q a) := by
        rw [trsOf_run_right (q0 := q0) h]
        exact List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_symList c))
      have := step_of_right (N := N) (q0 := q0) (s := St.run q a) hq ht rfl (encL L) (encL R)
      simpa [encL_cons] using this

theorem step_run_left {q q' : Λ} {a : Γ} (hq : q ∈ S)
    (h : N q a = some (q', TM0.Stmt.move Dir.left)) (L R : List Γ) :
    (simTSM N S q0).Step ⟨stCode S (St.run q a), encL L, encL R⟩
      ⟨stCode S (St.pr q' L.headI a), encL L.tail, encL R⟩ := by
  cases L with
  | nil =>
      have ht : (⟨stCode S (St.run q a), false, 0, [0], stCode S (St.pr q' default a)⟩ : Tr) ∈
          trsOf N S q0 (St.run q a) := by
        rw [trsOf_run_left (q0 := q0) h]; exact List.mem_cons_self ..
      have := step_of_left (N := N) (q0 := q0) (s := St.run q a) hq ht rfl [] (encL R)
      simpa [encL_nil] using this
  | cons c L =>
      have ht : (⟨stCode S (St.run q a), false, symCode c, [], stCode S (St.pr q' c a)⟩ : Tr) ∈
          trsOf N S q0 (St.run q a) := by
        rw [trsOf_run_left (q0 := q0) h]
        exact List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_symList c))
      have := step_of_left (N := N) (q0 := q0) (s := St.run q a) hq ht rfl (encL L) (encL R)
      simpa [encL_cons] using this

theorem step_pl {q : Λ} {y b : Γ} (hq : q ∈ S) (L : List Γ) (s2 : List ℕ) :
    (simTSM N S q0).Step ⟨stCode S (St.pl q y b), encL L, s2⟩
      ⟨stCode S (St.run q y), encL (b :: L), s2⟩ := by
  have ht : ∀ x ∈ allSyms Γ,
      (⟨stCode S (St.pl q y b), false, x, [symCode b, x], stCode S (St.run q y)⟩ : Tr) ∈
        trsOf N S q0 (St.pl q y b) := fun x hx => List.mem_map_of_mem hx
  cases L with
  | nil =>
      have := step_of_left (N := N) (q0 := q0) (s := St.pl q y b) hq (ht 0 zero_mem_allSyms)
        rfl [] s2
      simpa [encL_nil, encL_cons] using this
  | cons c L =>
      have := step_of_left (N := N) (q0 := q0) (s := St.pl q y b) hq
        (ht _ (symCode_mem_allSyms c)) rfl (encL L) s2
      simpa [encL_cons] using this

theorem step_pr {q : Λ} {y b : Γ} (hq : q ∈ S) (s1 : List ℕ) (R : List Γ) :
    (simTSM N S q0).Step ⟨stCode S (St.pr q y b), s1, encL R⟩
      ⟨stCode S (St.run q y), s1, encL (b :: R)⟩ := by
  have ht : ∀ x ∈ allSyms Γ,
      (⟨stCode S (St.pr q y b), true, x, [symCode b, x], stCode S (St.run q y)⟩ : Tr) ∈
        trsOf N S q0 (St.pr q y b) := fun x hx => List.mem_map_of_mem hx
  cases R with
  | nil =>
      have := step_of_right (N := N) (q0 := q0) (s := St.pr q y b) hq (ht 0 zero_mem_allSyms)
        rfl s1 []
      simpa [encL_nil, encL_cons] using this
  | cons c R =>
      have := step_of_right (N := N) (q0 := q0) (s := St.pr q y b) hq
        (ht _ (symCode_mem_allSyms c)) rfl s1 (encL R)
      simpa [encL_cons] using this

/-! ### The initial state -/

theorem start_reaches (l : List Γ) :
    (simTSM N S q0).Reaches ⟨0, encL ([] : List Γ), encL l⟩
      ⟨stCode S (St.run q0 l.headI), encL ([] : List Γ), encL l.tail⟩ := by
  refine Relation.ReflTransGen.single ?_
  cases l with
  | nil =>
      have ht : (⟨0, true, 0, [0], stCode S (St.run (Γ := Γ) q0 default)⟩ : Tr) ∈
          trsOf N S q0 (St.start (Γ := Γ) (Λ := Λ)) := List.mem_cons_self ..
      have := step_of_right (N := N) (q0 := q0) (s := St.start (Γ := Γ) (Λ := Λ)) trivial ht rfl
        (encL ([] : List Γ)) []
      simpa [encL_nil] using this
  | cons c l =>
      have ht : (⟨0, true, symCode c, [], stCode S (St.run (Γ := Γ) q0 c)⟩ : Tr) ∈
          trsOf N S q0 (St.start (Γ := Γ) (Λ := Λ)) :=
        List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_symList c))
      have := step_of_right (N := N) (q0 := q0) (s := St.start (Γ := Γ) (Λ := Λ)) trivial ht rfl
        (encL ([] : List Γ)) (encL l)
      simpa [encL_cons] using this

/-! ### The simulation -/

/-- **The two-stack machine replays a halting run of the Turing machine.** -/
theorem reaches_acc_of_reaches
    (hcl : ∀ {q : Λ} {a : Γ} {q' : Λ} {st : TM0.Stmt Γ}, (q', st) ∈ N q a → q ∈ S → q' ∈ S)
    {b : TM0.Cfg Γ Λ} (hb : TM0.step N b = none) :
    ∀ {c : TM0.Cfg Γ Λ}, Relation.ReflTransGen (fun x y => y ∈ TM0.step N x) c b →
      ∀ (q : Λ) (a : Γ) (L R : List Γ), c = ⟨q, tapeOf a L R⟩ → q ∈ S →
        (simTSM N S q0).Reaches ⟨stCode S (St.run q a), encL L, encL R⟩ ⟨3, [], []⟩ := by
  intro c hc
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro q a L R hcb hq
      subst hcb
      have hN : N q a = none := by
        simpa [TM0.step, tapeOf] using hb
      exact Relation.ReflTransGen.head (step_run_halt (q0 := q0) hq hN L (encL R))
        (flush_reaches L R)
  | head hstep _ ih =>
      rename_i c c₁ _
      intro q a L R hcb hq
      subst hcb
      simp only [TM0.step, Option.mem_def, Option.map_eq_some_iff] at hstep
      obtain ⟨⟨q', st⟩, hN, hc₁⟩ := hstep
      have hq' : q' ∈ S := hcl hN hq
      have hNqa : N q a = some (q', st) := by simpa [tapeOf] using hN
      cases st with
      | write bb =>
          have h1 : c₁ = ⟨q', tapeOf bb L R⟩ := by
            rw [← hc₁]
            exact congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_write bb a L R)
          refine Relation.ReflTransGen.head (step_run_write (q0 := q0) hq hNqa L (encL R)) ?_
          exact ih q' bb L R h1 hq'
      | move d =>
          cases d with
          | right =>
              have h1 : c₁ = ⟨q', tapeOf R.headI (a :: L) R.tail⟩ := by
                rw [← hc₁]
                exact congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_move_right a L R)
              refine Relation.ReflTransGen.head (step_run_right (q0 := q0) hq hNqa L R) ?_
              refine Relation.ReflTransGen.head (step_pl (q0 := q0) (N := N) hq' L (encL R.tail)) ?_
              exact ih q' R.headI (a :: L) R.tail h1 hq'
          | left =>
              have h1 : c₁ = ⟨q', tapeOf L.headI L.tail (a :: R)⟩ := by
                rw [← hc₁]
                exact congrArg (fun T => (⟨q', T⟩ : TM0.Cfg Γ Λ)) (tapeOf_move_left a L R)
              refine Relation.ReflTransGen.head (step_run_left (q0 := q0) hq hNqa L R) ?_
              refine Relation.ReflTransGen.head
                (step_pr (q0 := q0) (N := N) hq' (encL L.tail) R) ?_
              exact ih q' L.headI L.tail (a :: R) h1 hq'

/-- **If the Turing machine halts, the two-stack machine halts.** -/
theorem halts_of_dom
    (hcl : ∀ {q : Λ} {a : Γ} {q' : Λ} {st : TM0.Stmt Γ}, (q', st) ∈ N q a → q ∈ S → q' ∈ S)
    (hq0 : q0 ∈ S) (l : List Γ)
    (h : (Turing.eval (TM0.step N) ⟨q0, Tape.mk₁ l⟩).Dom) :
    (simTSM N S q0).Halts (encL ([] : List Γ)) (encL l) := by
  obtain ⟨b, hb⟩ : ∃ b, b ∈ Turing.eval (TM0.step N) (⟨q0, Tape.mk₁ l⟩ : TM0.Cfg Γ Λ) :=
    ⟨_, Part.get_mem h⟩
  rw [Turing.mem_eval] at hb
  refine Relation.ReflTransGen.trans (start_reaches (N := N) (S := S) l) ?_
  refine reaches_acc_of_reaches (q0 := q0) hcl hb.2 hb.1 q0 l.headI [] l.tail ?_ hq0
  simp [tapeOf_mk₁]

end Sim

end Undec

end HTN
