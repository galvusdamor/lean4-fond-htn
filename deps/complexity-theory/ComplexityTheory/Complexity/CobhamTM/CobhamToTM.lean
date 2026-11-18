import ComplexityTheory.Complexity.CobhamTM.RealizeBrn
import ComplexityTheory.Complexity.CobhamTM.TMToCobham
/-!
# Cobham's theorem: Cobham's class ⊆ polynomial-time TM2 machines

Every function of Cobham's class has a realizer (`nonempty_realizer`, by induction on the
class); the realizer of a unary function, placed with its input on stack `0`, its output on
stack `2` and its scratch stacks from `3` on, followed by the clearing of stack `0`, is compiled
to a TM2 machine (`ProgTM.lean`), which computes the function in polynomial time.

Together with `cobhamFun_of_tm2ComputableInPolyTime` this gives **Cobham's theorem**
(`cobhamFun_iff_tm2ComputableInPolyTime`).
-/

namespace HTN.PTime.CobhamTM

open HTN.PTime Turing

namespace Prog

theorem nonempty_multi {hs : List Fn} (h : ∀ k ∈ hs, Nonempty (Realizer k)) :
    Nonempty (MultiRealizer hs) := by
  induction hs with
  | nil => exact ⟨multi_nil⟩
  | cons k hs ih =>
    obtain ⟨Rk⟩ := h k (by simp)
    obtain ⟨Rm⟩ := ih fun j hj => h j (by simp [hj])
    exact ⟨multi_cons Rk Rm⟩

/-- **Every function of Cobham's class has a realizer.** -/
theorem nonempty_realizer {f : Fn} (hf : Cobham f) : Nonempty (Realizer f) := by
  induction hf with
  | empty => exact ⟨realizer_empty⟩
  | proj n => exact ⟨realizer_proj n⟩
  | cons b => exact ⟨realizer_cons b⟩
  | smash => exact ⟨realizer_smash⟩
  | @comp g hs _ hhs ihg ihs =>
    obtain ⟨Rg⟩ := ihg
    obtain ⟨Rm⟩ := nonempty_multi ihs
    obtain ⟨q, hq⟩ := exists_common_bound fun h hh => (hhs h hh).poly_length
    exact ⟨realizer_comp Rg Rm q hq⟩
  | @brn g h0 h1 bd _ _ _ hbd hbound ihg ih0 ih1 _ =>
    obtain ⟨Rg⟩ := ihg
    obtain ⟨R0⟩ := ih0
    obtain ⟨R1⟩ := ih1
    obtain ⟨p, hp⟩ := hbd.poly_length
    exact ⟨realizer_brn Rg R0 R1 p fun args => (hbound args).trans (hp args)⟩

noncomputable section

/-! ### The machine of a realizer -/

/-- The input placement: the input on stack `0`, all other arguments on the empty stack `1`. -/
def topInp : ℕ → ℕ := fun i => if i = 0 then 0 else 1

/-- The top-level program: compute into stack `2`, then clear the input stack. -/
def topProg {f : Fn} (R : Realizer f) : Prog := seq (R.P topInp 2 3) (clear 0)

/-- The largest stack index of the machine. -/
def topN {f : Fn} (R : Realizer f) : ℕ := max (maxStack (topProg R)) 3

/-- The compiled code. -/
def topCode {f : Fn} (R : Realizer f) : List Instr := compile (topProg R) 0

/-- The TM2 machine of a realizer. -/
def topTM {f : Fn} (R : Realizer f) : FinTM2 where
  K := Fin (topN R + 1)
  k₀ := 0
  k₁ := stk (topN R) 2
  Γ := Γb (topN R)
  Λ := Fin ((topCode R).length + 1)
  main := lab _ 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := progM (topCode R) (topN R)

/-- The running time of the machine of a realizer. -/
def topTime {f : Fn} (R : Realizer f) : Polynomial ℕ := 2 * R.time + 4 * Polynomial.X + 3

/-- The initial store. -/
def topStore (x : List Bool) : Store := fun j => if j = 0 then x else []

theorem topTM_outputs {f : Fn} (R : Realizer f) (x : List Bool) :
    Nonempty (TM2OutputsInTime (topTM R) x (some (f [x])) ((topTime R).eval x.length)) := by
  set N := topN R with hN
  set C := topCode R with hC
  set S₀ := topStore x with hS₀
  have hN3 : 3 ≤ N := le_max_right _ _
  have hNP : maxStack (topProg R) ≤ N := le_max_left _ _
  -- the run of the program
  have r1 := R.spec topInp 2 3 S₀ (fun i _ => by unfold topInp; split_ifs <;> omega) (by omega)
    (fun i _ => by unfold topInp; split_ifs <;> omega) (by simp [hS₀, topStore])
    (fun j hj => by simp only [hS₀, topStore]; rw [if_neg (by omega)])
  have hget : ∀ i < R.A, S₀ (topInp i) = [x].getD i [] := by
    intro i _
    rcases i with _ | i
    · simp [hS₀, topStore, topInp]
    · simp [hS₀, topStore, topInp]
  have hf : f (argsOf R.A topInp S₀) = f [x] :=
    (R.reads.congr fun i hi => by rw [getD_argsOf hi, hget i hi, getD_padArgs hi]).trans
      (R.reads _).symm
  have hsz : argSize (argsOf R.A topInp S₀) ≤ x.length :=
    (Prog.argSize_argsOf_le_of_getD hget).trans (by simp [argSize])
  rw [hf] at r1
  have r2 := runs_clear 0 (Function.update S₀ 2 (f [x]))
  rw [update_ne' _ (by omega)] at r2
  have e0 : S₀ 0 = x := by simp [hS₀, topStore]
  rw [e0] at r2
  have r3 : Runs (topProg R) S₀ (Function.update (Function.update S₀ 2 (f [x])) 0 [])
      ((R.time.eval (argSize (argsOf R.A topInp S₀))) + (2 * x.length + 1)) := r1.seq r2
  obtain ⟨t, ht, e⟩ := r3
  -- the run of the machine
  have hAt : At C 0 (compile (topProg R) 0) := fun i _ => by simp [hC, topCode]
  obtain ⟨v', hreach⟩ := reach_compile (C := C) (N := N) e hNP hAt
    (by rw [hC, topCode, length_compile]; omega) none
  have hlast : TM2.step (progM C N)
      ⟨some (lab C.length (0 + size (topProg R))), v',
        stkOf N (Function.update (Function.update S₀ 2 (f [x])) 0 [])⟩ =
      some ⟨none, none, stkOf N (Function.update (Function.update S₀ 2 (f [x])) 0 [])⟩ := by
    have hl : ¬ (lab C.length (0 + size (topProg R))).val < C.length := by
      simp only [lab, hC, topCode, length_compile]; omega
    show some (TM2.stepAux (progM C N (lab C.length (0 + size (topProg R)))) v' _) = _
    rw [progM, dif_neg hl]
    rfl
  obtain ⟨k, hk, ek⟩ := hreach.trans (Reach.single hlast)
  refine ⟨⟨⟨k, ?_⟩, ?_⟩⟩
  · have hinit : initList (topTM R) x = ⟨some (lab C.length 0), none, stkOf N S₀⟩ := by
      simp only [initList]
      congr 1
      funext j
      change Fin (topN R + 1) at j
      simp only [stkOf, hS₀, topStore]
      by_cases hj : j.val = 0
      · have h' : j = (topTM R).k₀ := Fin.ext hj
        rw [dif_pos h', if_pos hj]; rfl
      · have h' : j ≠ (topTM R).k₀ := fun h => hj (by rw [h]; rfl)
        rw [dif_neg h', if_neg hj]
    have hhalt : haltList (topTM R) (f [x]) =
        ⟨none, none, stkOf N (Function.update (Function.update S₀ 2 (f [x])) 0 [])⟩ := by
      simp only [haltList]
      congr 1
      funext j
      change Fin (topN R + 1) at j
      simp only [stkOf, Function.update_apply, hS₀, topStore]
      have h2 : (stk N 2).val = 2 := by simp [stk]; omega
      by_cases hj : j.val = 2
      · have h' : j = (topTM R).k₁ := Fin.ext (by rw [hj]; exact h2.symm)
        rw [dif_pos h', if_neg (by omega), if_pos hj]; rfl
      · have h' : j ≠ (topTM R).k₁ := fun h => hj (by rw [h]; exact h2)
        rw [dif_neg h', if_neg hj]
        split_ifs <;> rfl
    rw [hinit, Option.map_some, hhalt]
    exact ek
  · have := Polynomial.eval_mono_nat R.time hsz
    simp only [topTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    omega

/-- The TM2 machine of a realizer of `f` computes `x ↦ f [x]` in polynomial time. -/
def topComputable {f : Fn} (R : Realizer f) :
    TM2ComputableInPolyTime finEncodingListBool finEncodingListBool (fun x => f [x]) where
  tm := topTM R
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := topTime R
  outputsFun x := by
    show TM2OutputsInTime (topTM R) (List.map id x) (some (List.map id (f [x])))
      ((topTime R).eval x.length)
    rw [List.map_id, List.map_id]
    exact (topTM_outputs R x).some

end

end Prog

/-- **Cobham's theorem, Cobham's class ⊆ Turing machines.**  Every polynomial-time function in
the sense of this development (the unary restriction of a function of Cobham's class) is
computed in polynomial time by a TM2 machine (Mathlib's `Turing.TM2ComputableInPolyTime`, with
bit strings encoded by themselves). -/
theorem tm2ComputableInPolyTime_of_cobhamFun {F : List Bool → List Bool} (hF : CobhamFun F) :
    Nonempty (TM2ComputableInPolyTime finEncodingListBool finEncodingListBool F) := by
  obtain ⟨f, hf, hFf⟩ := hF
  obtain ⟨R⟩ := Prog.nonempty_realizer hf
  have : F = fun x => f [x] := funext hFf
  subst this
  exact ⟨Prog.topComputable R⟩

/-- **Cobham's theorem.**  A function on bit strings is in Cobham's class (`CobhamFun`) if and
only if it is computable in polynomial time by a TM2 machine in the sense of Mathlib's
`Turing.TM2ComputableInPolyTime` (bit strings encoded by themselves, over `Bool`). -/
theorem cobhamFun_iff_tm2ComputableInPolyTime {F : List Bool → List Bool} :
    CobhamFun F ↔ Nonempty (TM2ComputableInPolyTime finEncodingListBool finEncodingListBool F) :=
  ⟨tm2ComputableInPolyTime_of_cobhamFun, fun ⟨h⟩ => cobhamFun_of_tm2ComputableInPolyTime h⟩

end HTN.PTime.CobhamTM
