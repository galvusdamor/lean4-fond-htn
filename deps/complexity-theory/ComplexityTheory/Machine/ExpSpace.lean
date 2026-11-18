import ComplexityTheory.Machine.Kit
/-!
# `EXPSPACE` from nondeterministic search through exponentially long configurations

**Main theorem** (`HTN.Mach.inExpSpace_of_search`). Let `St` (the transition relation) and `Ac`
(the acceptance test) be predicates of Cobham's class, and `p` a polynomial such that
`St [x, c, c']` only holds for configurations `c'` of length at most `2 ^ p(|x|)`.  Then the
language of all `x` for which some configuration `c` reachable from the empty configuration
`[]` along `St` satisfies `Ac [x, c]` is in `EXPSPACE` (`HTN.Space.InExpSpace`,
nondeterministic single-tape Turing machines with an exponential space bound).

The machine is the simulation (`HTN.Mach.exists_tm`) of the stack machine `HTN.Mach.eCode`:
with `x` on stack `1` and the current configuration `c` on stack `2` it repeatedly tests
`Ac [x, c]` (accepting if it holds), guesses a configuration `c'` on stack `3`, tests
`St [x, c, c']` (halting if it fails) and replaces `c` by `c'`.  All stacks stay below a
polynomial in `|x| + 2 ^ p(|x|)`, however long the search.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog

section Search

variable {St Ac : Args → Bool} (RA : Realizer (fun args => [Ac args]))
  (RS : Realizer (fun args => [St args]))

/-- The input stacks of the acceptance test: `x` on `1`, `c` on `2`. -/
def inpA : ℕ → ℕ := fun i => if i = 0 then 1 else if i = 1 then 2 else 0

/-- The input stacks of the transition test: `x` on `1`, `c` on `2`, `c'` on `3`. -/
def inpS : ℕ → ℕ := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 0

/-- Replacing `c` by `c'`. -/
def mvP : Prog := seq (clear 2) (seq (moveRev 3 5) (moveRev 5 2))

/-- The addresses. -/
def eL : ℕ := size (moveRev 0 1)
def eL1 : ℕ := eL + size (RA.P inpA 4 6)
def eG : ℕ := eL1 RA + 2
def eV : ℕ := eG RA + 3
def eV1 : ℕ := eV RA + size (RS.P inpS 4 6)
def eM : ℕ := eV1 RA RS + 2
def eJ : ℕ := eM RA RS + size mvP

/-- The blocks of the machine. -/
def eB₀ : List Ins := (compile (moveRev 0 1) 0).map Ins.ofInstr
def eB₁ : List Ins := (compile (RA.P inpA 4 6) eL).map Ins.ofInstr
def eB₂ : List Ins := [.br 4 (eL1 RA + 1) (eL1 RA + 1) (eJ RA RS + 1), .pop 4]
def eB₃ : List Ins := [.choose (eG RA + 1) (eG RA + 3), .guess 3, .jmp (eG RA)]
def eB₄ : List Ins := (compile (RS.P inpS 4 6) (eV RA)).map Ins.ofInstr
def eB₅ : List Ins := [.br 4 (eJ RA RS + 2) (eJ RA RS + 2) (eV1 RA RS + 1), .pop 4]
def eB₆ : List Ins := (compile mvP (eM RA RS)).map Ins.ofInstr
def eB₇ : List Ins := [.jmp eL, .accept]

/-- **The search machine.** -/
def eCode : List Ins := eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS ++ eB₅ RA RS ++
  eB₆ RA RS ++ eB₇

theorem lookup_block {pre blk post : List Ins} {o i : ℕ} (h : pre.length = o) (hi : i < blk.length) :
    (pre ++ blk ++ post)[o + i]? = blk[i]? := by
  subst h
  rw [List.append_assoc, getElem?_append_at, List.getElem?_append_left hi]

theorem len₀ : eB₀.length = eL := by simp [eB₀, eL, length_compile]
theorem len₀₁ : (eB₀ ++ eB₁ RA).length = eL1 RA := by
  simp [eB₀, eB₁, eL1, eL, length_compile]
  all_goals omega

theorem len₀₂ : (eB₀ ++ eB₁ RA ++ eB₂ RA RS).length = eG RA := by
  simp [eB₀, eB₁, eB₂, eG, eL1, eL, length_compile]
  all_goals omega

theorem len₀₃ : (eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA).length = eV RA := by
  simp [eB₀, eB₁, eB₂, eB₃, eV, eG, eL1, eL, length_compile]
  all_goals omega

theorem len₀₄ : (eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS).length = eV1 RA RS := by
  simp [eB₀, eB₁, eB₂, eB₃, eB₄, eV1, eV, eG, eL1, eL, length_compile]
  all_goals omega

theorem len₀₅ : (eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS ++ eB₅ RA RS).length =
    eM RA RS := by
  simp [eB₀, eB₁, eB₂, eB₃, eB₄, eB₅, eM, eV1, eV, eG, eL1, eL, length_compile]
  all_goals omega

theorem len₀₆ : (eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS ++ eB₅ RA RS ++
    eB₆ RA RS).length = eJ RA RS := by
  simp [eB₀, eB₁, eB₂, eB₃, eB₄, eB₅, eB₆, eJ, eM, eV1, eV, eG, eL1, eL, length_compile]
  all_goals omega

theorem e_at₀ : AtS (eCode RA RS) 0 (compile (moveRev 0 1) 0) :=
  atS_of_append (pre := []) (post := eB₁ RA ++ eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS ++ eB₅ RA RS ++
    eB₆ RA RS ++ eB₇) (by simp [eCode, eB₀]) rfl

theorem e_at₁ : AtS (eCode RA RS) eL (compile (RA.P inpA 4 6) eL) :=
  atS_of_append (pre := eB₀) (post := eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS ++ eB₅ RA RS ++
    eB₆ RA RS ++ eB₇) (by simp [eCode, eB₁]) (len₀)

theorem e_at₄ : AtS (eCode RA RS) (eV RA) (compile (RS.P inpS 4 6) (eV RA)) :=
  atS_of_append (pre := eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA)
    (post := eB₅ RA RS ++ eB₆ RA RS ++ eB₇) (by simp [eCode, eB₄]) (len₀₃ RA RS)

theorem e_at₆ : AtS (eCode RA RS) (eM RA RS) (compile mvP (eM RA RS)) :=
  atS_of_append (pre := eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS ++ eB₅ RA RS)
    (post := eB₇) (by simp [eCode, eB₆]) (len₀₅ RA RS)

theorem e_blk₂ (i : ℕ) (hi : i < 2) : (eCode RA RS)[eL1 RA + i]? = (eB₂ RA RS)[i]? := by
  have := lookup_block (pre := eB₀ ++ eB₁ RA) (blk := eB₂ RA RS)
    (post := eB₃ RA ++ eB₄ RA RS ++ eB₅ RA RS ++ eB₆ RA RS ++ eB₇) (len₀₁ RA) (i := i)
    (by simp [eB₂]; omega)
  simpa [eCode, List.append_assoc] using this

theorem e_blk₃ (i : ℕ) (hi : i < 3) : (eCode RA RS)[eG RA + i]? = (eB₃ RA)[i]? := by
  have := lookup_block (pre := eB₀ ++ eB₁ RA ++ eB₂ RA RS) (blk := eB₃ RA)
    (post := eB₄ RA RS ++ eB₅ RA RS ++ eB₆ RA RS ++ eB₇) (len₀₂ RA RS) (i := i)
    (by simp [eB₃]; omega)
  simpa [eCode, List.append_assoc] using this

theorem e_blk₅ (i : ℕ) (hi : i < 2) : (eCode RA RS)[eV1 RA RS + i]? = (eB₅ RA RS)[i]? := by
  have := lookup_block (pre := eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS)
    (blk := eB₅ RA RS) (post := eB₆ RA RS ++ eB₇) (len₀₄ RA RS) (i := i) (by simp [eB₅]; omega)
  simpa [eCode, List.append_assoc] using this

theorem e_blk₇ (i : ℕ) : (eCode RA RS)[eJ RA RS + i]? = eB₇[i]? := by
  have h := getElem?_append_at (eB₀ ++ eB₁ RA ++ eB₂ RA RS ++ eB₃ RA ++ eB₄ RA RS ++ eB₅ RA RS ++
    eB₆ RA RS) eB₇ (i := i)
  rw [len₀₆] at h
  simpa [eCode] using h

theorem e_brA : (eCode RA RS)[eL1 RA]? = some (.br 4 (eL1 RA + 1) (eL1 RA + 1) (eJ RA RS + 1)) := by
  simpa [eB₂] using e_blk₂ RA RS 0 (by omega)
theorem e_popA : (eCode RA RS)[eL1 RA + 1]? = some (.pop 4) := by
  simpa [eB₂] using e_blk₂ RA RS 1 (by omega)
theorem e_choose : (eCode RA RS)[eG RA]? = some (.choose (eG RA + 1) (eG RA + 3)) := by
  simpa [eB₃] using e_blk₃ RA RS 0 (by omega)
theorem e_guess : (eCode RA RS)[eG RA + 1]? = some (.guess 3) := by
  simpa [eB₃] using e_blk₃ RA RS 1 (by omega)
theorem e_jmpG : (eCode RA RS)[eG RA + 2]? = some (.jmp (eG RA)) := by
  simpa [eB₃] using e_blk₃ RA RS 2 (by omega)
theorem e_brS : (eCode RA RS)[eV1 RA RS]? =
    some (.br 4 (eJ RA RS + 2) (eJ RA RS + 2) (eV1 RA RS + 1)) := by
  simpa [eB₅] using e_blk₅ RA RS 0 (by omega)
theorem e_popS : (eCode RA RS)[eV1 RA RS + 1]? = some (.pop 4) := by
  simpa [eB₅] using e_blk₅ RA RS 1 (by omega)
theorem e_jmpL : (eCode RA RS)[eJ RA RS]? = some (.jmp eL) := by
  simpa [eB₇] using e_blk₇ RA RS 0
theorem e_accept : (eCode RA RS)[eJ RA RS + 1]? = some .accept := e_blk₇ RA RS 1
theorem e_end : (eCode RA RS)[eJ RA RS + 2]? = none := e_blk₇ RA RS 2

/-- The number of stacks. -/
def eK : ℕ := 7 + RA.W + RS.W

theorem eCode_wf : ProgWF (eCode RA RS) (eK RA RS) := by
  intro pc ins hins k hk
  have hmem : ins ∈ eCode RA RS := List.mem_of_getElem? hins
  have hbA := RA.bound inpA 4 6 (fun i _ => by unfold inpA; split_ifs <;> omega) (by omega)
  have hbS := RS.bound inpS 4 6 (fun i _ => by unfold inpS; split_ifs <;> omega) (by omega)
  unfold eCode eB₀ eB₁ eB₂ eB₃ eB₄ eB₅ eB₆ eB₇ at hmem
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  unfold eK
  rcases hmem with ((((((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | h) | h) | ⟨i, hi, rfl⟩) | h) |
    ⟨i, hi, rfl⟩) | h
  · have := stk_compile _ _ _ hi k hk; simp [maxStack, moveRev, move1] at this; omega
  · have := stk_compile _ _ _ hi k hk; omega
  · rcases h with rfl | rfl <;> simp [Ins.stk] at hk <;> omega
  · rcases h with rfl | rfl | rfl <;> simp [Ins.stk] at hk; omega
  · have := stk_compile _ _ _ hi k hk; omega
  · rcases h with rfl | rfl <;> simp [Ins.stk] at hk <;> omega
  · have := stk_compile _ _ _ hi k hk
    simp [maxStack, mvP, moveRev, move1, clear] at this; omega
  · rcases h with rfl | rfl <;> simp [Ins.stk] at hk

/-! #### Stores -/

/-- The stores at the head of the loop: `x` on `1`, `c` on `2`, everything else empty. -/
def Can (x c : List Bool) (S : Store) : Prop := S 0 = [] ∧ S 1 = x ∧ S 2 = c ∧ ∀ j, 3 ≤ j → S j = []

theorem can_inStore (x : List Bool) :
    Can x [] (Function.update (Function.update (inStore 0 x) 0 []) 1
      ((inStore 0 x 0).reverse ++ inStore 0 x 1)) := by
  refine ⟨by simp, by simp [inStore], by simp [inStore], fun j hj => ?_⟩
  simp [inStore, Function.update_of_ne (show j ≠ 1 by omega), Function.update_of_ne (show j ≠ 0 by omega)]

theorem evalA {x c : List Bool} {S : Store} (h : Can x c S) :
    ∃ t ≤ RA.time.eval (x.length + c.length),
      Eval (RA.P inpA 4 6) S (Function.update S 4 [Ac [x, c]]) t := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨t, ht, e⟩ := realizer_eval RA inpA 4 6 [x, c] S
    (fun i _ => by unfold inpA; split_ifs <;> omega) (by omega)
    (fun i _ => by unfold inpA; split_ifs <;> omega)
    (fun i _ => by unfold inpA; rcases i with _ | _ | i <;> simp [h0, h1, h2])
    (h3 4 (by omega)) (fun j hj => h3 j (by omega))
  exact ⟨t, le_trans ht (Polynomial.eval_mono_nat _ (by simp [argSize] <;> omega)), e⟩

theorem evalS {x c c' : List Bool} {S : Store} (h : Can x c S) :
    ∃ t ≤ RS.time.eval (x.length + c.length + c'.length),
      Eval (RS.P inpS 4 6) (Function.update S 3 c')
        (Function.update (Function.update S 3 c') 4 [St [x, c, c']]) t := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨t, ht, e⟩ := realizer_eval RS inpS 4 6 [x, c, c'] (Function.update S 3 c')
    (fun i _ => by unfold inpS; split_ifs <;> omega) (by omega)
    (fun i _ => by unfold inpS; split_ifs <;> omega)
    (fun i _ => by unfold inpS; rcases i with _ | _ | _ | i <;> simp [h0, h1, h2])
    (by simp [h3 4 (by omega)]) (fun j hj => by simp [Function.update_of_ne (show j ≠ 3 by omega),
      h3 j (by omega)])
  exact ⟨t, le_trans ht (Polynomial.eval_mono_nat _ (by simp [argSize] <;> omega)), e⟩

theorem evalM {x c c' : List Bool} {S : Store} (h : Can x c S) :
    ∃ t ≤ 2 * c.length + 8 * c'.length + 3, ∃ S', Can x c' S' ∧
      Eval mvP (Function.update S 3 c') S' t := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have r := (runs_clear 2 (Function.update S 3 c')).seq ((runs_moveRev (show 3 ≠ 5 by omega) _).seq
    (runs_moveRev (show 5 ≠ 2 by omega) _))
  obtain ⟨t, ht, e⟩ := r
  refine ⟨t, ?_, _, ⟨?_, ?_, ?_, fun j hj => ?_⟩, e⟩
  · simp [h2, h3 5 (by omega)] at ht ⊢
    all_goals omega
  · simp [h0]
  · simp [h1]
  · simp [h3 5 (by omega)]
  · by_cases h5 : j = 5
    · subst h5; simp
    · by_cases h3' : j = 3
      · subst h3'; simp
      · simp [Function.update_of_ne h5, Function.update_of_ne h3', Function.update_of_ne
          (show j ≠ 2 by omega), h3 j hj]

/-! #### Soundness -/

theorem e_loop_sound {x : List Bool} :
    ∀ T (c : List Bool) (S : Store), Can x c S → AccIn (eCode RA RS) T ⟨eL, S⟩ →
      ∃ cf, Relation.ReflTransGen (fun c c' => St [x, c, c'] = true) c cf ∧ Ac [x, cf] = true := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    intro c S hS hacc
    obtain ⟨tA, -, eA⟩ := evalA RA hS
    obtain ⟨T₁, hT₁, h₁⟩ := hacc.of_sRunD (reach_compileD eA (e_at₁ RA RS))
    rw [show eL + size (RA.P inpA 4 6) = eL1 RA from rfl] at h₁
    cases hAc : Ac [x, c]
    · -- not accepting: continue
      rw [hAc] at h₁
      have hd₁ : DetAt (eCode RA RS) ⟨eL1 RA, Function.update S 4 [false]⟩ := ⟨.br 4 _ _ _, e_brA RA RS⟩
      obtain ⟨T₂, rfl, h₂⟩ := h₁.of_det hd₁ (SStep.brF (r := []) (e_brA RA RS) (by simp))
      have hd₂ : DetAt (eCode RA RS) ⟨eL1 RA + 1, Function.update S 4 [false]⟩ := ⟨.pop 4, e_popA RA RS⟩
      obtain ⟨T₃, rfl, h₃⟩ := h₂.of_det hd₂ (SStep.pop (e_popA RA RS))
      have hS4 : Function.update (Function.update S 4 [false]) 4 (Function.update S 4 [false] 4).tail
          = S := by simp [hS.2.2.2 4 (by omega)]
      rw [hS4, show eL1 RA + 1 + 1 = eG RA from rfl] at h₃
      obtain ⟨w, T₄, hT₄, h₄⟩ := loop_sound (e_choose RA RS) (e_guess RA RS) (e_jmpG RA RS) T₃ S h₃
      rw [show eG RA + 3 = eV RA from rfl, hS.2.2.2 3 (by omega), List.append_nil] at h₄
      obtain ⟨tS, -, eS⟩ := evalS RS hS (c' := w)
      obtain ⟨T₅, hT₅, h₅⟩ := h₄.of_sRunD (reach_compileD eS (e_at₄ RA RS))
      rw [show eV RA + size (RS.P inpS 4 6) = eV1 RA RS from rfl] at h₅
      set S₅ := Function.update (Function.update S 3 w) 4 [St [x, c, w]]
      have hd₅ : DetAt (eCode RA RS) ⟨eV1 RA RS, S₅⟩ := ⟨.br 4 _ _ _, e_brS RA RS⟩
      cases hSt : St [x, c, w]
      · exfalso
        rw [show S₅ = Function.update (Function.update S 3 w) 4 [false] by simp [S₅, hSt]] at h₅ hd₅
        obtain ⟨T₆, rfl, h₆⟩ := h₅.of_det hd₅ (SStep.brF (r := []) (e_brS RA RS) (by simp))
        exact not_accIn_of_none (e_end RA RS) h₆
      · rw [show S₅ = Function.update (Function.update S 3 w) 4 [true] by simp [S₅, hSt]] at h₅ hd₅
        obtain ⟨T₆, rfl, h₆⟩ := h₅.of_det hd₅ (SStep.brT (r := []) (e_brS RA RS) (by simp))
        have hd₆ : DetAt (eCode RA RS) ⟨eV1 RA RS + 1, Function.update (Function.update S 3 w) 4
            [true]⟩ := ⟨.pop 4, e_popS RA RS⟩
        obtain ⟨T₇, rfl, h₇⟩ := h₆.of_det hd₆ (SStep.pop (e_popS RA RS))
        have hS7 : Function.update (Function.update (Function.update S 3 w) 4 [true]) 4
            (Function.update (Function.update S 3 w) 4 [true] 4).tail = Function.update S 3 w := by
          simp [Function.update_comm (show (4 : ℕ) ≠ 3 by omega), hS.2.2.2 4 (by omega)]
        rw [hS7, show eV1 RA RS + 1 + 1 = eM RA RS from rfl] at h₇
        obtain ⟨tM, -, S', hS', eM'⟩ := evalM hS (c' := w)
        obtain ⟨T₈, hT₈, h₈⟩ := h₇.of_sRunD (reach_compileD eM' (e_at₆ RA RS))
        rw [show eM RA RS + size mvP = eJ RA RS from rfl] at h₈
        have hd₈ : DetAt (eCode RA RS) ⟨eJ RA RS, S'⟩ := ⟨.jmp eL, e_jmpL RA RS⟩
        obtain ⟨T₉, rfl, h₉⟩ := h₈.of_det hd₈ (SStep.jmp (e_jmpL RA RS))
        obtain ⟨cf, hcf, hAcf⟩ := ih T₉ (by omega) w S' hS' h₉
        exact ⟨cf, Relation.ReflTransGen.head hSt hcf, hAcf⟩
    · exact ⟨c, .refl, hAc⟩

/-- **Soundness of the search machine.** -/
theorem eCode_sound {x : List Bool} (h : AccFrom (eCode RA RS) ⟨0, inStore 0 x⟩) :
    ∃ c, Relation.ReflTransGen (fun c c' => St [x, c, c'] = true) [] c ∧ Ac [x, c] = true := by
  obtain ⟨T, hT⟩ := accIn_of_accFrom h
  obtain ⟨t₀, -, e₀⟩ := runs_moveRev (show (0 : ℕ) ≠ 1 by omega) (inStore 0 x)
  obtain ⟨T₁, -, h₁⟩ := hT.of_sRunD (reach_compileD e₀ (e_at₀ RA RS))
  simp only [zero_add] at h₁
  exact e_loop_sound RA RS T₁ [] _ (can_inStore x) h₁

/-! #### Completeness -/

/-- The heights of the stacks of a store. -/
def Small (h : ℕ) (S : Store) : Prop := ∀ j, (S j).length ≤ h

theorem Small.hgt {h K : ℕ} {S : Store} (hs : Small h S) : Hgt K h S := fun j _ => hs j

theorem Small.update {h : ℕ} {S : Store} (hs : Small h S) {j : ℕ} {l : List Bool}
    (hl : l.length ≤ h) : Small h (Function.update S j l) := by
  intro i
  by_cases hi : i = j
  · subst hi; simpa using hl
  · rw [Function.update_of_ne hi]; exact hs i

theorem Small.mono {h h' : ℕ} {S : Store} (hs : Small h S) (hh : h ≤ h') : Small h' S :=
  fun j => le_trans (hs j) hh

theorem can_small {x c : List Bool} {S : Store} (h : Can x c S) :
    Small (x.length + c.length) S := by
  intro j
  obtain ⟨h0, h1, h2, h3⟩ := h
  rcases j with _ | _ | _ | j
  · simp [h0]
  · simp [h1]
  · simp [h2]
  · simp [h3 (j + 3) (by omega)]

/-- The height bound of the search. -/
def eH (x : List Bool) (B : ℕ) : ℕ :=
  9 * x.length + 21 * B + 10 + 2 * RA.time.eval (x.length + B) + 2 * RS.time.eval (x.length + 2 * B)

/-- A segment of a run, starting with small stacks, stays below the height bound. -/
theorem seg_hgt {x : List Bool} {B : ℕ} {σ σ' : SCfg} {T : ℕ} (r : SRun (eCode RA RS) σ σ' T)
    (hs : Small (x.length + B + 1) σ.S)
    (hT : T ≤ 8 * x.length + 20 * B + 9 + 2 * RA.time.eval (x.length + B) +
      2 * RS.time.eval (x.length + 2 * B)) :
    ∃ n, SReachP (eCode RA RS) (fun τ => Hgt (eK RA RS) (eH RA RS x B) τ.S) n σ σ' := by
  obtain ⟨n, -, p⟩ := sReachP_of_sRun (K := eK RA RS) r hs.hgt
  exact ⟨n, p.mono fun τ h => hgt_mono h (by unfold eH; omega)⟩

/-- **One round of the search.** -/
theorem e_round {x c c' : List Bool} {S : Store} (hS : Can x c S) (hAc : Ac [x, c] = false)
    (hSt : St [x, c, c'] = true) {B : ℕ} (hc : c.length ≤ B) (hc' : c'.length ≤ B) :
    ∃ n S', Can x c' S' ∧ SReachP (eCode RA RS)
      (fun τ => Hgt (eK RA RS) (eH RA RS x B) τ.S) n ⟨eL, S⟩ ⟨eL, S'⟩ := by
  have hsm : Small (x.length + B + 1) S := (can_small hS).mono (by omega)
  have hA := Polynomial.eval_mono_nat RA.time (show x.length + c.length ≤ x.length + B by omega)
  have hSb := Polynomial.eval_mono_nat RS.time
    (show x.length + c.length + c'.length ≤ x.length + 2 * B by omega)
  obtain ⟨tA, htA, eA⟩ := evalA RA hS
  have r₁ := (reach_compileD eA (e_at₁ RA RS)).sRun
  rw [show eL + size (RA.P inpA 4 6) = eL1 RA from rfl, hAc] at r₁
  obtain ⟨n₁, p₁⟩ := seg_hgt RA RS (x := x) (B := B) r₁ hsm (by omega)
  have r₂ : SRun (eCode RA RS) ⟨eL1 RA, Function.update S 4 [false]⟩ ⟨eG RA, S⟩ 2 := by
    have := (SRun.single (SStep.brF (r := []) (e_brA RA RS) (by simp))).trans
      (SRun.single (SStep.pop (S := Function.update S 4 [false]) (e_popA RA RS)))
    have e : Function.update (Function.update S 4 [false]) 4 (Function.update S 4 [false] 4).tail
        = S := by
      rw [Function.update_idem, Function.update_self]
      exact Function.update_eq_self_iff.2 (hS.2.2.2 4 (by omega)).symm
    rw [e] at this
    exact this
  obtain ⟨n₂, p₂⟩ := seg_hgt RA RS (x := x) (B := B) r₂ (hsm.update (j := 4) (l := [false]) (by simp)) (by omega)
  have r₃ := loop_run (e_choose RA RS) (e_guess RA RS) (e_jmpG RA RS) c'.reverse S
  rw [List.reverse_reverse, hS.2.2.2 3 (by omega), List.append_nil,
    show eG RA + 3 = eV RA from rfl, List.length_reverse] at r₃
  obtain ⟨n₃, p₃⟩ := seg_hgt RA RS (x := x) (B := B) r₃ hsm (by omega)
  obtain ⟨tS, htS, eS⟩ := evalS RS hS (c' := c')
  have r₄ := (reach_compileD eS (e_at₄ RA RS)).sRun
  rw [show eV RA + size (RS.P inpS 4 6) = eV1 RA RS from rfl, hSt] at r₄
  obtain ⟨n₄, p₄⟩ := seg_hgt RA RS (x := x) (B := B) r₄ (hsm.update (j := 3) (l := c') (by omega)) (by omega)
  have r₅ : SRun (eCode RA RS) ⟨eV1 RA RS, Function.update (Function.update S 3 c') 4 [true]⟩
      ⟨eM RA RS, Function.update S 3 c'⟩ 2 := by
    have := (SRun.single (SStep.brT (r := []) (e_brS RA RS) (by simp))).trans
      (SRun.single (SStep.pop (S := Function.update (Function.update S 3 c') 4 [true])
        (e_popS RA RS)))
    have e : Function.update (Function.update (Function.update S 3 c') 4 [true]) 4
        (Function.update (Function.update S 3 c') 4 [true] 4).tail = Function.update S 3 c' := by
      rw [Function.update_idem, Function.update_self]
      exact Function.update_eq_self_iff.2 (by
        rw [Function.update_of_ne (show (4 : ℕ) ≠ 3 by omega)]; exact (hS.2.2.2 4 (by omega)).symm)
    rw [e] at this
    exact this
  obtain ⟨n₅, p₅⟩ := seg_hgt RA RS (x := x) (B := B) r₅ ((hsm.update (j := 3) (l := c') (by omega)).update
    (j := 4) (l := [true]) (by simp)) (by omega)
  obtain ⟨tM, htM, S', hS', eM'⟩ := evalM hS (c' := c')
  have r₆ := (reach_compileD eM' (e_at₆ RA RS)).sRun
  rw [show eM RA RS + size mvP = eJ RA RS from rfl] at r₆
  obtain ⟨n₆, p₆⟩ := seg_hgt RA RS (x := x) (B := B) r₆ (hsm.update (j := 3) (l := c') (by omega)) (by omega)
  have r₇ : SRun (eCode RA RS) ⟨eJ RA RS, S'⟩ ⟨eL, S'⟩ 1 := SRun.single (SStep.jmp (e_jmpL RA RS))
  obtain ⟨n₇, p₇⟩ := seg_hgt RA RS (x := x) (B := B) r₇ ((can_small hS').mono (by omega)) (by omega)
  exact ⟨_, S', hS', (((((p₁.trans p₂).trans p₃).trans p₄).trans p₅).trans p₆).trans p₇⟩

/-- **The final round**, when the configuration is accepting. -/
theorem e_final {x c : List Bool} {S : Store} (hS : Can x c S) (hAc : Ac [x, c] = true)
    {B : ℕ} (hc : c.length ≤ B) :
    ∃ n σ', Accepting (eCode RA RS) σ' ∧ SReachP (eCode RA RS)
      (fun τ => Hgt (eK RA RS) (eH RA RS x B) τ.S) n ⟨eL, S⟩ σ' := by
  have hsm : Small (x.length + B + 1) S := (can_small hS).mono (by omega)
  have hA := Polynomial.eval_mono_nat RA.time (show x.length + c.length ≤ x.length + B by omega)
  obtain ⟨tA, htA, eA⟩ := evalA RA hS
  have r₁ := (reach_compileD eA (e_at₁ RA RS)).sRun
  rw [show eL + size (RA.P inpA 4 6) = eL1 RA from rfl, hAc] at r₁
  have r₂ : SRun (eCode RA RS) ⟨eL1 RA, Function.update S 4 [true]⟩
      ⟨eJ RA RS + 1, Function.update S 4 [true]⟩ 1 :=
    SRun.single (SStep.brT (r := []) (e_brA RA RS) (by simp))
  obtain ⟨n₁, p₁⟩ := seg_hgt RA RS (x := x) (B := B) (r₁.trans r₂) hsm (by omega)
  exact ⟨_, ⟨eJ RA RS + 1, Function.update S 4 [true]⟩, e_accept RA RS, p₁⟩

theorem e_complete {x : List Bool} {B : ℕ}
    (hshort : ∀ c c', St [x, c, c'] = true → c'.length ≤ B) {cf : List Bool}
    (hAc : Ac [x, cf] = true) :
    ∀ c, Relation.ReflTransGen (fun c c' => St [x, c, c'] = true) c cf → c.length ≤ B →
      ∀ S, Can x c S → ∃ n σ', Accepting (eCode RA RS) σ' ∧ SReachP (eCode RA RS)
        (fun τ => Hgt (eK RA RS) (eH RA RS x B) τ.S) n ⟨eL, S⟩ σ' := by
  intro c hpath
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => intro hc S hS; exact e_final RA RS hS hAc hc
  | @head c c' hst _ ih =>
    intro hc S hS
    cases hAc' : Ac [x, c]
    · obtain ⟨n₁, S', hS', p₁⟩ := e_round RA RS hS hAc' hst hc (hshort c c' hst)
      obtain ⟨n₂, σ', hacc, p₂⟩ := ih (hshort c c' hst) S' hS'
      exact ⟨_, σ', hacc, p₁.trans p₂⟩
    · exact e_final RA RS hS hAc' hc

/-- **Completeness of the search machine.** -/
theorem eCode_complete {x : List Bool} {B : ℕ}
    (hshort : ∀ c c', St [x, c, c'] = true → c'.length ≤ B) {cf : List Bool}
    (hpath : Relation.ReflTransGen (fun c c' => St [x, c, c'] = true) [] cf)
    (hAc : Ac [x, cf] = true) :
    ∃ n σ', Accepting (eCode RA RS) σ' ∧ SReachP (eCode RA RS)
      (fun τ => Hgt (eK RA RS) (eH RA RS x B) τ.S) n ⟨0, inStore 0 x⟩ σ' := by
  obtain ⟨t₀, ht₀, e₀⟩ := runs_moveRev (show (0 : ℕ) ≠ 1 by omega) (inStore 0 x)
  have r₀ := (reach_compileD e₀ (e_at₀ RA RS)).sRun
  simp only [zero_add] at r₀
  have hlen : (inStore 0 x 0).length = x.length := by simp [inStore]
  have hs₀ : Small (x.length + B + 1) (inStore 0 x) := by
    intro j; unfold inStore
    by_cases hj : j = 0
    · subst hj; simp <;> omega
    · rw [Function.update_of_ne hj]; simp
  obtain ⟨n₀, p₀⟩ := seg_hgt RA RS (x := x) (B := B) r₀ hs₀ (by rw [hlen] at ht₀; omega)
  obtain ⟨n₁, σ', hacc, p₁⟩ := e_complete RA RS hshort hAc [] hpath (by simp) _ (can_inStore x)
  exact ⟨_, σ', hacc, p₀.trans p₁⟩

end Search

theorem acceptsInSpace_mono {k : ℕ} {M : NTM (Fin k) (Option Bool)} {w : List (Option Bool)}
    {S S' : ℕ} (h : M.AcceptsInSpace w S) (hS : S ≤ S') : M.AcceptsInSpace w S' := by
  obtain ⟨n, c, hr, hc⟩ := h
  exact ⟨n, c, hr.mono M hS, hc⟩

/-- **Nondeterministic search through exponentially long configurations is in `EXPSPACE`.** -/
theorem inExpSpace_of_search {L : List Bool → Prop} (St Ac : Args → Bool) (hSt : CobhamB St)
    (hAc : CobhamB Ac) (p : Polynomial ℕ)
    (hshort : ∀ x c c', St [x, c, c'] = true → c'.length ≤ 2 ^ p.eval x.length)
    (hL : ∀ x, L x ↔ ∃ c, Relation.ReflTransGen (fun c c' => St [x, c, c'] = true) [] c ∧
      Ac [x, c] = true) : Space.InExpSpace L := by
  obtain ⟨RA⟩ := Prog.nonempty_realizer hAc
  obtain ⟨RS⟩ := Prog.nonempty_realizer hSt
  obtain ⟨k, M, -, hM⟩ := exists_tm (eCode RA RS) (eK RA RS) 0 (eCode_wf RA RS) (by unfold eK; omega)
  set K := eK RA RS
  let PH : Polynomial ℕ := 30 * Polynomial.X + 10 + 2 * RA.time + 2 * RS.time
  let PSp : Polynomial ℕ := Polynomial.X + 2 + (PH + 1) * (Polynomial.C (K : ℕ) + 1)
  obtain ⟨q, hq⟩ := exists_two_pow_bound PSp (p + Polynomial.X + 1)
  refine ⟨k, M, q, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨cf, hpath, hacc⟩ := (hL x).1 hx
    set B := 2 ^ p.eval x.length
    obtain ⟨n, σ', ha, hr⟩ := eCode_complete RA RS (B := B) (fun c c' h => hshort x c c' h) hpath hacc
    have hH : x.length ≤ eH RA RS x B := by unfold eH; omega
    obtain ⟨-, hsp⟩ := (hM x).2 n _ σ' hH hr ha
    refine acceptsInSpace_mono hsp ?_
    set m := x.length + 2 * B
    have hm : m ≤ 2 ^ (p + Polynomial.X + 1).eval x.length := by
      have e1 : (p + Polynomial.X + 1).eval x.length = p.eval x.length + x.length + 1 := by
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      rw [e1, pow_succ, pow_add]
      have h1 : x.length + 1 ≤ 2 ^ x.length := Nat.lt_two_pow_self
      have h2 : 1 ≤ B := Nat.one_le_two_pow
      have h3 : B * (x.length + 1) ≤ B * 2 ^ x.length := Nat.mul_le_mul_left _ h1
      have h4 : x.length ≤ B * x.length := Nat.le_mul_of_pos_left _ h2
      have e2 : B * (x.length + 1) = B * x.length + B := by ring
      show x.length + 2 * B ≤ B * 2 ^ x.length * 2
      omega
    refine le_trans ?_ (hq x.length m hm)
    simp only [PSp, PH, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_ofNat]
    have hA := Polynomial.eval_mono_nat RA.time (show x.length + B ≤ m by omega)
    have hS := Polynomial.eval_mono_nat RS.time (show x.length + 2 * B ≤ m by omega)
    have hHm : eH RA RS x B ≤ 30 * m + 10 + 2 * RA.time.eval m + 2 * RS.time.eval m := by
      unfold eH; omega
    have : (eH RA RS x B + 1) * (K + 1) ≤
        (30 * m + 10 + 2 * RA.time.eval m + 2 * RS.time.eval m + 1) * (K + 1) :=
      Nat.mul_le_mul (by omega) le_rfl
    omega
  · obtain ⟨n, c, hr, hc⟩ := hx
    obtain ⟨T, σ', hr', ha⟩ := (hM x).1 ⟨n, c, hr.reaches M, hc⟩
    exact (hL x).2 (eCode_sound RA RS ⟨T, σ', hr', ha⟩)

end Mach

end HTN
