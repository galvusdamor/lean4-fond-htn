import ComplexityTheory.Complexity.CobhamTM.Simulate
import ComplexityTheory.Complexity.Basic
/-!
# Polynomial-time Turing machines compute functions of Cobham's class

**Main result.** `HTN.PTime.CobhamTM.cobhamFun_of_tm2ComputableInPolyTime`: every function
`f : List Bool → List Bool` computed in polynomial time by a TM2 machine in the sense of
Mathlib's `Turing.TM2ComputableInPolyTime` (with bit strings encoded by themselves,
`finEncodingListBool`) is a polynomial-time function in the sense of this development
(`HTN.PTime.CobhamFun`, Cobham's class).

The proof iterates the vector of step functions of `ComplexityTheory/Complexity/CobhamTM/Simulate.lean`
(`cobham_iterVec`) as many times as a polynomial counter is long — the number of steps of the
machine times the largest depth of a statement bounds the number of elementary operations — and
decodes the output stack block by block (`decodeBlocks`).
-/

namespace HTN.PTime.CobhamTM

open Turing

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.kFin FinTM2.Γk₀Fin

namespace TMSim

variable (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)

theorem initList_stk_k₀ (s : List (tm.Γ tm.k₀)) : (initList tm s).stk tm.k₀ = s := by
  simp [initList]

theorem initList_stk_ne (s : List (tm.Γ tm.k₀)) {k : tm.K} (hk : k ≠ tm.k₀) :
    (initList tm s).stk k = [] := by
  simp [initList, hk]

/-- The initial configuration on input `x`. -/
def c0 (x : List Bool) : MCfg tm := toM tm (initList tm (x.map ein.symm))

theorem inv_c0 (x : List Bool) : Inv tm (c0 tm ein x) := by
  refine ⟨fun q h => ?_, fun k γ hγ => ?_⟩
  · simp only [c0, toM, initList, Option.map_some, Option.some.injEq] at h
    rw [← h]; exact m_mem_Q tm _
  · by_cases hk : k = tm.k₀
    · subst hk
      exact mem_symFin_input tm γ
    · simp [c0, toM, initList_stk_ne tm _ hk] at hγ

theorem length_c0_le (x : List Bool) (k : tm.K) : ((c0 tm ein x).S k).length ≤ x.length := by
  by_cases hk : k = tm.k₀
  · subst hk; simp [c0, toM, initList_stk_k₀]
  · simp [c0, toM, initList_stk_ne tm _ hk]

/-- The initial value of a stack component. -/
noncomputable def initFn (k : tm.K) : Fn := fun args =>
  stkCode tm k ((c0 tm ein (args.getD 0 [])).S k)

/-- The initial vector. -/
noncomputable def inits : List Fn :=
  (fun _ => blkCode (toCtrl tm (some (tm.m tm.main)) tm.initialState)) ::
    (ks tm).map (initFn tm ein)

theorem initV_inits (args : Args) : initV (inits tm ein) args = encM tm (c0 tm ein (args.getD 0 [])) := by
  simp only [initV, inits, List.map_cons, List.map_map, encM]
  rfl

theorem cobham_initFn (k : tm.K) : Cobham (initFn tm ein k) := by
  by_cases hk : k = tm.k₀
  · subst hk
    refine (cobham_flatMapBits (fun b => symCode tm tm.k₀ (ein.symm b)) (Cobham.proj 0)).of_fun_eq
      fun args => ?_
    simp only [initFn, c0, toM, initList_stk_k₀, stkCode, List.flatMap_map, PTime.proj]
  · exact (cobham_const []).of_fun_eq fun args => by
      simp [initFn, c0, toM, initList_stk_ne tm _ hk, stkCode]

theorem cobham_inits : ∀ f ∈ inits tm ein, Cobham f := by
  intro f hf
  simp only [inits, List.mem_cons, List.mem_map] at hf
  rcases hf with rfl | ⟨k, -, rfl⟩
  · exact cobham_const _
  · exact cobham_initFn tm ein k

theorem length_steps_inits : (steps tm).length = (inits tm ein).length := by
  simp [steps, inits]

/-- The codes of a stack whose symbols lie in the finite set, as a list of codes of elements of
the finite type. -/
theorem stkCode_eq_flatMap (k : tm.K) (l : List (tm.Γ k)) (hl : ∀ γ ∈ l, γ ∈ symFin tm k) :
    stkCode tm k l = (l.pmap Subtype.mk hl).flatMap blkCode := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [stkCode_cons tm (hl γ (by simp)), List.pmap_cons, List.flatMap_cons,
      ih fun x hx => hl x (by simp [hx])]

theorem map_pmap_val {α β : Type} {P : α → Prop} (g : α → β) (l : List α) (hl : ∀ a ∈ l, P a) :
    (l.pmap Subtype.mk hl).map (fun x => g x.val) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.pmap_cons, List.map_cons, List.map_cons, ih fun x hx => hl x (by simp [hx])]

end TMSim

open TMSim

/-- **Clocked simulation.**  For every TM2 machine whose input and output alphabets are
identified with `Bool`, and every polynomial `time`, there is a function of Cobham's class that
agrees with the machine on every input on which the machine halts within `time` steps.  The
function of the class runs the machine for (a polynomial multiple of) `time` steps on *every*
input; only correctness is restricted to the inputs in `S`.  This is the general form used for
encodings that do not cover all bit strings (`ComplexityTheory/Complexity/PolyTimeTM.lean`). -/
theorem exists_cobham_of_outputsOn (tm : FinTM2) (ein : tm.Γ tm.k₀ ≃ Bool)
    (eout : tm.Γ tm.k₁ ≃ Bool) (time : Polynomial ℕ) (S : List Bool → Prop)
    (f : List Bool → List Bool)
    (hout : ∀ x, S x → TM2OutputsInTime tm (x.map ein.symm) (some ((f x).map eout.symm))
      (time.eval x.length)) :
    ∃ g : Fn, Cobham g ∧ ∀ x, S x → f x = g [x] := by
  obtain ⟨cnt, hcnt, hcntlen⟩ := exists_cobham_poly (time * Polynomial.C (depthMax tm))
  set M := Finset.univ.sup fun k => Fintype.card (Sym tm k) with hM
  set W := Fintype.card (Ctrl tm) with hW
  set bd : Fn := fun args =>
    (List.replicate M (args.getD 0 [] ++ cnt args)).flatten ++ List.replicate W false with hbddef
  have hbd : Cobham bd := by
    have : ∀ m, Cobham fun args => (List.replicate m (args.getD 0 [] ++ cnt args)).flatten := by
      intro m
      induction m with
      | zero => exact Cobham.empty
      | succ m ih =>
        exact (cobham_append' (cobham_append' (Cobham.proj 0) hcnt) ih).of_fun_eq fun args => by
          simp [List.replicate_succ, PTime.proj]
    exact cobham_appendConst (this M) _
  have hlenbd : ∀ args, (bd args).length = M * ((args.getD 0 []).length + (cnt args).length) + W := by
    intro args; simp [hbddef]
  have hb : ∀ args t, t ≤ (cnt args).length →
      ∀ c ∈ (stepV (steps tm) args)^[t] (initV (inits tm ein) args), c.length ≤ (bd args).length := by
    intro args t ht c hc
    rw [initV_inits, iterate_encM tm (inv_c0 tm ein _)] at hc
    set c' := (μ tm)^[t] (c0 tm ein (args.getD 0 [])) with hc'
    have hinv : Inv tm c' := (inv_c0 tm ein _).iterate tm t
    simp only [encM, List.mem_cons, List.mem_map] at hc
    rw [hlenbd]
    rcases hc with rfl | ⟨k, -, rfl⟩
    · rw [length_blkCode]; omega
    · rw [length_stkCode tm k _ (hinv.2 k)]
      have h1 := length_iterate_μ_le tm (c0 tm ein (args.getD 0 [])) k t
      have h2 := length_c0_le tm ein (args.getD 0 []) k
      have h3 : Fintype.card (Sym tm k) ≤ M :=
        Finset.le_sup (f := fun k => Fintype.card (Sym tm k)) (Finset.mem_univ k)
      calc Fintype.card (Sym tm k) * (c'.S k).length
          ≤ M * ((args.getD 0 []).length + (cnt args).length) :=
            Nat.mul_le_mul h3 (by rw [hc']; omega)
        _ ≤ _ := Nat.le_add_right _ _
  have hcomp := cobham_iterVec (inits tm ein) (steps tm) (length_steps_inits tm ein)
    (cobham_inits tm ein) (cobham_steps tm) hcnt hbd hb (pos tm tm.k₁)
  refine ⟨fun args => decodeBlocks (fun γ : Sym tm tm.k₁ => eout γ.val)
    [((stepV (steps tm) args)^[(cnt args).length] (initV (inits tm ein) args)).getD
      (pos tm tm.k₁) []], cobham_c1 (cobham_decodeBlocks _) hcomp, fun x hx => ?_⟩
  -- correctness on the input `x`
  have hout := hout x hx
  set l' : List (tm.Γ tm.k₁) := (f x).map eout.symm with hl'
  have hev : (flip Option.bind tm.step)^[hout.steps] (some (initList tm (x.map ein.symm))) =
      some (haltList tm l') := hout.evals_in_steps
  obtain ⟨n, hn, hrun⟩ := micro_run tm _ _ _ hev
  have hN : n ≤ (cnt [x]).length := by
    rw [hcntlen]
    simp only [List.getD_cons_zero, Polynomial.eval_mul, Polynomial.eval_C]
    have : hout.steps ≤ time.eval x.length := hout.steps_le_m
    exact le_trans hn (Nat.mul_le_mul_right _ this)
  have hhalt : (μ tm)^[(cnt [x]).length] (c0 tm ein x) = toM tm (haltList tm l') := by
    rw [← Nat.sub_add_cancel hN, Function.iterate_add_apply]
    change (μ tm)^[_] ((μ tm)^[n] (toM tm (initList tm (x.map ein.symm)))) = _
    rw [hrun]
    exact iterate_μ_halted tm _ _ _
  have hinvN : Inv tm ((μ tm)^[(cnt [x]).length] (c0 tm ein x)) := (inv_c0 tm ein x).iterate tm _
  rw [hhalt] at hinvN
  have hmem : ∀ γ ∈ l', γ ∈ symFin tm tm.k₁ := by
    have := hinvN.2 tm.k₁
    simpa [toM, haltList] using this
  simp only
  rw [initV_inits, iterate_encM tm (inv_c0 tm ein _)]
  simp only [List.getD_cons_zero]
  rw [hhalt, ← List.append_nil (encM tm _), getD_encM_append_pos]
  have hstk : (toM tm (haltList tm l')).S tm.k₁ = l' := by simp [toM, haltList]
  rw [hstk, stkCode_eq_flatMap tm _ _ hmem, decodeBlocks_spec, map_pmap_val (fun γ => eout γ)]
  simp [hl']

/-- **Cobham's theorem, Turing machines ⊆ Cobham's class.**  Every function on bit strings
computed in polynomial time by a TM2 machine (Mathlib's `Turing.TM2ComputableInPolyTime`, with
bit strings encoded by themselves) is the unary restriction of a function of Cobham's class. -/
theorem cobhamFun_of_tm2ComputableInPolyTime {f : List Bool → List Bool}
    (h : TM2ComputableInPolyTime finEncodingListBool finEncodingListBool f) :
    CobhamFun f := by
  obtain ⟨g, hg, hfg⟩ := exists_cobham_of_outputsOn h.tm h.inputAlphabet h.outputAlphabet h.time
    (fun _ => True) f (fun x _ => h.outputsFun x)
  exact ⟨g, hg, fun x => hfg x trivial⟩

end HTN.PTime.CobhamTM
