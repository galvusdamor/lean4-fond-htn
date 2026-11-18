import ComplexityTheory.Machine.EvalH
/-!
# Realizing functions of the polynomial-space class: Cobham's class and composition

`HTN.Mach.SRealizer f` is the polynomial-*space* counterpart of a realizer
(`HTN.PTime.CobhamTM.Prog.Realizer`): a program scheme computing `f` for every placement of
inputs, output and scratch stacks, whose run keeps all stacks below the initial heights plus a
polynomial `space` in the size of the inputs (`HTN.Mach.EvalH`).  Its running time is not
bounded.

* `HTN.Mach.SRealizer.ofRealizer` — a realizer (polynomial time) is a space realizer;
* `HTN.Mach.srealizer_comp` — composition, through `HTN.Mach.MultiSRealizer`.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog

noncomputable section

/-- **A space realizer of `f`.** -/
structure SRealizer (f : Fn) where
  A : ℕ
  P : (ℕ → ℕ) → ℕ → ℕ → Prog
  W : ℕ
  space : Polynomial ℕ
  reads : ReadsFirst A f
  bound : ∀ inp out base, (∀ i < A, inp i < base) → out < base → maxStack (P inp out base) ≤ base + W
  spec : ∀ inp out base (S : Store) (h₀ : ℕ), (∀ i < A, inp i < base) → out < base →
    (∀ i < A, inp i ≠ out) → S out = [] → Clean base S → HB h₀ S →
    EvalH (h₀ + space.eval (argSize (argsOf A inp S))) (P inp out base) S
      (Function.update S out (f (argsOf A inp S)))

/-- **Polynomial time is polynomial space.** -/
def SRealizer.ofRealizer {f : Fn} (R : Realizer f) : SRealizer f where
  A := R.A
  P := R.P
  W := R.W
  space := R.time
  reads := R.reads
  bound := R.bound
  spec inp out base S h₀ hinp hout hne hS hc hb := by
    obtain ⟨t, ht, e⟩ := R.spec inp out base S hinp hout hne hS hc
    exact (evalH_of_eval e hb).mono (by omega)

/-- Computing a list of functions into consecutive stacks, with bounded stacks. -/
structure MultiSRealizer (hs : List Fn) where
  A : ℕ
  P : (ℕ → ℕ) → ℕ → Prog
  W : ℕ
  space : Polynomial ℕ
  reads : ∀ h ∈ hs, ReadsFirst A h
  bound : ∀ inp r, (∀ i < A, inp i < r) → maxStack (P inp r) ≤ r + hs.length + 1 + W
  spec : ∀ inp r (S : Store) (h₀ : ℕ), (∀ i < A, inp i < r) → Clean r S → HB h₀ S →
    EvalH (h₀ + space.eval (argSize (argsOf A inp S))) (P inp r) S
      (writeList S r (hs.map fun h => h (argsOf A inp S)))

/-- The empty list of functions. -/
def smulti_nil : MultiSRealizer [] where
  A := 0
  P _ _ := skip
  W := 0
  space := 0
  reads h hh := by simp at hh
  bound _ _ _ := by simp [maxStack]
  spec _ _ S _ _ _ hb := .skip (by simpa using hb)

/-- Adding a function in front of a list. -/
def smulti_cons {h : Fn} {hs : List Fn} (Rh : SRealizer h) (Rm : MultiSRealizer hs) :
    MultiSRealizer (h :: hs) where
  A := max Rh.A Rm.A
  P inp r := seq (Rh.P inp r (r + hs.length + 2)) (Rm.P inp (r + 1))
  W := max Rh.W Rm.W
  space := Rh.space + Rm.space
  reads k hk := by
    rcases List.mem_cons.1 hk with rfl | hk
    · exact Rh.reads.mono (le_max_left _ _)
    · exact (Rm.reads k hk).mono (le_max_right _ _)
  bound inp r hinp := by
    have h1 := Rh.bound inp r (r + hs.length + 2) (fun i hi => by
      have := hinp i (by have := le_max_left Rh.A Rm.A; omega); omega) (by omega)
    have h2 := Rm.bound inp (r + 1) (fun i hi => by
      have := hinp i (by have := le_max_right Rh.A Rm.A; omega); omega)
    simp only [maxStack, List.length_cons]
    have := le_max_left Rh.W Rm.W; have := le_max_right Rh.W Rm.W
    omega
  spec inp r S h₀ hinp hc hb := by
    have hA1 : Rh.A ≤ max Rh.A Rm.A := le_max_left _ _
    have hA2 : Rm.A ≤ max Rh.A Rm.A := le_max_right _ _
    have r1 := Rh.spec inp r (r + hs.length + 2) S h₀ (fun i hi => by have := hinp i (by omega); omega)
      (by omega) (fun i hi => by have := hinp i (by omega); omega) (hc r le_rfl)
      (fun j hj => hc j (by omega)) hb
    set S₁ := Function.update S r (h (argsOf Rh.A inp S)) with hS₁
    have hargs : ∀ A', A' ≤ max Rh.A Rm.A → argsOf A' inp S₁ = argsOf A' inp S := fun A' hA' =>
      argsOf_congr fun i hi => by
        rw [hS₁, update_ne' _ (by have := hinp i (by omega); omega)]
    have r2 := Rm.spec inp (r + 1) S₁ _ (fun i hi => by have := hinp i (by omega); omega)
      (fun j hj => by rw [hS₁, update_ne' _ (by omega)]; exact hc j (by omega)) r1.hb_end
    rw [hargs _ hA2] at r2
    have e1 := Polynomial.eval_mono_nat Rh.space (argSize_argsOf_mono hA1 inp S)
    have e2 := Polynomial.eval_mono_nat Rm.space (argSize_argsOf_mono hA2 inp S)
    have hfin : writeList S₁ (r + 1) (hs.map fun k => k (argsOf Rm.A inp S)) =
        writeList S r ((h :: hs).map fun k => k (argsOf (max Rh.A Rm.A) inp S)) := by
      simp only [List.map_cons, writeList, hS₁]
      rw [readsFirst_argsOf Rh.reads hA1]
      congr 1
      exact List.map_congr_left fun k hk => (readsFirst_argsOf (Rm.reads k hk) hA2 inp S).symm
    rw [hfin] at r2
    refine .seq (r1.mono ?_) (r2.mono ?_)
    · simp only [Polynomial.eval_add]; omega
    · simp only [Polynomial.eval_add]; omega

/-- Space realizers for a list of functions. -/
def smultiOf : ∀ (hs : List Fn), (∀ h ∈ hs, SRealizer h) → MultiSRealizer hs
  | [], _ => smulti_nil
  | h :: hs, R => smulti_cons (R h (by simp)) (smultiOf hs fun k hk => R k (by simp [hk]))

/-- **Composition.** -/
def srealizer_comp {g : Fn} {hs : List Fn} (Rg : SRealizer g) (Rm : MultiSRealizer hs)
    (q : Polynomial ℕ) (hq : ∀ h ∈ hs, ∀ args, (h args).length ≤ q.eval (argSize args)) :
    SRealizer (compFn g hs) where
  A := Rm.A
  P inp out base := seq (Rm.P inp base)
    (seq (Rg.P (fun i => base + min i hs.length) out (base + hs.length + 1))
      (clearFrom base hs.length))
  W := hs.length + 1 + max Rm.W Rg.W
  space := Rm.space + Rg.space.comp q + Polynomial.C hs.length * (2 * q + 1)
  reads := fun args => by
    simp only [compFn]
    congr 1
    exact List.map_congr_left fun h hh => Rm.reads h hh args
  bound inp out base hinp hout := by
    have h1 := Rm.bound inp base hinp
    have h2 := Rg.bound (fun i => base + min i hs.length) out (base + hs.length + 1)
      (fun i _ => by dsimp only; omega) (by omega)
    have h3 := maxStack_clearFrom base hs.length
    have := le_max_left Rm.W Rg.W; have := le_max_right Rm.W Rg.W
    simp only [maxStack]
    omega
  spec inp out base S h₀ hinp hout hne hS hc hb := by
    set m := hs.length
    set L := hs.map fun h => h (argsOf Rm.A inp S) with hLdef
    have hLm : L.length = m := by simp [hLdef, m]
    have r1 := Rm.spec inp base S h₀ hinp hc hb
    set S' := writeList S base L with hS'
    have hSm : S (base + m) = [] := hc _ (by omega)
    have r2 := Rg.spec (fun i => base + min i m) out (base + m + 1) S' _ (fun i _ => by dsimp only; omega)
      (by omega) (fun i _ => by dsimp only; omega) (by rw [hS', writeList_of_lt _ _ _ hout]; exact hS)
      (fun j hj => by rw [hS', writeList_of_ge _ _ _ (by omega)]; exact hc j (by omega)) r1.hb_end
    have hg : g (argsOf Rg.A (fun i => base + min i m) S') = g L :=
      Rg.reads.congr fun i hi => getD_argsOf_writeList Rg.A S base m L hLm hSm hi
    rw [hg] at r2
    obtain ⟨t3, ht3, e3⟩ := runs_clearFrom L (Function.update S out (g L)) base fun i hi => by
      rw [update_ne' _ (by omega)]; exact hc _ (by omega)
    rw [hLm, ← update_writeList _ _ _ hout] at e3
    rw [hLm] at ht3
    have r3 := evalH_of_eval e3 r2.hb_end
    have hsz : argSize (argsOf Rg.A (fun i => base + min i m) S') ≤ argSize L :=
      argSize_argsOf_writeList_le Rg.A S base m L hLm hSm
    have hLq : argSize L ≤ q.eval (argSize (argsOf Rm.A inp S)) := argSize_map_le hq _
    set n := argSize (argsOf Rm.A inp S)
    have e1 := Polynomial.eval_mono_nat Rg.space (hsz.trans hLq)
    have : m * (2 * argSize L + 1) ≤ m * (2 * q.eval n + 1) := Nat.mul_le_mul_left _ (by omega)
    refine .seq (r1.mono ?_) (.seq (r2.mono ?_) (r3.mono ?_))
    · simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_one, Polynomial.eval_ofNat]; omega
    · simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_one, Polynomial.eval_ofNat]; omega
    · simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_one, Polynomial.eval_ofNat]; omega

end

end Mach

end HTN
