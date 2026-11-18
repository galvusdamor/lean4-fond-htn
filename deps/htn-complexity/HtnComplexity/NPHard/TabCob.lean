import HtnComplexity.NPHard.VerTab
import HtnComplexity.NPHard.Stage2Cob
/-!
# The tableau formula is written in polynomial time

For a tableau whose machine data are fixed and whose fixed input beginning `pre`, certificate
bound `B`, number of steps `T` and width `W` are computed by functions of Cobham's class, the
token list of the tableau formula is computed (in unary) by a function of Cobham's class
(`HTN.NPHard.cobList_toks_tabF`).
-/

namespace HTN.NPHard

open HTN.PTime HTN.PTime.CobhamTM
open HTN.PTime.CobhamTM.TMSim (Act)

/-! ### Token lists -/

theorem toks_append' (φ ψ : CNF) : toks (φ ++ ψ) = toks φ ++ toks ψ := by
  simp [toks]

theorem toks_flatMap' {α : Type} (l : List α) (F : α → CNF) :
    toks (l.flatMap F) = l.flatMap fun a => toks (F a) := by
  simp [toks, List.flatMap_assoc]

theorem toks_cons' (c : List (ℕ × Bool)) (φ : CNF) :
    toks (c :: φ) = (0 :: c.map litTok) ++ toks φ := by
  simp [toks]

theorem toks_nil' : toks [] = [] := rfl

theorem toks_map' {α : Type} (l : List α) (F : α → List (ℕ × Bool)) :
    toks (l.map F) = l.flatMap fun a => 0 :: (F a).map litTok := by
  simp [toks, List.flatMap_map]

theorem toks_ite' (P : Prop) [Decidable P] (φ ψ : CNF) :
    toks (if P then φ else ψ) = if P then toks φ else toks ψ := by
  split <;> rfl

/-! ### Cobham's class -/

theorem cobList_constIf (P : Prop) [Decidable P] {L L' : Args → List ℕ} (h : P → CobList L)
    (h' : ¬ P → CobList L') : CobList fun a => if P then L a else L' a := by
  by_cases hP : P
  · simpa [hP] using h hP
  · simpa [hP] using h' hP

theorem cobList_ite' {p : Args → Prop} [DecidablePred p] (hp : CobB fun a => decide (p a))
    {L L' : Args → List ℕ} (hL : CobList L) (hL' : CobList L') :
    CobList fun a => if p a then L a else L' a :=
  (cobList_ite hp hL hL').of_eq fun a => by by_cases h : p a <;> simp [h]

theorem cobB_and' {p q : Args → Prop} [DecidablePred p] [DecidablePred q]
    (hp : CobB fun a => decide (p a)) (hq : CobB fun a => decide (q a)) :
    CobB fun a => decide (p a ∧ q a) :=
  (hp.and hq).of_eq fun a => by simp

theorem cobList_mapFin {α : Type} (l : List α) {g : α → Args → ℕ} (h : ∀ x ∈ l, CobN (g x)) :
    CobList fun a => l.map fun x => g x a :=
  (cobList_flatMapFin l (F := fun x a => [g x a]) fun x hx => cobList_single (h x hx)).of_eq
    fun a => List.map_eq_flatMap.symm

theorem cobN_litTok {v : Args → ℕ} (hv : CobN v) (b : Bool) : CobN fun a => litTok (v a, b) := by
  unfold litTok
  cases b
  · exact cobN_add (cobN_mul (cobN_const 2) hv) (cobN_const 1)
  · exact cobN_add (cobN_mul (cobN_const 2) hv) (cobN_const 2)

/-! ### The tableau with computed parameters -/

variable {C K : Type} [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K] [Ix C] [Ix K]

/-- The tokens of the initial clauses of a cell, as a definition by cases. -/
theorem toks_initCell (M : Tab C K Bool) (k : K) (p : ℕ) :
    toks (M.initCell k p) =
      if k = M.k0 ∧ M.pre.length ≤ p ∧ p < M.pre.length + M.B then
        [0, litTok (M.svar 0 k p (some M.a0), true), litTok (M.svar 0 k p (some M.a1), true),
          litTok (M.svar 0 k p none, true), 0, litTok (M.svar 0 k p none, false),
          litTok (M.svar 0 k (p + 1) none, true)]
      else [0, litTok (M.svar 0 k p (if k = M.k0 ∧ p < M.pre.length then M.pre[p]? else none),
        true)] := by
  unfold Tab.initCell Tab.cellInit
  by_cases hk : k = M.k0
  · by_cases h1 : p < M.pre.length
    · simp [hk, h1, toks, show ¬ M.pre.length ≤ p by omega]
    · by_cases h2 : p < M.pre.length + M.B
      · simp [hk, h1, h2, toks, show M.pre.length ≤ p by omega]
      · simp [hk, h1, h2, toks]
  · simp [hk, toks]

/-- The index of the value of a cell of the fixed input beginning. -/
theorem cobN_ixO_pre {P : Fn} (hP : Cobham P) {pf : Args → ℕ} (hp : CobN pf) :
    CobN fun a => Tab.ixO (if pf a < (P a).length then (P a)[pf a]? else none) := by
  refine (cobN_ite (cobB_lt hp (cobN_len hP)) (cobN_ite (cobB_headIs true (cobham_dropBy hp hP))
    (cobN_const 1) (cobN_const 0)) (cobN_const 2)).of_eq fun a => ?_
  simp only [length_un]
  by_cases h : pf a < (P a).length
  · simp only [h, decide_true, if_true, List.head?_drop, List.getElem?_eq_getElem h]
    cases (P a)[pf a] <;> rfl
  · rw [if_neg h, decide_eq_false h]; rfl

section

variable (step : C → (K → Option Bool) → C × (K → Act Bool)) (c0 : C) (k0 : K) (acc : List C)
  (k1 : K) (aT : Bool)

/-- A tableau over the bits with the given machine data. -/
def tabF (pre : List Bool) (B T W : ℕ) : Tab C K Bool where
  step := step
  c0 := c0
  k0 := k0
  a0 := false
  a1 := true
  pre := pre
  B := B
  T := T
  W := W
  acc := acc
  k1 := k1
  aT := aT

section fields
variable (pre : List Bool) (B T W : ℕ)
@[simp] theorem tabF_T : (tabF step c0 k0 acc k1 aT pre B T W).T = T := rfl
@[simp] theorem tabF_W : (tabF step c0 k0 acc k1 aT pre B T W).W = W := rfl
@[simp] theorem tabF_B : (tabF step c0 k0 acc k1 aT pre B T W).B = B := rfl
@[simp] theorem tabF_pre : (tabF step c0 k0 acc k1 aT pre B T W).pre = pre := rfl
@[simp] theorem tabF_k0 : (tabF step c0 k0 acc k1 aT pre B T W).k0 = k0 := rfl
@[simp] theorem tabF_k1 : (tabF step c0 k0 acc k1 aT pre B T W).k1 = k1 := rfl
@[simp] theorem tabF_c0 : (tabF step c0 k0 acc k1 aT pre B T W).c0 = c0 := rfl
@[simp] theorem tabF_aT : (tabF step c0 k0 acc k1 aT pre B T W).aT = aT := rfl
@[simp] theorem tabF_a0 : (tabF step c0 k0 acc k1 aT pre B T W).a0 = false := rfl
@[simp] theorem tabF_a1 : (tabF step c0 k0 acc k1 aT pre B T W).a1 = true := rfl
@[simp] theorem tabF_acc : (tabF step c0 k0 acc k1 aT pre B T W).acc = acc := rfl
@[simp] theorem tabF_step : (tabF step c0 k0 acc k1 aT pre B T W).step = step := rfl
end fields

/-! #### The variables -/

theorem cvar_tabF (pre : List Bool) (B T W t : ℕ) (c : C) :
    (tabF step c0 k0 acc k1 aT pre B T W).cvar t c =
      t * (Ix.card C + Ix.card K * W * Tab.nO Bool) + Ix.ix c := rfl

theorem svar_tabF (pre : List Bool) (B T W t : ℕ) (k : K) (p : ℕ) (o : Option Bool) :
    (tabF step c0 k0 acc k1 aT pre B T W).svar t k p o =
      t * (Ix.card C + Ix.card K * W * Tab.nO Bool) +
        (Ix.card C + ((Ix.ix k * W + p) * Tab.nO Bool + Tab.ixO o)) := rfl

theorem cobN_cvar {P : Fn} {Bf Tf Wf tf : Args → ℕ} (hW : CobN Wf) (ht : CobN tf) (c : C) :
    CobN fun a => (tabF step c0 k0 acc k1 aT (P a) (Bf a) (Tf a) (Wf a)).cvar (tf a) c := by
  simp only [cvar_tabF]
  exact cobN_add (cobN_mul ht (cobN_add (cobN_const _) (cobN_mul (cobN_mul (cobN_const _) hW)
    (cobN_const _)))) (cobN_const _)

theorem cobN_svarG {Wf tf pf ov : Args → ℕ} (hW : CobN Wf) (ht : CobN tf) (hp : CobN pf)
    (hov : CobN ov) (k : K) :
    CobN fun a => tf a * (Ix.card C + Ix.card K * Wf a * Tab.nO Bool) +
        (Ix.card C + ((Ix.ix k * Wf a + pf a) * Tab.nO Bool + ov a)) :=
  cobN_add (cobN_mul ht (cobN_add (cobN_const _) (cobN_mul (cobN_mul (cobN_const _) hW)
    (cobN_const _)))) (cobN_add (cobN_const _) (cobN_add (cobN_mul (cobN_add
      (cobN_mul (cobN_const _) hW) hp) (cobN_const _)) hov))

theorem cobN_svar {P : Fn} {Bf Tf Wf tf pf : Args → ℕ} (hW : CobN Wf) (ht : CobN tf)
    (hp : CobN pf) (k : K) (o : Option Bool) :
    CobN fun a => (tabF step c0 k0 acc k1 aT (P a) (Bf a) (Tf a) (Wf a)).svar (tf a) k (pf a) o := by
  simp only [svar_tabF]
  exact cobN_svarG hW ht hp (cobN_const _) k

theorem cobList_prem {P : Fn} {Bf Tf Wf tf : Args → ℕ} (hW : CobN Wf) (ht : CobN tf) (c : C)
    (h : K → Option Bool) :
    CobList fun a => ((tabF step c0 k0 acc k1 aT (P a) (Bf a) (Tf a) (Wf a)).prem (tf a) c h).map
      litTok := by
  simp only [Tab.prem, List.map_cons, List.map_map]
  exact cobList_cons (cobN_litTok (cobN_cvar _ _ _ _ _ _ hW ht c) _)
    (cobList_mapFin _ fun k _ => cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht (cobN_const 0) k _) _)

theorem cobList_cellConcl {P : Fn} {Bf Tf Wf tf pf : Args → ℕ} (hW : CobN Wf) (ht : CobN tf)
    (hp : CobN pf) (k : K) (o : Option Bool) (act : Act Bool) :
    CobList fun a => ((tabF step c0 k0 acc k1 aT (P a) (Bf a) (Tf a) (Wf a)).cellConcl (tf a) k
      (pf a) o act).map litTok := by
  have ht1 : CobN fun a => tf a + 1 := cobN_add ht (cobN_const 1)
  cases act with
  | keep =>
    simp only [Tab.cellConcl, List.map_cons, List.map_nil]
    exact cobList_cons (cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht hp k o) _)
      (cobList_single (cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht1 hp k o) _))
  | pop =>
    simp only [Tab.cellConcl, apply_ite (List.map litTok), List.map_cons, List.map_nil, tabF_W]
    refine cobList_ite' (cobB_lt (cobN_add hp (cobN_const 1)) hW) ?_ ?_
    · exact cobList_cons (cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht (cobN_add hp (cobN_const 1))
        k o) _) (cobList_single (cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht1 hp k o) _))
    · exact cobList_single (cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht1 hp k _) _)
  | push b =>
    simp only [Tab.cellConcl, apply_ite (List.map litTok), List.map_cons, List.map_nil]
    refine cobList_ite' (cobB_eq hp (cobN_const 0)) ?_ ?_
    · exact cobList_single (cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht1 (cobN_const 0) k _) _)
    · exact cobList_cons (cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht (cobN_sub hp (cobN_const 1))
        k o) _) (cobList_single (cobN_litTok (cobN_svar _ _ _ _ _ _ hW ht1 hp k o) _))

variable {pre : Fn} {B T W : Args → ℕ}

/-! #### The parts of the formula -/

theorem cobList_amoC (hT : CobN T) (hW : CobN W) :
    CobList fun a => toks (tabF step c0 k0 acc k1 aT (pre a) (B a) (T a) (W a)).amoC := by
  simp only [Tab.amoC, toks_flatMap', toks_ite', toks_cons', toks_nil', List.map_cons,
    List.map_nil, List.append_nil]
  refine cobList_loop (cobN_add hT (cobN_const 1)) ?_
  refine cobList_flatMapFin _ fun c _ => cobList_flatMapFin _ fun c' _ => ?_
  refine cobList_constIf _ (fun _ => ?_) (fun _ => cobList_nil)
  exact cobList_cons (cobN_const 0) (cobList_cons (cobN_litTok (cobN_cvar _ _ _ _ _ _
    hW.drop1 (cobN_arg 0) c) _) (cobList_single (cobN_litTok (cobN_cvar _ _ _ _ _ _
    hW.drop1 (cobN_arg 0) c') _)))

theorem cobList_amoS (hT : CobN T) (hW : CobN W) :
    CobList fun a => toks (tabF step c0 k0 acc k1 aT (pre a) (B a) (T a) (W a)).amoS := by
  simp only [Tab.amoS, toks_flatMap', toks_ite', toks_cons', toks_nil', List.map_cons,
    List.map_nil, List.append_nil]
  refine cobList_loop (cobN_add hT (cobN_const 1)) ?_
  refine cobList_flatMapFin _ fun k _ => ?_
  refine cobList_loop hW.drop1 ?_
  refine cobList_flatMapFin _ fun o _ => cobList_flatMapFin _ fun o' _ => ?_
  refine cobList_constIf _ (fun _ => ?_) (fun _ => cobList_nil)
  exact cobList_cons (cobN_const 0) (cobList_cons (cobN_litTok (cobN_svar _ _ _ _ _ _
    hW.drop1.drop1 (cobN_arg 0).drop1 (cobN_arg 0) k o) _) (cobList_single (cobN_litTok
    (cobN_svar _ _ _ _ _ _ hW.drop1.drop1 (cobN_arg 0).drop1 (cobN_arg 0) k o') _)))

theorem cobList_initCNF (hpre : Cobham pre) (hB : CobN B) (hW : CobN W) :
    CobList fun a => toks (tabF step c0 k0 acc k1 aT (pre a) (B a) (T a) (W a)).initCNF := by
  simp only [Tab.initCNF, toks_append', toks_flatMap', toks_cons', toks_nil', List.map_cons,
    List.map_nil, List.append_nil, toks_initCell, tabF_k0, tabF_pre, tabF_B, tabF_a0, tabF_a1,
    tabF_W, tabF_c0]
  refine cobList_append (cobList_cons (cobN_const 0) (cobList_single (cobN_litTok
    (cobN_cvar _ _ _ _ _ _ hW (cobN_const 0) _) _))) ?_
  refine cobList_flatMapFin _ fun k _ => ?_
  refine cobList_loop hW ?_
  have hp : CobN fun a : Args => (a.getD 0 []).length := cobN_arg 0
  have hW' := hW.drop1
  have hpre' : Cobham fun a : Args => pre a.tail := CobhamTM.cobham_dropArgs hpre 1 |>.of_fun_eq
    fun a => by rcases a with _ | ⟨x, a⟩ <;> rfl
  have hB' := hB.drop1
  by_cases hk : k = k0
  · subst hk
    simp only [true_and]
    refine cobList_ite' (cobB_and' (cobB_le (cobN_len hpre') hp) (cobB_lt hp
      (cobN_add (cobN_len hpre') hB'))) ?_ ?_
    · exact cobList_cons (cobN_const 0) (cobList_cons (cobN_litTok (cobN_svar _ _ _ _ _ _ hW'
        (cobN_const 0) hp _ _) _) (cobList_cons (cobN_litTok (cobN_svar _ _ _ _ _ _ hW'
        (cobN_const 0) hp _ _) _) (cobList_cons (cobN_litTok (cobN_svar _ _ _ _ _ _ hW'
        (cobN_const 0) hp _ _) _) (cobList_cons (cobN_const 0) (cobList_cons (cobN_litTok
        (cobN_svar _ _ _ _ _ _ hW' (cobN_const 0) hp _ _) _) (cobList_single (cobN_litTok
        (cobN_svar _ _ _ _ _ _ hW' (cobN_const 0) (cobN_add hp (cobN_const 1)) _ _) _)))))))
    · simp only [svar_tabF]
      exact cobList_cons (cobN_const 0) (cobList_single (cobN_litTok (cobN_svarG hW'
        (cobN_const 0) hp (cobN_ixO_pre hpre' hp) _) _))
  · simp only [hk, false_and, if_false]
    exact cobList_cons (cobN_const 0) (cobList_single (cobN_litTok (cobN_svar _ _ _ _ _ _ hW'
      (cobN_const 0) hp _ _) _))

theorem cobList_transCNF (hT : CobN T) (hW : CobN W) :
    CobList fun a => toks (tabF step c0 k0 acc k1 aT (pre a) (B a) (T a) (W a)).transCNF := by
  simp only [Tab.transCNF, toks_flatMap', toks_cons', toks_map', List.map_append, tabF_T,
    tabF_W, tabF_step, List.map_cons, List.map_nil]
  refine cobList_loop hT ?_
  refine cobList_flatMapFin _ fun c _ => cobList_flatMapFin _ fun h _ => ?_
  refine cobList_append (cobList_cons (cobN_const 0) (cobList_append
    (cobList_prem _ _ _ _ _ _ hW.drop1 (cobN_arg 0) c h) (cobList_single (cobN_litTok
      (cobN_cvar _ _ _ _ _ _ hW.drop1 (cobN_add (cobN_arg 0) (cobN_const 1)) _) _)))) ?_
  refine cobList_flatMapFin _ fun k _ => ?_
  refine cobList_loop hW.drop1 ?_
  refine cobList_flatMapFin _ fun o _ => ?_
  exact cobList_cons (cobN_const 0) (cobList_append
    (cobList_prem _ _ _ _ _ _ hW.drop1.drop1 (cobN_arg 0).drop1 c h)
    (cobList_cellConcl _ _ _ _ _ _ hW.drop1.drop1 (cobN_arg 0).drop1 (cobN_arg 0) k o _))

theorem cobList_accCNF (hT : CobN T) (hW : CobN W) :
    CobList fun a => toks (tabF step c0 k0 acc k1 aT (pre a) (B a) (T a) (W a)).accCNF := by
  simp only [Tab.accCNF, toks_cons', toks_nil', List.map_cons, List.map_nil, List.append_nil,
    List.map_map, tabF_T, tabF_k1, tabF_aT, tabF_acc]
  refine cobList_append (cobList_cons (cobN_const 0) ?_) (cobList_cons (cobN_const 0)
    (cobList_single (cobN_litTok (cobN_svar _ _ _ _ _ _ hW hT (cobN_const 0) _ _) _)))
  exact cobList_mapFin acc fun c _ => cobN_litTok (cobN_cvar _ _ _ _ _ _ hW hT c) _

theorem cobList_toks_tabF (hpre : Cobham pre) (hB : CobN B) (hT : CobN T) (hW : CobN W) :
    CobList fun a => toks (tabF step c0 k0 acc k1 aT (pre a) (B a) (T a) (W a)).cnf := by
  simp only [Tab.cnf, toks_append']
  exact cobList_append (cobList_append (cobList_append (cobList_append
    (cobList_amoC _ _ _ _ _ _ hT hW) (cobList_amoS _ _ _ _ _ _ hT hW))
    (cobList_initCNF _ _ _ _ _ _ hpre hB hW)) (cobList_transCNF _ _ _ _ _ _ hT hW))
    (cobList_accCNF _ _ _ _ _ _ hT hW)

end

end HTN.NPHard
