import ComplexityTheory.Complexity.CobhamTM.TMMicro
/-!
# Simulating a TM2 machine inside Cobham's class

The configuration of the micro machine `TMSim.μ` is encoded as a vector of bit strings
(`TMSim.encM`): the one-hot code of the control (current statement and internal state) and, for
every stack, the concatenation of the one-hot codes of its symbols.  One operation of the micro
machine is a vector of functions of Cobham's class (`TMSim.steps`): each component chooses,
according to the finite observation "control and top symbols" (`TMSim.obs`), between keeping a
stack, popping a block and pushing a constant block (`TMSim.step_encM`).
-/

namespace HTN.PTime.CobhamTM

namespace TMSim

open Turing

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.kFin FinTM2.Γk₀Fin

variable (tm : FinTM2)

/-- The symbols of stack `k`, as a finite type. -/
abbrev Sym (k : tm.K) : Type := {γ : tm.Γ k // γ ∈ symFin tm k}

/-- The control of the micro machine, as a finite type. -/
abbrev Ctrl : Type := Option {q : tm.Stmt // q ∈ Q tm} × tm.σ

noncomputable instance decEqSym (k : tm.K) : DecidableEq (Sym tm k) := Classical.decEq _

noncomputable instance decEqCtrl : DecidableEq (Ctrl tm) := Classical.decEq _

open Classical in
/-- The control of a configuration. -/
noncomputable def toCtrl (q : Option tm.Stmt) (v : tm.σ) : Ctrl tm :=
  (q.bind fun q => if h : q ∈ Q tm then some ⟨q, h⟩ else none, v)

open Classical in
/-- The code of a stack symbol. -/
noncomputable def symCode (k : tm.K) (γ : tm.Γ k) : List Bool :=
  if h : γ ∈ symFin tm k then blkCode (⟨γ, h⟩ : Sym tm k) else []

/-- The code of a stack. -/
noncomputable def stkCode (k : tm.K) (l : List (tm.Γ k)) : List Bool := l.flatMap (symCode tm k)

/-- The stacks, in a fixed order. -/
noncomputable def ks : List tm.K := Finset.univ.toList

/-- The position of the code of stack `k` in the vector. -/
noncomputable def pos (k : tm.K) : ℕ := (ks tm).idxOf k + 1

/-- **The encoding of a configuration of the micro machine as a vector of bit strings.** -/
noncomputable def encM (c : MCfg tm) : List (List Bool) :=
  blkCode (toCtrl tm c.q c.v) :: (ks tm).map fun k => stkCode tm k (c.S k)

theorem getD_encM_append_pos (c : MCfg tm) (args : Args) (k : tm.K) :
    (encM tm c ++ args).getD (pos tm k) [] = stkCode tm k (c.S k) := by
  have hk : k ∈ ks tm := by simp [ks]
  have hlt : (ks tm).idxOf k < (ks tm).length := List.idxOf_lt_length_of_mem hk
  rw [pos, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [encM]; omega)]
  simp only [encM, List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hlt,
    List.getElem_idxOf, Option.map_some, Option.getD_some]

theorem getD_encM_append_zero (c : MCfg tm) (args : Args) :
    (encM tm c ++ args).getD 0 [] = blkCode (toCtrl tm c.q c.v) := rfl

/-! ### Reading the observation off the encoding -/

open Classical in
/-- The top symbol of a stack, as an element of the finite type. -/
noncomputable def headSym (k : tm.K) : List (tm.Γ k) → Option (Sym tm k)
  | [] => none
  | γ :: _ => if h : γ ∈ symFin tm k then some ⟨γ, h⟩ else none

theorem stkCode_cons {k : tm.K} {γ : tm.Γ k} (h : γ ∈ symFin tm k) (l : List (tm.Γ k)) :
    stkCode tm k (γ :: l) = blkCode (⟨γ, h⟩ : Sym tm k) ++ stkCode tm k l := by
  simp [stkCode, symCode, h]

theorem decBlk_stkCode (k : tm.K) (l : List (tm.Γ k)) (hl : ∀ γ ∈ l, γ ∈ symFin tm k) :
    decBlk (stkCode tm k l) = headSym tm k l := by
  cases l with
  | nil => exact decBlk_nil
  | cons γ l =>
    have h := hl γ (by simp)
    rw [stkCode_cons tm h, decBlk_blkCode_append]
    simp [headSym, h]

theorem length_stkCode (k : tm.K) (l : List (tm.Γ k)) (hl : ∀ γ ∈ l, γ ∈ symFin tm k) :
    (stkCode tm k l).length = Fintype.card (Sym tm k) * l.length := by
  induction l with
  | nil => simp [stkCode]
  | cons γ l ih =>
    have h := hl γ (by simp)
    rw [stkCode_cons tm h, List.length_append, length_blkCode, ih fun x hx => hl x (by simp [hx]),
      List.length_cons]
    ring

/-- The observation that drives one operation: the decoded control and top symbols. -/
abbrev Obs : Type := Option (Ctrl tm) × (∀ k, Option (Sym tm k))

/-- Reading the observation off a vector (followed by further arguments). -/
noncomputable def obs (args : Args) : Obs tm :=
  (decBlk (args.getD 0 []), fun k => decBlk (args.getD (pos tm k) []))

theorem cobObs_obs (a : Obs tm) : CobB fun args => decide (obs tm args = a) :=
  cobhamObs_pair _ _ (fun o => cobObs_decBlk (Cobham.proj 0) o)
    (cobhamObs_pi (fun k args => (decBlk (args.getD (pos tm k) []) : Option (Sym tm k)))
      fun k o => cobObs_decBlk (Cobham.proj (pos tm k)) o) a

theorem obs_encM {c : MCfg tm} (hc : Inv tm c) (args : Args) :
    obs tm (encM tm c ++ args) = (some (toCtrl tm c.q c.v), fun k => headSym tm k (c.S k)) := by
  simp only [obs, getD_encM_append_zero, getD_encM_append_pos]
  rw [← List.append_nil (blkCode _), decBlk_blkCode_append]
  congr 1
  funext k
  exact decBlk_stkCode tm k _ (hc.2 k)

/-! ### One operation, at the level of codes -/

/-- The statement and internal state of a decoded control. -/
def ctrlOf : Option (Ctrl tm) → Option tm.Stmt × tm.σ
  | some (q, v) => (q.map Subtype.val, v)
  | none => (none, tm.initialState)

/-- The result of one operation, given the observation. -/
def res (a : Obs tm) : Option tm.Stmt × tm.σ × (∀ k, Act (tm.Γ k)) :=
  mstep tm (ctrlOf tm a.1).1 (ctrlOf tm a.1).2 fun k => (a.2 k).map Subtype.val

theorem ctrlOf_toCtrl {q : Option tm.Stmt} (hq : ∀ q', q = some q' → q' ∈ Q tm) (v : tm.σ) :
    ctrlOf tm (some (toCtrl tm q v)) = (q, v) := by
  cases q with
  | none => rfl
  | some q => simp [ctrlOf, toCtrl, hq q rfl]

theorem map_headSym (k : tm.K) (l : List (tm.Γ k)) (hl : ∀ γ ∈ l, γ ∈ symFin tm k) :
    (headSym tm k l).map Subtype.val = l.head? := by
  cases l with
  | nil => rfl
  | cons γ l => simp [headSym, hl γ (by simp)]

theorem res_obs_encM {c : MCfg tm} (hc : Inv tm c) (args : Args) :
    res tm (obs tm (encM tm c ++ args)) = mstep tm c.q c.v fun k => (c.S k).head? := by
  rw [obs_encM tm hc, res]
  simp only
  rw [ctrlOf_toCtrl tm hc.1]
  congr 1
  funext k
  exact map_headSym tm k _ (hc.2 k)

/-- An action on a stack, at the level of codes. -/
noncomputable def actCode (k : tm.K) : Act (tm.Γ k) → List Bool → List Bool
  | .keep, s => s
  | .pop, s => s.drop (Fintype.card (Sym tm k))
  | .push γ, s => symCode tm k γ ++ s

theorem actCode_stkCode (k : tm.K) (a : Act (tm.Γ k)) (l : List (tm.Γ k))
    (hl : ∀ γ ∈ l, γ ∈ symFin tm k) :
    stkCode tm k (a.apply l) = actCode tm k a (stkCode tm k l) := by
  cases a with
  | keep => rfl
  | pop =>
    cases l with
    | nil => simp [Act.apply, actCode, stkCode]
    | cons γ l =>
      have h := hl γ (by simp)
      simp only [Act.apply, actCode, List.tail_cons]
      rw [stkCode_cons tm h, List.drop_left' (length_blkCode _)]
  | push γ => simp [Act.apply, actCode, stkCode]

/-- The control component of one operation. -/
noncomputable def ctrlFn : Fn := fun args =>
  blkCode (toCtrl tm (res tm (obs tm args)).1 (res tm (obs tm args)).2.1)

/-- The component of one operation for stack `k`. -/
noncomputable def stkFn (k : tm.K) : Fn := fun args =>
  actCode tm k ((res tm (obs tm args)).2.2 k) (args.getD (pos tm k) [])

/-- **One operation of the micro machine as a vector of functions of Cobham's class.** -/
noncomputable def steps : List Fn := ctrlFn tm :: (ks tm).map (stkFn tm)

theorem cobham_ctrlFn : Cobham (ctrlFn tm) :=
  cobham_dispatch (obs tm) (cobObs_obs tm)
    (fun a _ => blkCode (toCtrl tm (res tm a).1 (res tm a).2.1)) fun _ => cobham_const _

theorem cobham_actCode (k : tm.K) (a : Act (tm.Γ k)) :
    Cobham fun args => actCode tm k a (args.getD (pos tm k) []) := by
  cases a with
  | keep => exact Cobham.proj _
  | pop => exact cobham_dropConst _ (Cobham.proj _)
  | push γ => exact cobham_constAppend (Cobham.proj _) _

theorem cobham_stkFn (k : tm.K) : Cobham (stkFn tm k) :=
  cobham_dispatch (obs tm) (cobObs_obs tm)
    (fun a args => actCode tm k ((res tm a).2.2 k) (args.getD (pos tm k) []))
    fun a => cobham_actCode tm k _

theorem cobham_steps : ∀ f ∈ steps tm, Cobham f := by
  intro f hf
  simp only [steps, List.mem_cons, List.mem_map] at hf
  rcases hf with rfl | ⟨k, -, rfl⟩
  · exact cobham_ctrlFn tm
  · exact cobham_stkFn tm k

/-- **The vector of step functions performs one operation of the micro machine.** -/
theorem step_encM {c : MCfg tm} (hc : Inv tm c) (args : Args) :
    stepV (steps tm) args (encM tm c) = encM tm (μ tm c) := by
  have hres := res_obs_encM tm hc args
  unfold stepV steps
  rw [List.map_cons, List.map_map]
  show ctrlFn tm (encM tm c ++ args) :: _ = blkCode _ :: _
  congr 1
  · rw [ctrlFn, hres]; rfl
  · refine List.map_congr_left fun k _ => ?_
    show stkFn tm k (encM tm c ++ args) = stkCode tm k ((μ tm c).S k)
    rw [stkFn, hres, getD_encM_append_pos, ← actCode_stkCode tm k _ _ (hc.2 k)]
    rfl

theorem iterate_encM {c : MCfg tm} (hc : Inv tm c) (args : Args) (t : ℕ) :
    (stepV (steps tm) args)^[t] (encM tm c) = encM tm ((μ tm)^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, step_encM tm (hc.iterate tm t),
      Function.iterate_succ_apply']

end TMSim

end HTN.PTime.CobhamTM
