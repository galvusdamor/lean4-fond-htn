import HtnComplexity.PT.Lang
/-!
# Languages of codes in NP

`HTN.Syn.InNP` asks for a polynomial-time verifier `V` on the strings `pairStr x w` (the input
`x` with doubled bits, a separator, the certificate `w`).  This file shows:

* **`HTN.Syn.PolyDom.inNP_codeLang`** — if `Q a` holds iff some value `b` with a code of
  polynomially bounded length makes a polynomial-time Boolean function `r (a, b)` true, then the
  language of the codes of the values satisfying `Q` is in `NP`.

The verifier splits `pairStr x w` into `x` and `w` by finite-state transducers, recognises the
codes and decodes them (`HtnComplexity/PT/Decode.lean`), and runs `r`.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

/-- The transducer reading the input off `pairStr x w`. -/
def getXM : Mealy ℕ where
  step s b := match s with
    | 0 => if b then 2 else 1
    | 1 => if b then 3 else 0
    | 2 => 0
    | _ => 3
  out s b := match s with
    | 1 => if b then [] else [false]
    | 2 => [true]
    | _ => []

/-- The transducer reading the certificate off `pairStr x w`. -/
def getWM : Mealy ℕ where
  step := getXM.step
  out s b := match s with
    | 3 => [b]
    | _ => []

theorem getXM_st (x w : List Bool) : getXM.st 0 (x.flatMap fun b => [b, b]) = 0 := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simpa [Mealy.st, getXM] using ih

theorem getWM_st (x w : List Bool) : getWM.st 0 (x.flatMap fun b => [b, b]) = 0 := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simpa [Mealy.st, getWM, getXM] using ih

theorem getXM_outs_done (w : List Bool) : getXM.outs 3 w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [getXM] using ih

theorem getWM_outs_done (w : List Bool) : getWM.outs 3 w = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [getWM, getXM] using ih

theorem getXM_outs_pre (x : List Bool) : getXM.outs 0 (x.flatMap fun b => [b, b]) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simpa [getXM] using ih

theorem getWM_outs_pre (x : List Bool) : getWM.outs 0 (x.flatMap fun b => [b, b]) = [] := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simpa [getWM, getXM] using ih

/-- The input of `pairStr x w`. -/
def getX (z : List Bool) : List Bool := getXM.outs 0 z

/-- The certificate of `pairStr x w`. -/
def getW (z : List Bool) : List Bool := getWM.outs 0 z

theorem getX_pairStr (x w : List Bool) : getX (pairStr x w) = x := by
  unfold getX pairStr
  rw [List.append_assoc, Mealy.outs_append, getXM_outs_pre, getXM_st x w]
  simp only [List.cons_append, List.nil_append, Mealy.outs_cons]
  rw [show getXM.step (getXM.step 0 false) true = 3 from rfl, getXM_outs_done,
    show getXM.out 0 false = [] from rfl, show getXM.out (getXM.step 0 false) true = [] from rfl]
  simp

theorem getW_pairStr (x w : List Bool) : getW (pairStr x w) = w := by
  unfold getW pairStr
  rw [List.append_assoc, Mealy.outs_append, getWM_outs_pre, getWM_st x w]
  simp only [List.cons_append, List.nil_append, Mealy.outs_cons]
  rw [show getWM.step (getWM.step 0 false) true = 3 from rfl, getWM_outs_done,
    show getWM.out 0 false = [] from rfl, show getWM.out (getWM.step 0 false) true = [] from rfl]
  simp

theorem uc_getX : UC getX := by
  have h := Mealy.cobham_mealy getXM [0, 1, 2, 3] 0 (fun _ => []) (by simp)
    (fun s b hs => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> cases b <;> simp [getXM]) cobham_var0
  exact UC.of_eq (show UC fun z => getXM.outs 0 z ++ [] from h) fun z => by simp [getX]

theorem uc_getW : UC getW := by
  have h := Mealy.cobham_mealy getWM [0, 1, 2, 3] 0 (fun _ => []) (by simp)
    (fun s b hs => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> cases b <;> simp [getWM, getXM]) cobham_var0
  exact UC.of_eq (show UC fun z => getWM.outs 0 z ++ [] from h) fun z => by simp [getW]

/-- A Boolean function of the calculus on pairs of raw strings. -/
theorem uc_of_pt_pair {h : List Bool × List Bool → Bool} (hh : PT h) {F G : List Bool → List Bool}
    (hF : UC F) (hG : UC G) : UC fun z => [h (F z, G z)] := by
  obtain ⟨H, hH, hHh⟩ := hh
  have hcat : UC fun z => lift (F z) ++ lift (G z) :=
    (cobham_c2 cobham_append (uc_lift.comp hF) (uc_lift.comp hG)).of_eq'
      fun args => by simp [compFn]
  exact UC.of_eq (hH.comp hcat) fun z => by
    show H (enc (F z, G z)) = _
    rw [hHh]; rfl

/-- **A language of codes with polynomially checkable, polynomially bounded certificates is in
`NP`.** -/
theorem inNP_codeLang {α β : Type} [BEnc α] [BDec α] [BEnc β] [BDec β] {Q : α → Prop}
    {r : α × β → Bool} (hr : PT r) (k : ℕ)
    (hQ : ∀ a, Q a ↔ ∃ b : β, (enc b).length ≤ ((enc a).length + 1) ^ k ∧ r (a, b) = true) :
    Cx.NP (codeLang α Q) := by
  let h : List Bool × List Bool → Bool := fun p =>
    isCode α p.1 && isCode β p.2 && r ((decR p.1 : α × List Bool).1, (decR p.2 : β × List Bool).1)
  have hh : PT h := PT.and (PT.and ((pt_isCode α).comp PT.fst) ((pt_isCode β).comp PT.snd))
    (hr.comp (PT.pair (PT.fst.comp (BDec.pt_decR.comp PT.fst))
      (PT.fst.comp (BDec.pt_decR.comp PT.snd))))
  refine ⟨fun z => [h (getX z, getW z)], k, polyTimeFun_of_uc (uc_of_pt_pair hh uc_getX uc_getW),
    fun x => ?_⟩
  simp only [getX_pairStr, getW_pairStr, List.getD_cons_zero]
  have hdec : ∀ {γ : Type} [BEnc γ] [BDec γ] (c : γ), (decR (enc c) : γ × List Bool).1 = c := by
    intro γ _ _ c
    rw [show enc c = enc c ++ [] by simp, BDec.decR_enc]
  constructor
  · rintro ⟨a, rfl, ha⟩
    obtain ⟨b, hb, hrb⟩ := (hQ a).1 ha
    refine ⟨enc b, hb, ?_⟩
    simp only [h, Bool.and_eq_true, (isCode_iff _).2 ⟨a, rfl⟩, (isCode_iff _).2 ⟨b, rfl⟩, hdec,
      hrb, and_self]
  · rintro ⟨w, hw, hv⟩
    simp only [h, Bool.and_eq_true] at hv
    obtain ⟨⟨hx, hw'⟩, hrr⟩ := hv
    obtain ⟨a, rfl⟩ := (isCode_iff _).1 hx
    obtain ⟨b, rfl⟩ := (isCode_iff _).1 hw'
    rw [hdec, hdec] at hrr
    exact ⟨a, rfl, (hQ a).2 ⟨b, hw, hrr⟩⟩

end PolyDom

end Syn

end HTN
