import FondHtn.MPStrong.TOFair2Sem
import FondHtn.MPStrong.TODesc
import FondHtn.Alt.Buchi2
/-!
# Fair strong cyclic plan existence for totally ordered problems: the summary game

The summary game of `doc/notes_to_fair_3.md` on descriptions, decided by the fair game tool with
conjunctive nodes and separate safety/progress successors (`FondHtn/Alt/Buchi2.lean`).

Configurations `(k, c, s, d, E, μ, E', e')` (`FOND.TOF.FCfg`):

* `k = 0`, **position** `Pos(s, d, E, μ)`: the totally ordered network `d` from the state `s`,
  exit set `E` (`(true, _)`: every state), mode `μ` (`(false, _)`: reach some exit;
  `(true, e)`: reach the exit `e`);
* `k = 1`, **split** `Split(c, s, d, E, μ, E', e')`: the sub-call `c` with exit set `E'` and
  progress target `e'`, continuation `d`;
* `k = 2`, **call** `Call(c, s, E', e')`; `k = 3`, **method** `CallM(c, s, d, E', e')`.
-/

namespace FOND

namespace TOF

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS TO

/-- A configuration. -/
abbrev FCfg : Type :=
  ℕ × ℕ × List ℕ × TnDesc × (Bool × List (List ℕ)) × (Bool × List ℕ) × List (List ℕ) × List ℕ

instance decEqMu : DecidableEq (Bool × List ℕ) := inferInstance
instance decEqF7 : DecidableEq ((Bool × List ℕ) × List (List ℕ) × List ℕ) := inferInstance
instance decEqF5 : DecidableEq (TnDesc × (Bool × List (List ℕ)) × (Bool × List ℕ) ×
    List (List ℕ) × List ℕ) := inferInstance
instance decEqFCfg : DecidableEq FCfg := inferInstance
instance bEncFCfg : BEnc FCfg := inferInstance
instance bDecFCfg : BDec FCfg := inferInstance
instance bEncFArg : BEnc (FProbDesc × FCfg × FCfg) := inferInstance
instance bEncFArg1 : BEnc (FProbDesc × FCfg) := inferInstance

/-- A position. -/
def pos (s : List ℕ) (d : TnDesc) (E : Bool × List (List ℕ)) (μ : Bool × List ℕ) : FCfg :=
  (0, 0, s, d, E, μ, [], [])

/-- A call. -/
def call (c : ℕ) (s : List ℕ) (L : List (List ℕ)) (e : List ℕ) : FCfg :=
  (2, c, s, emptyD, (false, L), (false, []), [], e)

/-- A call with its method. -/
def callM (c : ℕ) (s : List ℕ) (d : TnDesc) (L : List (List ℕ)) (e : List ℕ) : FCfg :=
  (3, c, s, d, (false, L), (false, []), [], e)

/-- The first task is an applicable primitive task. -/
def primFirst (p : FProbDesc) (s : List ℕ) (d : TnDesc) : Bool :=
  d.ids.any fun y => unc d y && !(lblOf d y).1 && fApp p (lblOf d y).2 s

/-- The first task is compound. -/
def compFirst (d : TnDesc) : Bool := d.ids.any fun y => unc d y && (lblOf d y).1

/-- The kinds: `1` existential, `2` fair, `3` conjunctive, `0` none. -/
def fKd (x : FProbDesc × FCfg) : ℕ :=
  bif x.2.1 == 0 then
    (bif primFirst x.1 x.2.2.2.1 x.2.2.2.2.1 then 2 else bif compFirst x.2.2.2.2.1 then 1 else 0)
  else bif x.2.1 == 1 then 3 else bif x.2.1 == 2 then 1 else bif x.2.1 == 3 then 3 else 0

/-- Accepting configurations: positions with no task left, in the exit set resp. the target. -/
def fAcc (x : FProbDesc × FCfg) : Bool :=
  x.2.1 == 0 && x.2.2.2.2.1.ids.isEmpty &&
    (bif x.2.2.2.2.2.2.1.1 then sameSet x.2.2.2.2.2.2.1.2 x.2.2.2.1
      else inTgt x.2.2.2.2.2.1 x.2.2.2.1)

/-- The safety successors. -/
def stepXf (p : FProbDesc) (k c : ℕ) (s : List ℕ) (d : TnDesc) (E : Bool × List (List ℕ))
    (μ : Bool × List ℕ) (E' : List (List ℕ)) (e' : List ℕ) (g' : FCfg) : Bool :=
  bif k == 0 then
    (d.ids.any fun y => unc d y && !(lblOf d y).1 && fApp p (lblOf d y).2 s &&
      (outs p (lblOf d y).2 s).any fun o => decide (g' = pos o (progDesc d y) E (false, []))) ||
    (d.ids.any fun y => unc d y && (lblOf d y).1 &&
      decide (g' = (1, (lblOf d y).2, s, progDesc d y, E, μ, g'.2.2.2.2.2.2.1,
        g'.2.2.2.2.2.2.2)) && wfStates p g'.2.2.2.2.2.2.1 &&
      decide (g'.2.2.2.2.2.2.2 ∈ g'.2.2.2.2.2.2.1))
  else bif k == 1 then
    decide (g' = call c s E' e') || E'.any fun x => decide (g' = pos x d E (false, []))
  else bif k == 2 then
    decide (g' ∈ (p.methods.filter fun m => m.1 == c).map fun m => callM c s m.2 E.2 e')
  else bif k == 3 then decide (g' = pos s d (false, E.2) (false, []))
  else false

/-- The progress successors. -/
def stepZf (p : FProbDesc) (k c : ℕ) (s : List ℕ) (d : TnDesc) (E : Bool × List (List ℕ))
    (μ : Bool × List ℕ) (E' : List (List ℕ)) (e' : List ℕ) (g' : FCfg) : Bool :=
  bif k == 0 then
    d.ids.any fun y => unc d y && !(lblOf d y).1 && fApp p (lblOf d y).2 s &&
      (outs p (lblOf d y).2 s).any fun o => decide (g' = pos o (progDesc d y) E μ)
  else bif k == 1 then decide (g' = call c s E' e') || decide (g' = pos e' d E μ)
  else bif k == 3 then decide (g' = pos s d (false, E.2) (true, e'))
  else false

def fStepX (x : FProbDesc × FCfg × FCfg) : Bool :=
  stepXf x.1 x.2.1.1 x.2.1.2.1 x.2.1.2.2.1 x.2.1.2.2.2.1 x.2.1.2.2.2.2.1 x.2.1.2.2.2.2.2.1
    x.2.1.2.2.2.2.2.2.1 x.2.1.2.2.2.2.2.2.2 x.2.2

def fStepZ (x : FProbDesc × FCfg × FCfg) : Bool :=
  stepZf x.1 x.2.1.1 x.2.1.2.1 x.2.1.2.2.1 x.2.1.2.2.2.1 x.2.1.2.2.2.2.1 x.2.1.2.2.2.2.2.1
    x.2.1.2.2.2.2.2.2.1 x.2.1.2.2.2.2.2.2.2 x.2.2

/-- The initial configuration. -/
def fInit0 (p : FProbDesc) : FCfg := pos p.init.dedup (initF p).2 (true, []) (false, [])

/-- The initial test. -/
def fInit (x : FProbDesc × FCfg) : Bool :=
  FProbDesc.validB x.1 && fTOB x.1 && decide (x.2 = fInit0 x.1)

/-! ## The moves -/

section Moves

variable {p : FProbDesc} {k c : ℕ} {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)}
  {μ : Bool × List ℕ} {E' : List (List ℕ)} {e' : List ℕ} {g' : FCfg}

theorem stepX_cases (h : stepXf p k c s d E μ E' e' g' = true) :
    (k = 0 ∧ ((∃ y ∈ d.ids, unc d y = true ∧ (lblOf d y).1 = false ∧
        fApp p (lblOf d y).2 s = true ∧ ∃ o ∈ outs p (lblOf d y).2 s,
          g' = pos o (progDesc d y) E (false, [])) ∨
      (∃ y ∈ d.ids, unc d y = true ∧ (lblOf d y).1 = true ∧ ∃ L e,
        g' = (1, (lblOf d y).2, s, progDesc d y, E, μ, L, e) ∧ wfStates p L = true ∧ e ∈ L))) ∨
    (k = 1 ∧ (g' = call c s E' e' ∨ ∃ x ∈ E', g' = pos x d E (false, []))) ∨
    (k = 2 ∧ ∃ m ∈ p.methods, m.1 = c ∧ g' = callM c s m.2 E.2 e') ∨
    (k = 3 ∧ g' = pos s d (false, E.2) (false, [])) := by
  unfold stepXf at h
  rcases k with _ | _ | _ | _ | k
  · left
    refine ⟨rfl, ?_⟩
    simp only [beq_self_eq_true, cond_true, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true'] at h
    rcases h with ⟨y, hy, ⟨⟨hu, hl⟩, ha⟩, o, ho, he⟩ | ⟨y, hy, ⟨⟨⟨hu, hl⟩, he⟩, hw⟩, hm⟩
    · exact Or.inl ⟨y, hy, hu, hl, ha, o, ho, he⟩
    · exact Or.inr ⟨y, hy, hu, hl, _, _, he, hw, hm⟩
  · right; left
    rw [show ((0 + 1 : ℕ) == 0) = false from rfl, show ((0 + 1 : ℕ) == 1) = true from rfl] at h
    simp only [cond_false, cond_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    exact ⟨rfl, h⟩
  · right; right; left
    rw [show ((0 + 1 + 1 : ℕ) == 0) = false from rfl, show ((0 + 1 + 1 : ℕ) == 1) = false from rfl,
      show ((0 + 1 + 1 : ℕ) == 2) = true from rfl] at h
    simp only [cond_false, cond_true] at h
    have h' := of_decide_eq_true h
    simp only [List.mem_map, List.mem_filter, beq_iff_eq] at h'
    obtain ⟨m, ⟨hm, hc⟩, rfl⟩ := h'
    exact ⟨rfl, m, hm, hc, rfl⟩
  · right; right; right
    rw [show ((0 + 1 + 1 + 1 : ℕ) == 0) = false from rfl,
      show ((0 + 1 + 1 + 1 : ℕ) == 1) = false from rfl,
      show ((0 + 1 + 1 + 1 : ℕ) == 2) = false from rfl,
      show ((0 + 1 + 1 + 1 : ℕ) == 3) = true from rfl] at h
    simp only [cond_false, cond_true, decide_eq_true_eq] at h
    exact ⟨rfl, h⟩
  · exfalso
    have h0 : (k + 1 + 1 + 1 + 1 == 0) = false := by simp
    have h1 : (k + 1 + 1 + 1 + 1 == 1) = false := by simp
    have h2 : (k + 1 + 1 + 1 + 1 == 2) = false := by simp
    have h3 : (k + 1 + 1 + 1 + 1 == 3) = false := by simp
    rw [h0, h1, h2, h3] at h
    simp at h

theorem stepZ_cases (h : stepZf p k c s d E μ E' e' g' = true) :
    (k = 0 ∧ ∃ y ∈ d.ids, unc d y = true ∧ (lblOf d y).1 = false ∧
        fApp p (lblOf d y).2 s = true ∧ ∃ o ∈ outs p (lblOf d y).2 s,
          g' = pos o (progDesc d y) E μ) ∨
    (k = 1 ∧ (g' = call c s E' e' ∨ g' = pos e' d E μ)) ∨
    (k = 3 ∧ g' = pos s d (false, E.2) (true, e')) := by
  unfold stepZf at h
  rcases k with _ | _ | _ | _ | k
  · left
    refine ⟨rfl, ?_⟩
    simp only [beq_self_eq_true, cond_true, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨y, hy, ⟨⟨hu, hl⟩, ha⟩, o, ho, he⟩ := h
    exact ⟨y, hy, hu, hl, ha, o, ho, he⟩
  · right; left
    rw [show ((0 + 1 : ℕ) == 0) = false from rfl, show ((0 + 1 : ℕ) == 1) = true from rfl] at h
    simp only [cond_false, cond_true, Bool.or_eq_true, decide_eq_true_eq] at h
    exact ⟨rfl, h⟩
  · exfalso
    rw [show ((0 + 1 + 1 : ℕ) == 0) = false from rfl, show ((0 + 1 + 1 : ℕ) == 1) = false from rfl,
      show ((0 + 1 + 1 : ℕ) == 3) = false from rfl] at h
    simp at h
  · right; right
    rw [show ((0 + 1 + 1 + 1 : ℕ) == 0) = false from rfl,
      show ((0 + 1 + 1 + 1 : ℕ) == 1) = false from rfl,
      show ((0 + 1 + 1 + 1 : ℕ) == 3) = true from rfl] at h
    simp only [cond_false, cond_true, decide_eq_true_eq] at h
    exact ⟨rfl, h⟩
  · exfalso
    have h0 : (k + 1 + 1 + 1 + 1 == 0) = false := by simp
    have h1 : (k + 1 + 1 + 1 + 1 == 1) = false := by simp
    have h3 : (k + 1 + 1 + 1 + 1 == 3) = false := by simp
    rw [h0, h1, h3] at h
    simp at h

end Moves

/-! ## Invariant and sizes -/

/-- **The invariant of reachable configurations.** -/
structure FInv (p : FProbDesc) (g : FCfg) : Prop where
  kind : g.1 ≤ 3
  st : SInv p g.2.2.1
  d : DInv p g.2.2.2.1
  tgt : ∀ l ∈ g.2.2.2.2.1.2, SInv p l
  tgtsz : sz g.2.2.2.2.1.2 ≤ Mx p
  mu : SInv p g.2.2.2.2.2.1.2
  mid : wfStates p g.2.2.2.2.2.2.1 = true
  e : SInv p g.2.2.2.2.2.2.2
  name : g.1 ≠ 0 → (QP p).ReachableName g.2.1
  namesz : sz g.2.1 ≤ sz p + 5

/-- The reachable configurations. -/
def FReach (p : FProbDesc) (g : FCfg) : Prop :=
  Relation.ReflTransGen (fun g g' => fStepX (p, g, g') = true ∨ fStepZ (p, g, g') = true)
    (fInit0 p) g

theorem sInv_nil (p : FProbDesc) : SInv p [] := ⟨List.nodup_nil, by simp⟩

theorem FInv.step {p : FProbDesc} (hp : p.Valid) (hTO : FClass.TO p.toProblem) {g g' : FCfg}
    (h : FInv p g) (hs : fStepX (p, g, g') = true ∨ fStepZ (p, g, g') = true) : FInv p g' := by
  obtain ⟨k, c, s, d, E, μ, E', e'⟩ := g
  obtain ⟨hk, hst, hd, htgt, htgtsz, hmu, hmid, he, hname, hnamesz⟩ := h
  simp only at hk hst hd htgt htgtsz hmu hmid he hname hnamesz
  have hm := (wfStates_iff p E').1 hmid
  rcases hs with hs | hs
  · change stepXf p k c s d E μ E' e' g' = true at hs
    rcases stepX_cases hs with
      ⟨rfl, ⟨y, hy, hu, -, -, o, ho, rfl⟩ | ⟨y, hy, hu, hl, L, e₀, rfl, hw, he₀⟩⟩ |
      ⟨rfl, rfl | ⟨x, hx, rfl⟩⟩ | ⟨rfl, m, hmm, hc, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simp [pos], mem_ffacts_of_outs hst ho, hd.prog hy ((unc_iff _ _).1 hu), htgt,
        htgtsz, sInv_nil p, wfStates_nil p, sInv_nil p, fun h => absurd rfl h, sz_zero_le p⟩
    · have hL := (wfStates_iff p L).1 hw
      exact ⟨by simp, hst, hd.prog hy ((unc_iff _ _).1 hu), htgt, htgtsz, hmu, hw,
        ⟨(hL.2 e₀ he₀).1, (hL.2 e₀ he₀).2⟩, fun _ => hd.names y hy _ (Prod.ext hl rfl),
        (sz_lblOf_le d y).trans (by have := hd.size; omega)⟩
    · exact ⟨by simp [call], hst, dInv_empty p, fun l hl => ⟨(hm.2 l hl).1, (hm.2 l hl).2⟩, hm.1,
        sInv_nil p, wfStates_nil p, he, fun _ => hname (by decide), hnamesz⟩
    · exact ⟨by simp [pos], ⟨(hm.2 x hx).1, (hm.2 x hx).2⟩, hd, htgt, htgtsz, sInv_nil p,
        wfStates_nil p, sInv_nil p, fun h => absurd rfl h, sz_zero_le p⟩
    · exact ⟨by simp [callM], hst, dInv_method hp hTO hmm (hc ▸ hname (by decide)), htgt,
        htgtsz, sInv_nil p, wfStates_nil p, he, fun _ => hc ▸ hname (by decide), hnamesz⟩
    · exact ⟨by simp [pos], hst, hd, htgt, htgtsz, sInv_nil p, wfStates_nil p, sInv_nil p,
        fun h => absurd rfl h, sz_zero_le p⟩
  · change stepZf p k c s d E μ E' e' g' = true at hs
    rcases stepZ_cases hs with ⟨rfl, y, hy, hu, -, -, o, ho, rfl⟩ |
      ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simp [pos], mem_ffacts_of_outs hst ho, hd.prog hy ((unc_iff _ _).1 hu), htgt,
        htgtsz, hmu, wfStates_nil p, sInv_nil p, fun h => absurd rfl h, sz_zero_le p⟩
    · exact ⟨by simp [call], hst, dInv_empty p, fun l hl => ⟨(hm.2 l hl).1, (hm.2 l hl).2⟩, hm.1,
        sInv_nil p, wfStates_nil p, he, fun _ => hname (by decide), hnamesz⟩
    · exact ⟨by simp [pos], he, hd, htgt, htgtsz, hmu, wfStates_nil p, sInv_nil p,
        fun h => absurd rfl h, sz_zero_le p⟩
    · exact ⟨by simp [pos], hst, hd, htgt, htgtsz, he, wfStates_nil p, sInv_nil p,
        fun h => absurd rfl h, sz_zero_le p⟩

theorem fInv_init {p : FProbDesc} (hp : p.Valid) (hTO : FClass.TO p.toProblem) :
    FInv p (fInit0 p) :=
  ⟨by simp [fInit0, pos],
    ⟨List.nodup_dedup _, fun f hf => List.mem_append_left _ (List.mem_dedup.1 hf)⟩,
    dInv_init hp hTO, by simp [fInit0, pos], by
      show sz ([] : List (List ℕ)) ≤ Mx p
      simp only [sz_nil, Mx]; exact Nat.one_le_two_pow,
    sInv_nil p, wfStates_nil p, sInv_nil p, fun h => absurd rfl h, sz_zero_le p⟩

theorem fInv_of_reach {p : FProbDesc} (hp : p.Valid) (hTO : FClass.TO p.toProblem) {g : FCfg}
    (h : FReach p g) : FInv p g := by
  induction h with
  | refl => exact fInv_init hp hTO
  | tail _ hs ih => exact ih.step hp hTO hs

/-- The bound on reachable configurations. -/
def fBound (p : FProbDesc) : ℕ :=
  2 * Mx p + 3 * (sz p * (2 * sz p + 2) + 1) + 2 * sz p + 20

theorem sz_le_of_fInv {p : FProbDesc} {g : FCfg} (h : FInv p g) : sz g ≤ fBound p := by
  obtain ⟨k, c, s, d, E, μ, E', e'⟩ := g
  obtain ⟨hk, hst, hd, -, htgtsz, hmu, hmid, he, -, hnamesz⟩ := h
  simp only at hk hst hd htgtsz hmu hmid he hnamesz
  have h1 : sz k ≤ 5 := sz_nat_le_of_lt (k := 2) (by norm_num; omega)
  have h2 := sz_state_le hst.1 hst.2
  have h3 := hd.size
  have h4 := ((wfStates_iff p E').1 hmid).1
  have h5 : sz E = 1 + sz E.2 := by
    rw [show sz E = sz E.1 + sz E.2 from sz_prod _ _, sz_bool]
  have h6 : sz μ = 1 + sz μ.2 := by
    rw [show sz μ = sz μ.1 + sz μ.2 from sz_prod _ _, sz_bool]
  have h7 := sz_state_le hmu.1 hmu.2
  have h8 := sz_state_le he.1 he.2
  have hsz : sz ((k, c, s, d, E, μ, E', e') : FCfg) =
      sz k + sz c + sz s + sz d + sz E + sz μ + sz E' + sz e' := by
    simp only [sz_prod]; ring
  rw [hsz, h5, h6]
  unfold fBound
  omega

/-! ## More on sequential composition -/

section SeqMore

open HTN.TaskNetwork

variable {A C I : Type} [DecidableEq I]

theorem seqNet_assoc (a b c : TaskNetwork I A C) :
    Problem.seqNet (Problem.seqNet a b) c = Problem.seqNet a (Problem.seqNet b c) := by
  refine TaskNetwork.ext' ?_ ?_ ?_
  · simp [Problem.seqNet, Finset.union_assoc]
  · funext x y
    simp only [Problem.seqNet, Finset.mem_union, eq_iff_iff]
    tauto
  · funext x
    simp only [Problem.seqNet, Finset.mem_union]
    by_cases ha : x ∈ a.T
    · simp [ha]
    · by_cases hb : x ∈ b.T <;> simp [ha, hb]

theorem seqNet_agree_left {a a' c : TaskNetwork I A C} (h : a.Agree a') :
    (Problem.seqNet a c).Agree (Problem.seqNet a' c) := by
  obtain ⟨hT, ho, hα⟩ := h
  refine ⟨by simp [Problem.seqNet, hT], by funext x y; simp [Problem.seqNet, hT, ho],
    fun x _ => ?_⟩
  simp only [Problem.seqNet, ← hT]
  split_ifs with hx
  · exact hα x hx
  · rfl

theorem seqNet_nil_right {u v : TaskNetwork I A C} (hv : v.WF) (he : v.T = ∅) :
    (Problem.seqNet u v).Agree u := by
  refine ⟨by simp [Problem.seqNet, he], ?_, fun x hx => ?_⟩
  · funext a b
    simp only [Problem.seqNet, he, Finset.notMem_empty, and_false, or_false, eq_iff_iff]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd (hv.mem_left h) (by simp [he])
    · exact Or.inl
  · have : x ∈ u.T := by simpa [Problem.seqNet, he] using hx
    simp [Problem.seqNet, this]

omit [DecidableEq I] in
theorem IsFirst.isoVia {N N' : TaskNetwork I A C} {x : I} {σ : I → I}
    (h : Problem.IsFirst N x) (hσ : HTN.TaskNetwork.IsoVia σ N N') : Problem.IsFirst N' (σ x) := by
  refine ⟨hσ.mem h.1, fun b hb hbx => ?_⟩
  obtain ⟨b', hb', rfl⟩ := hσ.surj hb
  have hne : b' ≠ x := fun e => hbx (e ▸ rfl)
  exact (hσ.2.1 x h.1 b' hb').1 (h.2 b' hb' hne)

/-- The empty network. -/
def emptyTN : TaskNetwork ℕ ℕ ℕ := ⟨∅, fun _ _ => False, fun _ => Sum.inl 0⟩

theorem emptyTN_wf : (emptyTN).WF :=
  ⟨fun h => h.elim, fun h => h.elim, fun _ h => h, fun h _ => h.elim⟩

end SeqMore

/-! ## Soundness -/

section Sound

open HTN.TaskNetwork

variable (p : FProbDesc) (Xg : FCfg → Prop) (G : Set (Set ℕ))

/-- **Stacks of frames**: the networks of the soundness construction. -/
inductive Stk : TaskNetwork ℕ ℕ ℕ → Set ℕ → Prop
  | nil {v : TaskNetwork ℕ ℕ ℕ} {x : Set ℕ} (hv : v.WF) (he : v.T = ∅) (hx : x ∈ G) : Stk v x
  | push {u v : TaskNetwork ℕ ℕ ℕ} {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)}
      {σ : ℕ → ℕ} (hg : Xg (pos s d E (false, []))) (hr : FReach p (pos s d E (false, [])))
      (hσ : HTN.TaskNetwork.IsoVia σ (cfgNet d) u) (hu : u.WF) (hv : v.WF)
      (hd : Disjoint u.T v.T) (hc : ∀ x ∈ tgtSet E, Stk v x) :
      Stk (Problem.seqNet u v) {f | f ∈ s}

/-- The semantic set: networks isomorphic to stacks. -/
def XS : Problem.NSet ℕ ℕ ℕ ℕ := fun N S =>
  N.WF ∧ ∃ (N₀ : TaskNetwork ℕ ℕ ℕ) (σ : ℕ → ℕ), Stk p Xg G N₀ S ∧
    HTN.TaskNetwork.IsoVia σ N₀ N

/-- The targets of a mode. -/
def muSet (E : Bool × List (List ℕ)) (μ : Bool × List ℕ) : Set (Set ℕ) :=
  if μ.1 then {{f | f ∈ μ.2}} else tgtSet E

/-- What a position guarantees in every context. -/
def PosStmt (s : List ℕ) (d : TnDesc) (E : Bool × List (List ℕ)) (μ : Bool × List ℕ) : Prop :=
  ∀ (u v : TaskNetwork ℕ ℕ ℕ) (σ : ℕ → ℕ), HTN.TaskNetwork.IsoVia σ (cfgNet d) u → u.WF →
    v.WF → Disjoint u.T v.T → (∀ x ∈ tgtSet E, Stk p Xg G v x) →
    (∀ x ∈ muSet E μ, ∃ n, p.toProblem.FAttrT G (XS p Xg G) n v x) →
    ∃ n, p.toProblem.FAttrT G (XS p Xg G) n (Problem.seqNet u v) {f | f ∈ s}

/-- What a call guarantees. -/
def CallStmt (c : ℕ) (s : List ℕ) (L : List (List ℕ)) (e : List ℕ) : Prop :=
  ∃ m ∈ p.methods, m.1 = c ∧ Xg (pos s m.2 (false, L) (false, [])) ∧
    FReach p (pos s m.2 (false, L) (false, [])) ∧ PosStmt p Xg G s m.2 (false, L) (true, e)

/-- The motive of the soundness induction. -/
def Mot (g : FCfg) : Prop :=
  (g.1 = 0 → PosStmt p Xg G g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1) ∧
  (g.1 = 1 → CallStmt p Xg G g.2.1 g.2.2.1 g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2 ∧
    (∀ x ∈ g.2.2.2.2.2.2.1, Xg (pos x g.2.2.2.1 g.2.2.2.2.1 (false, [])) ∧
      FReach p (pos x g.2.2.2.1 g.2.2.2.2.1 (false, []))) ∧
    PosStmt p Xg G g.2.2.2.2.2.2.2 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1) ∧
  (g.1 = 2 → CallStmt p Xg G g.2.1 g.2.2.1 g.2.2.2.2.1.2 g.2.2.2.2.2.2.2) ∧
  (g.1 = 3 → Xg (pos g.2.2.1 g.2.2.2.1 (false, g.2.2.2.2.1.2) (false, [])) ∧
    FReach p (pos g.2.2.1 g.2.2.2.1 (false, g.2.2.2.2.1.2) (false, [])) ∧
    PosStmt p Xg G g.2.2.1 g.2.2.2.1 (false, g.2.2.2.2.1.2) (true, g.2.2.2.2.2.2.2))

variable {p Xg G}

theorem Stk.wf {N : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ} (h : Stk p Xg G N S) : N.WF := by
  cases h with
  | nil hv => exact hv
  | push _ _ _ hu hv hd => exact Problem.seqNet_wf hu hv hd

theorem XS_good : Problem.NGood (XS p Xg G) := by
  refine ⟨fun _ _ h => h.1, fun tn tn' S σ h hw' hσ => ?_⟩
  obtain ⟨-, N₀, τ, hN, hτ⟩ := h
  exact ⟨hw', N₀, σ ∘ τ, hN, hτ.comp hσ⟩

theorem XS_of_stk {N N' : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ} (h : Stk p Xg G N S)
    (hag : N.Agree N') : XS p Xg G N' S :=
  ⟨Problem.wf_of_agree h.wf hag, N, id, h, Problem.isoVia_of_agree' hag⟩

theorem iso_prog {d : TnDesc} {u : TaskNetwork ℕ ℕ ℕ} {σ : ℕ → ℕ} {y : ℕ}
    (hσ : HTN.TaskNetwork.IsoVia σ (cfgNet d) u) (hy : y ∈ d.ids)
    (hu : ∀ q ∈ d.ordList, q.2 ≠ y) :
    HTN.TaskNetwork.IsoVia (σ ∘ id) (cfgNet (progDesc d y)) (u.progress (σ y)) :=
  (Problem.isoVia_of_agree' (agree_progDesc hu).symm).comp (hσ.progress (List.mem_toFinset.2 hy))

/-- **Soundness of a primitive first task.** -/
theorem sound_prim {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)} {μ : Bool × List ℕ}
    (hd : DInv p d) {y a : ℕ} (hy : y ∈ d.ids) (hu : unc d y = true)
    (hl : lblOf d y = (false, a)) (happ : fApp p a s = true)
    (hall : ∀ o ∈ outs p a s, Xg (pos o (progDesc d y) E (false, [])) ∧
      FReach p (pos o (progDesc d y) E (false, [])))
    (hgood : ∃ o ∈ outs p a s, PosStmt p Xg G o (progDesc d y) E μ) :
    PosStmt p Xg G s d E μ := by
  intro u v σ hσ hwu hwv hdj hcont hprog
  have hu' := (unc_iff _ _).1 hu
  have hfirst := IsFirst.isoVia (isFirst_of hd hy hu) hσ
  have hunc := Problem.IsFirst.unconstrained hwu hfirst
  have hU := Problem.unconstrained_seqNet_of hwu hwv hdj hunc
  have hws := Problem.seqNet_wf hwu hwv hdj
  have hα : (Problem.seqNet u v).α (σ y) = Sum.inl a := by
    rw [Problem.seqNet_α hunc.1, hσ.α_eq (List.mem_toFinset.2 hy), cfgNet_label, hl]; rfl
  have hwr := progress_wf hwu hunc
  have hdr : Disjoint (u.progress (σ y)).T v.T :=
    Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdj
  have hisor := iso_prog hσ hy hu'
  have hag := (Problem.progress_seqNet hunc.1 hdj hwv).symm
  obtain ⟨o, ho, hpos⟩ := hgood
  obtain ⟨n, hn⟩ := hpos _ _ _ hisor hwr hwv hdr hcont hprog
  refine ⟨n + 1, .prim hU hα ((fApp_iff _ _ _).1 happ) (fun S' hS' => ?_) (outs_sound ho)
    (hn.isoVia XS_good (Problem.seqNet_wf hwr hwv hdr) (progress_wf hws hU)
      (Problem.isoVia_of_agree' hag))⟩
  obtain ⟨o', ho', rfl⟩ := outs_complete hS'
  obtain ⟨hX, hr⟩ := hall o' ho'
  exact XS_of_stk (Stk.push hX hr hisor hwr hwv hdr hcont) hag

/-- **Soundness of a compound first task.** -/
theorem sound_comp (hp : p.Valid) {s : List ℕ} {d : TnDesc}
    {E : Bool × List (List ℕ)} {μ : Bool × List ℕ} (hd : DInv p d) {y c : ℕ} (hy : y ∈ d.ids)
    (hu : unc d y = true) (hl : lblOf d y = (true, c)) {L : List (List ℕ)} {e : List ℕ}
    (hcall : CallStmt p Xg G c s L e)
    (hconts : ∀ x ∈ L, Xg (pos x (progDesc d y) E (false, [])) ∧
      FReach p (pos x (progDesc d y) E (false, [])))
    (hpos : PosStmt p Xg G e (progDesc d y) E μ) : PosStmt p Xg G s d E μ := by
  intro u v σ hσ hwu hwv hdj hcont hprog
  obtain ⟨m, hm, hmc, hXm, hrm, hposm⟩ := hcall
  have hu' := (unc_iff _ _).1 hu
  have hfirst := IsFirst.isoVia (isFirst_of hd hy hu) hσ
  have hunc := Problem.IsFirst.unconstrained hwu hfirst
  have hU := Problem.unconstrained_seqNet_of hwu hwv hdj hunc
  have hws := Problem.seqNet_wf hwu hwv hdj
  have hwr := progress_wf hwu hunc
  have hdr : Disjoint (u.progress (σ y)).T v.T :=
    Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdj
  have hisor := iso_prog hσ hy hu'
  have hmv := hp.methods m hm
  have hwm : (cfgNet m.2).WF := Problem.wf_of_agree (TnDesc.toTaskNetwork_wf m.2) (agree_tn hmv)
  obtain ⟨w, hww, hwiso, hwdisj⟩ := exists_fresh_iso_copy (cfgNet m.2) hwm (Problem.seqNet u v).T
  obtain ⟨τ, hτ⟩ := hwiso.symm
  have hwdj : Disjoint (u.T ∪ v.T) w.T := hwdisj
  have hwud : Disjoint u.T w.T := Finset.disjoint_of_subset_left Finset.subset_union_left hwdj
  have hwr' : Disjoint w.T (Problem.seqNet (u.progress (σ y)) v).T := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rcases Finset.mem_union.1 hz' with hz' | hz'
    · exact Finset.disjoint_left.1 hwud (Finset.mem_of_mem_erase hz') hz
    · exact Finset.disjoint_left.1 hwdj (Finset.mem_union_right _ hz') hz
  have hseqr := Problem.seqNet_wf hwr hwv hdr
  have hcont' : ∀ x ∈ tgtSet (false, L), Stk p Xg G (Problem.seqNet (u.progress (σ y)) v) x := by
    rintro x (h | ⟨l, hl', rfl⟩)
    · simp at h
    · obtain ⟨hX, hr⟩ := hconts l hl'
      exact Stk.push hX hr hisor hwr hwv hdr hcont
  have hstk : Stk p Xg G (Problem.seqNet w (Problem.seqNet (u.progress (σ y)) v)) {f | f ∈ s} :=
    Stk.push hXm hrm hτ hww hseqr hwr' hcont'
  have hprog' : ∀ x ∈ muSet (false, L) (true, e), ∃ n, p.toProblem.FAttrT G (XS p Xg G) n
      (Problem.seqNet (u.progress (σ y)) v) x := by
    intro x hx
    simp only [muSet, if_true, Set.mem_singleton_iff] at hx
    subst hx
    exact hpos _ _ _ hisor hwr hwv hdr hcont hprog
  obtain ⟨n, hn⟩ := hposm _ _ _ hτ hww hseqr hwr' hcont' hprog'
  -- the decomposition step in `u ; v`
  have hα : (Problem.seqNet u v).α (σ y) = Sum.inr m.toMethod.abstractTask := by
    rw [Problem.seqNet_α hunc.1, hσ.α_eq (List.mem_toFinset.2 hy), cfgNet_label, hl]
    simp [toSum, MethodDesc.toMethod, hmc]
  have hDS : DecompStep p.toProblem.methods (Problem.seqNet u v) (σ y) m.toMethod
      (decomposeWith (Problem.seqNet u v) (σ y) w) :=
    ⟨⟨m, hm, rfl⟩, hU.1, hα, w, hww,
      hwiso.trans (Problem.isoVia_of_agree' (agree_tn hmv).symm).iso, hwdisj, rfl⟩
  have hag : (decomposeWith (Problem.seqNet u v) (σ y) w).Agree
      (Problem.seqNet w (Problem.seqNet (u.progress (σ y)) v)) := by
    have h1 := Problem.decomposeWith_seqNet hunc.1 hdj hwv hww hwdj
    have h2 := seqNet_agree_left (c := v) (Problem.decomposeWith_first hwu hfirst hwud)
    rw [seqNet_assoc] at h2
    exact h1.trans h2
  have hwN : (decomposeWith (Problem.seqNet u v) (σ y) w).WF := decomposeWith_wf hws hww hwdisj
  exact ⟨n + 1, .decomp hU hDS (XS_of_stk hstk hag.symm)
    (hn.isoVia XS_good (hstk.wf) hwN (Problem.isoVia_of_agree' hag.symm))⟩

end Sound

/-! ### Single moves -/

section Intro

variable {p : FProbDesc} {c : ℕ} {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)}
  {μ : Bool × List ℕ} {E' : List (List ℕ)} {e' : List ℕ}

theorem stepX_prim {y : ℕ} (hy : y ∈ d.ids) (hu : unc d y = true) (hl : (lblOf d y).1 = false)
    (ha : fApp p (lblOf d y).2 s = true) {o : List ℕ} (ho : o ∈ outs p (lblOf d y).2 s) :
    stepXf p 0 c s d E μ E' e' (pos o (progDesc d y) E (false, [])) = true := by
  unfold stepXf
  simp only [beq_self_eq_true, cond_true, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true']
  exact Or.inl ⟨y, hy, ⟨⟨hu, hl⟩, ha⟩, o, ho, rfl⟩

theorem stepZ_prim {y : ℕ} (hy : y ∈ d.ids) (hu : unc d y = true) (hl : (lblOf d y).1 = false)
    (ha : fApp p (lblOf d y).2 s = true) {o : List ℕ} (ho : o ∈ outs p (lblOf d y).2 s) :
    stepZf p 0 c s d E μ E' e' (pos o (progDesc d y) E μ) = true := by
  unfold stepZf
  simp only [beq_self_eq_true, cond_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true']
  exact ⟨y, hy, ⟨⟨hu, hl⟩, ha⟩, o, ho, rfl⟩

theorem stepX_comp {y : ℕ} (hy : y ∈ d.ids) (hu : unc d y = true) (hl : (lblOf d y).1 = true)
    {L : List (List ℕ)} {e : List ℕ} (hw : wfStates p L = true) (he : e ∈ L) :
    stepXf p 0 c s d E μ E' e' (1, (lblOf d y).2, s, progDesc d y, E, μ, L, e) = true := by
  unfold stepXf
  simp only [beq_self_eq_true, cond_true, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Bool.not_eq_true']
  exact Or.inr ⟨y, hy, ⟨⟨⟨hu, hl⟩, rfl⟩, hw⟩, he⟩

theorem stepX_split_call : stepXf p 1 c s d E μ E' e' (call c s E' e') = true := by
  unfold stepXf; simp

theorem stepX_split_pos {x : List ℕ} (hx : x ∈ E') :
    stepXf p 1 c s d E μ E' e' (pos x d E (false, [])) = true := by
  unfold stepXf
  rw [show ((1 : ℕ) == 0) = false from rfl, show ((1 : ℕ) == 1) = true from rfl]
  simp only [cond_false, cond_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
  exact Or.inr ⟨x, hx, rfl⟩

theorem stepZ_split_call : stepZf p 1 c s d E μ E' e' (call c s E' e') = true := by
  unfold stepZf; simp

theorem stepZ_split_pos : stepZf p 1 c s d E μ E' e' (pos e' d E μ) = true := by
  unfold stepZf
  rw [show ((1 : ℕ) == 0) = false from rfl, show ((1 : ℕ) == 1) = true from rfl]
  simp

theorem stepX_call {m : MethodDesc} (hm : m ∈ p.methods) (hc : m.1 = c) :
    stepXf p 2 c s d E μ E' e' (callM c s m.2 E.2 e') = true := by
  unfold stepXf
  rw [show ((2 : ℕ) == 0) = false from rfl, show ((2 : ℕ) == 1) = false from rfl,
    show ((2 : ℕ) == 2) = true from rfl]
  simp only [cond_false, cond_true, decide_eq_true_eq, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨m, ⟨hm, hc⟩, rfl⟩

theorem stepX_callM : stepXf p 3 c s d E μ E' e' (pos s d (false, E.2) (false, [])) = true := by
  unfold stepXf
  rw [show ((3 : ℕ) == 0) = false from rfl, show ((3 : ℕ) == 1) = false from rfl,
    show ((3 : ℕ) == 2) = false from rfl, show ((3 : ℕ) == 3) = true from rfl]
  simp

theorem stepZ_callM : stepZf p 3 c s d E μ E' e' (pos s d (false, E.2) (true, e')) = true := by
  unfold stepZf
  rw [show ((3 : ℕ) == 0) = false from rfl, show ((3 : ℕ) == 1) = false from rfl,
    show ((3 : ℕ) == 3) = true from rfl]
  simp

theorem fKd_two {k : ℕ} (h : fKd (p, (k, c, s, d, E, μ, E', e')) = 2) :
    k = 0 ∧ primFirst p s d = true := by
  unfold fKd at h
  rcases k with _ | _ | _ | _ | k
  · cases hp : primFirst p s d <;> cases hc : compFirst d <;> simp_all
  · simp at h
  · simp at h
  · simp at h
  · simp at h

theorem fKd_one {k : ℕ} (h : fKd (p, (k, c, s, d, E, μ, E', e')) = 1) :
    (k = 0 ∧ primFirst p s d = false ∧ compFirst d = true) ∨ k = 2 := by
  unfold fKd at h
  rcases k with _ | _ | _ | _ | k
  · cases hp : primFirst p s d <;> cases hc : compFirst d <;> simp_all
  · simp at h
  · exact Or.inr rfl
  · simp at h
  · simp at h

theorem fKd_three {k : ℕ} (h : fKd (p, (k, c, s, d, E, μ, E', e')) = 3) : k = 1 ∨ k = 3 := by
  unfold fKd at h
  rcases k with _ | _ | _ | _ | k
  · cases hp : primFirst p s d <;> cases hc : compFirst d <;> simp_all
  · exact Or.inl rfl
  · simp at h
  · exact Or.inr rfl
  · simp at h

theorem primFirst_iff : primFirst p s d = true ↔ ∃ y ∈ d.ids, unc d y = true ∧
    (lblOf d y).1 = false ∧ fApp p (lblOf d y).2 s = true := by
  simp [primFirst, List.any_eq_true, and_assoc]

theorem compFirst_iff : compFirst d = true ↔ ∃ y ∈ d.ids, unc d y = true ∧ (lblOf d y).1 = true := by
  simp [compFirst, List.any_eq_true]

end Intro

/-! ### The soundness induction -/

section SoundMain

variable {p : FProbDesc} {Xg : FCfg → Prop} {G : Set (Set ℕ)}

theorem uniq_first {d : TnDesc} (hd : DInv p d) {y y' : ℕ} (hy : y ∈ d.ids) (hu : unc d y = true)
    (hy' : y' ∈ d.ids) (hu' : unc d y' = true) : y' = y :=
  Problem.IsFirst.eq (isFirst_of hd hy hu) (unconstrained_cfgNet hy' ((unc_iff _ _).1 hu'))

/-- **Soundness of the summary game.** -/
theorem sound (hp : p.Valid) (hTO : FClass.TO p.toProblem) {B : ℕ}
    (hsz : ∀ g, FReach p g → sz g ≤ B) {g : FCfg}
    (hw : B2Attr B fAcc fKd fStepX fStepZ p Xg g) : FReach p g → Mot p Xg G g := by
  induction hw with
  | @acc c _ ha =>
    intro _
    obtain ⟨k, c, s, d, E, μ, E', e'⟩ := c
    simp only [fAcc, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at ha
    obtain ⟨⟨rfl, hids⟩, hin⟩ := ha
    refine ⟨fun _ => ?_, fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp)⟩
    intro u v σ hσ hwu hwv hdj _ hprog
    have hue : u.T = ∅ := hσ.empty (by simp [cfgNet, hids])
    have hx : {f | f ∈ s} ∈ muSet E μ := by
      unfold muSet
      cases hμ : μ.1
      · simp only [hμ, cond_false] at hin
        simpa using (inTgt_iff _ _).1 hin
      · simp only [hμ, cond_true] at hin
        simp only [if_true, Set.mem_singleton_iff]
        exact ((sameSet_iff _ _).1 hin).symm
    obtain ⟨n, hn⟩ := hprog _ hx
    exact ⟨n, hn.isoVia XS_good hwv (Problem.seqNet_wf hwu hwv hdj)
      (Problem.isoVia_of_agree' (Problem.seqNet_empty hwu hue).symm)⟩
  | @ex c c' _ hk _ hs hX _ ih =>
    intro hr
    have ih' := ih (hr.tail (Or.inl hs))
    have hinv := fInv_of_reach hp hTO hr
    obtain ⟨k, c, s, d, E, μ, E', e'⟩ := c
    have hd := hinv.d
    simp only at hd
    change stepXf p k c s d E μ E' e' c' = true at hs
    rcases fKd_one hk with ⟨rfl, hpf, -⟩ | rfl
    · refine ⟨fun _ => ?_, fun h => absurd h (by simp), fun h => absurd h (by simp),
        fun h => absurd h (by simp)⟩
      rcases stepX_cases hs with
        ⟨-, ⟨y, hy, hu, hl, ha, -⟩ | ⟨y, hy, hu, hl, L, e, rfl, -, -⟩⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (primFirst_iff.2 ⟨y, hy, hu, hl, ha⟩) (by simp [hpf])
      · obtain ⟨-, h2, -, -⟩ := ih'
        obtain ⟨hcall, hconts, hpos⟩ := h2 rfl
        exact sound_comp hp hd hy hu (Prod.ext hl rfl) hcall hconts hpos
      · cases h1
      · cases h1
      · cases h1
    · refine ⟨fun h => absurd h (by simp), fun h => absurd h (by simp), fun _ => ?_,
        fun h => absurd h (by simp)⟩
      rcases stepX_cases hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, m, hm, hc, rfl⟩ | ⟨h1, -⟩
      · cases h1
      · cases h1
      · obtain ⟨-, -, -, h4⟩ := ih'
        obtain ⟨hX', hr', hpos⟩ := h4 rfl
        exact ⟨m, hm, hc, hX', hr', hpos⟩
      · cases h1
  | @fair c c' _ hk hall _ hs _ ih =>
    intro hr
    have ih' := ih (hr.tail (Or.inr hs))
    have hinv := fInv_of_reach hp hTO hr
    obtain ⟨k, c, s, d, E, μ, E', e'⟩ := c
    have hd := hinv.d
    simp only at hd
    change stepZf p k c s d E μ E' e' c' = true at hs
    obtain ⟨rfl, hpf⟩ := fKd_two hk
    refine ⟨fun _ => ?_, fun h => absurd h (by simp), fun h => absurd h (by simp),
      fun h => absurd h (by simp)⟩
    obtain ⟨y, hy, hu, hl, ha⟩ := primFirst_iff.1 hpf
    have hall' : ∀ o ∈ outs p (lblOf d y).2 s, Xg (pos o (progDesc d y) E (false, [])) ∧
        FReach p (pos o (progDesc d y) E (false, [])) := by
      intro o ho
      have hs' : fStepX (p, (0, c, s, d, E, μ, E', e'), pos o (progDesc d y) E (false, [])) =
          true := stepX_prim hy hu hl ha ho
      exact ⟨hall _ (hsz _ (hr.tail (Or.inl hs'))) hs', hr.tail (Or.inl hs')⟩
    rcases stepZ_cases hs with ⟨-, y', hy', hu', -, -, o, ho, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · obtain rfl := uniq_first hd hy hu hy' hu'
      exact sound_prim hd hy hu (Prod.ext hl rfl) ha hall' ⟨o, ho, ih'.1 rfl⟩
    · cases h1
    · cases h1
  | @conj c _ hk hall _ ih =>
    intro hr
    obtain ⟨k, c, s, d, E, μ, E', e'⟩ := c
    rcases fKd_three hk with rfl | rfl
    · refine ⟨fun h => absurd h (by simp), fun _ => ⟨?_, ?_, ?_⟩, fun h => absurd h (by simp),
        fun h => absurd h (by simp)⟩
      · have hs : fStepZ (p, (1, c, s, d, E, μ, E', e'), call c s E' e') = true :=
          stepZ_split_call
        exact (ih _ (hsz _ (hr.tail (Or.inr hs))) hs (hr.tail (Or.inr hs))).2.2.1 rfl
      · intro x hx
        have hs : fStepX (p, (1, c, s, d, E, μ, E', e'), pos x d E (false, [])) = true :=
          stepX_split_pos hx
        exact ⟨hall _ (hsz _ (hr.tail (Or.inl hs))) hs, hr.tail (Or.inl hs)⟩
      · have hs : fStepZ (p, (1, c, s, d, E, μ, E', e'), pos e' d E μ) = true := stepZ_split_pos
        exact (ih _ (hsz _ (hr.tail (Or.inr hs))) hs (hr.tail (Or.inr hs))).1 rfl
    · refine ⟨fun h => absurd h (by simp), fun h => absurd h (by simp),
        fun h => absurd h (by simp), fun _ => ⟨?_, ?_, ?_⟩⟩
      · have hs : fStepX (p, (3, c, s, d, E, μ, E', e'), pos s d (false, E.2) (false, [])) =
            true := stepX_callM
        exact hall _ (hsz _ (hr.tail (Or.inl hs))) hs
      · have hs : fStepX (p, (3, c, s, d, E, μ, E', e'), pos s d (false, E.2) (false, [])) =
            true := stepX_callM
        exact hr.tail (Or.inl hs)
      · have hs : fStepZ (p, (3, c, s, d, E, μ, E', e'), pos s d (false, E.2) (true, e')) =
            true := stepZ_callM
        exact (ih _ (hsz _ (hr.tail (Or.inr hs))) hs (hr.tail (Or.inr hs))).1 rfl

/-- **Stacks are in the attractor.** -/
theorem stk_attr (hp : p.Valid) (hTO : FClass.TO p.toProblem) {B : ℕ}
    (hsz : ∀ g, FReach p g → sz g ≤ B) (hXa : ∀ g, Xg g → B2Attr B fAcc fKd fStepX fStepZ p Xg g)
    {N : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ} (h : Stk p Xg G N S) :
    ∃ n, p.toProblem.FAttrT G (XS p Xg G) n N S := by
  induction h with
  | nil _ he hx => exact ⟨0, .goal he hx⟩
  | @push u v s d E σ hg hr hσ hu hv hd hc ih =>
    exact (sound (G := G) hp hTO hsz (hXa _ hg) hr).1 rfl u v σ hσ hu hv hd hc ih

/-- **Soundness of the fair game on descriptions.** -/
theorem fairWin_of_b2Win (hp : p.Valid) (hTO : FClass.TO p.toProblem) {B : ℕ}
    (hsz : ∀ g, FReach p g → sz g ≤ B) (hw : B2Win B fAcc fKd fStepX fStepZ p (fInit0 p)) :
    p.toProblem.FairWinT Set.univ (cfgNet (initF p).2) {f | f ∈ p.init.dedup} := by
  obtain ⟨Xg, hX₀, hXa⟩ := hw
  have hd₀ := dInv_init hp hTO
  have hstk : Stk p Xg Set.univ (Problem.seqNet (cfgNet (initF p).2) emptyTN)
      {f | f ∈ p.init.dedup} :=
    Stk.push hX₀ .refl (HTN.TaskNetwork.IsoVia.refl _) hd₀.wf emptyTN_wf (by simp [emptyTN])
      fun x _ => Stk.nil emptyTN_wf rfl trivial
  refine ⟨XS p Xg Set.univ, XS_good,
    XS_of_stk hstk (seqNet_nil_right emptyTN_wf rfl), fun tn S h => ?_⟩
  obtain ⟨hw, N₀, σ, hN, hσ⟩ := h
  obtain ⟨n, hn⟩ := stk_attr hp hTO hsz hXa hN
  exact ⟨n, hn.isoVia XS_good hN.wf hw hσ⟩

end SoundMain

/-! ## Completeness -/

section Complete

variable {p : FProbDesc}

theorem FAttrT.restrict_ff {G : Set (Set ℕ)} {X : Problem.NSet ℕ ℕ ℕ ℕ} {n : ℕ}
    {N : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ} (h : p.toProblem.FAttrT G X n N S)
    (hS : S ⊆ {f | f ∈ ffacts p}) :
    p.toProblem.FAttrT {S' | S' ∈ G ∧ S' ⊆ {f | f ∈ ffacts p}}
      (fun tn S' => X tn S' ∧ S' ⊆ {f | f ∈ ffacts p}) n N S := by
  induction h with
  | goal he hs => exact .goal he ⟨hs, hS⟩
  | prim hu hα happ hall hs₀ _ ih =>
    exact .prim hu hα happ (fun s' hs' => ⟨hall s' hs', outcome_sub hS hs'⟩) hs₀
      (ih (outcome_sub hS hs₀))
  | decomp hu hd hX _ ih => exact .decomp hu hd ⟨hX, hS⟩ (ih hS)

theorem FAttrT.exists_goal {G : Set (Set ℕ)} {X : Problem.NSet ℕ ℕ ℕ ℕ} {n : ℕ}
    {N : TaskNetwork ℕ ℕ ℕ} {S : Set ℕ} (h : p.toProblem.FAttrT G X n N S) : ∃ x, x ∈ G := by
  induction h with
  | goal _ hs => exact ⟨_, hs⟩
  | prim _ _ _ _ _ _ ih => exact ih
  | decomp _ _ _ _ ih => exact ih

/-- The semantic content of a position. -/
def SemP (p : FProbDesc) (s : List ℕ) (d : TnDesc) (E : Bool × List (List ℕ))
    (μ : Bool × List ℕ) : Prop :=
  ∃ X : Problem.NSet ℕ ℕ ℕ ℕ, Problem.NGood X ∧
    (∀ tn S, X tn S → ∃ n, p.toProblem.FAttrT (tgtSet E) X n tn S) ∧
    X (cfgNet d) {f | f ∈ s} ∧
    (μ.1 = true → ∃ n, p.toProblem.FAttrT (muSet E μ) X n (cfgNet d) {f | f ∈ s})

/-- The semantic content of a call. -/
def SemCall (p : FProbDesc) (c : ℕ) (s : List ℕ) (L : List (List ℕ)) (e : List ℕ) : Prop :=
  ∃ m ∈ p.methods, m.1 = c ∧ SemP p s m.2 (false, L) (true, e)

/-- The semantic content of a configuration. -/
def SemC (p : FProbDesc) (g : FCfg) : Prop :=
  (g.1 = 0 → SemP p g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1) ∧
  (g.1 = 1 → SemCall p g.2.1 g.2.2.1 g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2 ∧
    (∀ x ∈ g.2.2.2.2.2.2.1, SemP p x g.2.2.2.1 g.2.2.2.2.1 (false, [])) ∧
    SemP p g.2.2.2.2.2.2.2 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1) ∧
  (g.1 = 2 → SemCall p g.2.1 g.2.2.1 g.2.2.2.2.1.2 g.2.2.2.2.2.2.2) ∧
  (g.1 = 3 → SemP p g.2.2.1 g.2.2.2.1 (false, g.2.2.2.2.1.2) (true, g.2.2.2.2.2.2.2))

/-- The set of the completeness construction. -/
def Xc (p : FProbDesc) (g : FCfg) : Prop := FReach p g ∧ SemC p g

theorem semP_mu_any {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)}
    {X : Problem.NSet ℕ ℕ ℕ ℕ} (hXa : ∀ tn S, X tn S → ∃ n, p.toProblem.FAttrT (tgtSet E) X n tn S)
    (hX : X (cfgNet d) {f | f ∈ s}) :
    ∃ n, p.toProblem.FAttrT (muSet E (false, [])) X n (cfgNet d) {f | f ∈ s} := by
  simpa [muSet] using hXa _ _ hX

theorem acc_of_mem {k c : ℕ} {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)}
    {μ : Bool × List ℕ} {E' : List (List ℕ)} {e' : List ℕ} (hk : k = 0) (hids : d.ids = [])
    (h : {f | f ∈ s} ∈ muSet E μ) : fAcc (p, (k, c, s, d, E, μ, E', e')) = true := by
  subst hk
  simp only [fAcc, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff]
  refine ⟨hids, ?_⟩
  unfold muSet at h
  cases hμ : μ.1
  · simp only [hμ, Bool.false_eq_true, if_false] at h
    simpa using (inTgt_iff _ _).2 h
  · simp only [hμ, if_true, Set.mem_singleton_iff] at h
    simpa using (sameSet_iff _ _).2 h.symm

variable (hp : p.Valid) (hTO : FClass.TO p.toProblem) {B : ℕ}
  (hsz : ∀ g, FReach p g → sz g ≤ B)
include hp hTO hsz

/-- **Completeness for positions**, by induction on the rank. -/
theorem cpos (n : ℕ) : ∀ {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)}
    {μ : Bool × List ℕ} {X : Problem.NSet ℕ ℕ ℕ ℕ}, FReach p (pos s d E μ) → Problem.NGood X →
    (∀ tn S, X tn S → ∃ n, p.toProblem.FAttrT (tgtSet E) X n tn S) →
    X (cfgNet d) {f | f ∈ s} →
    p.toProblem.FAttrT (muSet E μ) X n (cfgNet d) {f | f ∈ s} →
    B2Attr B fAcc fKd fStepX fStepZ p (Xc p) (pos s d E μ) := by
  classical
  have hM := (FProbDesc.toProblem_wf hp).methods
  induction n with
  | zero =>
    intro s d E μ X hr hX hXa hXd h
    have hinv := fInv_of_reach hp hTO hr
    have hd : DInv p d := hinv.d
    by_cases hids : d.ids = []
    · exact B2Attr.acc (hsz _ hr) (acc_of_mem rfl hids (h.of_empty (by simp [cfgNet, hids])))
    · exfalso
      cases h with
      | goal he => exact hids (by simpa [cfgNet] using he)
  | succ k ih =>
    intro s d E μ X hr hX hXa hXd h
    have hinv := fInv_of_reach hp hTO hr
    have hd : DInv p d := hinv.d
    have hst : SInv p s := hinv.st
    have hS : {f | f ∈ s} ⊆ {f | f ∈ ffacts p} := fun f hf => hst.2 f hf
    by_cases hids : d.ids = []
    · exact B2Attr.acc (hsz _ hr) (acc_of_mem rfl hids (h.of_empty (by simp [cfgNet, hids])))
    obtain ⟨y, hyU⟩ := TaskNetwork.exists_unconstrained hd.wf (by
      obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hids
      exact ⟨z, List.mem_toFinset.2 hz⟩)
    obtain ⟨hy, hu⟩ := unc_of_unconstrained hd hyU
    have hfirst := isFirst_of hd hy hu
    have hu' := (unc_iff _ _).1 hu
    have hwp := TaskNetwork.progress_wf hd.wf hyU
    have hagp := agree_progDesc hu'
    have hdp := hd.prog hy hu'
    rcases hl : lblOf d y with ⟨_ | _, a⟩
    · -- primitive first task
      cases h with
      | goal he => exact absurd (by simpa [cfgNet] using he) hids
      | decomp hu₂ hd₂ =>
        obtain rfl := Problem.IsFirst.eq hfirst hu₂
        have := hd₂.2.2.1
        rw [cfgNet_label, hl] at this
        cases this
      | @prim _ _ _ t a' hu₂ hα happ hall s₀ hs₀ h₀ =>
        obtain rfl := Problem.IsFirst.eq hfirst hu₂
        have ha' : a' = a := by
          rw [cfgNet_label, hl] at hα; exact (Sum.inl_injective hα).symm
        subst ha'
        have hpf : primFirst p s d = true :=
          primFirst_iff.2 ⟨t, hy, hu, by rw [hl], by rw [hl]; exact (fApp_iff _ _ _).2 happ⟩
        have hkd : fKd (p, pos s d E μ) = 2 := by simp [fKd, pos, hpf]
        obtain ⟨o₀, ho₀, rfl⟩ := outs_complete hs₀
        have hs₀' : fStepZ (p, pos s d E μ, pos o₀ (progDesc d t) E μ) = true :=
          stepZ_prim hy hu (by rw [hl]) (by rw [hl]; exact (fApp_iff _ _ _).2 happ)
            (by rw [hl]; exact ho₀)
        refine B2Attr.fair (hsz _ hr) hkd (fun c'' _ hs'' => ?_) (hsz _ (hr.tail (Or.inr hs₀')))
          hs₀' (ih (hr.tail (Or.inr hs₀')) hX hXa
            (hX.2 _ _ _ _ (hall _ hs₀) hdp.wf (Problem.isoVia_of_agree' hagp))
            (h₀.isoVia hX hwp hdp.wf (Problem.isoVia_of_agree' hagp)))
        change stepXf p 0 0 s d E μ [] [] c'' = true at hs''
        rcases stepX_cases hs'' with
          ⟨-, ⟨y', hy', hu₃, -, -, o, ho, rfl⟩ | ⟨y', hy', hu₃, hl₃, -, -, -, -, -⟩⟩ |
          ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · obtain rfl := uniq_first hd hy hu hy' hu₃
          rw [hl] at ho
          refine ⟨hr.tail (Or.inl hs''), ?_, fun h => absurd h (by simp [pos]),
            fun h => absurd h (by simp [pos]), fun h => absurd h (by simp [pos])⟩
          intro _
          refine ⟨X, hX, hXa, hX.2 _ _ _ _ (hall _ (outs_sound ho)) hdp.wf
            (Problem.isoVia_of_agree' hagp), fun h => absurd h (by simp [pos])⟩
        · obtain rfl := uniq_first hd hy hu hy' hu₃
          rw [hl] at hl₃; cases hl₃
        · cases h1
        · cases h1
        · cases h1
    · -- compound first task
      cases h with
      | goal he => exact absurd (by simpa [cfgNet] using he) hids
      | prim hu₂ hα =>
        obtain rfl := Problem.IsFirst.eq hfirst hu₂
        rw [cfgNet_label, hl] at hα; cases hα
      | @decomp _ _ N' _ t m hu₂ hd₂ hXN h' =>
        obtain rfl := Problem.IsFirst.eq hfirst hu₂
        obtain ⟨hmM, -, hαt, w, hww, hwiso, hwdisj, rfl⟩ := hd₂
        obtain ⟨m', hm', rfl⟩ := (mem_methods_iff (p := p)).1 hmM
        have hc' : m'.1 = a := by
          rw [cfgNet_label, hl] at hαt
          exact (Sum.inr_injective hαt).symm
        set v := (cfgNet d).progress t with hv
        have hdisj' : Disjoint w.T v.T := by
          rw [Finset.disjoint_left]
          intro z hz hz'
          exact Finset.disjoint_left.1 hwdisj (Finset.mem_of_mem_erase hz') hz
        have hag := Problem.decomposeWith_first hd.wf hfirst hwdisj
        have hwN : (decomposeWith (cfgNet d) t w).WF := decomposeWith_wf hd.wf hww hwdisj
        have hXs : X (Problem.seqNet w v) {f | f ∈ s} :=
          hX.2 _ _ _ _ hXN (Problem.seqNet_wf hww hwp hdisj') (Problem.isoVia_of_agree' hag)
        have hrank := h'.isoVia hX hwN (Problem.seqNet_wf hww hwp hdisj')
          (Problem.isoVia_of_agree' hag)
        obtain ⟨-, e₀, hreach, hXv, hcont⟩ :=
          Problem.FAttrT.split hX hwp k hww hdisj' hXs hrank
        -- the restricted projected set
        set ff : Set ℕ := {f | f ∈ ffacts p} with hff
        let Xr : Problem.NSet ℕ ℕ ℕ ℕ := fun tn S' => Problem.projSet X v tn S' ∧ S' ⊆ ff
        have hXr : Problem.NGood Xr := by
          refine ⟨fun _ _ h => h.1.1, fun tn tn' S' σ h hw' hσ => ⟨?_, h.2⟩⟩
          exact Problem.projSet_good.2 _ _ _ _ h.1 hw' hσ
        set L := ((ffacts p).dedup.sublists).filter fun l =>
          decide (X (cfgNet (progDesc d t)) {f | f ∈ l}) with hL
        have hmemL : ∀ x : Set ℕ, x ⊆ ff → X v x →
            ∃ l ∈ L, x = {f | f ∈ l} := by
          intro x hxf hxv
          have hset : {f | f ∈ (ffacts p).dedup.filter fun f => decide (f ∈ x)} = x := by
            ext f
            simp only [Set.mem_setOf_eq, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
            exact ⟨fun h => h.2, fun h => ⟨hxf h, h⟩⟩
          refine ⟨_, List.mem_filter.2 ⟨List.mem_sublists.2 List.filter_sublist, ?_⟩, hset.symm⟩
          rw [hset]
          simpa using hX.2 _ _ _ _ hxv hdp.wf (Problem.isoVia_of_agree' hagp)
        have hXra : ∀ tn S', Xr tn S' → ∃ n, p.toProblem.FAttrT (tgtSet (false, L)) Xr n tn S' := by
          intro tn S' h
          obtain ⟨n, hn⟩ := Problem.projSet_attr hX hXa hwp tn S' h.1
          refine ⟨n, ((FAttrT.restrict_ff hn h.2).monoG (G' := tgtSet (false, L))
            fun x hx => ?_)⟩
          obtain ⟨hxv, hxf⟩ := hx
          obtain ⟨l, hl', rfl⟩ := hmemL x hxf hxv
          exact Or.inr ⟨l, hl', rfl⟩
        have hreach' := FAttrT.restrict_ff (p := p) hreach hS
        obtain ⟨x₀, hx₀, hx₀f⟩ := FAttrT.exists_goal hreach'
        obtain rfl : x₀ = e₀ := hx₀
        obtain ⟨l₀, hl₀, he₀⟩ := hmemL x₀ hx₀f hXv
        subst he₀
        -- the method network
        have hmv := hp.methods m' hm'
        have hwm : (cfgNet m'.2).WF :=
          Problem.wf_of_agree (TnDesc.toTaskNetwork_wf m'.2) (agree_tn hmv)
        obtain ⟨τ, hτ⟩ := hwiso.trans (Problem.isoVia_of_agree' (agree_tn hmv)).iso
        have hXrm : Xr (cfgNet m'.2) {f | f ∈ s} :=
          hXr.2 _ _ _ _ ⟨Problem.projSet_mem hww hdisj' hXs, hS⟩ hwm hτ
        have hrankm : p.toProblem.FAttrT (muSet (false, L) (true, l₀)) Xr k (cfgNet m'.2)
            {f | f ∈ s} := by
          simp only [muSet, if_true]
          refine ((hreach'.monoG (G' := {{f | f ∈ l₀}}) fun x hx => ?_).isoVia hXr hww hwm hτ)
          exact hx.1
        have hsemCall : SemCall p a s L l₀ :=
          ⟨m', hm', hc', Xr, hXr, hXra, hXrm, fun _ => ⟨k, hrankm⟩⟩
        have hsemConts : ∀ x ∈ L, SemP p x (progDesc d t) E (false, []) := by
          intro x hx
          have hx' := (List.mem_filter.1 hx).2
          simp only [decide_eq_true_eq] at hx'
          exact ⟨X, hX, hXa, hx', fun h => absurd h (by simp)⟩
        have hXe : X (cfgNet (progDesc d t)) {f | f ∈ l₀} :=
          hX.2 _ _ _ _ hXv hdp.wf (Problem.isoVia_of_agree' hagp)
        have hranke : p.toProblem.FAttrT (muSet E μ) X k (cfgNet (progDesc d t)) {f | f ∈ l₀} :=
          hcont.isoVia hX hwp hdp.wf (Problem.isoVia_of_agree' hagp)
        have hsemE : SemP p l₀ (progDesc d t) E μ :=
          ⟨X, hX, hXa, hXe, fun _ => ⟨k, hranke⟩⟩
        -- the moves
        have hwL : wfStates p L = true := by
          rw [wfStates_iff]
          refine ⟨sz_sublists_le p _, fun l hl' => ?_⟩
          have hsub := List.mem_sublists.1 (List.mem_filter.1 hl').1
          exact ⟨(List.nodup_dedup _).sublist hsub,
            fun f hf => List.mem_dedup.1 (hsub.subset hf)⟩
        have hls : lblOf d t = (true, a) := hl
        set g₁ : FCfg := (1, a, s, progDesc d t, E, μ, L, l₀) with hg₁
        have hs₁ : fStepX (p, pos s d E μ, g₁) = true := by
          have := stepX_comp (p := p) (c := 0) (s := s) (μ := μ) (E' := []) (e' := []) (E := E) hy hu
            (by rw [hls]) hwL hl₀
          rw [hls] at this
          exact this
        have hr₁ := hr.tail (Or.inl hs₁)
        have hpf : primFirst p s d = false := by
          by_contra hc
          simp only [Bool.not_eq_false] at hc
          obtain ⟨y', hy', hu₃, hl₃, -⟩ := primFirst_iff.1 hc
          obtain rfl := uniq_first hd hy hu hy' hu₃
          rw [hls] at hl₃; cases hl₃
        have hcf : compFirst d = true := compFirst_iff.2 ⟨t, hy, hu, by rw [hls]⟩
        have hkd : fKd (p, pos s d E μ) = 1 := by simp [fKd, pos, hpf, hcf]
        -- the call and its method
        have hsc : fStepZ (p, g₁, call a s L l₀) = true := stepZ_split_call
        have hrc := hr₁.tail (Or.inr hsc)
        have hsm : fStepX (p, call a s L l₀, callM a s m'.2 L l₀) = true :=
          stepX_call (E := (false, L)) hm' hc'
        have hrm := hrc.tail (Or.inl hsm)
        have hsmp : fStepX (p, callM a s m'.2 L l₀, pos s m'.2 (false, L) (false, [])) = true :=
          stepX_callM (E := (false, L))
        have hsmz : fStepZ (p, callM a s m'.2 L l₀, pos s m'.2 (false, L) (true, l₀)) = true :=
          stepZ_callM (E := (false, L))
        have hXcM : Xc p (callM a s m'.2 L l₀) :=
          ⟨hrm, fun h => absurd h (by simp [callM]), fun h => absurd h (by simp [callM]),
            fun h => absurd h (by simp [callM]), fun _ => ⟨Xr, hXr, hXra, hXrm, fun _ => ⟨k, hrankm⟩⟩⟩
        have hBM : B2Attr B fAcc fKd fStepX fStepZ p (Xc p) (callM a s m'.2 L l₀) := by
          refine B2Attr.conj (hsz _ hrm) (by simp [fKd, callM]) (fun c'' _ hs'' => ?_)
            (fun c'' _ hs'' => ?_)
          · change stepXf p 3 a s m'.2 (false, L) (false, []) [] l₀ c'' = true at hs''
            rcases stepX_cases hs'' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩
            · cases h1
            · cases h1
            · cases h1
            · refine ⟨hrm.tail (Or.inl hs''), fun _ => ⟨Xr, hXr, hXra, hXrm,
                fun h => absurd h (by simp [pos])⟩, fun h => absurd h (by simp [pos]),
                fun h => absurd h (by simp [pos]), fun h => absurd h (by simp [pos])⟩
          · change stepZf p 3 a s m'.2 (false, L) (false, []) [] l₀ c'' = true at hs''
            rcases stepZ_cases hs'' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩
            · cases h1
            · cases h1
            · exact ih (hrm.tail (Or.inr hs'')) hXr hXra hXrm hrankm
        have hXcC : Xc p (call a s L l₀) :=
          ⟨hrc, fun h => absurd h (by simp [call]), fun h => absurd h (by simp [call]),
            fun _ => hsemCall, fun h => absurd h (by simp [call])⟩
        have hBC : B2Attr B fAcc fKd fStepX fStepZ p (Xc p) (call a s L l₀) :=
          B2Attr.ex (hsz _ hrc) (by simp [fKd, call]) (hsz _ hrm) hsm hXcM hBM
        -- the continuation in the target exit
        have hse : fStepZ (p, g₁, pos l₀ (progDesc d t) E μ) = true := stepZ_split_pos
        have hre := hr₁.tail (Or.inr hse)
        have hBE := ih hre hX hXa hXe hranke
        -- the split
        have hXc₁ : Xc p g₁ :=
          ⟨hr₁, fun h => absurd h (by simp [hg₁]), fun _ => ⟨hsemCall, hsemConts, hsemE⟩,
            fun h => absurd h (by simp [hg₁]), fun h => absurd h (by simp [hg₁])⟩
        refine B2Attr.ex (hsz _ hr) hkd (hsz _ hr₁) hs₁ hXc₁ ?_
        refine B2Attr.conj (hsz _ hr₁) (by simp [fKd, hg₁]) (fun c'' _ hs'' => ?_)
          (fun c'' _ hs'' => ?_)
        · change stepXf p 1 a s (progDesc d t) E μ L l₀ c'' = true at hs''
          rcases stepX_cases hs'' with ⟨h1, -⟩ | ⟨-, rfl | ⟨x, hx, rfl⟩⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · cases h1
          · exact hXcC
          · exact ⟨hr₁.tail (Or.inl hs''), fun _ => hsemConts x hx,
              fun h => absurd h (by simp [pos]), fun h => absurd h (by simp [pos]),
              fun h => absurd h (by simp [pos])⟩
          · cases h1
          · cases h1
        · change stepZf p 1 a s (progDesc d t) E μ L l₀ c'' = true at hs''
          rcases stepZ_cases hs'' with ⟨h1, -⟩ | ⟨-, rfl | rfl⟩ | ⟨h1, -⟩
          · cases h1
          · exact hBC
          · exact hBE
          · cases h1

end Complete

section Complete2

variable {p : FProbDesc}

theorem reach_pos_shape {g : FCfg} (h : FReach p g) (hk : g.1 = 0) :
    ∃ s d E μ, g = pos s d E μ := by
  induction h with
  | refl => exact ⟨_, _, _, _, rfl⟩
  | @tail g₁ g₂ _ hs _ =>
    obtain ⟨k, c, s, d, E, μ, E', e'⟩ := g₁
    rcases hs with hs | hs
    · change stepXf p k c s d E μ E' e' g₂ = true at hs
      rcases stepX_cases hs with ⟨-, ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl, _, _⟩⟩ |
        ⟨-, rfl | ⟨_, _, rfl⟩⟩ | ⟨-, _, _, _, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨_, _, _, _, rfl⟩
      · simp at hk
      · simp [call] at hk
      · exact ⟨_, _, _, _, rfl⟩
      · simp [callM] at hk
      · exact ⟨_, _, _, _, rfl⟩
    · change stepZf p k c s d E μ E' e' g₂ = true at hs
      rcases stepZ_cases hs with ⟨-, _, _, _, _, _, _, _, rfl⟩ | ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩
      · exact ⟨_, _, _, _, rfl⟩
      · simp [call] at hk
      · exact ⟨_, _, _, _, rfl⟩
      · exact ⟨_, _, _, _, rfl⟩

variable (hp : p.Valid) (hTO : FClass.TO p.toProblem) {B : ℕ}
  (hsz : ∀ g, FReach p g → sz g ≤ B)
include hp hTO hsz

theorem semP_attr {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)} {μ : Bool × List ℕ}
    (hr : FReach p (pos s d E μ)) (h : SemP p s d E μ) :
    B2Attr B fAcc fKd fStepX fStepZ p (Xc p) (pos s d E μ) := by
  obtain ⟨X, hX, hXa, hXd, hμ⟩ := h
  cases hm : μ.1
  · obtain ⟨n, hn⟩ := hXa _ _ hXd
    exact cpos hp hTO hsz n hr hX hXa hXd (by simpa [muSet, hm] using hn)
  · obtain ⟨n, hn⟩ := hμ hm
    exact cpos hp hTO hsz n hr hX hXa hXd hn

theorem callM_attr {c : ℕ} {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)}
    {μ : Bool × List ℕ} {E' : List (List ℕ)} {e' : List ℕ}
    (hr : FReach p (3, c, s, d, E, μ, E', e')) (h : SemP p s d (false, E.2) (true, e')) :
    B2Attr B fAcc fKd fStepX fStepZ p (Xc p) (3, c, s, d, E, μ, E', e') := by
  refine B2Attr.conj (hsz _ hr) (by simp [fKd]) (fun c'' _ hs'' => ?_) (fun c'' _ hs'' => ?_)
  · change stepXf p 3 c s d E μ E' e' c'' = true at hs''
    rcases stepX_cases hs'' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩
    · cases h1
    · cases h1
    · cases h1
    · obtain ⟨X, hX, hXa, hXd, -⟩ := h
      exact ⟨hr.tail (Or.inl hs''), fun _ => ⟨X, hX, hXa, hXd, fun h => absurd h (by simp [pos])⟩,
        fun h => absurd h (by simp [pos]), fun h => absurd h (by simp [pos]),
        fun h => absurd h (by simp [pos])⟩
  · change stepZf p 3 c s d E μ E' e' c'' = true at hs''
    rcases stepZ_cases hs'' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl⟩
    · cases h1
    · cases h1
    · exact semP_attr hp hTO hsz (hr.tail (Or.inr hs'')) h

theorem call_attr {c : ℕ} {s : List ℕ} {d : TnDesc} {E : Bool × List (List ℕ)}
    {μ : Bool × List ℕ} {E' : List (List ℕ)} {e' : List ℕ}
    (hr : FReach p (2, c, s, d, E, μ, E', e')) (h : SemCall p c s E.2 e') :
    B2Attr B fAcc fKd fStepX fStepZ p (Xc p) (2, c, s, d, E, μ, E', e') := by
  obtain ⟨m, hm, hc, hsem⟩ := h
  have hs : fStepX (p, (2, c, s, d, E, μ, E', e'), callM c s m.2 E.2 e') = true :=
    stepX_call hm hc
  have hrm := hr.tail (Or.inl hs)
  refine B2Attr.ex (hsz _ hr) (by simp [fKd]) (hsz _ hrm) hs ⟨hrm, fun h => absurd h (by simp [callM]),
    fun h => absurd h (by simp [callM]), fun h => absurd h (by simp [callM]), fun _ => hsem⟩ ?_
  exact callM_attr hp hTO hsz hrm hsem

theorem xc_attr {g : FCfg} (h : Xc p g) : B2Attr B fAcc fKd fStepX fStepZ p (Xc p) g := by
  obtain ⟨hr, hsem⟩ := h
  have hk := (fInv_of_reach hp hTO hr).kind
  obtain ⟨k, c, s, d, E, μ, E', e'⟩ := g
  simp only at hk
  rcases k with _ | _ | _ | _ | k
  · obtain ⟨s₁, d₁, E₁, μ₁, he⟩ := reach_pos_shape hr rfl
    simp only [pos, Prod.mk.injEq] at he
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
    exact semP_attr hp hTO hsz hr (hsem.1 rfl)
  · obtain ⟨hcall, hconts, hpos⟩ := hsem.2.1 rfl
    refine B2Attr.conj (hsz _ hr) (by simp [fKd]) (fun c'' _ hs'' => ?_) (fun c'' _ hs'' => ?_)
    · change stepXf p 1 c s d E μ E' e' c'' = true at hs''
      rcases stepX_cases hs'' with ⟨h1, -⟩ | ⟨-, rfl | ⟨x, hx, rfl⟩⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · cases h1
      · exact ⟨hr.tail (Or.inl hs''), fun h => absurd h (by simp [call]),
          fun h => absurd h (by simp [call]), fun _ => hcall, fun h => absurd h (by simp [call])⟩
      · exact ⟨hr.tail (Or.inl hs''), fun _ => hconts x hx, fun h => absurd h (by simp [pos]),
          fun h => absurd h (by simp [pos]), fun h => absurd h (by simp [pos])⟩
      · cases h1
      · cases h1
    · change stepZf p 1 c s d E μ E' e' c'' = true at hs''
      rcases stepZ_cases hs'' with ⟨h1, -⟩ | ⟨-, rfl | rfl⟩ | ⟨h1, -⟩
      · cases h1
      · exact call_attr hp hTO hsz (hr.tail (Or.inr hs'')) hcall
      · exact semP_attr hp hTO hsz (hr.tail (Or.inr hs'')) hpos
      · cases h1
  · exact call_attr hp hTO hsz hr (hsem.2.2.1 rfl)
  · exact callM_attr hp hTO hsz hr (hsem.2.2.2 rfl)
  · omega

/-- **Completeness of the fair game on descriptions.** -/
theorem b2Win_of_fairWin
    (h : p.toProblem.FairWinT Set.univ (cfgNet (initF p).2) {f | f ∈ p.init.dedup}) :
    B2Win B fAcc fKd fStepX fStepZ p (fInit0 p) := by
  obtain ⟨X, hX, hX₀, hXa⟩ := h
  have htgt : tgtSet (true, []) = Set.univ := by ext; simp [tgtSet]
  refine ⟨Xc p, ⟨.refl, fun _ => ⟨X, hX, by
      show ∀ tn S, X tn S → ∃ n, p.toProblem.FAttrT (tgtSet (true, [])) X n tn S
      rw [htgt]; exact hXa, hX₀,
    fun h => absurd h (by simp [fInit0, pos])⟩, fun h => absurd h (by simp [fInit0, pos]),
    fun h => absurd h (by simp [fInit0, pos]), fun h => absurd h (by simp [fInit0, pos])⟩,
    fun g hg => xc_attr hp hTO hsz hg⟩

end Complete2

/-! ## Polynomial time -/

section PTs

theorem pt_primFirst : PT fun x : FProbDesc × List ℕ × TnDesc => primFirst x.1 x.2.1 x.2.2 := by
  unfold primFirst
  have hd : PT fun x : FProbDesc × List ℕ × TnDesc => x.2.2 := PT.snd.comp PT.snd
  have zl : PT fun z : (FProbDesc × List ℕ × TnDesc) × ℕ => lblOf z.1.2.2 z.2 :=
    pt_lblOf (hd.comp PT.fst) PT.snd
  exact PT.any (PT.fst.comp hd) (PT.and (PT.and (pt_unc.comp (PT.pair (hd.comp PT.fst) PT.snd))
    (PT.not (PT.fst.comp zl))) (pt_fApp.comp (PT.pair (PT.pair (PT.fst.comp PT.fst)
      (PT.snd.comp zl)) (PT.fst.comp (PT.snd.comp PT.fst)))))

theorem pt_compFirst : PT compFirst := by
  unfold compFirst
  exact PT.any (PT.fst) (PT.and (pt_unc.comp (PT.pair PT.fst PT.snd))
    (PT.fst.comp (pt_lblOf PT.fst PT.snd)))

theorem pt_fKd : PT fKd := by
  have hk : PT fun x : FProbDesc × FCfg => x.2.1 := PT.fst.comp PT.snd
  have hs : PT fun x : FProbDesc × FCfg => x.2.2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hd : PT fun x : FProbDesc × FCfg => x.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))
  unfold fKd
  exact PT.cond (PT.beq hk (PT.const 0))
    (PT.cond (pt_primFirst.comp (PT.pair PT.fst (PT.pair hs hd))) (PT.const 2)
      (PT.cond (pt_compFirst.comp hd) (PT.const 1) (PT.const 0)))
    (PT.cond (PT.beq hk (PT.const 1)) (PT.const 3) (PT.cond (PT.beq hk (PT.const 2)) (PT.const 1)
      (PT.cond (PT.beq hk (PT.const 3)) (PT.const 3) (PT.const 0))))

theorem pt_sameSet : PT fun x : List ℕ × List ℕ => sameSet x.1 x.2 := by
  unfold sameSet
  exact PT.and (PT.all PT.fst (PT.elem (PT.snd.comp PT.fst) PT.snd))
    (PT.all PT.snd (PT.elem (PT.fst.comp PT.fst) PT.snd))

theorem pt_inTgt : PT fun x : (Bool × List (List ℕ)) × List ℕ => inTgt x.1 x.2 := by
  unfold inTgt
  exact PT.or (PT.fst.comp PT.fst) (PT.any (PT.snd.comp PT.fst)
    (pt_sameSet.comp (PT.pair PT.snd (PT.snd.comp PT.fst))))

theorem pt_fAcc : PT fAcc := by
  have hk : PT fun x : FProbDesc × FCfg => x.2.1 := PT.fst.comp PT.snd
  have hs : PT fun x : FProbDesc × FCfg => x.2.2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hd : PT fun x : FProbDesc × FCfg => x.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))
  have hE : PT fun x : FProbDesc × FCfg => x.2.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))))
  have hμ : PT fun x : FProbDesc × FCfg => x.2.2.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))
  unfold fAcc
  exact PT.and (PT.and (PT.beq hk (PT.const 0)) (PT.isEmpty (PT.fst.comp hd)))
    (PT.cond (PT.fst.comp hμ) (pt_sameSet.comp (PT.pair (PT.snd.comp hμ) hs))
      (pt_inTgt.comp (PT.pair hE hs)))

section Proj

/-- Projections of the step arguments. -/
abbrev SA : Type := FProbDesc × FCfg × FCfg

theorem pt_proj :
    PT (fun x : SA => x.1) ∧ PT (fun x : SA => x.2.1.1) ∧ PT (fun x : SA => x.2.1.2.1) ∧
    PT (fun x : SA => x.2.1.2.2.1) ∧ PT (fun x : SA => x.2.1.2.2.2.1) ∧
    PT (fun x : SA => x.2.1.2.2.2.2.1) ∧ PT (fun x : SA => x.2.1.2.2.2.2.2.1) ∧
    PT (fun x : SA => x.2.1.2.2.2.2.2.2.1) ∧ PT (fun x : SA => x.2.1.2.2.2.2.2.2.2) ∧
    PT (fun x : SA => x.2.2) := by
  have hg : PT fun x : SA => x.2.1 := PT.fst.comp PT.snd
  exact ⟨PT.fst, PT.fst.comp hg, PT.fst.comp (PT.snd.comp hg),
    PT.fst.comp (PT.snd.comp (PT.snd.comp hg)),
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hg))),
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hg)))),
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hg))))),
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp
      (PT.snd.comp hg)))))),
    PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp
      (PT.snd.comp hg)))))),
    PT.snd.comp PT.snd⟩

theorem pt_pos {β : Type} [BEnc β] {fs : β → List ℕ} {fd : β → TnDesc}
    {fE : β → Bool × List (List ℕ)} {fμ : β → Bool × List ℕ} (hs : PT fs) (hd : PT fd)
    (hE : PT fE) (hμ : PT fμ) : PT fun b => pos (fs b) (fd b) (fE b) (fμ b) := by
  unfold pos
  exact PT.pair (PT.const 0) (PT.pair (PT.const 0) (PT.pair hs (PT.pair hd (PT.pair hE
    (PT.pair hμ (PT.pair (PT.const []) (PT.const [])))))))

theorem pt_fStepX : PT fStepX := by
  obtain ⟨hP, hk, hc, hs, hd, hE, hμ, hE', he', hg'⟩ := pt_proj
  have hgE' : PT fun x : SA => x.2.2.2.2.2.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp
      (PT.snd.comp hg'))))))
  have hge' : PT fun x : SA => x.2.2.2.2.2.2.2.2.2 :=
    PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp
      (PT.snd.comp hg'))))))
  have zunc : PT fun z : SA × ℕ => unc z.1.2.1.2.2.2.1 z.2 :=
    pt_unc.comp (PT.pair (hd.comp PT.fst) PT.snd)
  have zl : PT fun z : SA × ℕ => lblOf z.1.2.1.2.2.2.1 z.2 := pt_lblOf (hd.comp PT.fst) PT.snd
  have zprog : PT fun z : SA × ℕ => progDesc z.1.2.1.2.2.2.1 z.2 :=
    pt_progDesc.comp (PT.pair (hd.comp PT.fst) PT.snd)
  have zarg : PT fun z : SA × ℕ => ((z.1.1, (lblOf z.1.2.1.2.2.2.1 z.2).2), z.1.2.1.2.2.1) :=
    PT.pair (PT.pair (hP.comp PT.fst) (PT.snd.comp zl)) (hs.comp PT.fst)
  have hA : PT fun x : SA => x.2.1.2.2.2.1.ids.any fun y => unc x.2.1.2.2.2.1 y &&
      !(lblOf x.2.1.2.2.2.1 y).1 && fApp x.1 (lblOf x.2.1.2.2.2.1 y).2 x.2.1.2.2.1 &&
      (outs x.1 (lblOf x.2.1.2.2.2.1 y).2 x.2.1.2.2.1).any fun o =>
        decide (x.2.2 = pos o (progDesc x.2.1.2.2.2.1 y) x.2.1.2.2.2.2.1 (false, [])) :=
    PT.any (PT.fst.comp hd) (PT.and (PT.and (PT.and zunc (PT.not (PT.fst.comp zl)))
      (pt_fApp.comp zarg)) (PT.any (pt_outs.comp zarg) (PT.eq (hg'.comp (PT.fst.comp PT.fst))
        (pt_pos PT.snd (zprog.comp PT.fst) (hE.comp (PT.fst.comp PT.fst)) (PT.const _)))))
  have hB : PT fun x : SA => x.2.1.2.2.2.1.ids.any fun y => unc x.2.1.2.2.2.1 y &&
      (lblOf x.2.1.2.2.2.1 y).1 &&
      decide (x.2.2 = (1, (lblOf x.2.1.2.2.2.1 y).2, x.2.1.2.2.1, progDesc x.2.1.2.2.2.1 y,
        x.2.1.2.2.2.2.1, x.2.1.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2)) &&
      wfStates x.1 x.2.2.2.2.2.2.2.2.1 && decide (x.2.2.2.2.2.2.2.2.2 ∈ x.2.2.2.2.2.2.2.2.1) :=
    PT.any (PT.fst.comp hd) (PT.and (PT.and (PT.and (PT.and zunc (PT.fst.comp zl))
      (PT.eq (hg'.comp PT.fst) (PT.pair (PT.const 1) (PT.pair (PT.snd.comp zl)
        (PT.pair (hs.comp PT.fst) (PT.pair zprog (PT.pair (hE.comp PT.fst) (PT.pair (hμ.comp PT.fst)
          (PT.pair (hgE'.comp PT.fst) (hge'.comp PT.fst))))))))))
      (pt_wfStates.comp (PT.pair (hP.comp PT.fst) (hgE'.comp PT.fst))))
      (PT.elemL (I := fun _ => inferInstance) (hgE'.comp PT.fst) (hge'.comp PT.fst)))
  have hcall : PT fun x : SA => call x.2.1.2.1 x.2.1.2.2.1 x.2.1.2.2.2.2.2.2.1
      x.2.1.2.2.2.2.2.2.2 := by
    unfold call
    exact PT.pair (PT.const 2) (PT.pair hc (PT.pair hs (PT.pair (PT.const _) (PT.pair
      (PT.pair (PT.const false) hE') (PT.pair (PT.const _) (PT.pair (PT.const []) he'))))))
  have hK1 : PT fun x : SA => decide (x.2.2 = call x.2.1.2.1 x.2.1.2.2.1 x.2.1.2.2.2.2.2.2.1
      x.2.1.2.2.2.2.2.2.2) || x.2.1.2.2.2.2.2.2.1.any fun l =>
        decide (x.2.2 = pos l x.2.1.2.2.2.1 x.2.1.2.2.2.2.1 (false, [])) :=
    PT.or (PT.eq hg' hcall) (PT.any hE' (PT.eq (hg'.comp PT.fst)
      (pt_pos PT.snd (hd.comp PT.fst) (hE.comp PT.fst) (PT.const _))))
  have hK2 : PT fun x : SA => decide (x.2.2 ∈ (x.1.methods.filter fun m => m.1 == x.2.1.2.1).map
      fun m => callM x.2.1.2.1 x.2.1.2.2.1 m.2 x.2.1.2.2.2.2.1.2 x.2.1.2.2.2.2.2.2.2) := by
    refine PT.elemL (I := fun _ => inferInstance) (PT.map (PT.filter (PT.snd.comp (PT.fst.comp hP))
      (PT.beq (PT.fst.comp PT.snd) (hc.comp PT.fst))) ?_) hg'
    unfold callM
    exact PT.pair (PT.const 3) (PT.pair (hc.comp PT.fst) (PT.pair (hs.comp PT.fst)
      (PT.pair (PT.snd.comp PT.snd) (PT.pair (PT.pair (PT.const false) (PT.snd.comp (hE.comp PT.fst)))
        (PT.pair (PT.const _) (PT.pair (PT.const []) (he'.comp PT.fst)))))))
  have hK3 : PT fun x : SA => decide (x.2.2 = pos x.2.1.2.2.1 x.2.1.2.2.2.1
      (false, x.2.1.2.2.2.2.1.2) (false, [])) :=
    PT.eq hg' (pt_pos hs hd (PT.pair (PT.const false) (PT.snd.comp hE)) (PT.const _))
  exact (PT.cond (PT.beq hk (PT.const 0)) (PT.or hA hB) (PT.cond (PT.beq hk (PT.const 1)) hK1
    (PT.cond (PT.beq hk (PT.const 2)) hK2 (PT.cond (PT.beq hk (PT.const 3)) hK3
      (PT.const false))))).of_eq fun _ => rfl

theorem pt_fStepZ : PT fStepZ := by
  obtain ⟨hP, hk, hc, hs, hd, hE, hμ, hE', he', hg'⟩ := pt_proj
  have zunc : PT fun z : SA × ℕ => unc z.1.2.1.2.2.2.1 z.2 :=
    pt_unc.comp (PT.pair (hd.comp PT.fst) PT.snd)
  have zl : PT fun z : SA × ℕ => lblOf z.1.2.1.2.2.2.1 z.2 := pt_lblOf (hd.comp PT.fst) PT.snd
  have zprog : PT fun z : SA × ℕ => progDesc z.1.2.1.2.2.2.1 z.2 :=
    pt_progDesc.comp (PT.pair (hd.comp PT.fst) PT.snd)
  have zarg : PT fun z : SA × ℕ => ((z.1.1, (lblOf z.1.2.1.2.2.2.1 z.2).2), z.1.2.1.2.2.1) :=
    PT.pair (PT.pair (hP.comp PT.fst) (PT.snd.comp zl)) (hs.comp PT.fst)
  have hA : PT fun x : SA => x.2.1.2.2.2.1.ids.any fun y => unc x.2.1.2.2.2.1 y &&
      !(lblOf x.2.1.2.2.2.1 y).1 && fApp x.1 (lblOf x.2.1.2.2.2.1 y).2 x.2.1.2.2.1 &&
      (outs x.1 (lblOf x.2.1.2.2.2.1 y).2 x.2.1.2.2.1).any fun o =>
        decide (x.2.2 = pos o (progDesc x.2.1.2.2.2.1 y) x.2.1.2.2.2.2.1 x.2.1.2.2.2.2.2.1) :=
    PT.any (PT.fst.comp hd) (PT.and (PT.and (PT.and zunc (PT.not (PT.fst.comp zl)))
      (pt_fApp.comp zarg)) (PT.any (pt_outs.comp zarg) (PT.eq (hg'.comp (PT.fst.comp PT.fst))
        (pt_pos PT.snd (zprog.comp PT.fst) (hE.comp (PT.fst.comp PT.fst))
          (hμ.comp (PT.fst.comp PT.fst))))))
  have hcall : PT fun x : SA => call x.2.1.2.1 x.2.1.2.2.1 x.2.1.2.2.2.2.2.2.1
      x.2.1.2.2.2.2.2.2.2 := by
    unfold call
    exact PT.pair (PT.const 2) (PT.pair hc (PT.pair hs (PT.pair (PT.const _) (PT.pair
      (PT.pair (PT.const false) hE') (PT.pair (PT.const _) (PT.pair (PT.const []) he'))))))
  have hK1 : PT fun x : SA => decide (x.2.2 = call x.2.1.2.1 x.2.1.2.2.1 x.2.1.2.2.2.2.2.2.1
      x.2.1.2.2.2.2.2.2.2) || decide (x.2.2 = pos x.2.1.2.2.2.2.2.2.2 x.2.1.2.2.2.1
        x.2.1.2.2.2.2.1 x.2.1.2.2.2.2.2.1) :=
    PT.or (PT.eq hg' hcall) (PT.eq hg' (pt_pos he' hd hE hμ))
  have hK3 : PT fun x : SA => decide (x.2.2 = pos x.2.1.2.2.1 x.2.1.2.2.2.1
      (false, x.2.1.2.2.2.2.1.2) (true, x.2.1.2.2.2.2.2.2.2)) :=
    PT.eq hg' (pt_pos hs hd (PT.pair (PT.const false) (PT.snd.comp hE))
      (PT.pair (PT.const true) he'))
  exact (PT.cond (PT.beq hk (PT.const 0)) hA (PT.cond (PT.beq hk (PT.const 1)) hK1
    (PT.cond (PT.beq hk (PT.const 3)) hK3 (PT.const false)))).of_eq fun _ => rfl

end Proj

theorem pt_fInit : PT fInit := by
  unfold fInit fInit0
  exact PT.and (PT.and (FProbDesc.pt_validB.comp PT.fst) (pt_fTOB.comp PT.fst))
    (PT.eq PT.snd (pt_pos (PT.dedup (PT.fst.comp (PT.snd.comp PT.fst)))
      (PT.snd.comp (pt_initF.comp PT.fst)) (PT.const _) (PT.const _)))

end PTs

end TOF

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime

/-- **Fair strong cyclic plan existence for totally ordered problems is in `2-EXPTIME`.** -/
theorem fairMP_TO_mem : HTN.Cx.EXPTIME2 (PlanExMPFair FClass.TO) := by
  let q : Polynomial ℕ := 4 * Polynomial.X + 10
  have hq : ∀ n, q.eval n = 4 * n + 10 := fun n => by simp [q]
  have hbound : ∀ p : FProbDesc, TOF.fBound p ≤ 2 ^ q.eval (sz p) := by
    intro p
    rw [hq]
    unfold TOF.fBound TO.Mx
    set S := sz p
    have hX : S + 1 ≤ 2 ^ S := Nat.lt_two_pow_self
    have h1 : 2 ^ (4 * S + 10) = 4 * 2 ^ (4 * S + 8) := by
      rw [show 4 * S + 10 = 2 + (4 * S + 8) by ring, pow_add]; norm_num
    have h2 : 2 ^ (4 * S + 8) = 256 * (2 ^ S) ^ 4 := by
      rw [← pow_mul, show 4 * S + 8 = 8 + S * 4 by ring, pow_add]; norm_num
    rw [h1, h2]
    have h3 : 1 ≤ 2 ^ S := Nat.one_le_two_pow
    have h4 : (S + 1) ^ 2 ≤ (2 ^ S) ^ 2 := Nat.pow_le_pow_left hX 2
    have h5 : (2 ^ S) ^ 2 ≤ (2 ^ S) ^ 4 := Nat.pow_le_pow_right h3 (by norm_num)
    nlinarith
  refine inExp2Time_codeLang_of_buchi2 (α := FProbDesc) (σ := TOF.FCfg)
    (Q := fun p => p.Valid ∧ FClass.TO p.toProblem ∧ p.toProblem.MPStrongCyclicFairSolvable)
    TOF.pt_fInit TOF.pt_fAcc TOF.pt_fKd TOF.pt_fStepX TOF.pt_fStepZ q fun p => ?_
  have hi : p.toProblem.init = {f | f ∈ p.init.dedup} := MPS.init_state p
  constructor
  · rintro ⟨hp, hTO, hsol⟩
    have hsz : ∀ g, TOF.FReach p g → sz g ≤ 2 ^ q.eval (sz p) := fun g hg =>
      (TOF.sz_le_of_fInv (TOF.fInv_of_reach hp hTO hg)).trans (hbound p)
    refine ⟨TOF.fInit0 p, hsz _ .refl, ?_, ?_⟩
    · simp [TOF.fInit, (FProbDesc.validB_iff p).2 hp, (fTOB_iff hp).2 hTO]
    · have h1 := (Problem.mpStrongCyclicFairSolvable_iff_prog
        (FProbDesc.toProblem_wf hp).tnI).1 hsol
      obtain ⟨X, hX, hX₀, hXa⟩ := Problem.fairWinT_univ_iff.2 h1
      rw [hi] at hX₀
      exact TOF.b2Win_of_fairWin hp hTO hsz ⟨X, hX, hX.2 _ _ _ _ hX₀
        (TO.tInv_init hp hTO).d.wf (MPS.isoVia_art (isoVia_id_of_agree (MPS.agree_initF hp))),
        hXa⟩
  · rintro ⟨c₀, -, hc₀, hw⟩
    simp only [TOF.fInit, Bool.and_eq_true, decide_eq_true_eq] at hc₀
    obtain ⟨⟨hv, hto⟩, rfl⟩ := hc₀
    have hp := (FProbDesc.validB_iff p).1 hv
    have hTO := (fTOB_iff hp).1 hto
    have hsz : ∀ g, TOF.FReach p g → sz g ≤ 2 ^ q.eval (sz p) := fun g hg =>
      (TOF.sz_le_of_fInv (TOF.fInv_of_reach hp hTO hg)).trans (hbound p)
    refine ⟨hp, hTO, ?_⟩
    obtain ⟨X, hX, hX₀, hXa⟩ := TOF.fairWin_of_b2Win hp hTO hsz hw
    have h1 : p.toProblem.FairWinT Set.univ p.toProblem.tnI p.toProblem.init := by
      rw [hi]
      exact ⟨X, hX, hX.2 _ _ _ _ hX₀ (FProbDesc.toProblem_wf hp).tnI
        (MPS.isoVia_art (isoVia_id_of_agree (MPS.agree_initF hp).symm)), hXa⟩
    exact (Problem.mpStrongCyclicFairSolvable_iff_prog (FProbDesc.toProblem_wf hp).tnI).2
      (Problem.fairWinT_univ_iff.1 h1)

/-- Membership in `2-EXPTIME` with the inherited lower bound (EXPTIME-hardness). -/
theorem fairMP_TO_bounds :
    HTN.Cx.EXPTIME2 (PlanExMPFair FClass.TO) ∧ Cx.Hard Cx.EXPTIME (PlanExMPFair FClass.TO) :=
  ⟨fairMP_TO_mem, hardFair_TO⟩

/-- Strong method-based plan existence for totally ordered problems: in `2-EXPTIME`, and
EXPTIME-hard (inherited). -/
theorem strongMP_TO_bounds :
    HTN.Cx.EXPTIME2 (PlanExMP .strong FClass.TO) ∧
      Cx.Hard Cx.EXPTIME (PlanExMP .strong FClass.TO) :=
  ⟨strongMP_TO_mem, hard_TO_mp .strong (by decide)⟩

end FOND
