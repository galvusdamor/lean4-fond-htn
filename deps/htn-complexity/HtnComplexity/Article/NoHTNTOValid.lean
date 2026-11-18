import HtnComplexity.Article.NoHTNTOFmt
/-!
# Well-formedness, non-hierarchy and total order, checked in logarithmic space

* `HTN.Article.NoHTNTO.tnValidT` — a task network description is well formed
  (`HTN.Article.NoHTNTO.eval_tnValidT`); the declared action names are those of the actions at
  the start of the input;
* `HTN.Article.NoHTNTO.validT` — the description is well formed (`HTN.Article.NoHTNTO.eval_validT`);
* `HTN.Article.NoHTNTO.noHTNT`, `HTN.Article.NoHTNTO.toT` — all labels primitive, the initial
  task network totally ordered.
-/

namespace HTN

namespace Article

namespace NoHTNTO

open Cx Cx.LTerm Syn Syn.PolyDom Logspace

variable {y : List Bool} {M : ℕ}

theorem ne0_and {env : List ℕ} {a b : LTerm} :
    eval y M env (and a b) ≠ 0 ↔ eval y M env a ≠ 0 ∧ eval y M env b ≠ 0 := by
  rw [eval_and]; split_ifs with h <;> simp_all

theorem ne0_or {env : List ℕ} {a b : LTerm} :
    eval y M env (or a b) ≠ 0 ↔ eval y M env a ≠ 0 ∨ eval y M env b ≠ 0 := by
  rw [eval_or]; split_ifs with h <;> simp_all

theorem ne0_not {env : List ℕ} {a : LTerm} : eval y M env (not a) ≠ 0 ↔ eval y M env a = 0 := by
  rw [eval_not]; split_ifs with h <;> simp_all

theorem ne0_natEqT (hM : y.length + 2 ≤ M) {d₁ d₂ : ℕ} {p₁ p₂ : LTerm} {env : List ℕ} {n₁ n₂ : ℕ}
    (h₁ : At y d₁ (eval y M env p₁) .nat n₁) (h₂ : At y d₂ (eval y M env p₂) .nat n₂) :
    eval y M env (natEqT d₁ p₁ d₂ p₂) ≠ 0 ↔ n₁ = n₂ := by
  rw [eval_natEqT hM h₁ h₂]; split_ifs with h <;> simp [h]

/-! ### Well-formed task networks -/

/-- Well-formedness in the form checked. -/
def TnValidL (prim : ℕ → Prop) (t : TnDesc) : Prop :=
  t.ids.Nodup ∧ (∀ q ∈ t.ordList, q.1 ∈ t.ids ∧ q.2 ∈ t.ids) ∧ (∀ q ∈ t.ordList, q.1 ≠ q.2) ∧
  (∀ q ∈ t.ordList, ∀ q' ∈ t.ordList, q.2 = q'.1 → (q.1, q'.2) ∈ t.ordList) ∧
  (t.lbl.map Prod.fst).Nodup ∧ t.lbl.length = t.ids.length ∧ (∀ q ∈ t.lbl, q.1 ∈ t.ids) ∧
  (∀ q ∈ t.lbl, q.2.1 = true ∨ prim q.2.2)

theorem tnValidL_iff (prim : ℕ → Prop) (t : TnDesc) : TnValidL prim t ↔ TnValid prim t := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨h1, h2, fun a ha => h3 _ ha rfl, fun a b c hab hbc => h4 _ hab _ hbc rfl, ?_, ?_⟩
    · refine (List.Nodup.subperm h5 fun x hx => ?_).perm_of_length_le (by simp [h6])
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact h7 q hq
    · intro q hq hb
      rcases h8 q hq with h | h
      · rw [hb] at h; simp at h
      · exact h
  · intro h
    refine ⟨h.nodup, h.ord_mem, ?_, ?_, h.lbl_perm.nodup_iff.2 h.nodup,
      by simpa using h.lbl_perm.length_eq, ?_, ?_⟩
    · intro q hq he
      apply h.irrefl q.1
      have : q = (q.1, q.1) := Prod.ext rfl he.symm
      rw [this] at hq; exact hq
    · intro q hq q' hq' he
      exact h.trans q.1 q.2 q'.2 hq (by rw [he]; exact hq')
    · intro q hq; exact h.lbl_perm.subset (List.mem_map_of_mem hq)
    · intro q hq
      cases hb : q.2.1
      · exact Or.inr (h.prim_ok q hq hb)
      · exact Or.inl rfl

/-- The entry `i` (variable `1`) of the list at `(d, L)`, inside one quantifier. -/
abbrev E1 (d : ℕ) (L : LTerm) : LTerm := entryT d (lift 2 L) (.var 1)

/-- **The task network at `(d, T)` is well formed**, the declared names being those of the actions
at `(0, 0)`. -/
def tnValidT (d : ℕ) (T : LTerm) : LTerm :=
  and (nodupKeyT d T)
  (and (allE d (ordLoc d T) (and (memKeyT (d + 1) (E1 d (ordLoc d T)) d (lift 2 T))
      (memKeyT (d + 1) (sndT .nat (d + 1) (E1 d (ordLoc d T))) d (lift 2 T))))
  (and (allE d (ordLoc d T) (not (natEqT (d + 1) (E1 d (ordLoc d T)) (d + 1)
      (sndT .nat (d + 1) (E1 d (ordLoc d T))))))
  (and (allE d (ordLoc d T) (allE d (lift 2 (ordLoc d T))
      (or (not (natEqT (d + 1) (sndT .nat (d + 1) (entryT d (lift 2 (lift 2 (ordLoc d T))) (.var 3))) (d + 1)
          (entryT d (lift 2 (lift 2 (ordLoc d T))) (.var 1))))
        (pairMemT (d + 1) (entryT d (lift 2 (lift 2 (ordLoc d T))) (.var 3)) (d + 1)
          (sndT .nat (d + 1) (entryT d (lift 2 (lift 2 (ordLoc d T))) (.var 1))) d (lift 2 (lift 2 (ordLoc d T)))))))
  (and (nodupKeyT d (lblLoc d T))
  (and (eq (lenT d (lblLoc d T)) (lenT d T))
  (and (allE d (lblLoc d T) (memKeyT (d + 1) (E1 d (lblLoc d T)) d (lift 2 T)))
    (allE d (lblLoc d T) (or (boolT (d + 1) (sndT .nat (d + 1) (E1 d (lblLoc d T))))
      (memKeyT (d + 1) (sndT .bool (d + 1) (sndT .nat (d + 1) (E1 d (lblLoc d T)))) 0 (.lit 0))))))))))

section Tn

variable (hM : y.length + 2 ≤ M) {d : ℕ} {T : LTerm} {env : List ℕ} {t : TnDesc}
  (ht : At y d (eval y M env T) fTn t) {A : List ActDesc} (hA : At y 0 0 (.list fAct) A)
include hM ht

include hA in
/-- **The meaning of the check of a task network.** -/
theorem eval_tnValidT :
    eval y M env (tnValidT d T) ≠ 0 ↔ TnValid (fun a => a ∈ A.map ActDesc.name) t := by
  have hI := at_ids hM ht
  have hO := at_ord hM ht
  have hL := at_lbl hM ht
  rw [← tnValidL_iff, TnValidL, tnValidT]
  simp only [ne0_and]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_
    (and_congr ?_ ?_))))))
  · rw [eval_nodupKeyT hM hI (key_nat _), List.map_id]
  · rw [eval_allE hM hO, ← List.forall_getElem]
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    have he := At.entry2 hM hO hi 1
    rw [ne0_and, eval_memKeyT hM (At.p1 he) (hI.lift2 1 i) (key_nat _),
      eval_memKeyT hM (At.p2 hM he) (hI.lift2 1 i) (key_nat _), List.map_id]
  · rw [eval_allE hM hO, ← List.forall_getElem]
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    have he := At.entry2 hM hO hi 1
    rw [ne0_not, eval_natEqT hM (At.p1 he) (At.p2 hM he)]
    split_ifs with h <;> simp [h]
  · rw [eval_allE hM hO, ← List.forall_getElem]
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    rw [eval_allE hM (hO.lift2 1 i), ← List.forall_getElem]
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    have hO2 : At y d (eval y M (1 :: j :: 1 :: i :: env) (lift 2 (lift 2 (ordLoc d T)))) fOrd t.ordList := by
      rw [eval_lift2, eval_lift2]; exact hO
    have he3 : At y (d + 1) (eval y M (1 :: j :: 1 :: i :: env) (entryT d (lift 2 (lift 2 (ordLoc d T))) (.var 3)))
        (.pair .nat .nat) t.ordList[i] := At.entry hM hO2 hi (by simp [eval])
    have he1 : At y (d + 1) (eval y M (1 :: j :: 1 :: i :: env) (entryT d (lift 2 (lift 2 (ordLoc d T))) (.var 1)))
        (.pair .nat .nat) t.ordList[j] := At.entry hM hO2 hj (by simp [eval])
    rw [ne0_or, ne0_not, eval_natEqT hM (At.p2 hM he3) (At.p1 he1),
      eval_pairMemT hM (At.p1 he3) (At.p2 hM he1) hO2]
    by_cases h : t.ordList[i].2 = t.ordList[j].1 <;> simp [h]
  · rw [eval_nodupKeyT hM hL (key_fst _ _)]
  · rw [eval_eq _ _ _ (by omega), eval_lenT hM hL, eval_lenT hM hI]
    split_ifs with h <;> simp [h]
  · rw [eval_allE hM hL, ← List.forall_getElem]
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    have he := At.entry2 hM hL hi 1
    rw [eval_memKeyT hM (At.p1 he) (hI.lift2 1 i) (key_nat _), List.map_id]
  · rw [eval_allE hM hL, ← List.forall_getElem]
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    have he := At.entry2 hM hL hi 1
    have he2 := At.p2 hM he
    rw [ne0_or, eval_boolT hM (At.p1 he2), eval_memKeyT hM (At.p2 hM he2) (show At y 0 (eval y M (1 :: i :: env) (.lit 0)) (.list fAct) A from hA) (key_fst _ _)]
    cases t.lbl[i].2.1 <;> simp [ActDesc.name]

end Tn

/-! ### Well-formed descriptions -/

/-- The names of the actions at `(0, 0)` are distinct, the initial task network and the networks
of all methods are well formed. -/
def validT : LTerm :=
  and (nodupKeyT 0 (.lit 0))
    (and (tnValidT 0 locTn) (allE 0 locMeths (tnValidT 1 (sndT .nat 1 (E1 0 locMeths)))))

theorem eval_validT (hM : y.length + 2 ≤ M) {p : ProbDesc} (hp : At y 0 0 fProb p) (env : List ℕ) :
    eval y M env validT ≠ 0 ↔ p.Valid := by
  have hA := at_acts hM hp env
  have hA0 : At y 0 0 (.list fAct) p.actions := hA
  rw [validT, ne0_and, ne0_and, eval_nodupKeyT hM hA (key_fst _ _),
    eval_tnValidT hM (at_tn hM hp env) hA0, eval_allE hM (at_meths hM hp env)]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun m hm => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    exact (eval_tnValidT hM (At.p2 hM (At.entry2 hM (at_meths hM hp env) hi 1)) hA0).1 (h3 i hi)
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i hi => (eval_tnValidT hM (At.p2 hM (At.entry2 hM (at_meths hM hp env) hi 1)) hA0).2
      (h3 _ (List.getElem_mem _))⟩

/-! ### Primitive labels and total order -/

/-- All labels of the initial task network are primitive. -/
def noHTNT : LTerm :=
  allE 0 (lblLoc 0 locTn) (not (boolT 1 (sndT .nat 1 (E1 0 (lblLoc 0 locTn)))))

theorem eval_noHTNT (hM : y.length + 2 ≤ M) {p : ProbDesc} (hp : At y 0 0 fProb p) (env : List ℕ) :
    eval y M env noHTNT ≠ 0 ↔ ∀ q ∈ p.tnI.lbl, q.2.1 = false := by
  have hL := at_lbl hM (at_tn hM hp env)
  rw [noHTNT, eval_allE hM hL, ← List.forall_getElem]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [ne0_not, eval_boolT hM (At.p1 (At.p2 hM (At.entry2 hM hL hi 1)))]
  cases p.tnI.lbl[i].2.1 <;> simp

/-- The initial task network is totally ordered. -/
def toT : LTerm :=
  allE 0 locTn (allE 0 (lift 2 locTn)
    (or (natEqT 1 (entryT 0 (lift 2 (lift 2 locTn)) (.var 3)) 1 (entryT 0 (lift 2 (lift 2 locTn)) (.var 1)))
      (or (pairMemT 1 (entryT 0 (lift 2 (lift 2 locTn)) (.var 3)) 1 (entryT 0 (lift 2 (lift 2 locTn)) (.var 1)) 0
          (lift 2 (lift 2 (ordLoc 0 locTn))))
        (pairMemT 1 (entryT 0 (lift 2 (lift 2 locTn)) (.var 1)) 1 (entryT 0 (lift 2 (lift 2 locTn)) (.var 3)) 0
          (lift 2 (lift 2 (ordLoc 0 locTn)))))))

theorem eval_toT (hM : y.length + 2 ≤ M) {p : ProbDesc} (hp : At y 0 0 fProb p) (env : List ℕ) :
    eval y M env toT ≠ 0 ↔ TOL p.tnI := by
  have ht := at_tn hM hp env
  have hI := at_ids hM ht
  rw [toT, eval_allE hM hI, TOL, ← List.forall_getElem]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [eval_allE hM (hI.lift2 1 i), ← List.forall_getElem]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  have ht2 : At y 0 (eval y M (1 :: j :: 1 :: i :: env) (lift 2 (lift 2 locTn))) fTn p.tnI := by
    rw [eval_lift2, eval_lift2]; exact ht
  have hI2 := at_ids hM ht2
  have hO2 : At y 0 (eval y M (1 :: j :: 1 :: i :: env) (lift 2 (lift 2 (ordLoc 0 locTn)))) fOrd
      p.tnI.ordList := by rw [eval_lift2, eval_lift2]; exact at_ord hM ht
  have he3 : At y 1 (eval y M (1 :: j :: 1 :: i :: env) (entryT 0 (lift 2 (lift 2 locTn)) (.var 3))) .nat
      p.tnI.ids[i] := At.entry hM hI2 hi (by simp [eval])
  have he1 : At y 1 (eval y M (1 :: j :: 1 :: i :: env) (entryT 0 (lift 2 (lift 2 locTn)) (.var 1))) .nat
      p.tnI.ids[j] := At.entry hM hI2 hj (by simp [eval])
  rw [ne0_or, ne0_or, ne0_natEqT hM he3 he1, eval_pairMemT hM he3 he1 hO2, eval_pairMemT hM he1 he3 hO2]
  by_cases h : p.tnI.ids[i] = p.tnI.ids[j] <;> simp [h]

end NoHTNTO

end Article

end HTN
