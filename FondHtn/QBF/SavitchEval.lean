import FondHtn.QBF.Savitch
/-!
# Savitch's construction: evaluating the formula

* `FOND.QBF.Savitch.eval_base` — the bottom level states `Reach₀(X_K, Y_K)`;
* `FOND.QBF.Savitch.eval_steps` — the levels `r, …, K - 1` state `Reach_{K-r}(X_r, Y_r)`;
* `FOND.QBF.Savitch.holds_formula_iff` — the formula is true iff some `X` (the initial state)
  reaches some goal state `Y` within `2 ^ n` steps (on bit vectors).
-/

namespace FOND

namespace QBF

namespace Savitch

open HTN HTN.Article

variable (d : StripsDesc)

/-! ## Variables of the parts -/

theorem mem_exB {l : List ℕ} {x : Bool × ℕ} : x ∈ exB l ↔ x.1 = false ∧ x.2 ∈ l := by
  obtain ⟨q, v⟩ := x
  simp only [exB, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨v', hv', rfl, rfl⟩; exact ⟨rfl, hv'⟩
  · rintro ⟨rfl, hv⟩; exact ⟨v, hv, rfl, rfl⟩

theorem mem_vars {n w x : ℕ} : x ∈ vars n w ↔ ∃ i < n, x = vv w i := by
  simp only [vars, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem vars_steps (K : ℕ) : ∀ c r, ∀ x ∈ steps d K r c, ∃ w i, x.2 = vv w i ∧
    ((3 * r + 2 ≤ w ∧ w ≤ 3 * (r + c) + 1) ∨ (w = 3 * K + 2 ∧ r ≤ i ∧ i < r + c)) := by
  intro c
  induction c with
  | zero => intro r x hx; simp [steps] at hx
  | succ c ih =>
    intro r x hx
    simp only [steps, stepPre, List.mem_append, List.mem_cons] at hx
    rcases hx with ((hx | rfl | hx | hx) | hx)
    · obtain ⟨i, -, h⟩ := mem_vars.1 (mem_exB.1 hx).2
      exact ⟨_, i, h, Or.inl ⟨le_rfl, by omega⟩⟩
    · exact ⟨_, r, rfl, Or.inr ⟨rfl, le_rfl, by omega⟩⟩
    · obtain ⟨i, -, h⟩ := mem_vars.1 (mem_exB.1 hx).2
      exact ⟨_, i, h, Or.inl ⟨by omega, by omega⟩⟩
    · obtain ⟨i, -, h⟩ := mem_vars.1 (mem_exB.1 hx).2
      exact ⟨_, i, h, Or.inl ⟨by omega, by omega⟩⟩
    · obtain ⟨w, i, h, h'⟩ := ih (r + 1) x hx
      exact ⟨w, i, h, by omega⟩

theorem vars_basePre (K : ℕ) : ∀ x ∈ basePre d K, ∃ j, x.2 = vv (3 * K + 3) j := by
  intro x hx
  simp only [basePre, mem_exB, List.mem_map] at hx
  obtain ⟨-, j, -, h⟩ := hx
  exact ⟨j, h.symm⟩

theorem lits_guard {g : Lit} {cls : List Clause} {l : Lit} {cl : Clause} (hcl : cl ∈ guard g cls)
    (hl : l ∈ cl) : l = g ∨ ∃ c ∈ cls, l ∈ c := by
  simp only [guard, List.mem_map] at hcl
  obtain ⟨c, hc, rfl⟩ := hcl
  rcases List.mem_cons.1 hl with h | h
  · exact Or.inl h
  · exact Or.inr ⟨c, hc, h⟩

theorem lits_eqs {n U V : ℕ} {l : Lit} {cl : Clause} (hcl : cl ∈ eqs n U V) (hl : l ∈ cl) :
    ∃ i, l.1 = vv U i ∨ l.1 = vv V i := by
  simp only [eqs, List.mem_flatMap, eq2, List.mem_cons, List.not_mem_nil, or_false] at hcl
  obtain ⟨i, -, rfl | rfl⟩ := hcl <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨i, by simp⟩
    · exact ⟨i, by simp⟩

theorem vars_stepCl (K r : ℕ) : ∀ cl ∈ stepCl d K r, ∀ l ∈ cl, ∃ w i, l.1 = vv w i ∧
    ((3 * r ≤ w ∧ w ≤ 3 * r + 4) ∨ (w = 3 * K + 2 ∧ i = r)) := by
  intro cl hcl l hl
  simp only [stepCl, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · rcases lits_guard hcl hl with rfl | ⟨c, hc, hl'⟩
    · exact ⟨_, r, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · rcases List.mem_append.1 hc with hc | hc <;>
      · obtain ⟨i, h | h⟩ := lits_eqs hc hl'
        · exact ⟨_, i, h, Or.inl ⟨by omega, by omega⟩⟩
        · exact ⟨_, i, h, Or.inl ⟨by omega, by omega⟩⟩
  · rcases lits_guard hcl hl with rfl | ⟨c, hc, hl'⟩
    · exact ⟨_, r, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · rcases List.mem_append.1 hc with hc | hc <;>
      · obtain ⟨i, h | h⟩ := lits_eqs hc hl'
        · exact ⟨_, i, h, Or.inl ⟨by omega, by omega⟩⟩
        · exact ⟨_, i, h, Or.inl ⟨by omega, by omega⟩⟩

theorem vars_initCl : ∀ cl ∈ initCl d, ∀ l ∈ cl, ∃ w i, l.1 = vv w i ∧ w ≤ 1 := by
  intro cl hcl l hl
  simp only [initCl, List.mem_flatMap, List.mem_append] at hcl
  obtain ⟨i, -, (h | h) | h⟩ := hcl
  · simp only [List.mem_singleton] at h; subst h
    simp only [List.mem_singleton] at hl; subst hl
    exact ⟨0, i, rfl, by omega⟩
  · split_ifs at h
    · simp only [List.mem_singleton] at h; subst h
      simp only [List.mem_singleton] at hl; subst hl
      exact ⟨1, i, rfl, le_rfl⟩
    · simp at h
  · split_ifs at h
    · simp only [List.mem_singleton] at h; subst h
      simp only [List.mem_singleton] at hl; subst hl
      exact ⟨1, i, rfl, le_rfl⟩
    · simp at h

/-! ## The bottom level -/

theorem sat_alo (K : ℕ) (σ : ℕ → Bool) :
    Sat [(List.range (nA d + 1)).map fun j => (cV K j, true)] σ ↔
      ∃ j < nA d + 1, σ (cV K j) = true := by
  simp only [Sat, List.mem_singleton, forall_eq, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, h⟩; exact ⟨j, hj, h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨_, ⟨j, hj, rfl⟩, h⟩

theorem sat_baseCl (K : ℕ) (σ : ℕ → Bool) : Sat (baseCl d K) σ ↔
    (∃ j < nA d + 1, σ (cV K j) = true) ∧
    (σ (cV K 0) = false ∨ ∀ i < nF d, σ (vv (3 * K) i) = σ (vv (3 * K + 1) i)) ∧
    ∀ j < nA d, σ (cV K (j + 1)) = false ∨
      ActSem d (d.actions.getI j) (read σ (3 * K)) (read σ (3 * K + 1)) := by
  simp only [baseCl, sat_append, sat_alo, sat_guard, sat_eqs, sat_flatMap, List.mem_range,
    sat_actBody, and_assoc]

theorem eval_base (K : ℕ) (σ : ℕ → Bool) :
    Eval (basePre d K) (baseCl d K) σ ↔ ReachV d 0 (read σ (3 * K)) (read σ (3 * K + 1)) := by
  rw [basePre, ← List.append_nil (exB _), eval_exB]
  set l := (List.range (nA d + 1)).map (cV K)
  have hr : ∀ τ w, w < 3 * K + 3 → read (updL l τ σ) w = read σ w := fun τ w hw =>
    funext fun i => by
      simp only [read, updL, l, cV, List.mem_map, vv_inj]
      rw [if_neg]; rintro ⟨j, -, h, -⟩; omega
  have hc : ∀ τ, ∀ j < nA d + 1, updL l τ σ (cV K j) = τ (cV K j) := fun τ j hj => by
    simp only [updL, l]; rw [if_pos (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)]
  simp only [eval_nil, sat_baseCl, ReachV]
  constructor
  · rintro ⟨τ, ⟨j, hj, hjt⟩, h0, hacts⟩
    rw [hr τ _ (by omega), hr τ _ (by omega)] at hacts
    cases j with
    | zero =>
      rw [hc τ 0 hj] at hjt
      rw [hc τ 0 hj, hjt] at h0
      refine Or.inl fun i hi => ?_
      have := (h0.resolve_left (by simp)) i hi
      have e0 := congrFun (hr τ (3 * K) (by omega)) i
      have e1 := congrFun (hr τ (3 * K + 1) (by omega)) i
      simp only [read] at e0 e1
      rwa [e0, e1] at this
    | succ j =>
      rw [hc τ _ hj] at hjt
      have := hacts j (by omega)
      rw [hc τ _ hj, hjt] at this
      exact Or.inr ⟨j, by omega, this.resolve_left (by simp)⟩
  · rintro (h | ⟨j₀, hj₀, h⟩)
    · refine ⟨fun x => decide (x = cV K 0), ⟨0, by omega, by rw [hc _ 0 (by omega)]; simp⟩,
        Or.inr fun i hi => ?_, fun j hj => Or.inl ?_⟩
      · have e0 := congrFun (hr (fun x => decide (x = cV K 0)) (3 * K) (by omega)) i
        have e1 := congrFun (hr (fun x => decide (x = cV K 0)) (3 * K + 1) (by omega)) i
        simp only [read] at e0 e1
        rw [e0, e1]; exact h i hi
      · rw [hc _ _ (by omega)]; simp [cV, vv_inj]
    · refine ⟨fun x => decide (x = cV K (j₀ + 1)), ⟨j₀ + 1, by omega, by rw [hc _ _ (by omega)]; simp⟩,
        Or.inl ?_, fun j hj => ?_⟩
      · rw [hc _ 0 (by omega)]; simp [cV, vv_inj]
      · rw [hr _ _ (by omega), hr _ _ (by omega), hc _ _ (by omega)]
        by_cases hjj : j = j₀
        · subst hjj; exact Or.inr h
        · left; simp [cV, vv_inj]; omega

/-! ## The levels -/

theorem sat_stepCl (K r : ℕ) (σ : ℕ → Bool) : Sat (stepCl d K r) σ ↔
    (σ (bV K r) = true ∨ (∀ i < nF d, σ (vv (3 * r + 3) i) = σ (vv (3 * r) i)) ∧
      ∀ i < nF d, σ (vv (3 * r + 4) i) = σ (vv (3 * r + 2) i)) ∧
    (σ (bV K r) = false ∨ (∀ i < nF d, σ (vv (3 * r + 3) i) = σ (vv (3 * r + 2) i)) ∧
      ∀ i < nF d, σ (vv (3 * r + 4) i) = σ (vv (3 * r + 1) i)) := by
  simp only [stepCl, sat_append, sat_guard, sat_eqs]

/-- The logical core of a level. -/
theorem level_core (c : ℕ) (X Y : ℕ → Bool) (wZ wX wY : ℕ) :
    (∃ τZ : ℕ → Bool, ∀ bb : Bool, ∃ τX τY : ℕ → Bool,
      ((bb = true ∨ (∀ i < nF d, τX (vv wX i) = X i) ∧ ∀ i < nF d, τY (vv wY i) = τZ (vv wZ i)) ∧
       (bb = false ∨ (∀ i < nF d, τX (vv wX i) = τZ (vv wZ i)) ∧ ∀ i < nF d, τY (vv wY i) = Y i)) ∧
      ReachV d c (fun i => τX (vv wX i)) (fun i => τY (vv wY i))) ↔ ReachV d (c + 1) X Y := by
  constructor
  · rintro ⟨τZ, h⟩
    obtain ⟨τX, τY, ⟨h1, -⟩, hr⟩ := h false
    obtain ⟨τX', τY', ⟨-, h2⟩, hr'⟩ := h true
    have h1 := h1.resolve_left (by simp)
    have h2 := h2.resolve_left (by simp)
    exact ⟨fun i => τZ (vv wZ i), reachV_congr d c h1.1 h1.2 hr, reachV_congr d c h2.1 h2.2 hr'⟩
  · rintro ⟨Z, h1, h2⟩
    have e : ∀ (V : ℕ → Bool) w, (fun i => (fun x => V (Nat.unpair x).2) (vv w i)) = V :=
      fun V w => funext fun i => by simp [vv, Nat.unpair_pair]
    refine ⟨fun x => Z (Nat.unpair x).2, fun bb => ?_⟩
    cases bb
    · refine ⟨fun x => X (Nat.unpair x).2, fun x => Z (Nat.unpair x).2, ⟨Or.inr ⟨fun i _ => ?_,
        fun i _ => ?_⟩, Or.inl rfl⟩, ?_⟩
      · simp [vv, Nat.unpair_pair]
      · simp [vv, Nat.unpair_pair]
      · rw [e, e]; exact h1
    · refine ⟨fun x => Z (Nat.unpair x).2, fun x => Y (Nat.unpair x).2, ⟨Or.inl rfl,
        Or.inr ⟨fun i _ => ?_, fun i _ => ?_⟩⟩, ?_⟩
      · simp [vv, Nat.unpair_pair]
      · simp [vv, Nat.unpair_pair]
      · rw [e, e]; exact h2

theorem eval_steps (K : ℕ) : ∀ c r, r + c = K → ∀ σ : ℕ → Bool,
    Eval (steps d K r c ++ basePre d K) (stepsCl d K r c ++ baseCl d K) σ ↔
      ReachV d c (read σ (3 * r)) (read σ (3 * r + 1)) := by
  intro c
  induction c with
  | zero =>
    intro r hr σ
    rw [add_zero] at hr; subst hr
    simp only [steps, stepsCl, List.nil_append]
    exact eval_base d r σ
  | succ c ih =>
    intro r hr σ
    have ih' : ∀ σ : ℕ → Bool,
        Eval (steps d K (r + 1) c ++ basePre d K) (stepsCl d K (r + 1) c ++ baseCl d K) σ ↔
          ReachV d c (read σ (3 * r + 3)) (read σ (3 * r + 4)) := fun σ => by
      rw [ih (r + 1) (by omega) σ]
      rw [show 3 * (r + 1) = 3 * r + 3 by ring, show 3 * r + 3 + 1 = 3 * r + 4 by ring]
    have hQ : steps d K r (c + 1) ++ basePre d K = exB (vars (nF d) (3 * r + 2)) ++
        ((true, bV K r) :: (exB (vars (nF d) (3 * r + 3)) ++ (exB (vars (nF d) (3 * r + 4)) ++
          (steps d K (r + 1) c ++ basePre d K)))) := by
      simp [steps, stepPre, List.append_assoc]
    have hH : stepsCl d K r (c + 1) ++ baseCl d K =
        stepCl d K r ++ (stepsCl d K (r + 1) c ++ baseCl d K) := by
      simp [stepsCl, List.append_assoc]
    have hdisj : ∀ cl ∈ stepCl d K r, ∀ l ∈ cl, ∀ x ∈ steps d K (r + 1) c ++ basePre d K,
        l.1 ≠ x.2 := by
      intro cl hcl l hl x hx
      obtain ⟨w, i, hw, hwi⟩ := vars_stepCl d K r cl hcl l hl
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨w', i', hw', hwi'⟩ := vars_steps d K c (r + 1) x hx
        rw [hw, hw', Ne, vv_inj]; omega
      · obtain ⟨j, hj⟩ := vars_basePre d K x hx
        rw [hw, hj, Ne, vv_inj]; omega
    rw [hQ, hH, eval_exB]
    simp only [eval_forall, eval_exB, eval_append_indep _ hdisj, ih', sat_stepCl]
    rw [← level_core d c _ _ (3 * r + 2) (3 * r + 3) (3 * r + 4)]
    have hbW : ∀ j ≤ 4, 3 * K + 2 ≠ 3 * r + j := fun j hj => by omega
    refine exists_congr fun τZ => forall_congr' fun bb => exists_congr fun τX =>
      exists_congr fun τY => ?_
    set σ5 := updL (vars (nF d) (3 * r + 4)) τY (updL (vars (nF d) (3 * r + 3)) τX
      (Function.update (updL (vars (nF d) (3 * r + 2)) τZ σ) (bV K r) bb))
    have hb : σ5 (bV K r) = bb := by
      simp only [σ5, bV, updL_vars_ne (hbW 4 (by omega)), updL_vars_ne (hbW 3 (by omega)),
        Function.update_self]
    have hv : ∀ w, w < 3 * r + 2 → ∀ i, σ5 (vv w i) = σ (vv w i) := fun w hw i => by
      simp only [σ5, bV]
      rw [updL_vars_ne (by omega), updL_vars_ne (by omega), Function.update_of_ne
        (by rw [Ne, vv_inj]; omega), updL_vars_ne (by omega)]
    have hZ : ∀ i < nF d, σ5 (vv (3 * r + 2) i) = τZ (vv (3 * r + 2) i) := fun i hi => by
      simp only [σ5, bV]
      rw [updL_vars_ne (by omega), updL_vars_ne (by omega), Function.update_of_ne
        (by rw [Ne, vv_inj]; omega), updL_vars_self hi]
    have hX : ∀ i < nF d, σ5 (vv (3 * r + 3) i) = τX (vv (3 * r + 3) i) := fun i hi => by
      simp only [σ5]
      rw [updL_vars_ne (by omega), updL_vars_self hi]
    have hY : ∀ i < nF d, σ5 (vv (3 * r + 4) i) = τY (vv (3 * r + 4) i) := fun i hi => by
      simp only [σ5]
      rw [updL_vars_self hi]
    have hR : ReachV d c (read σ5 (3 * r + 3)) (read σ5 (3 * r + 4)) ↔
        ReachV d c (fun i => τX (vv (3 * r + 3) i)) (fun i => τY (vv (3 * r + 4) i)) :=
      ⟨reachV_congr d c (fun i hi => hX i hi) (fun i hi => hY i hi),
        reachV_congr d c (fun i hi => (hX i hi).symm) (fun i hi => (hY i hi).symm)⟩
    rw [hR, hb]
    refine and_congr_left fun _ => ?_
    have e1 : ∀ w, w < 3 * r + 2 → read σ w = fun i => σ5 (vv w i) :=
      fun w hw => funext fun i => (hv w hw i).symm
    simp only [read]
    refine and_congr (or_congr_right (and_congr ?_ ?_)) (or_congr_right (and_congr ?_ ?_)) <;>
      refine forall₂_congr fun i hi => ?_
    · rw [hX i hi, hv _ (by omega)]
    · rw [hY i hi, hZ i hi]
    · rw [hX i hi, hZ i hi]
    · rw [hY i hi, hv _ (by omega)]

/-! ## The whole formula -/

/-- `X` is the initial state and `Y` a goal state (on bit vectors). -/
def IG (X Y : ℕ → Bool) : Prop :=
  (∀ i < nF d, X i = decide (fI d i ∈ d.init)) ∧ (∀ i < nF d, fI d i ∈ d.goalPos → Y i = true) ∧
    ∀ i < nF d, fI d i ∈ d.goalNeg → Y i = false

theorem ig_congr {X Y X' Y' : ℕ → Bool} (hX : ∀ i < nF d, X i = X' i)
    (hY : ∀ i < nF d, Y i = Y' i) (h : IG d X Y) : IG d X' Y' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i hi => ?_, fun i hi hf => ?_, fun i hi hf => ?_⟩
  · rw [← hX i hi]; exact h1 i hi
  · rw [← hY i hi]; exact h2 i hi hf
  · rw [← hY i hi]; exact h3 i hi hf

theorem sat_initCl (σ : ℕ → Bool) : Sat (initCl d) σ ↔ IG d (read σ 0) (read σ 1) := by
  simp only [initCl, sat_flatMap, sat_append, sat_unit, sat_ite, sat_nil, List.mem_range, IG,
    read, imp_true_iff, and_true]
  constructor
  · intro h
    exact ⟨fun i hi => (h i hi).1.1, fun i hi hf => (h i hi).1.2 hf, fun i hi hf => (h i hi).2 hf⟩
  · rintro ⟨h1, h2, h3⟩ i hi
    exact ⟨⟨h1 i hi, h2 i hi⟩, h3 i hi⟩

/-- **The formula states plan existence on bit vectors** (within `2 ^ n` steps). -/
theorem holds_formula_iff : Holds (formula d) ↔ ∃ X Y, IG d X Y ∧ ReachV d (nF d) X Y := by
  have hst := eval_steps d (nF d) (nF d) 0 (zero_add _)
  simp only [Nat.mul_zero, zero_add] at hst
  have hdisj : ∀ cl ∈ initCl d, ∀ l ∈ cl, ∀ x ∈ steps d (nF d) 0 (nF d) ++ basePre d (nF d),
      l.1 ≠ x.2 := by
    intro cl hcl l hl x hx
    obtain ⟨w, i, hw, hwi⟩ := vars_initCl d cl hcl l hl
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨w', i', hw', hwi'⟩ := vars_steps d (nF d) (nF d) 0 x hx
      rw [hw, hw', Ne, vv_inj]; omega
    · obtain ⟨j, hj⟩ := vars_basePre d (nF d) x hx
      rw [hw, hj, Ne, vv_inj]; omega
  unfold Holds formula
  dsimp only
  rw [eval_exB]
  simp only [eval_exB, eval_append_indep _ hdisj, hst, sat_initCl]
  constructor
  · rintro ⟨τ0, τ1, h1, h2⟩; exact ⟨_, _, h1, h2⟩
  · rintro ⟨X, Y, h1, h2⟩
    refine ⟨fun x => X (Nat.unpair x).2, fun x => Y (Nat.unpair x).2, ?_⟩
    have e0 : ∀ i < nF d, X i = read (updL (vars (nF d) 1) (fun x => Y (Nat.unpair x).2)
        (updL (vars (nF d) 0) (fun x => X (Nat.unpair x).2) fun _ => false)) 0 i := fun i hi => by
      simp only [read]
      rw [updL_vars_ne (by omega), updL_vars_self hi]; simp [vv, Nat.unpair_pair]
    have e1 : ∀ i < nF d, Y i = read (updL (vars (nF d) 1) (fun x => Y (Nat.unpair x).2)
        (updL (vars (nF d) 0) (fun x => X (Nat.unpair x).2) fun _ => false)) 1 i := fun i hi => by
      simp only [read]
      rw [updL_vars_self hi]; simp [vv, Nat.unpair_pair]
    exact ⟨ig_congr d e0 e1 h1, reachV_congr d _ e0 e1 h2⟩

end Savitch

end QBF

end FOND
