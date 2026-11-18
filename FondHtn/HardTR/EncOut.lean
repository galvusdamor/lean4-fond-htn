import FondHtn.HardTR.Enc
/-!
# CB22 Thm 5, P2: the outcomes of the encoded actions

**`FOND.HardTR.TE.out_eq`**: on good states the outcomes of an encoded action are the encodings of
the outcomes of the machine action.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TE

open TL TT HardMP

variable {S : Type} {cS : S → ℕ} {X : Spec S} {allS : List S}

/-! ## Outcomes -/

theorem dkill (b x : ℕ) : (decide (b = x) && !decide (x = b)) = false := by
  by_cases h : b = x <;> simp [h, eq_comm]

theorem dsym (a x : ℕ) : decide (a = x) = decide (x = a) := by
  by_cases h : a = x <;> simp [h, eq_comm]


section Out

variable {r : Rec (Ctl S)}

theorem eff_toCfg {a : ASpec} (ha : a.cnew = []) {e : List ℕ × List ℕ} {r' : Rec (Ctl S)}
    (h : ∀ t x, fv cS r' t x = ((fv cS r t x && !decide (Nat.pair t x ∈ e.2)) ||
      decide (Nat.pair t x ∈ e.1))) :
    a.eff e (toCfg cS r) = toCfg cS r' := by
  refine cfg_ext (fun t x => ?_) ?_
  · simp only [ASpec.eff, val_pair, h]
  · simp [ASpec.eff, ha]

theorem out_single {a : ASpec} (ha : a.cnew = []) {e : List ℕ × List ℕ} (he : a.effs = [e])
    {r' : Rec (Ctl S)} (h : a.eff e (toCfg cS r) = toCfg cS r') {O : Set (Rec (Ctl S))} (hO : O = {r'}) :
    a.Out (toCfg cS r) = toCfg cS '' O := by
  ext c
  simp [ASpec.Out, he, h, hO, eq_comm]

theorem out_wb (hG : Good X r) {p : Bool} {k : ℕ} {b : Bool} (happ : X.mach.app (.wb p k b) r) :
    (aspec cS X allS (.wb p k b)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.wb p k b) r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  obtain ⟨hph, -, -⟩ := happ
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
    simp [fv, fPh, Nat.pair_eq_pair, hph, dkill, dsym, bval]

theorem out_rv {p γ : Bool} (happ : X.mach.app (.rv p γ) r) :
    (aspec cS X allS (.rv p γ)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.rv p γ) r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  obtain ⟨hph, -⟩ := happ
  have hm : X.mach.m = mm X := rfl
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;> cases γ <;>
    simp [fv, fPh, fB, pos, neg, Nat.pair_eq_pair, hph, dkill, dsym, bval, hm] <;>
    rcases x with _ | _ | _ | _ | _ | _ | _ | x <;> simp [bvalT]

theorem out_rb {p : Bool} {k : ℕ} {b : Bool} (happ : X.mach.app (.rb p k b) r) :
    (aspec cS X allS (.rb p k b)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.rb p k b) r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  obtain ⟨hph, -⟩ := happ
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
    simp [fv, fPh, Nat.pair_eq_pair, hph, dkill, dsym, bval]

theorem out_nrd {p : Bool} (happ : X.mach.app (.nrd p) r) :
    (aspec cS X allS (.nrd p)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.nrd p) r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  obtain ⟨hph, -⟩ := happ
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
    simp [fv, fPh, fB, Nat.pair_eq_pair, hph, dkill, dsym, bval] <;>
    rcases x with _ | _ | _ | _ | _ | _ | _ | x <;> simp [bvalT]

theorem out_dr {p : Bool} :
    (aspec cS X allS (.dr p)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.dr p) r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  simp

theorem out_fin (happ : X.mach.app .fin r) :
    (aspec cS X allS .fin).Out (toCfg cS r) = toCfg cS '' X.mach.outs .fin r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  obtain ⟨hph, -⟩ := happ
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
    simp [fv, fPh, Nat.pair_eq_pair, hph, dkill, dsym, bval]

theorem out_inc {p : Bool} {k : ℕ} (happ : X.mach.app (.inc p k) r) :
    (aspec cS X allS (.inc p k)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.inc p k) r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  obtain ⟨hph, -, -, h0, h1⟩ := happ
  have hinc := TOHard2.incF_testBit h1 h0
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t
  · simp [fv, fPh, fC, Nat.pair_eq_pair, hph, dkill, dsym]
  · simp only [fv, fPh, fC]
    rw [← hinc]
    simp only [TOHard2.incF]
    simp only [Nat.pair_eq_pair, true_and, exists_eq_right, List.mem_append, List.mem_cons,
      List.mem_map, List.mem_range, List.not_mem_nil, or_false, fPh, fC]
    by_cases h1 : x < k
    · simp [h1, show x ≠ k by omega]
    · by_cases h2 : x = k
      · subst h2; simp
      · simp [h1, h2]
  all_goals simp [fv, fPh, fC, Nat.pair_eq_pair, bval]

theorem out_wrap (hG : Good X r) {p : Bool} (happ : X.mach.app (.wrap p) r) :
    (aspec cS X allS (.wrap p)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.wrap p) r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  obtain ⟨hph, -, -⟩ := happ
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t
  · simp [fv, fPh, fC, Nat.pair_eq_pair, hph, dkill, dsym]
  · simp only [fv, fPh, fC]
    simp only [Nat.pair_eq_pair, true_and, List.mem_append, List.mem_cons, List.mem_map,
      List.mem_range, List.not_mem_nil, or_false, fPh, fC, exists_eq_right]
    by_cases hx : x < mm X
    · simp [hx]
    · have : r.c.testBit x = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hG.c_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hx, this]
  all_goals simp [fv, fPh, fC, Nat.pair_eq_pair, bval]

theorem ord_kill (o : Ordering) (x : ℕ) :
    (decide (codeOrd o = x) && !decide (x = 0 ∨ x = 1 ∨ x = 2)) = false := by
  cases o <;> by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;>
    simp [codeOrd, h0, h1, h2] <;> omega

theorem gs_absurd (hG : Good X r) {x : ℕ} (h1 : x = codeGs r.g.gs) (h2 : ¬ x = 0)
    (h3 : ∀ a < X.no, ¬ a + 1 = x) : False := by
  cases hgs : r.g.gs with
  | none => rw [hgs] at h1; exact h2 h1
  | some ℓ => rw [hgs] at h1; exact h3 ℓ (hG.gs_lt ℓ hgs) h1.symm

theorem ord_eff (o : Ordering) (w k : Bool) (x : ℕ) :
    decide (x = codeOrd (upd o w k)) =
      ((decide (x = codeOrd o) && (decide (w = k) || !decide (x = codeOrd .lt) &&
        (!decide (x = codeOrd .eq) && !decide (x = codeOrd .gt)))) ||
      !decide (w = k) && decide (x = codeOrd (if w = true then .gt else .lt))) := by
  cases o <;> cases w <;> cases k <;> simp [upd, codeOrd] <;> omega

theorem bvalT_eq {par sym : Bool} {g g' : Ctl S} (h1 : g'.boot = g.boot) (h2 : g'.bo = g.bo)
    (h3 : g'.cy = g.cy) (h4 : g'.dec = g.dec) (h5 : g'.zi = g.zi) (x : ℕ) :
    bvalT par sym g' x = bvalT par sym g x := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | x <;> simp [bvalT, h1, h2, h3, h4, h5]

theorem out_op (hG : Good X r) {p : Bool} {o : Op} (happ : X.mach.app (.op p o) r) :
    (aspec cS X allS (.op p o)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.op p o) r := by
  refine out_single rfl rfl (eff_toCfg rfl fun t x => ?_) rfl
  obtain ⟨hph, -, hok⟩ := happ
  simp only [Spec.mach] at hok ⊢
  cases o with
  | t gs b w =>
    cases gs <;> cases b <;> rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
      simp [fv, fPh, fB, fGs, gsCodes, opSpec, Spec.opEff, Nat.pair_eq_pair, hph, dkill, dsym, bval,
        codeGs]
    all_goals first
      | (rcases x with _ | _ | _ | _ | _ | _ | _ | x <;> simp [bvalT]; done)
      | exact fun h1 h2 h3 => (gs_absurd hG h1 h2 h3).elim
  | i dec b w sp =>
    have hs : ∀ ℓ s, sp = some (ℓ, s) → r.g.s = s := fun ℓ s h => (hok.2.2.2.2.2 ℓ s h).2.1
    cases sp with
    | none =>
      rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
        simp [fv, fPh, fB, fCl, fCh, fSc, clCodes, chCodes, opSpec, Spec.opEff, Nat.pair_eq_pair, hph,
          dkill, dsym, bval]
      all_goals first
        | exact ord_eff _ _ _ _
        | (rcases x with _ | _ | _ | _ | _ | _ | _ | x <;> cases dec <;> cases b <;> cases w <;>
            simp [bvalT]; done)
    | some q =>
      obtain ⟨ℓ, s0⟩ := q
      have hs0 := hs ℓ s0 rfl
      rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
        simp [fv, fPh, fB, fCl, fCh, fSc, clCodes, chCodes, opSpec, Spec.opEff, Nat.pair_eq_pair, hph,
          dkill, dsym, bval, hs0]
      all_goals first
        | exact ord_eff _ _ _ _
        | (rcases x with _ | _ | _ | _ | _ | _ | _ | x <;> cases dec <;> cases b <;> cases w <;>
            simp [bvalT]; done)
  | bt w =>
    rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
      simp [fv, fPh, opSpec, Spec.opEff, Nat.pair_eq_pair, hph, dkill, dsym, bval]
  | bi w =>
    rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
      simp [fv, fPh, opSpec, Spec.opEff, Nat.pair_eq_pair, hph, dkill, dsym, bval]

set_option maxHeartbeats 2000000 in
theorem rst_eff (hall : ∀ s, s ∈ allS) (hG : Good X r) {p : Bool} (hph : r.ph = .fin)
    (σ : S) (cy dec : Bool) {a : ASpec} (ha : a.cnew = []) :
    a.eff ([fPh (.wb 0)] ++ pos (fB 0) (!p) ++ (rstEff cS X allS σ cy dec).1,
        [fPh .fin] ++ neg (fB 0) (!p) ++ (rstEff cS X allS σ cy dec).2) (toCfg cS r) =
      toCfg cS { r with ph := .wb 0, par := !p, g := rst σ cy dec } := by
  refine eff_toCfg ha fun t x => ?_
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;> cases p <;> cases cy <;> cases dec <;>
    simp [fv, fPh, fB, fSg, fGs, fCl, fCh, fSc, rstEff, sgCodes, gsCodes, clCodes, chCodes,
      scCodes, pos, neg, Nat.pair_eq_pair, hph, dkill, dsym, bval, rst]
  all_goals first
    | (rcases x with _ | _ | _ | _ | _ | _ | _ | x <;> simp [bvalT]; done)
    | exact fun h1 h2 => (h2 _ (hall _) h1.symm).elim
    | exact fun h1 h2 h3 => (gs_absurd hG h1 h2 h3).elim
    | (intro h1; cases hc : r.g.cl <;> cases hh : r.g.ch <;> simp_all [codeOrd] <;> omega)
    | (intro h1 h2; have := hG.s_le; omega)


theorem endOut_eq (e : En S) (g : Ctl S) :
    Spec.endOut e g = {g' | ∃ q ∈ (endSpec cS X e).2.2, g' = rst q.1 q.2.1 q.2.2} := by
  cases e with
  | boot σ => ext g'; simp [Spec.endOut, endSpec]
  | norm z l c r' =>
    ext g'
    cases z <;> simp [Spec.endOut, endSpec]

theorem out_rend (hall : ∀ s, s ∈ allS) (hG : Good X r) {p : Bool} {e : En S}
    (happ : X.mach.app (.rend p e) r) :
    (aspec cS X allS (.rend p e)).Out (toCfg cS r) = toCfg cS '' X.mach.outs (.rend p e) r := by
  obtain ⟨hph, hpar, -⟩ := happ
  ext c
  have heffs : (aspec cS X allS (.rend p e)).effs = (endSpec cS X e).2.2.map fun q =>
      ([fPh (.wb 0)] ++ pos (fB 0) (!p) ++ (rstEff cS X allS q.1 q.2.1 q.2.2).1,
        [fPh .fin] ++ neg (fB 0) (!p) ++ (rstEff cS X allS q.1 q.2.1 q.2.2).2) := rfl
  simp only [ASpec.Out, heffs, List.mem_map, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [rst_eff hall hG hph q.1 q.2.1 q.2.2 rfl]
    refine ⟨_, ?_, rfl⟩
    simp only [Spec.mach, Mach.outs, Set.mem_setOf_eq]
    exact ⟨_, by rw [endOut_eq (cS := cS) (X := X)]; exact ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨r', hr', rfl⟩
    simp only [Spec.mach, Mach.outs, Set.mem_setOf_eq] at hr'
    obtain ⟨g', hg', rfl⟩ := hr'
    rw [endOut_eq (cS := cS) (X := X)] at hg'
    obtain ⟨q, hq, rfl⟩ := hg'
    exact ⟨_, ⟨q, hq, rfl⟩, (rst_eff hall hG hph q.1 q.2.1 q.2.2 rfl).symm⟩

/-- **The outcomes agree on good states.** -/
theorem out_eq (hall : ∀ s, s ∈ allS) (hG : Good X r) {a : Act Op (En S)} (happ : X.mach.app a r) :
    (aspec cS X allS a).Out (toCfg cS r) = toCfg cS '' X.mach.outs a r := by
  cases a with
  | wb p k b => exact out_wb hG happ
  | rv p γ => exact out_rv happ
  | rb p k b => exact out_rb happ
  | op p o => exact out_op hG happ
  | inc p k => exact out_inc happ
  | wrap p => exact out_wrap hG happ
  | rend p e => exact out_rend hall hG happ
  | nrd p => exact out_nrd happ
  | dr p => exact out_dr
  | fin => exact out_fin happ

/-- **Good states stay good.** -/
theorem good_out (hX : X.Valid) (hG : Good X r) {a : Act Op (En S)} (happ : X.mach.app a r)
    {r' : Rec (Ctl S)} (hr' : r' ∈ X.mach.outs a r) : Good X r' := by
  have hm : X.mach.m = mm X := rfl
  have hm1 : 1 ≤ mm X := by simp [mm]
  cases a with
  | wb p k b =>
    obtain ⟨hph, -, -⟩ := happ
    have hk := hG.wb_lt k hph
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    refine ⟨hG.c_lt, fun k' h => ?_, fun k' h => ?_, hG.gs_lt, hG.s_le⟩ <;>
      simp only [Mach.nextWb, hm] at h <;> split_ifs at h with h' <;> cases h <;> omega
  | rv p γ =>
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    refine ⟨hG.c_lt, (fun k' h => by cases h), fun k' h => ?_, hG.gs_lt, hG.s_le⟩
    simp only [hm] at h; cases h; omega
  | rb p k b =>
    obtain ⟨hph, -, -⟩ := happ
    have hk := hG.rb_lt k hph
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    refine ⟨hG.c_lt, fun k' h => ?_, fun k' h => ?_, hG.gs_lt, hG.s_le⟩ <;>
      simp only [Mach.nextRb] at h <;> split_ifs at h <;> cases h; omega
  | op p o =>
    obtain ⟨-, -, hok⟩ := happ
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    refine ⟨hG.c_lt, (fun k' h => by cases h), (fun k' h => by cases h), fun ℓ h => ?_, ?_⟩
    · simp only [Spec.mach] at h hok
      cases o with
      | t gs b w =>
        cases gs with
        | none => exact hG.gs_lt ℓ h
        | some ℓ' =>
          obtain rfl : ℓ' = ℓ := by simpa [Spec.opEff] using h
          exact (hok.2.2.2.2 ℓ' rfl).2.1
      | i dec b w sp => exact hG.gs_lt ℓ h
      | bt w => exact hG.gs_lt ℓ h
      | bi w => exact hG.gs_lt ℓ h
    · simp only [Spec.mach] at hok ⊢
      cases o with
      | t gs b w => exact hG.s_le
      | i dec b w sp =>
        cases sp with
        | none => exact hG.s_le
        | some q =>
          obtain ⟨ℓ', s'⟩ := q
          obtain ⟨-, hs, hlt, -⟩ := hok.2.2.2.2.2 ℓ' s' rfl
          simp [Spec.opEff, hs]; omega
      | bt w => exact hG.s_le
      | bi w => exact hG.s_le
  | inc p k =>
    obtain ⟨-, -, hk, h0, h1⟩ := happ
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    refine ⟨?_, fun k' h => ?_, (fun k' h => by cases h), hG.gs_lt, hG.s_le⟩
    · have hne : r.c + 1 ≠ 2 ^ mm X := fun he =>
        absurd ((TOHard2.all_ones_iff hG.c_lt).2 he k (by simpa [hm] using hk)) (by simp [h0])
      have := hG.c_lt
      show r.c + 1 < 2 ^ mm X
      omega
    · cases h; omega
  | wrap p =>
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    exact ⟨Nat.two_pow_pos _, (fun k' h => by cases h), (fun k' h => by cases h), hG.gs_lt, hG.s_le⟩
  | rend p e =>
    simp only [Mach.outs, Set.mem_setOf_eq] at hr'
    obtain ⟨g', hg', rfl⟩ := hr'
    simp only [Spec.mach] at hg'
    rw [endOut_eq (cS := fun _ => 0) (X := X)] at hg'
    obtain ⟨q, -, rfl⟩ := hg'
    exact ⟨hG.c_lt, (fun k' h => by cases h; omega), (fun k' h => by cases h), (fun ℓ h => by cases h),
      by simp [rst]⟩
  | nrd p =>
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    exact ⟨hG.c_lt, (fun k' h => by cases h), (fun k' h => by cases h), hG.gs_lt, hG.s_le⟩
  | dr p =>
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    exact hG
  | fin =>
    simp only [Mach.outs, Set.mem_singleton_iff] at hr'; subst hr'
    exact ⟨hG.c_lt, (fun k' h => by cases h), (fun k' h => by cases h), hG.gs_lt, hG.s_le⟩


end Out

end TE

end HardTR

end FOND
